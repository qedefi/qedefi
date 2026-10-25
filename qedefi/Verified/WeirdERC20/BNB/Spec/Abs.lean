import QEDefi.ERC20.Spec.Storage
import QEDefi.ERC20.Spec.Instances.BNB
import Verified.WeirdERC20.BNB.Contracts.BNB

/-!
# BNB under the ERC-20 spec: the abstraction and the statement

`bnbSpec : Prop` is `ERC20Spec` for the mainnet BNB runtime code (solc 0.4.12, unoptimised)
against `bnbModel` (`QEDefi.ERC20.Spec.Instances.BNB`), through `bnbAbs`.

**Storage** (`contracts/mainnet/BNB/storageLayout.json`): `name` 0, `symbol` 1, `decimals` 2,
`totalSupply` 3, `owner` 4 (an address in the low 160 bits), `balanceOf` 5, `freezeOf` 6,
`allowance` 7. The model state, for the actors `Act`: their balances (`balanceOf`), their
frozen balances (`freezeOf`), the allowances between them, the supply, the owner as the
privileged account (`admin`, who alone may `withdrawEther`), and the token's ether balance
(the payable fallback keeps what it receives). The fields BNB does not have are constants.

`bnbSound crypto Act`: the actors' rows of `balanceOf`, `freezeOf` and `allowance` are pairwise
distinct and avoid the `totalSupply` and `owner` slots (`ActorRows`).

**Other entry points** (`bnbOps`): `burn(v)`, `freeze(v)`, `unfreeze(v)` with one argument
word and no value (they are not payable). `withdrawEther(v)` is not decoded: its outcome
depends on the owner's code accepting the ether (`Variant.Op.withdrawEther … sendOk`), which no
decoder of the calldata can know.
-/

namespace Verified.WeirdERC20.BNB.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec
open QEDefi.ERC20.Spec.BNB Verified.WeirdERC20.BNB.Contracts

/-- The model state of BNB at `token` in `w`, for the actors `Act`. -/
noncomputable def bnbRead (crypto : Crypto) (Act : Finset Address) (w : World)
    (token : Address) : VState Address where
  self := token
  bal := readMap crypto Act w token 5#256
  supply := readSlot w token 3#256
  allowance := readMap2 crypto Act w token 7#256
  scale := 1
  admin := (w.sload token 4#256).toAddress
  paused := false
  blacklisted := fun _ => false
  feeBps := 0
  feeMax := 0
  ether := (w.balance token).toNat
  frozen := readMap crypto Act w token 6#256
  nonces := 0

/-- The slots `bnbRead` reads: `totalSupply`, `owner` and the actors' rows. -/
def bnbFootprint (crypto : Crypto) (Act : Finset Address) (k : Word) : Prop :=
  k = 3#256 ∨ k = 4#256 ∨ MapSlots crypto Act 5#256 k ∨ MapSlots crypto Act 6#256 k ∨
    Map2Slots crypto Act 7#256 k

/-- The hash hypotheses: the actors' rows are distinct and avoid the fixed slots. -/
def bnbSound (crypto : Crypto) (Act : Finset Address) : Prop :=
  ActorRows crypto Act [5#256, 6#256] [7#256] [3#256, 4#256]

theorem bnbRead_congr (crypto : Crypto) (Act : Finset Address) (w w' : World) (token : Address)
    (h : ∀ k, bnbFootprint crypto Act k → w'.sload token k = w.sload token k)
    (hb : w'.balance token = w.balance token) :
    bnbRead crypto Act w' token = bnbRead crypto Act w token := by
  unfold bnbRead
  rw [readMap_congr (fun k hk => h k (.inr (.inr (.inl hk)))),
    readMap_congr (fun k hk => h k (.inr (.inr (.inr (.inl hk))))),
    readMap2_congr (fun k hk => h k (.inr (.inr (.inr (.inr hk))))),
    readSlot_congr (h _ (.inl rfl)), h _ (.inr (.inl rfl)), hb]

/-- **The storage abstraction of BNB.** -/
noncomputable def bnbAbs : TokenAbs (VState Address) where
  read := bnbRead
  footprint := bnbFootprint
  read_congr := bnbRead_congr
  Sound := bnbSound

/-! ## The statement -/

/-- The model. -/
noncomputable abbrev M : TokenModel (VState Address) Address (Variant.Op Address) := bnbModel

/-- The gas from which every obligation is exact. -/
def g₀ : Nat := 100000

/-- The dispatcher's selectors (`BNB.selectors`). -/
def sel : List Nat := BNB.selectors.map (·.2.toNat)

/-- The `i`-th argument word of `data`. -/
def argWord (data : ByteArray) (i : Nat) : Word := Bytes.toWord (readBytes data (4 + 32 * i) 32)

/-- **The other entry points**: `burn(v)`, `freeze(v)`, `unfreeze(v)` of the caller, one
argument word, no value. -/
def bnbOps (caller : Address) (data : ByteArray) (value : ℕ) : Option (Variant.Op Address) :=
  if value ≠ 0 ∨ data.size < 36 then none
  else if Abi.selectorOf data = 0x42966c68 then some (.burn caller caller (argWord data 0).toNat)
  else if Abi.selectorOf data = 0xd7a78db8 then some (.freeze caller (argWord data 0).toNat)
  else if Abi.selectorOf data = 0x6623fc46 then some (.unfreeze caller (argWord data 0).toNat)
  else none

/-- The accounts an operation names (only the caller, already an actor). -/
def bnbOpAddrs : Variant.Op Address → List Address
  | .burn _ a _ => [a]
  | _ => []

/-- **The bytecode spec of BNB.** -/
abbrev bnbSpec : Prop := ERC20Spec BNB.runtimeCode bnbAbs M g₀ sel bnbOps bnbOpAddrs

end Verified.WeirdERC20.BNB.Spec
