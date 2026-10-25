import QEDefi.ERC20.Spec.Storage
import QEDefi.ERC20.Spec.Instances.STA
import Verified.WeirdERC20.STA.Contracts.STA

/-!
# STA (Statera) under the ERC-20 spec: the abstraction and the statement

`staSpec : Prop` is `ERC20Spec` for the mainnet Statera runtime code (solc 0.5.0) against
`staModel` (`QEDefi.ERC20.Spec.Instances.STA`), through `staAbs`.

**Storage** (`contracts/mainnet/STA/storageLayout.json`): `_name` 0, `_symbol` 1, `_decimals` 2,
`_balances` 3, `_allowed` 4, `_totalSupply` 5, `basePercent` 6. The model state, for the actors
`Act`: their balances, the allowances between them, the supply; the fields Statera does not have
are constants, `ether` is the token's balance.

**`basePercent`.** The model's fee is `⌈v/100⌉` (`FeeRule.ceilPercent 100`): it fixes
`basePercent = 100`, which the constructor stores and no function changes. The code reads slot
6 on every transfer, so a world whose slot 6 holds anything else is not a state of the model:
`staRead` maps it to a supply above `MAX`, outside the model's invariant (`Variant.WF`), which
every obligation assumes (`Start.wf`). Such worlds are unreachable from the deployment.

`staSound crypto Act`: the actors' rows of `_balances` and `_allowed` are pairwise distinct and
avoid slots 5 and 6 (`ActorRows`).

**Other entry points** (`staOps`): `destroy(v)`, `destroyFrom(src, v)`, `upAllowance(sp, x)`,
`downAllowance(sp, x)`, with clean address arguments and no value.
-/

namespace Verified.WeirdERC20.STA.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec
open QEDefi.ERC20.Spec.STA Verified.WeirdERC20.STA.Contracts

/-- The model state of Statera at `token` in `w`, for the actors `Act` (a supply above `MAX`
when `basePercent ≠ 100`, see the module docstring). -/
noncomputable def staRead (crypto : Crypto) (Act : Finset Address) (w : World)
    (token : Address) : VState Address where
  self := token
  bal := readMap crypto Act w token 3#256
  supply := if readSlot w token 6#256 = 100 then readSlot w token 5#256 else QEDefi.Math.MAX + 1
  allowance := readMap2 crypto Act w token 4#256
  scale := 1
  admin := 0
  paused := false
  blacklisted := fun _ => false
  feeBps := 0
  feeMax := 0
  ether := (w.balance token).toNat
  frozen := 0
  nonces := 0

/-- The slots `staRead` reads: `_totalSupply`, `basePercent` and the actors' rows. -/
def staFootprint (crypto : Crypto) (Act : Finset Address) (k : Word) : Prop :=
  k = 5#256 ∨ k = 6#256 ∨ MapSlots crypto Act 3#256 k ∨ Map2Slots crypto Act 4#256 k

/-- The hash hypotheses: the actors' rows are distinct and avoid the fixed slots. -/
def staSound (crypto : Crypto) (Act : Finset Address) : Prop :=
  ActorRows crypto Act [3#256] [4#256] [5#256, 6#256]

theorem staRead_congr (crypto : Crypto) (Act : Finset Address) (w w' : World) (token : Address)
    (h : ∀ k, staFootprint crypto Act k → w'.sload token k = w.sload token k)
    (hb : w'.balance token = w.balance token) :
    staRead crypto Act w' token = staRead crypto Act w token := by
  unfold staRead
  rw [readMap_congr (fun k hk => h k (.inr (.inr (.inl hk)))),
    readMap2_congr (fun k hk => h k (.inr (.inr (.inr hk)))),
    readSlot_congr (h _ (.inl rfl)), readSlot_congr (h _ (.inr (.inl rfl))), hb]

/-- **The storage abstraction of Statera.** -/
noncomputable def staAbs : TokenAbs (VState Address) where
  read := staRead
  footprint := staFootprint
  read_congr := staRead_congr
  Sound := staSound

/-! ## The statement -/

/-- The model. -/
noncomputable abbrev M : TokenModel (VState Address) Address (Variant.Op Address) := staModel

/-- The gas from which every obligation is exact. `transferFrom` makes four `SSTORE`s and two
`LOG3`s after up to eight `SLOAD`s; with each access priced at its cold worst case that exceeds
`100000`, so the bound is `200000` (a larger `g₀` only weakens the obligations). -/
def g₀ : Nat := 200000

/-- The dispatcher's selectors (`STA.selectors`). -/
def sel : List Nat := STA.selectors.map (·.2.toNat)

/-- The `i`-th argument word of `data`. -/
def argWord (data : ByteArray) (i : Nat) : Word := Bytes.toWord (readBytes data (4 + 32 * i) 32)

/-- An address argument word, if it is clean. -/
def addrArg (x : Word) : Option Address := if x.toNat < 2 ^ 160 then some x.toAddress else none

/-- **The other entry points**: `destroy(v)`, `destroyFrom(src, v)`, `upAllowance(sp, x)`,
`downAllowance(sp, x)`, well-formed arguments, no value. -/
def staOps (caller : Address) (data : ByteArray) (value : ℕ) : Option (Variant.Op Address) :=
  if value ≠ 0 ∨ data.size < 36 then none
  else if Abi.selectorOf data = 0x9d118770 then some (.burn caller caller (argWord data 0).toNat)
  else if data.size < 68 then none
  else if Abi.selectorOf data = 0x33393efa then
    (addrArg (argWord data 0)).map fun a => .burnFrom caller a (argWord data 1).toNat
  else if Abi.selectorOf data = 0xe5981a42 then
    (addrArg (argWord data 0)).map fun a => .adjustAllowance caller a true (argWord data 1).toNat
  else if Abi.selectorOf data = 0xdf401a96 then
    (addrArg (argWord data 0)).map fun a => .adjustAllowance caller a false (argWord data 1).toNat
  else none

/-- The accounts an operation names. -/
def staOpAddrs : Variant.Op Address → List Address
  | .burn _ a _ => [a]
  | .burnFrom _ a _ => [a]
  | .adjustAllowance _ a _ _ => [a]
  | _ => []

/-- **The bytecode spec of Statera.** -/
abbrev staSpec : Prop := ERC20Spec STA.runtimeCode staAbs M g₀ sel staOps staOpAddrs

end Verified.WeirdERC20.STA.Spec
