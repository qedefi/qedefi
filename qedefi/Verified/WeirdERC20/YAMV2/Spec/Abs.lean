import QEDefi.ERC20.Spec.Storage
import QEDefi.ERC20.Spec.Instances.YAMV2
import Verified.WeirdERC20.YAMV2.Contracts.YAMV2

/-!
# YAMv2: the bytecode spec statement

The data `ERC20Spec` is applied to for YAMv2 (`contracts/mainnet/YAMV2/`): the storage
abstraction `abs` (layout from `storageLayout.json`, checked against mainnet in
`layout-check.txt`), the dispatcher's selectors `sel`, the decoder `ops` of `mint`,
`increaseAllowance` and `decreaseAllowance`, the gas bound `g₀`, and `yamv2Spec`, the
statement the bytecode proofs target. The model is `QEDefi.ERC20.Spec.YAMV2.model`.

Layout: `minter` at slot 0, `_balances` at 1, `_allowances` at 2, `_totalSupply` at 3,
`_name`, `_symbol`, `_decimals` at 4, 5, 6 (not part of the model: no entry point writes them,
so `FrameKeeps` pins them).
-/

namespace Verified.WeirdERC20.YAMV2.Spec
open EvmLean EvmLogic EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec

/-- The slot of `minter`. -/
def minterSlot : Word := 0
/-- The slot of `_balances`. -/
def balancesSlot : Word := 1
/-- The slot of `_allowances`. -/
def allowancesSlot : Word := 2
/-- The slot of `_totalSupply`. -/
def supplySlot : Word := 3

/-- YAMv2 as the actors `Act` see it: their balances and allowances, the supply, and the minter
(`admin`, the low 160 bits of slot 0, as solc reads an `address`); `self` is the token, the
other fields of `VState` are unused. -/
noncomputable def read (crypto : Crypto) (Act : Finset Address) (w : World) (token : Address) :
    VState Address :=
  VState.ofToken ⟨readMap crypto Act w token balancesSlot, readSlot w token supplySlot,
    readMap2 crypto Act w token allowancesSlot⟩ token (Word.toAddress (w.sload token minterSlot))

/-- The slots `read` depends on. -/
def footprint (crypto : Crypto) (Act : Finset Address) (k : Word) : Prop :=
  k = minterSlot ∨ k = supplySlot ∨ MapSlots crypto Act balancesSlot k ∨
    Map2Slots crypto Act allowancesSlot k

/-- **YAMv2's storage abstraction.** `Sound`: the actors' rows of `_balances` and
`_allowances` are pairwise distinct and none is a declared slot (`0 … 6`). -/
noncomputable def abs : TokenAbs (VState Address) where
  read := read
  footprint := footprint
  read_congr := by
    intro crypto Act w w' token h _
    simp only [read]
    rw [readMap_congr (fun k hk => h k (Or.inr (Or.inr (Or.inl hk)))),
      readSlot_congr (h _ (Or.inr (Or.inl rfl))),
      readMap2_congr (fun k hk => h k (Or.inr (Or.inr (Or.inr hk)))),
      h _ (Or.inl rfl)]
  Sound crypto Act :=
    ActorRows crypto Act [balancesSlot] [allowancesSlot] [0, 1, 2, 3, 4, 5, 6]

/-- The dispatcher's selectors (the verified ABI). -/
def sel : List Nat := Contracts.YAMV2.selectors.map (·.2.toNat)

/-- The `i`-th static argument word of the calldata. -/
def argWord (data : ByteArray) (i : ℕ) : Word := Bytes.toWord (Interpreter.readBytes data (4 + 32 * i) 32)

/-- The `i`-th argument as an address, if its upper 96 bits are clear (clean ABI encoding;
dirty words are `MalformedSpec`'s concern). -/
def addrArg (data : ByteArray) (i : ℕ) : Option Address :=
  if Word.ofAddress (Word.toAddress (argWord data i)) = argWord data i then
    some (Word.toAddress (argWord data i))
  else none

/-- **The other entry points**, ABI-encoded with clean arguments and no value (all three are
non-payable): `mint(address,uint256)`, `increaseAllowance(address,uint256)`,
`decreaseAllowance(address,uint256)`. -/
def ops (caller : Address) (data : ByteArray) (value : ℕ) : Option (YAMV2.Op Address) :=
  if value ≠ 0 ∨ data.size < 4 + 32 * 2 then none
  else match addrArg data 0 with
    | none => none
    | some a =>
      let x := (argWord data 1).toNat
      if Abi.selectorOf data = 0x40c10f19 then some (.mint caller a x)
      else if Abi.selectorOf data = 0x39509351 then some (.increaseAllowance caller a x)
      else if Abi.selectorOf data = 0xa457c2d7 then some (.decreaseAllowance caller a x)
      else none

/-- The account each operation names besides its caller: the recipient of `mint`, the spender
of the allowance helpers. -/
def opAddrs : YAMV2.Op Address → List Address
  | .mint _ d _ => [d]
  | .increaseAllowance _ sp _ => [sp]
  | .decreaseAllowance _ sp _ => [sp]

/-- The gas from which every outcome is exact: a `transferFrom` writes three rows (at most
`3 · 22100` gas for fresh nonzero slots) and two logs; `mint` two slots and a log;
`100000` covers each with room for the dispatcher and the ABI decoding. -/
def g₀ : Nat := 100000

/-- **The bytecode spec of YAMv2**: the deployed runtime code is the YAMv2 model through
`abs`. -/
abbrev yamv2Spec : Prop :=
  ERC20Spec Contracts.YAMV2.runtimeCode abs
    (QEDefi.ERC20.Spec.YAMV2.model : TokenModel (VState Address) Address (YAMV2.Op Address))
    g₀ sel ops opAddrs

end Verified.WeirdERC20.YAMV2.Spec
