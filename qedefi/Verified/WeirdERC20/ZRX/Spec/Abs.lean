import QEDefi.ERC20.Spec.Storage
import QEDefi.ERC20.Spec.Instances.ZRX
import Verified.WeirdERC20.ZRX.Contracts.ZRX

/-!
# ZRX: the bytecode spec statement

The data `ERC20Spec` is applied to for ZRX (`contracts/mainnet/ZRX/`): the storage abstraction
`abs` (layout from `storageLayout.json`, checked against mainnet in `layout-check.txt`), the
dispatcher's selectors `sel`, the (empty) decoder of other entry points, the gas bound `g₀`,
and `zrxSpec`, the statement the bytecode proofs target. The model is
`QEDefi.ERC20.Spec.ZRX.model`.

Layout: `balances` at slot 0, `allowed` at slot 1, `ZRXToken.totalSupply` at slot 3. Slot 2 is
the shadowed `StandardToken.totalSupply`: never written, never read by the runtime code (the
getter reads slot 3), so it is not in the footprint and `FrameKeeps` pins it.
-/

namespace Verified.WeirdERC20.ZRX.Spec
open EvmLean EvmLogic EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec

/-- The slot of `balances`. -/
def balancesSlot : Word := 0
/-- The slot of `allowed`. -/
def allowedSlot : Word := 1
/-- The slot of `ZRXToken.totalSupply` (the one the getter reads). -/
def supplySlot : Word := 3

/-- ZRX as the actors `Act` see it: their balances and allowances, the supply of slot 3; the
other fields of `VState` are unused (`self` is the token, `admin` is `0`). -/
noncomputable def read (crypto : Crypto) (Act : Finset Address) (w : World) (token : Address) :
    VState Address :=
  VState.ofToken ⟨readMap crypto Act w token balancesSlot, readSlot w token supplySlot,
    readMap2 crypto Act w token allowedSlot⟩ token 0

/-- The slots `read` depends on: the supply slot and the actors' rows. -/
def footprint (crypto : Crypto) (Act : Finset Address) (k : Word) : Prop :=
  k = supplySlot ∨ MapSlots crypto Act balancesSlot k ∨ Map2Slots crypto Act allowedSlot k

/-- **ZRX's storage abstraction.** `Sound`: the actors' rows of `balances` and `allowed` are
pairwise distinct and none is a declared slot (`0 … 3`). -/
noncomputable def abs : TokenAbs (VState Address) where
  read := read
  footprint := footprint
  read_congr := by
    intro crypto Act w w' token h _
    simp only [read]
    rw [readMap_congr (fun k hk => h k (Or.inr (Or.inl hk))),
      readSlot_congr (h _ (Or.inl rfl)),
      readMap2_congr (fun k hk => h k (Or.inr (Or.inr hk)))]
  Sound crypto Act := ActorRows crypto Act [balancesSlot] [allowedSlot] [0, 1, 2, 3]

/-- The dispatcher's selectors (the verified ABI). -/
def sel : List Nat := Contracts.ZRX.selectors.map (·.2.toNat)

/-- ZRX has no other entry point. -/
def ops (_caller : Address) (_data : ByteArray) (_value : ℕ) : Option Empty := none

/-- No operation names an account. -/
def opAddrs : Empty → List Address := fun e => e.elim

/-- The gas from which every outcome is exact: a `transferFrom` writes three rows (at most
`3 · 22100` gas for fresh nonzero slots) and one log; `100000` covers it with room for the
dispatcher. -/
def g₀ : Nat := 100000

/-- **The bytecode spec of ZRX**: the deployed runtime code is the ZRX model through `abs`. -/
abbrev zrxSpec : Prop :=
  ERC20Spec Contracts.ZRX.runtimeCode abs
    (QEDefi.ERC20.Spec.ZRX.model : TokenModel (VState Address) Address Empty) g₀ sel ops opAddrs

end Verified.WeirdERC20.ZRX.Spec
