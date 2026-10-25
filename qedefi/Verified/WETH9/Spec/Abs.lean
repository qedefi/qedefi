import QEDefi.ERC20.Spec.Storage
import QEDefi.ERC20.Spec.Instances.WETH9
import Verified.WETH9.Contracts.WETH9

/-!
# WETH9's storage as the WETH9 token model

`weth9Abs`: the model state of the deployed WETH9 (`Verified.WETH9.Contracts.WETH9`, solc
0.4.19) for a set of actors `Act`, read from its storage (`contracts/mainnet/WETH9/
storageLayout.json`: `balanceOf` is the mapping at slot `3`, `allowance` the nested mapping at
slot `4`; `name`, `symbol`, `decimals` at slots `0`–`2` are not part of the model) and its ether
(`ether` is the contract's balance, which `totalSupply()` returns; there is no supply slot).
The fields of `VState` that WETH9's policies never read are constants. `Sound` is `ActorRows`
for the two mappings: the actors' rows are pairwise distinct (WETH9 has no fixed slot the ERC-20
functions write or read).

Also here: the dispatcher's selectors (`weth9Sel`, from the generated module), the decoder of
the other entry points (`weth9Ops`: `deposit()`, payable, as `Op.deposit caller value`), and the
model's outcomes for WETH9 (`weth9_call_transfer`, …).

`withdraw(wad)` is not decoded: it sends `wad` wei to the caller with a `CALL` that runs the
caller's code (2300-gas stipend), and the model's `Op.withdraw` takes whether that code accepts
the ether as a parameter, which a frame-level decoder cannot know. It stays covered by
`Verified.WETH9.withdraw_halts_refines` (atomic for any gas and any recipient).
-/

namespace Verified.WETH9.Spec
open EvmLean EvmLogic EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.WETH9
open QEDefi.Math Verified.WETH9.Contracts

/-! ## The abstraction -/

/-- The model state of WETH9 at `token` in `w`, for the actors `Act`. -/
noncomputable def weth9Read (crypto : Crypto) (Act : Finset Address) (w : World)
    (token : Address) : VState Address where
  self := token
  bal := readMap crypto Act w token 3
  supply := 0
  allowance := readMap2 crypto Act w token 4
  scale := 1
  admin := 0
  paused := false
  blacklisted := fun _ => false
  feeBps := 0
  feeMax := 0
  ether := (w.balance token).toNat
  frozen := 0
  nonces := 0

/-- The slots `weth9Read` reads: the actors' `balanceOf` rows and the `allowance` rows of pairs
of actors. -/
def weth9Footprint (crypto : Crypto) (Act : Finset Address) (k : Word) : Prop :=
  MapSlots crypto Act 3 k ∨ Map2Slots crypto Act 4 k

/-- **WETH9's storage abstraction.** -/
noncomputable def weth9Abs : TokenAbs (VState Address) where
  read := weth9Read
  footprint := weth9Footprint
  read_congr := by
    intro crypto Act w w' token hk hb
    simp only [weth9Read, hb]
    rw [readMap_congr (fun k h => hk k (.inl h)), readMap2_congr (fun k h => hk k (.inr h))]
  Sound crypto Act := ActorRows crypto Act [3] [4] []

/-- The selectors WETH9's dispatcher knows. -/
def weth9Sel : List Nat := WETH9.selectors.map fun p => p.2.toNat

/-- The selector of `deposit()`. -/
def depositSelector : Nat := 0xd0e30db0

/-- **WETH9's other entry points**: `deposit()` (payable, no arguments; trailing calldata is
ignored) is `Op.deposit caller value`. `withdraw` is left out (see the module docstring). -/
def weth9Ops (caller : Address) (data : ByteArray) (value : ℕ) : Option (Variant.Op Address) :=
  if 4 ≤ data.size ∧ Abi.selectorOf data = depositSelector then some (.deposit caller value)
  else none

/-- The accounts a decoded operation names: `deposit` names only its caller. -/
def weth9OpAddrs : Variant.Op Address → List Address
  | .deposit c _ => [c]
  | _ => []

theorem weth9Model_wf (s : VState Address) :
    (weth9Model : TokenModel (VState Address) Address (Variant.Op Address)).wf s ↔
      total s.bal ≤ s.ether := by
  simp [weth9Model, Variant.WF, Variant.weth9, Variant.standard]

end Verified.WETH9.Spec
