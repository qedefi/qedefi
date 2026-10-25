import Verified.Solmate.ERC20.Spec.SubCert
import Verified.Solmate.ERC20.Spec.LowGas
import Verified.Solmate.ERC4626.LowGas.Certify

/-!
# The asset reads no gas outside `permit`

The asset's only instructions reading the gas are `GAS` and `STATICCALL` at pcs 1630 and 1631
(`ecrecover` in `permit`). A frame that passes through one of the *targets* (the entries of the
other functions, and the dispatcher's `REVERT`s) never executes them before its exit
(`noGasRead_of_steps`), whatever the code at the precompile address `0x01` (an EIP-7702
delegation there would make the `STATICCALL` start a child, which `AssetHigh`'s
`EcrecoverOk` excludes; here it needs no exclusion):

* every machine of the frame is described by the whole code's table `t0` (`asset_certify`), at
  pcs whose bytes read no gas except 1630 and 1631 (`t0_check`);
* from the table's states at 1630 and 1631, no target is reachable (`tP_check`); so a frame at
  1630 or 1631 before its target cannot reach the target;
* from the table's states at the targets, neither 1630 nor 1631 is reachable (`tT_check`).
-/

namespace Verified.Solmate.ERC20.Spec
open EvmLean EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested EvmLogic.GasMono
open EvmLogic.AbsInt Verified.Solmate.Contracts Verified.Solmate.ERC4626.LowGas

/-- The whole code's table (from pc `0`). -/
def t0 : Tree := (certify assetTargets SolmateAsset.runtimeCode [] [] certFuel).getD .leaf

/-- The function entries and dispatcher `REVERT`s the frames below pass through: `transfer`
515, `transferFrom` 321, `approve` 263, `balanceOf` 426, `allowance` 553, `totalSupply` 298,
`mint` 405, `burn` 496; the `REVERT`s of a call with value (14), and of unknown selectors and
short calldata (98, 135, 194, 232). -/
def targets : List Nat := [515, 321, 263, 426, 553, 298, 405, 496, 14, 98, 135, 194, 232]

/-- The pcs reading the gas. -/
def gasPcs : List Nat := [1630, 1631]

/-- The table explored from `t0`'s states at the pcs reading the gas. -/
def tP : Tree := (subcert SolmateAsset.runtimeCode t0 gasPcs certFuel).getD .leaf

/-- The table explored from `t0`'s states at the targets. -/
def tT : Tree := (subcert SolmateAsset.runtimeCode t0 targets certFuel).getD .leaf

/-- A byte whose instruction may read the gas. -/
def readsGasByte (b : UInt8) : Bool := b == 0x5a || isCallByteB b

/-- `q` lies in an immutable's window of the code. -/
def inWindow (q : Nat) : Bool := [1063, 1116, 345].any fun o => o ≤ q && q < o + 32

/-- **The kernel checks**: the explorations succeed, `t0`'s pcs lie outside the immutables and
read no gas except at 1630 and 1631, the targets are not reachable from those, and those are
not reachable from the targets. -/
def checks : Bool :=
  (subcert SolmateAsset.runtimeCode t0 gasPcs certFuel).isSome &&
  (subcert SolmateAsset.runtimeCode t0 targets certFuel).isSome &&
  (recorded t0).all (fun q => !inWindow q &&
    (gasPcs.contains q || !readsGasByte (Bytes.getD SolmateAsset.runtimeCode q))) &&
  targets.all (fun q => !(recorded tP).contains q) &&
  gasPcs.all (fun q => !(recorded tT).contains q)

theorem checks_ok : checks = true := by kernel_decide

end Verified.Solmate.ERC20.Spec
