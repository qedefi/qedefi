import Verified.WeirdERC20.USDT.Spec.ViewTotalSupply
import Verified.WeirdERC20.USDT.Spec.ViewBalanceOf
import Verified.WeirdERC20.USDT.Spec.ViewAllowance

/-!
# USDT's views satisfy `ViewSpec`

`totalSupply()`, `balanceOf(a)` and `allowance(o, sp)` of mainnet `TetherToken`, in every frame
`Start` admits, at any gas and with any value: with no value they return slot 1, `a`'s
`balances` row, the `allowed[o][sp]` row (the code first checks `deprecated`, which is false in
a live token, and then reads its own storage) and change nothing; with value they revert at
the non-payable check; below `g₀` they may also fail.

The symbolic runs are of the lift (`*_high`); `halts_of_high` gives the frame's end
(`usdt_totalSupply`, `usdt_balanceOf`, `usdt_allowance`, and `usdt_views` for every view).
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Verified.WeirdERC20.USDT.Contracts EvmLogic.Program.Nested EvmLogic.GasMono
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.Math

/-- **`ViewSpec` for `totalSupply()`.** -/
theorem usdt_totalSupply : ViewSpec USDT.runtimeCode usdtAbs M g₀ .totalSupply := by
  intro Act m hs hv _
  obtain ⟨hsel, hsize, -⟩ := hv
  refine viewSpec_of_out hs (fun hval => ?_)
    (totalSupply_high m hs.fresh _ (by omega) hsel (by simpa using hsize) hs.size
      (dep_of_start hs))
  rw [(live_of_start hs).2, world_of_start hs hval]
  rfl

/-- **`ViewSpec` for `balanceOf(a)`.** -/
theorem usdt_balanceOf (a : Address) : ViewSpec USDT.runtimeCode usdtAbs M g₀ (.balanceOf a) := by
  intro Act m hs hv ha
  obtain ⟨hsel, hsize, harg⟩ := hv
  have ha' : a ∈ Act := ha a (by simp [View.addrs])
  refine viewSpec_of_out hs (fun hval => ?_)
    (balanceOf_high m hs.fresh _ a (by omega) hsel (by simpa using hsize) hs.size
      (harg 0 (by simp)) (dep_of_start hs))
  rw [(live_of_start hs).2, world_of_start hs hval]
  simp [View.value, readState, ha']

/-- **`ViewSpec` for `allowance(o, sp)`.** -/
theorem usdt_allowance (o sp : Address) :
    ViewSpec USDT.runtimeCode usdtAbs M g₀ (.allowance o sp) := by
  intro Act m hs hv ha
  obtain ⟨hsel, hsize, harg⟩ := hv
  have ho : o ∈ Act := ha o (by simp [View.addrs])
  have hsp : sp ∈ Act := ha sp (by simp [View.addrs])
  refine viewSpec_of_out hs (fun hval => ?_)
    (allowance_high m hs.fresh _ o sp (by omega) hsel (by simpa using hsize) hs.size
      (harg 0 (by simp)) (harg 1 (by simp)) (dep_of_start hs))
  rw [(live_of_start hs).2, world_of_start hs hval]
  simp [View.value, readState, readMap2, ho, hsp]

/-- **USDT's three views satisfy `ViewSpec`.** -/
theorem usdt_views (v : View) : ViewSpec USDT.runtimeCode usdtAbs M g₀ v := by
  cases v with
  | balanceOf a => exact usdt_balanceOf a
  | allowance o sp => exact usdt_allowance o sp
  | totalSupply => exact usdt_totalSupply

end Verified.WeirdERC20.USDT.Spec
