import Verified.WETH9.Spec.Fallback
import Verified.WETH9.Spec.Abs
import QEDefi.Solvency.Bank

/-!
# WETH9's `deposit()` refutes `OpSpec`

`opSpec_false`: `OpSpec` fails for WETH9 with the decoder `weth9Ops` (`deposit()` as
`Op.deposit caller value`), whatever the gas `g₀`. Its model state is read in the frame's
snapshot (`pre`), before the value moved, and `Op.deposit` adds the value to the ether; the
bytecode's ether after the frame is what `transferValue` left. When the caller is the token itself
(`caller = currentTarget`, value `≠ 0`, the value moved), `moveEther` from an account to itself
leaves its balance, so the token's ether after the deposit is its snapshot ether, not that plus
the value. `Start` admits such a frame (WETH9 never calls itself and EIP-3607 keeps an account
with code from sending transactions, so it does not occur on chain); the frame is a
counterexample to the spec as stated, not to WETH9. (A second one, not formalised here: a
snapshot balance with `balance + value ≥ 2²⁵⁶`, where the `Word` balance wraps in `transferValue`
and the model's `ℕ` ether does not.)
-/

namespace Verified.WETH9.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
open EvmLogic.GasMono EvmLogic.Solidity Verified.WETH9.Contracts
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.WETH9

/-- The world a finished top-level message call reports. -/
theorem world_finish_top {mf : Machine} {out : ByteArray} {ko ks : Nat}
    (hp : mf.parents = []) (hk : mf.frame.kind = .call ko ks) :
    ∃ r, finishFrame mf (.success out) = .done r ∧ r.world = mf.world := by
  rw [finishFrame_of_top _ hp, frameResult_success_call hk]
  refine ⟨_, rfl, ?_⟩
  simp [topLevelResult, ChildResult.success]

/-- **`OpSpec` is false for WETH9**: a `Start` frame at the top level, of a message call that
moves a nonzero value from the token to itself, non-static, with `deposit()` calldata and gas at
least `g₀` and `50000`, contradicts it. -/
theorem opSpec_false {g₀ : Nat}
    (hO : OpSpec WETH9.runtimeCode weth9Abs weth9Model g₀ weth9Ops weth9OpAddrs)
    {Act : Finset Address} {m : Machine} (hS : Start WETH9.runtimeCode weth9Abs weth9Model Act m)
    (hp : m.parents = []) {ko ks : Nat} (hk : m.frame.kind = .call ko ks)
    (hsel : Abi.selectorOf m.frame.msg.data = depositSelector) (hsize : 4 ≤ m.frame.msg.data.size)
    (hst : m.frame.msg.isStatic = false) (hg₀ : g₀ ≤ m.frame.gasLeft)
    (hg : 50000 ≤ m.frame.gasLeft) (hself : m.frame.msg.caller = m.frame.msg.currentTarget)
    (hv : m.frame.msg.value ≠ 0) (htv : m.frame.msg.shouldTransferValue = true) : False := by
  have hdec : weth9Ops m.frame.msg.caller m.frame.msg.data m.frame.msg.value.toNat =
      some (.deposit m.frame.msg.caller m.frame.msg.value.toNat) := by
    simp [weth9Ops, hsize, hsel]
  have h1 := hO Act m _ hS hdec (by simpa [weth9OpAddrs] using hS.caller)
  have h2 : Halts m (fun mf o => o = .success .empty ∧ mf.world = m.world.sstore
      m.frame.msg.currentTarget (mappingSlot m.ctx.crypto (Word.ofAddress m.frame.msg.caller) 3)
      (m.world.sload m.frame.msg.currentTarget
        (mappingSlot m.ctx.crypto (Word.ofAddress m.frame.msg.caller) 3) + m.frame.msg.value)) :=
    halts_of_low (g₀ := 50000) hS.fresh (fun h => absurd hg h) (fun _ _ _ _ _ h => h)
      fun g hg' => deposit_low hsel hsize hS.size (by omega)
        (fun h => by rw [hst] at h; cases h) fun _ mf hw _ _ _ => ⟨rfl, hw⟩
  obtain ⟨n, mf, o, hex, mf1, o1, hP1, hs1, hf1⟩ := exit_of_halts_top hp h1
  obtain ⟨n', mf', o', hex', mf2, o2, hP2, hs2, hf2⟩ := exit_of_halts_top hp h2
  obtain ⟨rfl, rfl, rfl⟩ := hex.unique hex'
  obtain ⟨rfl, hw2⟩ := hP2
  -- the spec's side: the ether after the deposit is the snapshot's plus the value
  have hP1' : ∃ out, o1 = .success out ∧
      (mf1.world.balance m.frame.msg.currentTarget).toNat =
        (m.frame.snapshot.1.balance m.frame.msg.currentTarget).toNat + m.frame.msg.value.toNat := by
    rcases hP1 with hM | ⟨hfo, hn⟩
    · simp only [OpMatches, weth9Model, Variant.model_op, Variant.stepOp, Variant.deposit,
        Variant.weth9, Variant.standard, ↓reduceIte] at hM
      obtain ⟨⟨out, ho⟩, hr, -⟩ := hM
      refine ⟨out, ho, ?_⟩
      have := congrArg VState.ether hr
      simpa [weth9Abs, weth9Read, pre] using this
    · exact absurd ⟨hg₀, hst⟩ hn
  obtain ⟨out, rfl, hb1⟩ := hP1'
  have hk1 : mf1.frame.kind = .call ko ks := hs1.kind.trans hk
  have hk2 : mf2.frame.kind = .call ko ks := hs2.kind.trans hk
  obtain ⟨r1, hr1, hw1⟩ := world_finish_top (out := out) (hs1.parents.trans hp) hk1
  obtain ⟨r2, hr2, hw2'⟩ := world_finish_top (out := .empty) (hs2.parents.trans hp) hk2
  have h12 : StepResult.done r1 = StepResult.done r2 :=
    hr1.symm.trans (hf1.trans (hf2.symm.trans hr2))
  injection h12 with h12
  subst h12
  -- the bytecode's side: the self-transfer left the ether
  have hb2 : mf2.world.balance m.frame.msg.currentTarget =
      m.frame.snapshot.1.balance m.frame.msg.currentTarget := by
    rw [hw2, World.balance_sstore, hS.launched]
    simp only [transferValue, htv, hv, ne_eq, not_false_eq_true, Bool.true_and,
      decide_true, ↓reduceIte, hself]
    exact QEDefi.Solvency.balance_moveEther_self _ _ _
  rw [← hw1, hw2', hb2] at hb1
  exact hv (BitVec.eq_of_toNat_eq (by simp; omega))

end Verified.WETH9.Spec
