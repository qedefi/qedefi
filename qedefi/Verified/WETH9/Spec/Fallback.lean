import Verified.WETH9.Spec.DepositLow
import Verified.WETH9.Spec.TransferLow
import Verified.WETH9.Spec.Frame

/-!
# WETH9's fallback refutes `FallbackSpec`

`fallback_short_low`: with calldata shorter than a selector (a plain ether transfer), WETH9 runs
`deposit()`: it credits the value to the caller and logs `Deposit(caller, value)`.

`fallbackSpec_false`: hence `FallbackSpec` fails for WETH9, whatever the gas `g₀` and the
selector list: in any top-level message-call frame satisfying `Start`, non-static, with enough
gas and calldata shorter than four bytes, the spec's `Matches` asks the logs to be unchanged (the
model's events of a fallback call are `[]`, and `Event` has no `Deposit`), while the bytecode
appends the `Deposit` log. The frame is a counterexample to the spec as stated, not to WETH9.
-/

namespace Verified.WETH9.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
open EvmLogic.GasMono EvmLogic.Solidity Verified.WETH9.Contracts QEDefi.ERC4626
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.WETH9

variable {ctx : Context} {pre : PrecompileImpl} {w : World} {tr : TransientStorage}
  {ow : World} {cr : AddressSet} {msg : Message} {sub : Substate}
  {snap : World × TransientStorage} {k : FrameKind} {ps : List Frame} {gas : Nat}
  {Hf : Machine → Outcome → Prop}

theorem lt_calldatasize_short {n : Nat} (h : n < 4) :
    Word.lt (BitVec.ofNat 256 n) (BitVec.ofNat 256 4) = 1#256 :=
  lt_one_of_lt (by simp only [BitVec.toNat_ofNat]; omega)

set_option maxHeartbeats 8000000 in
/-- **The fallback with calldata shorter than a selector, every gas**: `deposit()`. -/
theorem fallback_short_low (hsize : msg.data.size < 4) (hg : 50000 ≤ gas)
    (hstat : msg.isStatic = true → ∀ mf e, Hf mf (.halt e))
    (hok : msg.isStatic = false → ∀ mf,
      mf.world = w.sstore msg.currentTarget (mappingSlot ctx.crypto (Word.ofAddress msg.caller) 3)
        (w.sload msg.currentTarget (mappingSlot ctx.crypto (Word.ofAddress msg.caller) 3) +
          msg.value) →
      mf.transient = tr → mf.createdAccounts = cr →
      mf.frame.sub.logs = sub.logs.push (depositLog9 msg.currentTarget msg.caller msg.value) →
      Hf mf (.success .empty)) :
    LowOK Hf (wethM ctx pre w tr ow cr msg sub snap k ps gas) := by
  have hlt := lt_calldatasize_short hsize
  cases hst : msg.isStatic
  · low_steps [hlt]
    low_step
    refine hok hst _ rfl rfl rfl ?_
    simp only [warmKey_logs, addRefund_logs, depositLog9, EvmLogic.Solidity.eventLog,
      encodeArgs_one, logEntry,
      readBytes_bytes, Memory.read_expand, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      Memory.read_storeWord]
    rfl
  · low_steps [hlt]
    low_static hst
    exact hstat hst _

/-- The logs a finished top-level message call reports. -/
theorem logs_finish_top {mf : Machine} {out : ByteArray} {ko ks : Nat}
    (hp : mf.parents = []) (hk : mf.frame.kind = .call ko ks) :
    ∃ r, finishFrame mf (.success out) = .done r ∧ r.logs = mf.frame.sub.logs := by
  rw [finishFrame_of_top _ hp, frameResult_success_call hk]
  refine ⟨_, rfl, ?_⟩
  simp [topLevelResult, ChildResult.success]

/-- **`FallbackSpec` is false for WETH9**: a `Start` frame at the top level, of a message call,
non-static, with calldata shorter than a selector and gas at least `g₀` and `50000`, contradicts
it. -/
theorem fallbackSpec_false {g₀ : Nat} {sel : List Nat}
    (hF : FallbackSpec WETH9.runtimeCode weth9Abs weth9Model g₀ sel)
    {Act : Finset Address} {m : Machine} (hS : Start WETH9.runtimeCode weth9Abs weth9Model Act m)
    (hp : m.parents = []) {ko ks : Nat} (hk : m.frame.kind = .call ko ks)
    (hsize : m.frame.msg.data.size < 4) (hst : m.frame.msg.isStatic = false)
    (hg₀ : g₀ ≤ m.frame.gasLeft) (hg : 50000 ≤ m.frame.gasLeft) : False := by
  have h1 := hF Act m hS (.inl hsize)
  have h2 : Halts m (fun mf o => o = .success .empty ∧
      mf.frame.sub.logs = m.frame.sub.logs.push
        (depositLog9 m.frame.msg.currentTarget m.frame.msg.caller m.frame.msg.value)) :=
    halts_of_low (g₀ := 50000) hS.fresh (fun h => absurd hg h) (fun _ _ _ _ _ h => h)
      fun g hg' => fallback_short_low hsize hg' (fun h => by rw [hst] at h; cases h)
        fun _ mf _ _ _ hl => ⟨rfl, hl⟩
  obtain ⟨n, mf, o, hex, mf1, o1, hP1, hs1, hf1⟩ := EvmLogic.GasMono.exit_of_halts_top hp h1
  obtain ⟨n', mf', o', hex', mf2, o2, hP2, hs2, hf2⟩ := EvmLogic.GasMono.exit_of_halts_top hp h2
  obtain ⟨rfl, rfl, rfl⟩ := hex.unique hex'
  obtain ⟨rfl, hl2⟩ := hP2
  -- the spec's side: a successful fallback appends no log
  have hl1 : o1 = .success .empty ∧ mf1.frame.sub.logs = m.frame.sub.logs := by
    rcases hP1 with hM | ⟨hfo, hn⟩
    · simp only [weth9Model, Variant.model_call, Variant.model_events, weth9Events] at hM
      have hc : (Variant.weth9 : Variant Address).call (pre weth9Abs Act m) m.frame.msg.caller
          (.other m.frame.msg.value.toNat) = .ok (Variant.weth9.deposit (pre weth9Abs Act m)
            m.frame.msg.caller m.frame.msg.value.toNat |>.getD (pre weth9Abs Act m)) .empty := by
        simp [Variant.call, Variant.step, Variant.fallbackCall, Variant.deposit, Variant.retData,
          Variant.weth9, Variant.standard]
      rw [hc] at hM
      obtain ⟨ho, -, -, -, -, hl⟩ := hM
      exact ⟨ho, by simpa using hl⟩
    · exact absurd ⟨hg₀, hst⟩ hn
  obtain ⟨rfl, hl1⟩ := hl1
  have hk1 : mf1.frame.kind = .call ko ks := hs1.kind.trans hk
  have hk2 : mf2.frame.kind = .call ko ks := hs2.kind.trans hk
  obtain ⟨r1, hr1, hlr1⟩ := logs_finish_top (out := .empty) (hs1.parents.trans hp) hk1
  obtain ⟨r2, hr2, hlr2⟩ := logs_finish_top (out := .empty) (hs2.parents.trans hp) hk2
  have h12 : StepResult.done r1 = StepResult.done r2 :=
    hr1.symm.trans (hf1.trans (hf2.symm.trans hr2))
  injection h12 with h12
  subst h12
  have := congrArg Array.size (hlr1.symm.trans (hlr2.trans hl2) |>.symm.trans hl1)
  simp at this

end Verified.WETH9.Spec
