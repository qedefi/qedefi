import EvmLogic.GasMono.Lockstep
import EvmLogic.GasMono.LockstepTop
import EvmLogic.AbsInt.Effect

/-!
# The depth limit: a frame at depth 1024 behaves as one level up, or fails

The only instructions that read a frame's message depth are the `CALL` and `CREATE` families
(the depth-limit check of `generic_call` / `generic_create`). So a frame at the call-depth
limit (`Gas.stackDepthLimit < depth + 1`: every call it makes fails at once with `0` pushed)
runs in lockstep with the same frame one level up (`setDepth`) until the first call
(`exec_setDepth`). In code satisfying the lockstep conditions (`CodeOk`: every call is a
`CALL`/`STATICCALL` returning to a point where a failed call makes the frame fail), the first
call makes the frame at the limit fail. Hence (`depth_lockstep`) the frame at the limit fails,
or ends exactly as the frame one level up; and a frame summary of the top-level frame one
level up transfers (`halts_world_of_depth`).
-/

namespace EvmLean.Program.GasMono

open Interpreter Nested

/-- The machine whose executing frame has message depth `d`. -/
def setDepth (d : Nat) (m : Machine) : Machine :=
  { m with frame := { m.frame with msg := { m.frame.msg with depth := d } } }

/-- The instructions reading the depth: the `CALL` and `CREATE` families. -/
def readsDepthB : Opcode → Bool
  | .call | .callcode | .delegatecall | .staticcall | .create | .create2 => true
  | _ => false

set_option maxHeartbeats 8000000 in
/-- **Every instruction not reading the depth commutes with changing it.** -/
theorem exec_setDepth_wp (op : Opcode) (hop : readsDepthB op = false) (m : Machine) (d : Nat) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = setDepth d m') (setDepth d m)) m := by
  cases op
  case call | callcode | delegatecall | staticcall | create | create2 =>
    simp [readsDepthB] at hop
  case dup n =>
    simp [exec, setDepth]
    intro _
    split <;> simp <;> intros <;> omega
  case swap n =>
    simp [exec, setDepth]
    intro _
    split <;> simp <;> intros <;> omega
  case log n =>
    simp [exec, execLog, setDepth, memoryExpansion, expandMemory, requireNonStatic, readMemory]
    intros
    subst_vars
    simp_all
  case returndatacopy =>
    simp [exec, memoryExpansion, expandMemory, writeMemory, setDepth]
    intros
    simp_all
    intro hz
    simp only [hz] at *
    exact ⟨by omega, by omega, .inl (by omega)⟩
  all_goals simp [exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    setDepth, execSstore, execSelfdestruct] <;> intros <;> (try simp_all) <;> omega

/-- **Changing the depth**, as run equations. -/
theorem exec_setDepth (op : Opcode) (hop : readsDepthB op = false) {m m' : Machine} {a : Action}
    (h : (exec op).run m = .ok (a, m')) (d : Nat) :
    (exec op).run (setDepth d m) = .ok (a, setDepth d m') := by
  have hw := (exec_setDepth_wp op hop m d).of_run h
  unfold Twp at hw
  split at hw
  · rename_i a' m'' he
    obtain ⟨rfl, rfl⟩ := hw
    exact he
  · exact hw.elim

theorem setDepth_setDepth (d d' : Nat) (m : Machine) :
    setDepth d (setDepth d' m) = setDepth d m := rfl

theorem setDepth_self (m : Machine) : setDepth m.frame.msg.depth m = m := rfl

/-- An instruction not reading the depth fails at every depth if it fails at one. -/
theorem exec_setDepth_error (op : Opcode) (hop : readsDepthB op = false) {m : Machine}
    {e : ExceptionalHalt} (h : (exec op).run m = .error e) (d : Nat) :
    ∃ e', (exec op).run (setDepth d m) = .error e' := by
  cases h' : (exec op).run (setDepth d m) with
  | error e' => exact ⟨e', rfl⟩
  | ok p =>
    exfalso
    have := exec_setDepth op hop h' m.frame.msg.depth
    rw [setDepth_setDepth, setDepth_self] at this
    rw [this] at h
    cases h

/-- Changing the depth keeps "same frame" (up to the depth). -/
theorem sameFrame_setDepth {m m' : Machine} (h : SameFrame m m') (d : Nat) :
    SameFrame (setDepth d m) (setDepth d m') :=
  ⟨h.ctx, h.precompiles, h.originalWorld, h.parents, by simp [setDepth, h.msg], h.code,
    h.jumpDests, h.kind, h.snapshot⟩

/-- Instructions not reading the depth request no child. -/
theorem effOf_ne_call {op : Opcode} (hop : readsDepthB op = false) :
    (∀ p, AbsInt.effOf op ≠ .call p) ∧ ∀ p, AbsInt.effOf op ≠ .create p := by
  cases op <;> simp_all [readsDepthB, AbsInt.effOf]

/-- The bytes of the instructions reading the depth. -/
theorem isCallByte_of_readsDepth (fork : Fork) {b : UInt8}
    (h : readsDepthB (Opcode.decode fork b) = true) : IsCallByte b := by
  have hg : readsGasB (Opcode.decode fork b) = true := by
    revert h; cases Opcode.decode fork b <;> simp [readsDepthB, readsGasB]
  rcases readsGas_decode fork b hg with h5 | h5 | h5 | h5 | h5 | h5 | h5
  · subst h5; cases fork <;> simp [Opcode.decode, readsDepthB] at h
  all_goals (subst h5; decide)

set_option maxHeartbeats 1000000 in
/-- **A call at the depth limit fails at once**: `CALL`/`STATICCALL` from a frame at the limit
continue with `0` on the stack. -/
theorem execCall_limit (k : CallKind) (hk : k = .call ∨ k = .staticcall) (m : Machine)
    (hd : Gas.stackDepthLimit < m.frame.msg.depth + 1) :
    Wp (execCall k) (fun a m' => a = .next ∧ m'.frame.pc = m.frame.pc + 1 ∧
      m'.frame.stack.head? = some 0) m := by
  rcases hk with rfl | rfl <;>
  simp [execCall, memoryExpansion, expandMemory, readMemory, setReturnData, genericCall, hd]

/-- How the frame at the limit ends against the frame one level up: it fails, or ends with the
same outcome from the same machine (at its depth). -/
def DepthPost (d : Nat) (mfh : Machine) (oh : Outcome) (mf : Machine) (o : Outcome) : Prop :=
  Failed o ∨ (o = oh ∧ mf = setDepth d mfh)

/-- An instruction that fails ends the frame there. -/
theorem exitOf_of_error {m : Machine} {b : UInt8} {e : ExceptionalHalt}
    (hcode : m.frame.code[m.frame.pc]? = some b)
    (hexec : (exec (Opcode.decode m.ctx.fork b)).run m = .error e) :
    exitOf m = some (m, .halt e) := by
  rw [getElem?_eq_some_iff] at hcode
  obtain ⟨hlt, hb⟩ := hcode
  unfold exitOf
  simp only [hlt, ↓reduceDIte, hb, hexec]

/-- **The depth lockstep.** Following the frame one level up to its exit, the same frame at the
depth limit (any depth `d` with `Gas.stackDepthLimit < d + 1`) fails or ends identically. -/
theorem depth_lockstep {code : ByteArray} {n : Nat} (hc : CodeOk code n) {d : Nat}
    (hd : Gas.stackDepthLimit < d + 1) :
    ∀ N mh mfh oh, Exit mh N mfh oh → mh.frame.code = code →
      mh.frame.jumpDests = validJumpDests code → PcOk code n mh.frame.pc →
      Halts (setDepth d mh) (DepthPost d mfh oh) := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
  intro mh mfh oh hex hcode hjd hpc
  have hb : mh.frame.code[mh.frame.pc]? = some (Bytes.getD code mh.frame.pc) :=
    code_getElem? hcode hpc
  have hbl : (setDepth d mh).frame.code[(setDepth d mh).frame.pc]? =
      some (Bytes.getD code mh.frame.pc) := hb
  cases hrd : readsDepthB (Opcode.decode mh.ctx.fork (Bytes.getD code mh.frame.pc)) with
  | false =>
    cases hrun : (exec (Opcode.decode mh.ctx.fork (Bytes.getD code mh.frame.pc))).run mh with
    | error e =>
      have hx := exitOf_of_error hb hrun
      obtain ⟨-, rfl, rfl⟩ := (exit_zero hx).unique hex
      obtain ⟨e', he'⟩ := exec_setDepth_error _ hrd hrun d
      exact Halts.of_step (step_of_exec_error hbl he') (.refl _) (.inl fun out h => by cases h)
    | ok p =>
      obtain ⟨a, m'⟩ := p
      have hlow := exec_setDepth _ hrd hrun d
      have hif := ((exec_frame _ mh).of_run hrun).1
      have hpost := (AbsInt.exec_eff _ mh).of_run hrun
      have hnc := effOf_ne_call hrd
      cases a with
      | next =>
        have hst : step mh = .running m' := step_of_exec_next hb hrun
        have hstl : step (setDepth d mh) = .running (setDepth d m') := step_of_exec_next hbl hlow
        obtain ⟨hN, hex'⟩ := hex.next hst hif.same
        exact Halts.of_steps (Steps.of_step hstl (sameFrame_setDepth hif.same d))
          (ih (N - 1) (by omega) m' mfh oh hex' (hif.same.code.trans hcode)
            (hif.same.jumpDests.trans hjd) (pcOk_of_exec' hc.region hcode hjd hpc hb hrun))
      | stop out =>
        obtain ⟨-, rfl, rfl⟩ := (exit_zero ((exitOf_of_exec hb hrun).1 out rfl)).unique hex
        exact Halts.of_step (step_of_exec_stop hbl hlow) (sameFrame_setDepth hif.same d)
          (.inr ⟨rfl, rfl⟩)
      | revert out =>
        obtain ⟨-, rfl, rfl⟩ := (exit_zero ((exitOf_of_exec hb hrun).2 out rfl)).unique hex
        exact Halts.of_step (step_of_exec_revert hbl hlow) (sameFrame_setDepth hif.same d)
          (.inr ⟨rfl, rfl⟩)
      | call req =>
        exfalso
        simp only [AbsInt.EffPost] at hpost
        cases he : AbsInt.effOf (Opcode.decode mh.ctx.fork (Bytes.getD code mh.frame.pc)) <;>
          rw [he] at hpost <;> simp only [AbsInt.CallPost] at hpost
        exact hnc.1 _ he
      | create msg =>
        exfalso
        simp only [AbsInt.EffPost] at hpost
        cases he : AbsInt.effOf (Opcode.decode mh.ctx.fork (Bytes.getD code mh.frame.pc)) <;>
          rw [he] at hpost <;> simp only [AbsInt.CreatePost] at hpost
        exact hnc.2 _ he
  | true =>
    have hcb := isCallByte_of_readsDepth mh.ctx.fork hrd
    obtain ⟨hcs, hret⟩ := callsFed_call hc.feed hc.fed hpc.1 hpc.2 hcb
    have hdl : Gas.stackDepthLimit < (setDepth d mh).frame.msg.depth + 1 := hd
    have hw : Wp (exec (Opcode.decode (setDepth d mh).ctx.fork (Bytes.getD code mh.frame.pc)))
        (fun a m' => a = .next ∧ m'.frame.pc = (setDepth d mh).frame.pc + 1 ∧
          m'.frame.stack.head? = some 0) (setDepth d mh) := by
      rcases decode_call mh.ctx.fork hcs with hop | hop
      · rw [show (setDepth d mh).ctx = mh.ctx from rfl, hop]
        exact execCall_limit .call (.inl rfl) _ hdl
      · rw [show (setDepth d mh).ctx = mh.ctx from rfl, hop]
        exact execCall_limit .staticcall (.inr rfl) _ hdl
    cases hl : (exec (Opcode.decode (setDepth d mh).ctx.fork
        (Bytes.getD code mh.frame.pc))).run (setDepth d mh) with
    | error e =>
      exact Halts.of_step (step_of_exec_error hbl hl) (.refl _) (.inl fun out h => by cases h)
    | ok p =>
      obtain ⟨a, ml'⟩ := p
      obtain ⟨rfl, hpc', hhd⟩ := hw.of_run hl
      have hifl := ((exec_frame _ (setDepth d mh)).of_run hl).1
      have hstl : step (setDepth d mh) = .running ml' := step_of_exec_next hbl hl
      have hfail := hc.reverts _ hret ml' (hifl.same.code.trans hcode) hpc' hhd
      exact Halts.of_steps (Steps.of_step hstl hifl.same) (hfail.mono fun _ _ _ hf => .inl hf)

/-- **A frame summary at the depth limit**: a summary (success → `P` of the world) of the same
top-level frame at another depth transfers to the frame at the limit. -/
theorem halts_world_of_depth {code : ByteArray} {n : Nat} (hc : CodeOk code n) {m : Machine}
    (hp : m.parents = []) (hcode : m.frame.code = code) (hjd : m.frame.jumpDests = validJumpDests code)
    (hpc : PcOk code n m.frame.pc) (hd : Gas.stackDepthLimit < m.frame.msg.depth + 1) {ko ks : Nat}
    (hk : m.frame.kind = .call ko ks) {d' : Nat} {P : World → Prop}
    (h : Halts (setDepth d' m) (fun mf o => ∀ out, o = .success out → P mf.world)) :
    Halts m (fun mf o => ∀ out, o = .success out → P mf.world) := by
  obtain ⟨N, mfh, oh, hex, mf', o', hH, hs', hfin⟩ := exit_of_halts_top (m := setDepth d' m) hp h
  have hlow := depth_lockstep hc hd N (setDepth d' m) mfh oh hex hcode hjd hpc
  rw [setDepth_setDepth, setDepth_self] at hlow
  refine hlow.mono fun mfl ol _ hpost out hol => ?_
  rcases hpost with hf | ⟨rfl, hmf⟩
  · exact absurd hol (hf out)
  · subst hol
    have hfh := hex.finish
    have hph : mfh.parents = [] := hfh.2.parents.trans hp
    have hp' : mf'.parents = [] := hs'.parents.trans hp
    have hkh : mfh.frame.kind = .call ko ks := hfh.2.kind.trans hk
    have hk' : mf'.frame.kind = .call ko ks := hs'.kind.trans hk
    rw [finishFrame_of_top _ hp', finishFrame_of_top _ hph, hs'.msg, hfh.2.msg] at hfin
    injection hfin with hfin
    obtain ⟨out', ho', hw⟩ := topLevelResult_frameResult_success hkh hk' hfin
    have := hH out' ho'
    rw [hw] at this
    rw [hmf]
    exact this

end EvmLean.Program.GasMono
