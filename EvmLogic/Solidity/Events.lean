import EvmLogic.Step.Log
import EvmLogic.Step.Storage
import EvmLogic.Program.Call
import EvmLogic.Program.Summary
import EvmLogic.Solidity.Abi
import EvmLogic.Solidity.Memory

/-!
# Solidity events and where logs go

`eventLog` is the log of a Solidity event (`logEntry_eq_eventLog` converts a `LOGn` entry);
lemmas track logs through child calls (kept on success, dropped on failure); and
`processMessageCall_logs_of_fail` shows a failed top-level call has no logs, for any code, so
reverting cases need no re-run of their symbolic execution.
-/

namespace EvmLogic.Solidity
open EvmLean EvmLogic.Tactic EvmLean.Interpreter EvmLogic EvmLogic.Program

/-- The log of a Solidity event: indexed `topics` (signature hash first) and static
unindexed arguments `data` (one ABI word each). -/
def eventLog (emitter : Address) (topics data : List Word) : Log :=
  { address := emitter, topics := topics.toArray, data := Abi.encodeArgs data }

theorem logEntry_eq (m : Machine) (x y : Word) (topics : List Word) :
    logEntry m x y topics =
      Log.mk m.frame.msg.currentTarget topics.toArray (m.frame.memory.read x.toNat y.toNat) := by
  simp only [logEntry, readBytes_bytes, Memory.read_expand]

/-- A `LOGn` entry is an `eventLog` when its memory window holds `Abi.encodeArgs data`. -/
theorem logEntry_eq_eventLog {m : Machine} {x y : Word} {topics data : List Word}
    (h : m.frame.memory.read x.toNat y.toNat = Abi.encodeArgs data) :
    logEntry m x y topics = eventLog m.frame.msg.currentTarget topics data := by
  rw [logEntry_eq, h]; rfl

theorem encodeArgs_one (x : Word) : Abi.encodeArgs [x] = Bytes.ofWord x := by
  simp [Abi.encodeArgs]

theorem encodeArgs_two (x y : Word) : Abi.encodeArgs [x, y] = Bytes.ofWord x ++ Bytes.ofWord y := by
  simp [Abi.encodeArgs]

theorem read_eq_encodeArgs_one {mem : Memory} {off : Nat} {x : Word}
    (h : mem.read off 32 = Bytes.ofWord x) : mem.read off 32 = Abi.encodeArgs [x] := by
  rw [h, encodeArgs_one]

theorem read_eq_encodeArgs_two {mem : Memory} {off : Nat} {x y : Word}
    (h₁ : mem.read off 32 = Bytes.ofWord x) (h₂ : mem.read (off + 32) 32 = Bytes.ofWord y) :
    mem.read off 64 = Abi.encodeArgs [x, y] := by
  rw [Memory.read_64, h₁, h₂, encodeArgs_two]

/-! ## Where a frame's logs go -/

@[simp] theorem mergeSub_logs (p c : Substate) (w : World) (t : Address) :
    (mergeSub p c w t).logs = p.logs ++ c.logs := rfl

@[simp] theorem failSub_logs (p c : Substate) (w : World) (t : Address) :
    (failSub p c w t).logs = p.logs := by
  unfold failSub; split <;> rfl

theorem resumeAfter_success_logs {p : Frame} {ps : List Frame} {mf : Machine} {out : ByteArray}
    {o s : Nat} (hk : mf.frame.kind = .call o s) :
    (resumeAfter p ps mf (.success out)).frame.sub.logs = p.sub.logs ++ mf.frame.sub.logs := by
  rw [resumeAfter_success hk]; rfl

theorem resumeAfter_revert_logs {p : Frame} {ps : List Frame} {mf : Machine} {out : ByteArray}
    {o s : Nat} (hk : mf.frame.kind = .call o s) :
    (resumeAfter p ps mf (.revert out)).frame.sub.logs = p.sub.logs := by
  rw [resumeAfter_revert hk]; exact failSub_logs ..

theorem resumeAfter_halt_logs {p : Frame} {ps : List Frame} {mf : Machine} {e : ExceptionalHalt}
    {o s : Nat} (hk : mf.frame.kind = .call o s) :
    (resumeAfter p ps mf (.halt e)).frame.sub.logs = p.sub.logs := by
  rw [resumeAfter_halt hk]; exact failSub_logs ..

@[simp] theorem warmKey_logs (s : Substate) (a : Address) (k : Word) :
    (s.warmKey a k).logs = s.logs := rfl

@[simp] theorem addRefund_logs (s : Substate) (r : Int) : (s.addRefund r).logs = s.logs := rfl

@[simp] theorem warmAddr_logs (s : Substate) (a : Address) : (s.warmAddr a).logs = s.logs := rfl

@[simp] theorem ofMessage_logs (msg : Message) : (Substate.ofMessage msg).logs = #[] := rfl

@[simp] theorem resumeWith_logs (m : Machine) (pc : Nat) (stack : List Word) (mem : Memory)
    (gas : Nat) (rd : ByteArray) (sub : Substate) :
    (m.resumeWith pc stack mem gas rd sub).frame.sub.logs = sub.logs := rfl

@[simp] theorem frameInit_logs (msg : Message) (kind : FrameKind) (snap : World × TransientStorage) :
    (Frame.init msg kind snap).sub.logs = #[] := rfl

@[simp] theorem startMachine_logs (ctx : Context) (w : World) (tr : TransientStorage)
    (msg : Message) : (startMachine ctx w tr msg).frame.sub.logs = #[] := rfl

theorem topLevelResult_logs_success {t : Option Address} {mf : Machine} {out : ByteArray}
    {o s : Nat} (hk : mf.frame.kind = .call o s) :
    (topLevelResult t (frameResult mf (.success out)).2.1 (frameResult mf (.success out)).2.2
      (frameResult mf (.success out)).1).logs = mf.frame.sub.logs :=
  (topLevelResult_success_call (t := t) (out := out) hk).2.2.2.2

/-! ## Failed top-level calls have no logs -/

theorem topLevelResult_logs_of_fail {t : Option Address} {w : World} {tr : TransientStorage}
    {r : ChildResult} (h : (topLevelResult t w tr r).success = false) :
    (topLevelResult t w tr r).logs = #[] := by
  unfold topLevelResult at h ⊢
  split
  · rename_i hs
    simp [hs, MessageResult.success] at h
  · rfl

theorem finishFrame_done {m : Machine} {o : Outcome} {r : MessageResult}
    (h : finishFrame m o = .done r) : ∃ t w tr c, r = topLevelResult t w tr c := by
  rw [finishFrame_eq] at h
  split at h
  · cases h; exact ⟨_, _, _, _, rfl⟩
  · cases h

theorem step_done {m : Machine} {r : MessageResult} (h : step m = .done r) :
    ∃ t w tr c, r = topLevelResult t w tr c := by
  simp only [step] at h
  split at h
  · split at h
    · exact finishFrame_done h
    · cases h
    · exact finishFrame_done h
    · exact finishFrame_done h
    · cases h
    · cases h
  · exact finishFrame_done h

theorem run_logs_of_fail {fuel : Nat} {m : Machine} {r : MessageResult}
    (h : run fuel m = .ok r) (hs : r.success = false) : r.logs = #[] := by
  induction fuel generalizing m with
  | zero => cases h
  | succ n ih =>
    unfold run at h
    split at h
    · rename_i r' hstep
      cases h
      obtain ⟨t, w, tr, c, rfl⟩ := step_done hstep
      exact topLevelResult_logs_of_fail hs
    · exact ih h

/-- **A failed top-level call emits nothing**: a `processMessageCall` result with
`success = false` has no logs. -/
theorem processMessageCall_logs_of_fail {fuel : Nat} {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} {r : MessageResult}
    (h : processMessageCall fuel ctx w tr msg = .ok r) (hs : r.success = false) :
    r.logs = #[] := by
  unfold processMessageCall processMessageCallWith at h
  dsimp only at h
  split at h
  · rename_i r' hinit
    cases h
    unfold initMachine at hinit
    dsimp only at hinit
    split at hinit
    · cases hinit; rfl
    · split at hinit
      · cases hinit; rfl
      · split at hinit
        · split at hinit
          · cases hinit; rfl
          · cases hinit
        · split at hinit
          · cases hinit
            exact topLevelResult_logs_of_fail (by simpa [MessageResult.success] using hs)
          · cases hinit
  · rename_i m' _
    cases hrun : run fuel m' with
    | error e => rw [hrun] at h; cases h
    | ok r' =>
      rw [hrun] at h
      cases h
      exact run_logs_of_fail (r := r') hrun (by simpa [MessageResult.success] using hs)

end EvmLogic.Solidity
