import EvmLogic.Step.Log
import EvmLogic.Step.Storage
import EvmLogic.Program.Call
import EvmLogic.Program.Summary
import EvmLogic.Solidity.Abi
import EvmLogic.Solidity.Memory

/-!
# Solidity events and where logs go

Generic facts for proving which logs a compiled contract emits:

* `eventLog emitter topics data`: the log of a Solidity event with indexed `topics` (topic 0 is
  the event signature hash, indexed addresses are left-padded words) and static unindexed
  arguments `data`, ABI-encoded (`Abi.encodeArgs`). `logEntry_eq_eventLog` turns the entry the
  `LOGn` step lemmas append (`logEntry`, a memory read) into this form.
* Where logs go: a successful child's logs are appended to its parent's (`mergeSub_logs`,
  `resumeAfter_success_logs`); a failed child's logs are dropped (`resumeAfter_revert_logs`,
  `resumeAfter_halt_logs`); a top-level frame starts with none (`startMachine_logs`).
* **Failed top-level calls have no logs** (`processMessageCall_logs_of_fail`): whatever the
  code does, a `MessageResult` that `processMessageCall` returns with `success = false` has
  `logs = #[]` (the reference's `process_message_call` drops them). So every reverting call of
  a refinement theorem emits nothing, without re-running its symbolic execution.
-/

namespace EvmLean.Solidity

open Interpreter Program

/-- The log of a Solidity event: emitted by `emitter`, with indexed `topics` (signature hash
first) and static unindexed arguments `data` (one ABI word each). -/
def eventLog (emitter : Address) (topics data : List Word) : Log :=
  { address := emitter, topics := topics.toArray, data := Abi.encodeArgs data }

/-- The entry that `LOGn` appends reads its data from memory. -/
theorem logEntry_eq (m : Machine) (x y : Word) (topics : List Word) :
    logEntry m x y topics =
      Log.mk m.frame.msg.currentTarget topics.toArray (m.frame.memory.read x.toNat y.toNat) := by
  simp only [logEntry, readBytes_bytes, Memory.read_expand]

/-- The entry that `LOGn` appends is an `eventLog` when the memory window holds the ABI
encoding of `data`. -/
theorem logEntry_eq_eventLog {m : Machine} {x y : Word} {topics data : List Word}
    (h : m.frame.memory.read x.toNat y.toNat = Abi.encodeArgs data) :
    logEntry m x y topics = eventLog m.frame.msg.currentTarget topics data := by
  rw [logEntry_eq, h]; rfl

/-- One word of data. -/
theorem encodeArgs_one (x : Word) : Abi.encodeArgs [x] = Bytes.ofWord x := by
  simp [Abi.encodeArgs]

/-- Two words of data. -/
theorem encodeArgs_two (x y : Word) : Abi.encodeArgs [x, y] = Bytes.ofWord x ++ Bytes.ofWord y := by
  simp [Abi.encodeArgs]

/-- A 32-byte memory read of a stored word, for event data. -/
theorem read_eq_encodeArgs_one {mem : Memory} {off : Nat} {x : Word}
    (h : mem.read off 32 = Bytes.ofWord x) : mem.read off 32 = Abi.encodeArgs [x] := by
  rw [h, encodeArgs_one]

/-- A 64-byte memory read of two stored words, for event data. -/
theorem read_eq_encodeArgs_two {mem : Memory} {off : Nat} {x y : Word}
    (h₁ : mem.read off 32 = Bytes.ofWord x) (h₂ : mem.read (off + 32) 32 = Bytes.ofWord y) :
    mem.read off 64 = Abi.encodeArgs [x, y] := by
  rw [Memory.read_64, h₁, h₂, encodeArgs_two]

/-! ## Where a frame's logs go -/

/-- After a successful child, the caller's logs are its own followed by the child's. -/
@[simp] theorem mergeSub_logs (p c : Substate) (w : World) (t : Address) :
    (mergeSub p c w t).logs = p.logs ++ c.logs := rfl

/-- After a failed child, the caller's logs are unchanged. -/
@[simp] theorem failSub_logs (p c : Substate) (w : World) (t : Address) :
    (failSub p c w t).logs = p.logs := by
  unfold failSub; split <;> rfl

/-- The parent's logs after a successful child call. -/
theorem resumeAfter_success_logs {p : Frame} {ps : List Frame} {mf : Machine} {out : ByteArray}
    {o s : Nat} (hk : mf.frame.kind = .call o s) :
    (resumeAfter p ps mf (.success out)).frame.sub.logs = p.sub.logs ++ mf.frame.sub.logs := by
  rw [resumeAfter_success hk]; rfl

/-- The parent's logs after a reverted child call: the child's are dropped. -/
theorem resumeAfter_revert_logs {p : Frame} {ps : List Frame} {mf : Machine} {out : ByteArray}
    {o s : Nat} (hk : mf.frame.kind = .call o s) :
    (resumeAfter p ps mf (.revert out)).frame.sub.logs = p.sub.logs := by
  rw [resumeAfter_revert hk]; exact failSub_logs ..

/-- The parent's logs after an exceptionally halted child call: the child's are dropped. -/
theorem resumeAfter_halt_logs {p : Frame} {ps : List Frame} {mf : Machine} {e : ExceptionalHalt}
    {o s : Nat} (hk : mf.frame.kind = .call o s) :
    (resumeAfter p ps mf (.halt e)).frame.sub.logs = p.sub.logs := by
  rw [resumeAfter_halt hk]; exact failSub_logs ..

/-- Warming a storage key keeps the logs. -/
@[simp] theorem warmKey_logs (s : Substate) (a : Address) (k : Word) :
    (s.warmKey a k).logs = s.logs := rfl

/-- A refund keeps the logs. -/
@[simp] theorem addRefund_logs (s : Substate) (r : Int) : (s.addRefund r).logs = s.logs := rfl

/-- Warming an address keeps the logs. -/
@[simp] theorem warmAddr_logs (s : Substate) (a : Address) : (s.warmAddr a).logs = s.logs := rfl

/-- A child's substate starts with no logs. -/
@[simp] theorem ofMessage_logs (msg : Message) : (Substate.ofMessage msg).logs = #[] := rfl

/-- The frame's logs after resuming at an internal function's return address. -/
@[simp] theorem resumeWith_logs (m : Machine) (pc : Nat) (stack : List Word) (mem : Memory)
    (gas : Nat) (rd : ByteArray) (sub : Substate) :
    (m.resumeWith pc stack mem gas rd sub).frame.sub.logs = sub.logs := rfl

/-- A fresh frame has no logs. -/
@[simp] theorem frameInit_logs (msg : Message) (kind : FrameKind) (snap : World × TransientStorage) :
    (Frame.init msg kind snap).sub.logs = #[] := rfl

/-- A top-level call starts with no logs. -/
@[simp] theorem startMachine_logs (ctx : Context) (w : World) (tr : TransientStorage)
    (msg : Message) : (startMachine ctx w tr msg).frame.sub.logs = #[] := rfl

/-- The logs of a successful top-level frame are the result's. -/
theorem topLevelResult_logs_success {t : Option Address} {mf : Machine} {out : ByteArray}
    {o s : Nat} (hk : mf.frame.kind = .call o s) :
    (topLevelResult t (frameResult mf (.success out)).2.1 (frameResult mf (.success out)).2.2
      (frameResult mf (.success out)).1).logs = mf.frame.sub.logs :=
  (topLevelResult_success_call (t := t) (out := out) hk).2.2.2.2

/-! ## Failed top-level calls have no logs -/

/-- A failed top-level result has no logs. -/
theorem topLevelResult_logs_of_fail {t : Option Address} {w : World} {tr : TransientStorage}
    {r : ChildResult} (h : (topLevelResult t w tr r).success = false) :
    (topLevelResult t w tr r).logs = #[] := by
  unfold topLevelResult at h ⊢
  split
  · rename_i hs
    simp [hs, MessageResult.success] at h
  · rfl

/-- What `finishFrame` returns as a final result is a `topLevelResult`. -/
theorem finishFrame_done {m : Machine} {o : Outcome} {r : MessageResult}
    (h : finishFrame m o = .done r) : ∃ t w tr c, r = topLevelResult t w tr c := by
  rw [finishFrame_eq] at h
  split at h
  · cases h; exact ⟨_, _, _, _, rfl⟩
  · cases h

/-- What `step` returns as a final result is a `topLevelResult`. -/
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

/-- Every result of `run` with `success = false` has no logs. -/
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

/-- **A failed top-level call emits nothing**: every result of `processMessageCall` with
`success = false` (a revert, an exceptional halt, or a call that never ran) has no logs. -/
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

end EvmLean.Solidity
