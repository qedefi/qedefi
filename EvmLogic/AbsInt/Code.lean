import EvmLogic.AbsInt.Frame

/-!
# Abstract interpretation: the code of every account during a frame

No instruction changes the code of any account (`exec_code`: `SSTORE` writes storage, value
transfers and `SELFDESTRUCT` move balances — an account whose balance or nonce changes keeps
its code, and an account deleted for being empty had none —, `CREATE` only bumps the
sender's nonce). Code is only deposited by a finished creation frame. So a frame that starts
no creation and whose children keep the code (`frame_code`) runs, from its start to its exit,
in worlds with the code of its starting world.
-/

namespace EvmLean.Program.AbsInt

open Interpreter Nested GasMono

/-- Two worlds with the same code at every address. -/
def SameCode (w w' : World) : Prop := ∀ a, w'.code a = w.code a

theorem SameCode.refl (w : World) : SameCode w w := fun _ => rfl

theorem SameCode.trans {w₁ w₂ w₃ : World} (h₁ : SameCode w₁ w₂) (h₂ : SameCode w₂ w₃) :
    SameCode w₁ w₃ := fun a => (h₂ a).trans (h₁ a)

/-- An empty byte array is `.empty`. -/
theorem eq_empty_of_size {b : ByteArray} (h : b.size = 0) : b = .empty :=
  Classical.byContradiction fun hne => size_ne_zero_of_ne_empty hne h

/-- `modifyState` with a function keeping code keeps every account's code. -/
theorem code_modifyState {w : World} {a : Address} {f : Account → Account}
    (hf : ∀ acc, (f acc).code = acc.code) : SameCode w (modifyState w a f) := by
  intro b
  have hs := size_code_modifyState (w := w) (a := a) (b := b) hf
  unfold modifyState World.code at *
  by_cases hab : a = b
  · subst hab
    dsimp only at hs ⊢
    split
    · rename_i he
      simp only [Account.isEmpty, Bool.and_eq_true, decide_eq_true_eq, hf] at he
      have h1 : (World.account (Std.ExtTreeMap.erase w a) a).code = .empty := by
        simp [World.account]
      rw [h1, eq_empty_of_size he.2]
    · simp [World.account, hf]
  · dsimp only
    split <;> simp [World.account, Std.ExtTreeMap.getD_erase, Std.ExtTreeMap.getD_insert, hab]

theorem code_moveEther (w : World) (src dst : Address) (v : Word) :
    SameCode w (moveEther w src dst v) := by
  unfold moveEther
  exact SameCode.trans (code_modifyState (f := fun acc => { acc with balance := acc.balance - v })
    fun _ => rfl) (code_modifyState fun _ => rfl)

theorem code_setAccountBalance (w : World) (a : Address) (v : Word) :
    SameCode w (setAccountBalance w a v) := code_modifyState fun _ => rfl

theorem code_incrementNonce (w : World) (a : Address) : SameCode w (incrementNonce w a) :=
  code_modifyState fun _ => rfl

theorem code_transferValue (w : World) (msg : Message) : SameCode w (transferValue w msg) := by
  unfold transferValue
  split
  · exact code_moveEther _ _ _ _
  · exact SameCode.refl w

theorem code_sstore' (w : World) (a : Address) (k v : Word) : SameCode w (w.sstore a k v) :=
  fun b => World.code_sstore w a k v b

/-- Postcondition: the world's code is unchanged. -/
abbrev CodePost (m : Machine) (_ : Action) (m' : Machine) : Prop := SameCode m.world m'.world

set_option maxHeartbeats 1000000 in
/-- The `CALL` family. -/
theorem execCall_code (k : CallKind) (m : Machine) : Wp (execCall k) (CodePost m) m := by
  cases k <;> simp [CodePost, SameCode.refl, execCall, memoryExpansion, expandMemory,
    readMemory, setReturnData, genericCall]

set_option maxHeartbeats 1000000 in
/-- The `CREATE` family. -/
theorem execCreate_code (b : Bool) (m : Machine) : Wp (execCreate b) (CodePost m) m := by
  cases b <;> simp [CodePost, SameCode.refl, code_incrementNonce, execCreate, requireNonStatic,
    memoryExpansion, expandMemory, readMemory, setReturnData]

set_option maxHeartbeats 4000000 in
/-- **No instruction changes the code of any account.** -/
theorem exec_code (op : Opcode) (m : Machine) : Wp (exec op) (CodePost m) m := by
  cases op
  case create => exact execCreate_code false m
  case create2 => exact execCreate_code true m
  case call => exact execCall_code .call m
  case callcode => exact execCall_code .callcode m
  case delegatecall => exact execCall_code .delegatecall m
  case staticcall => exact execCall_code .staticcall m
  all_goals simp [CodePost, SameCode.refl, exec, binOp, unOp, ternOp, pushValue, copyToMemory,
    readOutput, execLog, memoryExpansion, expandMemory, writeMemory, readMemory,
    accessStorageKey, requireNonStatic, execSstore, execSelfdestruct, setStorage, code_sstore']
  case dup => intro _; split <;> simp [SameCode.refl]
  case swap => intro _; split <;> simp [SameCode.refl]
  case selfdestruct =>
    intro x _ _ _ _
    have h := code_moveEther m.world m.frame.msg.currentTarget (Word.toAddress x)
      (m.world.balance m.frame.msg.currentTarget)
    have h' := h.trans (code_setAccountBalance _ m.frame.msg.currentTarget 0)
    exact ⟨fun _ => ⟨fun _ => h', fun _ => h'⟩, fun _ => ⟨fun _ => h, fun _ => h⟩⟩

/-- **A step staying in the frame keeps the code** (an instruction, or a precompile call: the
value transfer or the rollback). -/
theorem within_code {m m' m₁ : Machine} {b : UInt8} {a : Action}
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m')) (hw : Within m' a m₁) :
    SameCode m.world m₁.world := by
  have h := (exec_code _ m).of_run he
  rcases hw with ⟨-, rfl⟩ | ⟨req, -, hpre, rfl⟩
  · exact h
  · obtain ⟨w, tr, r, hl, hw⟩ := launchCall_some hpre
    rw [hl]
    show SameCode m.world w
    rcases hw with rfl | rfl
    · exact h.trans (code_transferValue _ _)
    · exact h

/-- A pushed call frame starts after the value transfer. -/
theorem pushCall_code (m : Machine) (req : CallRequest) : SameCode m.world (pushCall m req).world :=
  code_transferValue _ _

/-- The world a call frame hands back: its own (success) or its snapshot (failure). -/
theorem resumeAfter_world {p : Frame} {ps : List Frame} {mf : Machine} {o : Outcome}
    {ko ks : Nat} (hk : mf.frame.kind = .call ko ks) :
    (resumeAfter p ps mf o).world = mf.world ∨
      (resumeAfter p ps mf o).world = mf.frame.snapshot.1 := by
  cases o with
  | success out => left; simp [resumeAfter, frameResult, hk, resume]
  | revert out => right; simp [resumeAfter, frameResult, resume]
  | halt e => right; simp [resumeAfter, frameResult, resume]

end EvmLean.Program.AbsInt
