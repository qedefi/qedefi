import EvmLogic.AbsInt.Code

/-!
# Who a child message is from, and nonces never decrease

Two facts about single instructions, used by `Guard.lean` to show that an **idle** account (one
holding no code that has sent a transaction, `nonce ≠ 0`) never acts in a message call:

- `exec_ids`: a requested call's sender is the requesting frame's own account, or (for
  `DELEGATECALL`) that frame's sender, in which case it also runs at the frame's account; its
  account is the frame's own or the target on the stack (`CallIds`). A creation is sent by the
  frame's account (`execCreate_caller`) and lands on a deployable account, so one with nonce
  zero (`execCreate_deployable`).
- `exec_nonce`: no instruction decreases any account's nonce, and neither do value transfers,
  nonce increments, storage writes or code deposits (`NonceLe`). Self-destruction only schedules
  deletion, which happens after the message call.
-/

section

namespace EvmLogic.Program.Nested
open EvmLean EvmLogic.Program EvmLean.Interpreter EvmLogic.AbsInt EvmLogic.GasMono

/-! ## Nonces -/

/-- No account's nonce decreased. -/
def NonceLe (w w' : World) : Prop := ∀ a, (w.account a).nonce ≤ (w'.account a).nonce

theorem NonceLe.refl (w : World) : NonceLe w w := fun _ => Nat.le_refl _

theorem NonceLe.trans {w₁ w₂ w₃ : World} (h₁ : NonceLe w₁ w₂) (h₂ : NonceLe w₂ w₃) :
    NonceLe w₁ w₃ := fun a => Nat.le_trans (h₁ a) (h₂ a)

theorem nonce_modifyState {w : World} {a : Address} {f : Account → Account}
    (hf : ∀ acc, acc.nonce ≤ (f acc).nonce) : NonceLe w (modifyState w a f) := by
  intro b
  unfold modifyState
  by_cases hab : a = b
  · subst hab
    dsimp only
    split
    · rename_i he
      simp only [Account.isEmpty, Bool.and_eq_true, decide_eq_true_eq] at he
      have := hf (w.account a)
      omega
    · simp [World.account]; exact hf _
  · dsimp only
    split <;> simp [World.account, Std.ExtTreeMap.getD_erase, Std.ExtTreeMap.getD_insert, hab]

theorem nonce_moveEther (w : World) (src dst : Address) (v : Word) :
    NonceLe w (moveEther w src dst v) := by
  unfold moveEther
  exact NonceLe.trans (nonce_modifyState (f := fun acc => { acc with balance := acc.balance - v })
    fun _ => Nat.le_refl _) (nonce_modifyState fun _ => Nat.le_refl _)

theorem nonce_setAccountBalance (w : World) (a : Address) (v : Word) :
    NonceLe w (setAccountBalance w a v) := nonce_modifyState fun _ => Nat.le_refl _

theorem nonce_incrementNonce (w : World) (a : Address) : NonceLe w (incrementNonce w a) :=
  nonce_modifyState fun _ => Nat.le_succ _

theorem nonce_setCode (w : World) (a : Address) (c : ByteArray) : NonceLe w (setCode w a c) :=
  nonce_modifyState fun _ => Nat.le_refl _

theorem nonce_transferValue (w : World) (msg : Message) : NonceLe w (transferValue w msg) := by
  unfold transferValue
  split
  · exact nonce_moveEther _ _ _ _
  · exact NonceLe.refl w

theorem nonce_sstore (w : World) (a : Address) (k v : Word) : NonceLe w (w.sstore a k v) := by
  intro b
  unfold World.sstore World.modify
  by_cases hab : a = b
  · subst hab; simp [World.account]
  · simp [World.account, Std.ExtTreeMap.getD_insert, hab]

/-- Postcondition: no nonce decreased. -/
abbrev NoncePost (m : Machine) (_ : Action) (m' : Machine) : Prop := NonceLe m.world m'.world

set_option maxHeartbeats 1000000 in
theorem execCall_nonce (k : CallKind) (m : Machine) : Wp (execCall k) (NoncePost m) m := by
  cases k <;> simp [NoncePost, NonceLe.refl, execCall, memoryExpansion, expandMemory,
    readMemory, setReturnData, genericCall]

set_option maxHeartbeats 1000000 in
theorem execCreate_nonce (b : Bool) (m : Machine) : Wp (execCreate b) (NoncePost m) m := by
  cases b <;> simp [NoncePost, NonceLe.refl, nonce_incrementNonce, execCreate, requireNonStatic,
    memoryExpansion, expandMemory, readMemory, setReturnData]

set_option maxHeartbeats 4000000 in
/-- **No instruction decreases a nonce.** -/
theorem exec_nonce (op : Opcode) (m : Machine) : Wp (exec op) (NoncePost m) m := by
  cases op
  case create => exact execCreate_nonce false m
  case create2 => exact execCreate_nonce true m
  case call => exact execCall_nonce .call m
  case callcode => exact execCall_nonce .callcode m
  case delegatecall => exact execCall_nonce .delegatecall m
  case staticcall => exact execCall_nonce .staticcall m
  all_goals simp [NoncePost, NonceLe.refl, exec, binOp, unOp, ternOp, pushValue, copyToMemory,
    readOutput, execLog, memoryExpansion, expandMemory, writeMemory, readMemory,
    accessStorageKey, requireNonStatic, execSstore, execSelfdestruct, setStorage, nonce_sstore]
  case dup => intro _; split <;> simp [NonceLe.refl]
  case swap => intro _; split <;> simp [NonceLe.refl]
  case selfdestruct =>
    intro x _ _ _ _
    have h := nonce_moveEther m.world m.frame.msg.currentTarget (Word.toAddress x)
      (m.world.balance m.frame.msg.currentTarget)
    have h' := h.trans (nonce_setAccountBalance _ m.frame.msg.currentTarget 0)
    exact ⟨fun _ => ⟨fun _ => h', fun _ => h'⟩, fun _ => ⟨fun _ => h, fun _ => h⟩⟩

/-! ## Who a child message is from -/

/-- The identity of a requested call: its sender is the requesting frame's account, or (for
`DELEGATECALL`) that frame's sender while running at the frame's account; it runs at the frame's
account or at the target on the stack. -/
def CallIds (m : Machine) (req : CallRequest) : Prop :=
  (req.msg.caller = m.frame.msg.currentTarget ∨
    (req.msg.caller = m.frame.msg.caller ∧ req.msg.currentTarget = m.frame.msg.currentTarget)) ∧
  (req.msg.currentTarget = m.frame.msg.currentTarget ∨
    ∃ t, m.frame.stack[1]? = some t ∧ req.msg.currentTarget = Word.toAddress t)

set_option maxHeartbeats 1000000 in
theorem execCall_ids (k : CallKind) (m : Machine) :
    Wp (execCall k) (fun a _ => ∀ req, a = .call req → CallIds m req) m := by
  cases k <;> simp [CallIds, execCall, memoryExpansion, expandMemory, readMemory,
    setReturnData, genericCall] <;>
  intros <;> subst_vars <;> simp_all

/-- **The identity of every requested call.** -/
theorem exec_ids (op : Opcode) (m : Machine) :
    Wp (exec op) (fun a _ => ∀ req, a = .call req → CallIds m req) m := by
  cases op
  case call => exact execCall_ids .call m
  case callcode => exact execCall_ids .callcode m
  case delegatecall => exact execCall_ids .delegatecall m
  case staticcall => exact execCall_ids .staticcall m
  all_goals refine (exec_eff _ m).mono fun a m' h req ha => ?_
  all_goals exact absurd (ha ▸ h) (by simp [EffPost, CallPost, effOf])

/-- The identity of a requested creation: sent by the frame's account, at an account that was
deployable (nonce zero, no code, no storage) when it was requested. -/
def CreateIds (m : Machine) (msg : Message) : Prop :=
  msg.caller = m.frame.msg.currentTarget ∧ accountDeployable m.world msg.currentTarget = true

set_option maxHeartbeats 1000000 in
theorem execCreate_ids (b : Bool) (m : Machine) :
    Wp (execCreate b) (fun a _ => ∀ msg, a = .create msg → CreateIds m msg) m := by
  cases b <;> simp [CreateIds, execCreate, requireNonStatic, memoryExpansion, expandMemory,
    readMemory, setReturnData] <;>
  intros <;> subst_vars <;> simp_all

/-- **The identity of every requested creation.** -/
theorem exec_create_ids (op : Opcode) (m : Machine) :
    Wp (exec op) (fun a _ => ∀ msg, a = .create msg → CreateIds m msg) m := by
  cases op
  case create => exact execCreate_ids false m
  case create2 => exact execCreate_ids true m
  all_goals refine (exec_eff _ m).mono fun a m' h msg ha => ?_
  all_goals exact absurd (ha ▸ h) (by simp [EffPost, CreatePost, effOf])

end EvmLogic.Program.Nested

end
