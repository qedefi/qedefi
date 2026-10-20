import EvmLogic.Program.Nested.Wp
import EvmLogic.State
import EvmLogic.Program.Call

/-!
# What one instruction can change

`exec_frame`: for **every** opcode and every machine, a successful instruction

* keeps the frame's identity (`SameFrame`: message, code, kind, snapshot, parents, context),
  the created accounts, and never increases the frame's gas;
* keeps the storage and code of every account that holds code and is not *writable* by the
  frame (`Writable`: the executing account of a non-static frame) — `SSTORE` only writes the
  executing account and needs a non-static frame, value transfers and `SELFDESTRUCT` change
  balances only, and an account holding code is never empty, so it is never deleted;
* if it requests a child message call (`Action.call`), the child's message is described by
  `CallOk`: depth, gas taken from the caller, and — for a non-static child — who the caller is
  and which code runs; if it requests a creation (`Action.create`), the new account holds no
  code (`CreateOk`).

This is the frame condition the nested-call simulation (`EvmLogic.Program.Nested.Run`) needs: code that is
not running at a protected account (or runs statically) cannot touch its storage, whatever it
does.
-/

namespace EvmLogic.Program.Nested
open EvmLean

open EvmLean.Interpreter

/-! ## Accounts that stay unchanged -/

/-- Storage and code of `p` are the same in `w` and `w'`. -/
def Keep (p : Address) (w w' : World) : Prop :=
  (w'.account p).storage = (w.account p).storage ∧ (w'.account p).code = (w.account p).code

@[simp] theorem keep_refl (p : Address) (w : World) : Keep p w w := ⟨rfl, rfl⟩

theorem Keep.trans {p : Address} {w₁ w₂ w₃ : World} (h₁ : Keep p w₁ w₂) (h₂ : Keep p w₂ w₃) :
    Keep p w₁ w₃ := ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

theorem Keep.sload {p : Address} {w w' : World} (h : Keep p w w') (k : Word) :
    w'.sload p k = w.sload p k := by
  simp only [World.sload, h.1]

theorem Keep.code {p : Address} {w w' : World} (h : Keep p w w') : w'.code p = w.code p := h.2

/-- `modifyState` with a function keeping storage and code keeps every account holding code
(such an account is never empty, so it is never deleted). -/
theorem keep_modifyState {w : World} {a p : Address} {f : Account → Account}
    (hf : ∀ acc, (f acc).storage = acc.storage ∧ (f acc).code = acc.code)
    (hp : (w.code p).size ≠ 0) : Keep p w (modifyState w a f) := by
  unfold modifyState
  by_cases hap : a = p
  · subst hap
    have hne : (f (w.account a)).isEmpty = false := by
      simp only [Account.isEmpty, (hf _).2, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      right; exact hp
    simp only [hne, Bool.false_eq_true, ite_false]
    refine ⟨?_, ?_⟩ <;> simp [World.account, (hf _).1, (hf _).2]
  · dsimp only
    split
    · refine ⟨?_, ?_⟩ <;> simp [World.account, Std.ExtTreeMap.getD_erase, hap]
    · refine ⟨?_, ?_⟩ <;> simp [World.account, Std.ExtTreeMap.getD_insert, hap]

theorem keep_moveEther {w : World} {src dst p : Address} {v : Word} (hp : (w.code p).size ≠ 0) :
    Keep p w (moveEther w src dst v) := by
  unfold moveEther
  have h₁ := keep_modifyState (a := src) (f := fun acc => { acc with balance := acc.balance - v })
    (fun _ => ⟨rfl, rfl⟩) hp
  refine h₁.trans (keep_modifyState (fun _ => ⟨rfl, rfl⟩) ?_)
  rw [Keep.code h₁]; exact hp

theorem keep_setAccountBalance {w : World} {a p : Address} {v : Word} (hp : (w.code p).size ≠ 0) :
    Keep p w (setAccountBalance w a v) :=
  keep_modifyState (fun _ => ⟨rfl, rfl⟩) hp

theorem keep_incrementNonce {w : World} {a p : Address} (hp : (w.code p).size ≠ 0) :
    Keep p w (incrementNonce w a) :=
  keep_modifyState (fun _ => ⟨rfl, rfl⟩) hp

theorem keep_sstore {w : World} {a p : Address} {k v : Word} (h : p ≠ a) :
    Keep p w (w.sstore a k v) := by
  unfold Keep World.sstore
  rw [World.account_modify_ne _ _ h]; exact ⟨rfl, rfl⟩

theorem keep_transferValue {w : World} {msg : Message} {p : Address} (hp : (w.code p).size ≠ 0) :
    Keep p w (transferValue w msg) := by
  unfold transferValue
  split
  · exact keep_moveEther hp
  · exact keep_refl p w

/-- `modifyState` with a function keeping code keeps the size of every account's code. -/
theorem size_code_modifyState {w : World} {a b : Address} {f : Account → Account}
    (hf : ∀ acc, (f acc).code = acc.code) :
    ((modifyState w a f).code b).size = (w.code b).size := by
  unfold modifyState World.code
  by_cases hab : a = b
  · subst hab
    dsimp only
    split
    · rename_i he
      simp only [Account.isEmpty, Bool.and_eq_true, decide_eq_true_eq, hf] at he
      have h2 := he.2
      have h3 : (World.account (Std.ExtTreeMap.erase w a) a).code.size = 0 := by
        simp [World.account]
      rw [h3, ← h2]
    · simp [World.account, hf]
  · dsimp only
    split <;> simp [World.account, Std.ExtTreeMap.getD_erase, Std.ExtTreeMap.getD_insert, hab]

theorem size_code_incrementNonce {w : World} {a b : Address} :
    ((incrementNonce w a).code b).size = (w.code b).size :=
  size_code_modifyState (fun _ => rfl)

theorem size_code_of_deployable {w : World} {a : Address} (h : accountDeployable w a = true) :
    (w.code a).size = 0 := by
  simp only [accountDeployable, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

/-- A byte array that is not empty has positive size. -/
theorem size_ne_zero_of_ne_empty {b : ByteArray} (h : ¬ b = ByteArray.empty) : b.size ≠ 0 := by
  intro h0; apply h
  cases b with
  | mk data =>
    simp only [ByteArray.size] at h0
    simp only [ByteArray.empty, ByteArray.emptyWithCapacity, Array.eq_empty_of_size_eq_zero h0]
    rfl

/-! ## The frame condition of one instruction -/

/-- The executing frame may write the storage of `p`: `p` is the executing account and the
frame is not static. -/
def Writable (m : Machine) (p : Address) : Prop :=
  p = m.frame.msg.currentTarget ∧ m.frame.msg.isStatic = false

/-- What every successful instruction preserves. -/
structure InstrFrame (m m' : Machine) : Prop where
  /-- Same frame, parents and transaction constants. -/
  same : SameFrame m m'
  /-- Same created accounts. -/
  created : m'.createdAccounts = m.createdAccounts
  /-- Gas never increases. -/
  gas : m'.frame.gasLeft ≤ m.frame.gasLeft
  /-- Accounts holding code that the frame may not write keep their storage and code. -/
  keep : ∀ p, (m.world.code p).size ≠ 0 → ¬ Writable m p → Keep p m.world m'.world

theorem InstrFrame.refl (m : Machine) : InstrFrame m m :=
  ⟨.refl m, rfl, Nat.le_refl _, fun _ _ _ => keep_refl _ _⟩

theorem InstrFrame.trans {m₁ m₂ m₃ : Machine} (h₁ : InstrFrame m₁ m₂) (h₂ : InstrFrame m₂ m₃) :
    InstrFrame m₁ m₃ where
  same := h₁.same.trans h₂.same
  created := h₂.created.trans h₁.created
  gas := Nat.le_trans h₂.gas h₁.gas
  keep p hp hw := by
    have k₁ := h₁.keep p hp hw
    refine k₁.trans (h₂.keep p (by rw [k₁.code]; exact hp) ?_)
    unfold Writable at *
    rw [h₁.same.msg]; exact hw

/-- A machine update that only touches the frame's mutable fields (and not the world, or only
keeping it) is an `InstrFrame` step, when gas does not increase. -/
theorem instrFrame_iff {m m' : Machine} :
    InstrFrame m m' ↔ m'.ctx = m.ctx ∧ m'.precompiles = m.precompiles ∧
      m'.originalWorld = m.originalWorld ∧ m'.parents = m.parents ∧
      m'.frame.msg = m.frame.msg ∧ m'.frame.code = m.frame.code ∧
      m'.frame.jumpDests = m.frame.jumpDests ∧ m'.frame.kind = m.frame.kind ∧
      m'.frame.snapshot = m.frame.snapshot ∧ m'.createdAccounts = m.createdAccounts ∧
      m'.frame.gasLeft ≤ m.frame.gasLeft ∧
      (∀ p, (m.world.code p).size ≠ 0 → ¬ Writable m p → Keep p m.world m'.world) := by
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, hc, hg, hk⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hc, hg, hk⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hc, hg, hk⟩
    exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, hc, hg, hk⟩

/-! ## Requested children -/

/-- What a child message call requested by an instruction looks like. -/
structure CallOk (m m' : Machine) (req : CallRequest) : Prop where
  /-- One level deeper. -/
  depth : req.msg.depth = m.frame.msg.depth + 1
  /-- Within the depth limit. -/
  depthLe : req.msg.depth ≤ Gas.stackDepthLimit
  /-- The child's gas was taken from the caller. -/
  gas : m'.frame.gasLeft + req.msg.gas ≤ m.frame.gasLeft
  /-- A message call. -/
  target : req.msg.target = some req.msg.currentTarget
  /-- A non-static child comes from a non-static frame and either runs at the caller's own
  account (`CALLCODE`, `DELEGATECALL`) or is a `CALL` from the caller's account running the
  callee's code (when the callee holds no EIP-7702 designator). -/
  nonstatic : req.msg.isStatic = false → m.frame.msg.isStatic = false ∧
    (req.msg.currentTarget = m.frame.msg.currentTarget ∨
      (req.msg.caller = m.frame.msg.currentTarget ∧
        (delegatedAddress? (m.world.code req.msg.currentTarget) = none →
          req.msg.code = m.world.code req.msg.currentTarget ∧
          req.msg.codeAddress = some req.msg.currentTarget ∧ req.msg.disablePrecompiles = false)))

/-- What a creation requested by an instruction looks like. -/
structure CreateOk (m m' : Machine) (msg : Message) : Prop where
  /-- A creation. -/
  target : msg.target = none
  /-- Not static. -/
  static : msg.isStatic = false
  /-- The new account holds no code. -/
  code : (m'.world.code msg.currentTarget).size = 0
  /-- The child's gas was taken from the caller. -/
  gas : m'.frame.gasLeft + msg.gas ≤ m.frame.gasLeft
  /-- Within the depth limit. -/
  depthLe : msg.depth ≤ Gas.stackDepthLimit

/-- What an instruction's action requests. -/
def ActionOk (m m' : Machine) : Action → Prop
  | .call req => CallOk m m' req
  | .create msg => CreateOk m m' msg
  | _ => True

/-! ## Access lists and delegation -/

@[simp] theorem wp_accessAddress {m : Machine} (a : Address) {Q : Bool → Machine → Prop} :
    Wp (accessAddress a) Q m ↔ Q (m.frame.sub.accessedAddresses.contains a)
      { m with frame := { m.frame with sub := m.frame.sub.warmAddr a } } := by
  unfold Wp; rw [run_accessAddress]; rfl

@[simp] theorem wp_accessDelegation {m : Machine} (a : Address)
    {Q : Bool × Address × ByteArray × Nat → Machine → Prop} :
    Wp (accessDelegation a) Q m ↔
      ((m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code a) = none) →
        Q (false, a, m.world.code a, 0) m) ∧
      (∀ d, ¬ m.ctx.fork < .prague → delegatedAddress? (m.world.code a) = some d →
        Q (true, d, delegateCode m.precompiles.isPrecompile m.world d,
            Gas.accessCost (m.frame.sub.accessedAddresses.contains d))
          { m with frame := { m.frame with sub := m.frame.sub.warmAddr d } }) := by
  unfold accessDelegation
  by_cases hf : m.ctx.fork < .prague
  · simp [hf]
  · cases hd : delegatedAddress? (m.world.code a) with
    | none => simp [hf, hd]
    | some d => simp [hf, hd]

/-- The gas handed to a callee never exceeds what the caller is charged for it (the stipend
of a value transfer is covered by the value-transfer cost). -/
theorem messageCallGas_subCall_le {v g L mc e : Nat} (h : v = 0 ∨ Gas.callStipend ≤ e) :
    (Gas.messageCallGas v g L mc e).subCall ≤ (Gas.messageCallGas v g L mc e).cost := by
  unfold Gas.messageCallGas
  split <;> split <;> simp only <;> omega

/-- A call's charge followed by a refund of the callee's gas never increases the caller's
gas. -/
theorem refund_le {v g L mc e E G : Nat} (h : v = 0 ∨ Gas.callStipend ≤ e)
    (hle : (Gas.messageCallGas v g L mc e).cost + E ≤ G) :
    G - ((Gas.messageCallGas v g L mc e).cost + E) + (Gas.messageCallGas v g L mc e).subCall ≤ G := by
  have := messageCallGas_subCall_le (g := g) (L := L) (mc := mc) h
  omega

/-- The side condition of `refund_le` for a value transfer. -/
theorem stipend_side (value : Word) (e : Nat) :
    value.toNat = 0 ∨ Gas.callStipend ≤ e + (if value = 0 then 0 else Gas.callValue) := by
  by_cases hv : value = 0
  · left; simp [hv]
  · right; simp only [hv, ite_false]; simp only [Gas.callStipend, Gas.callValue]; omega

/-! ## Every instruction -/

/-- The postcondition of `exec_frame`. -/
abbrev ExecPost (m : Machine) (a : Action) (m' : Machine) : Prop :=
  InstrFrame m m' ∧ ActionOk m m' a

set_option maxHeartbeats 1000000 in
/-- The `CALL*` family. -/
theorem execCall_frame (k : CallKind) (m : Machine) : Wp (execCall k) (ExecPost m) m := by
  cases k <;> simp [ExecPost, execCall, instrFrame_iff, ActionOk, memoryExpansion, expandMemory, readMemory,
    setReturnData, genericCall] <;>
  repeat' (first | (intro _) | apply And.intro)
  all_goals (first
    | (apply refund_le <;> first | assumption | (left; rfl) | apply stipend_side)
    | (constructor <;> simp only <;> first
        | rfl | assumption
        | (apply refund_le <;> first | assumption | (left; rfl) | apply stipend_side)
        | (intro h; simp at h)
        | (intro h; simp_all)))

set_option maxHeartbeats 1000000 in
/-- `CREATE` and `CREATE2`. -/
theorem execCreate_frame (b : Bool) (m : Machine) : Wp (execCreate b) (ExecPost m) m := by
  have hk : ∀ p, ¬ m.world.code p = ByteArray.empty → ¬ Writable m p →
      Keep p m.world (incrementNonce m.world m.frame.msg.currentTarget) :=
    fun p hp _ => keep_incrementNonce (size_ne_zero_of_ne_empty hp)
  cases b <;> simp [ExecPost, execCreate, requireNonStatic, instrFrame_iff, ActionOk, memoryExpansion,
    expandMemory, readMemory, setReturnData] <;>
  repeat' (first | exact hk | (intro _) | apply And.intro)
  all_goals (first
    | assumption | omega
    | (simp only [Gas.maxMessageCallGas]; omega)
    | (constructor <;> simp only <;> first
        | rfl | assumption | omega
        | (simp only [Gas.maxMessageCallGas]; omega)
        | (rw [size_code_incrementNonce]; exact size_code_of_deployable (by assumption))))

/-- `SSTORE` writes only the executing account, and only in a non-static frame. -/
theorem execSstore_frame (m : Machine) : Wp execSstore (ExecPost m) m := by
  simp [ExecPost, execSstore, accessStorageKey, requireNonStatic, instrFrame_iff, ActionOk,
    setStorage]
  intro _ _ _ _ _ _ _
  constructor <;> intro _ _ hs p _ hw <;> exact keep_sstore (fun h => hw ⟨h, hs⟩)

/-- `SELFDESTRUCT` moves the balance only. -/
theorem execSelfdestruct_frame (m : Machine) : Wp execSelfdestruct (ExecPost m) m := by
  simp [ExecPost, execSelfdestruct, requireNonStatic, instrFrame_iff, ActionOk]
  intro x _ _ _ _
  have hk : ∀ p, ¬ m.world.code p = ByteArray.empty → Keep p m.world
      (moveEther m.world m.frame.msg.currentTarget (Word.toAddress x)
        (m.world.balance m.frame.msg.currentTarget)) :=
    fun p hp => keep_moveEther (size_ne_zero_of_ne_empty hp)
  refine ⟨fun _ => ⟨?_, ?_⟩, fun _ => ⟨?_, ?_⟩⟩ <;> intro _ p hp _
  · exact (hk p hp).trans (keep_setAccountBalance (by rw [(hk p hp).code]; exact size_ne_zero_of_ne_empty hp))
  · exact (hk p hp).trans (keep_setAccountBalance (by rw [(hk p hp).code]; exact size_ne_zero_of_ne_empty hp))
  · exact hk p hp
  · exact hk p hp

set_option maxHeartbeats 4000000 in
/-- **The frame condition of every instruction.** -/
theorem exec_frame (op : Opcode) (m : Machine) : Wp (exec op) (ExecPost m) m := by
  cases op
  case sstore => exact execSstore_frame m
  case selfdestruct => exact execSelfdestruct_frame m
  case create => exact execCreate_frame false m
  case create2 => exact execCreate_frame true m
  case call => exact execCall_frame .call m
  case callcode => exact execCall_frame .callcode m
  case delegatecall => exact execCall_frame .delegatecall m
  case staticcall => exact execCall_frame .staticcall m
  all_goals simp [ExecPost, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    instrFrame_iff, ActionOk]
  case dup => intro _; split <;> simp [ExecPost, instrFrame_iff, ActionOk]
  case swap => intro _; split <;> simp [ExecPost, instrFrame_iff, ActionOk]
  case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp)

end EvmLogic.Program.Nested
