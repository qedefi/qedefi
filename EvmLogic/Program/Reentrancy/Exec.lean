import EvmLogic.Program.Nested.Frame

/-!
# What one instruction costs, and what it can do with little gas

Two per-instruction facts used by the reentrancy rules (`EvmLogic.Program.Reentrancy.Halts`):

* `exec_strict`: every successful instruction that continues the frame or requests a child
  **strictly** decreases the gas of the frame: `.next` leaves less gas, and a requested child
  gets strictly less than what the caller gave up (a call always pays at least the warm access
  cost, a creation at least 32000). This makes every frame terminate (`halts_inv`).
* `exec_low`: with at most `Gas.callStipend` (2300) gas, an instruction leaves the world
  unchanged (`SSTORE` throws below the EIP-2200 sentry, `SELFDESTRUCT` costs 5000), requests no
  creation (32000) and no call that moves value (9000). This is the stipend lemma's
  per-instruction part (`halts_low`).
-/

namespace EvmLogic.Program.Reentrancy
open EvmLean EvmLean.Interpreter EvmLogic.Program.Nested

/-- What a successful instruction does to the frame's gas: strictly less after `.next`, and a
requested child gets strictly less than the caller gave up; a creation comes from a non-static
frame. -/
def StrictPost (m : Machine) : Action → Machine → Prop
  | .next, m' => m'.frame.gasLeft < m.frame.gasLeft
  | .call req, m' => m'.frame.gasLeft + req.msg.gas < m.frame.gasLeft
  | .create msg, m' => m'.frame.gasLeft + msg.gas < m.frame.gasLeft ∧ m.frame.msg.isStatic = false
  | .stop _, _ => True
  | .revert _, _ => True

/-- What a successful instruction does with at most `Gas.callStipend` gas: the world is
unchanged, no creation, no call that moves value. -/
def LowPost (m : Machine) : Action → Machine → Prop
  | .call req, m' => m'.world = m.world ∧
      (req.msg.shouldTransferValue = false ∨ req.msg.value = 0)
  | .create _, _ => False
  | _, m' => m'.world = m.world

@[simp] theorem strictPost_next {m m' : Machine} :
    StrictPost m .next m' ↔ m'.frame.gasLeft < m.frame.gasLeft := Iff.rfl
@[simp] theorem strictPost_call {m m' : Machine} {req : CallRequest} :
    StrictPost m (.call req) m' ↔ m'.frame.gasLeft + req.msg.gas < m.frame.gasLeft := Iff.rfl
@[simp] theorem strictPost_create {m m' : Machine} {msg : Message} :
    StrictPost m (.create msg) m' ↔
      m'.frame.gasLeft + msg.gas < m.frame.gasLeft ∧ m.frame.msg.isStatic = false := Iff.rfl
@[simp] theorem strictPost_stop {m m' : Machine} {o : ByteArray} : StrictPost m (.stop o) m' :=
  trivial
@[simp] theorem strictPost_revert {m m' : Machine} {o : ByteArray} :
    StrictPost m (.revert o) m' := trivial

@[simp] theorem lowPost_next {m m' : Machine} : LowPost m .next m' ↔ m'.world = m.world :=
  Iff.rfl
@[simp] theorem lowPost_stop {m m' : Machine} {o : ByteArray} :
    LowPost m (.stop o) m' ↔ m'.world = m.world := Iff.rfl
@[simp] theorem lowPost_revert {m m' : Machine} {o : ByteArray} :
    LowPost m (.revert o) m' ↔ m'.world = m.world := Iff.rfl
@[simp] theorem lowPost_call {m m' : Machine} {req : CallRequest} :
    LowPost m (.call req) m' ↔ m'.world = m.world ∧
      (req.msg.shouldTransferValue = false ∨ req.msg.value = 0) := Iff.rfl
@[simp] theorem lowPost_create {m m' : Machine} {msg : Message} :
    LowPost m (.create msg) m' ↔ False := Iff.rfl

/-- The postcondition of `exec_strict`. -/
abbrev ExecStrict (m : Machine) (a : Action) (m' : Machine) : Prop :=
  StrictPost m a m' ∧ (m.frame.gasLeft ≤ Gas.callStipend → LowPost m a m')


/-- Positivity of an instruction's gas cost (unfolds the constants, splits the warm/cold cases). -/
macro "gas_pos" : tactic => `(tactic| (simp only [Gas.veryLow, Gas.low, Gas.mid, Gas.high, Gas.base,
  Gas.fastStep, Gas.warmAccess, Gas.coldStorageAccess, Gas.coldAccountAccess, Gas.accessCost,
  Gas.blockhash, Gas.jumpdest, Gas.blobhash, Gas.expCost, Gas.expBase, Gas.keccak256Cost,
  Gas.keccak256Base, Gas.logCost, Gas.logBase, Gas.callStipend]; (repeat' split) <;> omega))

/-- Close a goal `g - c < g` (and the low-gas world conjunct) left by `exec_strict`. -/
macro "gas_close" : tactic => `(tactic| first
  | (apply Nat.sub_lt_self (by gas_pos) (by assumption))
  | (refine ⟨Nat.sub_lt_self (by gas_pos) (by assumption), ?_⟩; intros; first | rfl | omega)
  | omega)


/-- `SSTORE` costs at least a warm read. -/
theorem sstoreCost_ge (o c n : Nat) (w : Bool) : 100 ≤ (Gas.sstoreCostRefund o c n w).1 := by
  unfold Gas.sstoreCostRefund
  simp only [Gas.coldStorageAccess, Gas.storageSet, Gas.coldStorageWrite, Gas.warmAccess]
  split <;> (try split) <;> (try split) <;> omega

/-- `SELFDESTRUCT` costs at least 5000. -/
theorem selfdestructCost_ge (a b c : Bool) : 5000 ≤ Gas.selfdestructCost a b c := by
  unfold Gas.selfdestructCost; simp only [Gas.selfdestructBase]; omega

/-- `SELFDESTRUCT` is unaffordable with a stipend. -/
theorem selfdestruct_contra {a b c : Bool} {g : Nat} (h : Gas.selfdestructCost a b c ≤ g)
    (h2 : g ≤ Gas.callStipend) : False := by
  have := selfdestructCost_ge a b c; simp only [Gas.callStipend] at h2; omega

/-- A call request costs the caller strictly more than the child gets, when the extra cost is
positive and exceeds the stipend if value moves. -/
theorem call_lt {v g L mc e E G : Nat} (he : (v = 0 ∧ 0 < e) ∨ Gas.callStipend < e)
    (h : (Gas.messageCallGas v g L mc e).cost + E ≤ G) :
    G - ((Gas.messageCallGas v g L mc e).cost + E) + (Gas.messageCallGas v g L mc e).subCall < G := by
  have hs : (Gas.messageCallGas v g L mc e).subCall + e =
      (Gas.messageCallGas v g L mc e).cost + (if v = 0 then 0 else Gas.callStipend) := by
    simp only [Gas.messageCallGas]
    by_cases hL : L < e + mc <;> simp only [hL, ite_true, ite_false] <;> omega
  generalize (Gas.messageCallGas v g L mc e).subCall = s at hs ⊢
  generalize (Gas.messageCallGas v g L mc e).cost = c at hs h ⊢
  simp only [Gas.callStipend] at he hs
  by_cases hv : v = 0 <;> simp only [hv, ite_true, ite_false, true_and, false_and, false_or] at he hs <;> omega

/-- The caller pays at least the extra cost of a call. -/
theorem cost_ge {v g L mc e : Nat} : e ≤ (Gas.messageCallGas v g L mc e).cost := by
  simp only [Gas.messageCallGas]
  by_cases hL : L < e + mc <;> simp only [hL, ite_true, ite_false] <;> omega

/-- With a stipend, a call moving value is unaffordable. -/
theorem value_zero_of_low {x : Word} {v g L mc e E G : Nat}
    (h : (Gas.messageCallGas v g L mc e).cost + E ≤ G) (hG : G ≤ Gas.callStipend)
    (he : ¬ x = 0#256 → Gas.callValue ≤ e) : x = 0#256 := by
  have := cost_ge (v := v) (g := g) (L := L) (mc := mc) (e := e)
  apply Classical.byContradiction
  intro hx
  have := he hx
  simp only [Gas.callValue, Gas.callStipend] at *; omega


set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_strict` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_strict_0 (op : Opcode) (hk : op.ctorIdx ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8]) (m : Machine) : Wp (exec op) (ExecStrict m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [ExecStrict, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [ExecStrict] <;> (repeat' (first | (intro _) | apply And.intro)) <;> gas_close
  try case swap => intro _; split <;> simp [ExecStrict] <;> (repeat' (first | (intro _) | apply And.intro)) <;> gas_close
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp; intros; gas_close)
  all_goals (repeat' (first | (intro _) | apply And.intro)); all_goals (try gas_close)

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_strict` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_strict_1 (op : Opcode) (hk : op.ctorIdx ∈ [9, 10, 11, 12, 13, 14, 15, 16, 17, 18]) (m : Machine) : Wp (exec op) (ExecStrict m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [ExecStrict, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [ExecStrict] <;> (repeat' (first | (intro _) | apply And.intro)) <;> gas_close
  try case swap => intro _; split <;> simp [ExecStrict] <;> (repeat' (first | (intro _) | apply And.intro)) <;> gas_close
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp; intros; gas_close)
  all_goals (repeat' (first | (intro _) | apply And.intro)); all_goals (try gas_close)

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_strict` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_strict_2 (op : Opcode) (hk : op.ctorIdx ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27]) (m : Machine) : Wp (exec op) (ExecStrict m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [ExecStrict, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [ExecStrict] <;> (repeat' (first | (intro _) | apply And.intro)) <;> gas_close
  try case swap => intro _; split <;> simp [ExecStrict] <;> (repeat' (first | (intro _) | apply And.intro)) <;> gas_close
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp; intros; gas_close)
  all_goals (repeat' (first | (intro _) | apply And.intro)); all_goals (try gas_close)

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_strict` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_strict_3 (op : Opcode) (hk : op.ctorIdx ∈ [28, 29, 30, 31, 32, 33, 34, 35, 36, 37]) (m : Machine) : Wp (exec op) (ExecStrict m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [ExecStrict, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [ExecStrict] <;> (repeat' (first | (intro _) | apply And.intro)) <;> gas_close
  try case swap => intro _; split <;> simp [ExecStrict] <;> (repeat' (first | (intro _) | apply And.intro)) <;> gas_close
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp; intros; gas_close)
  all_goals (repeat' (first | (intro _) | apply And.intro)); all_goals (try gas_close)

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_strict` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_strict_4 (op : Opcode) (hk : op.ctorIdx ∈ [38, 39, 40, 41, 42, 43, 44, 45, 46]) (m : Machine) : Wp (exec op) (ExecStrict m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [ExecStrict, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [ExecStrict] <;> (repeat' (first | (intro _) | apply And.intro)) <;> gas_close
  try case swap => intro _; split <;> simp [ExecStrict] <;> (repeat' (first | (intro _) | apply And.intro)) <;> gas_close
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp; intros; gas_close)
  all_goals (repeat' (first | (intro _) | apply And.intro)); all_goals (try gas_close)

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_strict` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_strict_5 (op : Opcode) (hk : op.ctorIdx ∈ [47, 48, 49, 50, 51, 52, 53, 54, 55, 56]) (m : Machine) : Wp (exec op) (ExecStrict m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [ExecStrict, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [ExecStrict] <;> (repeat' (first | (intro _) | apply And.intro)) <;> gas_close
  try case swap => intro _; split <;> simp [ExecStrict] <;> (repeat' (first | (intro _) | apply And.intro)) <;> gas_close
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp; intros; gas_close)
  all_goals (repeat' (first | (intro _) | apply And.intro)); all_goals (try gas_close)

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_strict` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_strict_6 (op : Opcode) (hk : op.ctorIdx ∈ [57, 58, 59, 61, 62, 63, 64, 65, 66]) (m : Machine) : Wp (exec op) (ExecStrict m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [ExecStrict, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [ExecStrict] <;> (repeat' (first | (intro _) | apply And.intro)) <;> gas_close
  try case swap => intro _; split <;> simp [ExecStrict] <;> (repeat' (first | (intro _) | apply And.intro)) <;> gas_close
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp; intros; gas_close)
  all_goals (repeat' (first | (intro _) | apply And.intro)); all_goals (try gas_close)

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_strict` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_strict_7 (op : Opcode) (hk : op.ctorIdx ∈ [67, 68, 69, 70, 71, 72, 73, 77, 81, 82]) (m : Machine) : Wp (exec op) (ExecStrict m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [ExecStrict, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [ExecStrict] <;> (repeat' (first | (intro _) | apply And.intro)) <;> gas_close
  try case swap => intro _; split <;> simp [ExecStrict] <;> (repeat' (first | (intro _) | apply And.intro)) <;> gas_close
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp; intros; gas_close)
  all_goals (repeat' (first | (intro _) | apply And.intro)); all_goals (try gas_close)

/-- `exec_strict` for `SSTORE`. -/
theorem execSstore_strict (m : Machine) : Wp execSstore (ExecStrict m) m := by
  simp [ExecStrict, execSstore, accessStorageKey, requireNonStatic, setStorage]
  repeat' (first | (intro _) | apply And.intro)
  all_goals first
    | (apply Nat.sub_lt_self (Nat.lt_of_lt_of_le (by decide) (sstoreCost_ge _ _ _ _)) (by assumption))
    | omega

/-- `exec_strict` for `SELFDESTRUCT`. -/
theorem execSelfdestruct_strict (m : Machine) : Wp execSelfdestruct (ExecStrict m) m := by
  simp [ExecStrict, execSelfdestruct, requireNonStatic]
  repeat' (first | (intro _) | apply And.intro)
  all_goals exact (selfdestruct_contra (by assumption) (by assumption)).elim

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_strict` for `CREATE`/`CREATE2`. -/
theorem execCreate_strict (b : Bool) (m : Machine) : Wp (execCreate b) (ExecStrict m) m := by
  cases b <;> simp [ExecStrict, execCreate, requireNonStatic, memoryExpansion,
    expandMemory, readMemory, setReturnData]
  all_goals (repeat' (first | (intro _) | apply And.intro))
  all_goals first
    | assumption
    | (simp only [Gas.createCost, Gas.create2Cost, Gas.createBase, Gas.maxMessageCallGas,
        Gas.callStipend] at *; omega)

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_strict` for `CALL`. -/
theorem execCall_strict_call (m : Machine) : Wp (execCall .call) (ExecStrict m) m := by
  simp [ExecStrict, execCall, memoryExpansion, expandMemory, readMemory,
    setReturnData, genericCall]
  all_goals (repeat' (first | (intro _) | apply And.intro))
  all_goals (try (apply call_lt _ (by assumption); simp only [Gas.accessCost, Gas.newAccount, Gas.callValue, Gas.callStipend, Gas.warmAccess, Gas.coldAccountAccess]; (repeat' split) <;> (try subst_vars) <;> simp <;> omega))
  all_goals (apply value_zero_of_low <;> first | assumption | (intro hx; simp only [hx, ite_false, false_or, Gas.callValue]; omega))

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_strict` for `CALLCODE`. -/
theorem execCall_strict_callcode (m : Machine) : Wp (execCall .callcode) (ExecStrict m) m := by
  simp [ExecStrict, execCall, memoryExpansion, expandMemory, readMemory,
    setReturnData, genericCall]
  all_goals (repeat' (first | (intro _) | apply And.intro))
  all_goals (try (apply call_lt _ (by assumption); simp only [Gas.accessCost, Gas.newAccount, Gas.callValue, Gas.callStipend, Gas.warmAccess, Gas.coldAccountAccess]; (repeat' split) <;> (try subst_vars) <;> simp <;> omega))
  all_goals (apply value_zero_of_low <;> first | assumption | (intro hx; simp only [hx, ite_false, false_or, Gas.callValue]; omega))

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_strict` for `DELEGATECALL`. -/
theorem execCall_strict_delegatecall (m : Machine) : Wp (execCall .delegatecall) (ExecStrict m) m := by
  simp [ExecStrict, execCall, memoryExpansion, expandMemory, readMemory,
    setReturnData, genericCall]
  all_goals (repeat' (first | (intro _) | apply And.intro))
  all_goals (try (apply call_lt _ (by assumption); simp only [Gas.accessCost, Gas.newAccount, Gas.callValue, Gas.callStipend, Gas.warmAccess, Gas.coldAccountAccess]; (repeat' split) <;> (try subst_vars) <;> simp <;> omega))
  all_goals (apply value_zero_of_low <;> first | assumption | (intro hx; simp only [hx, ite_false, false_or, Gas.callValue]; omega))

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_strict` for `STATICCALL`. -/
theorem execCall_strict_staticcall (m : Machine) : Wp (execCall .staticcall) (ExecStrict m) m := by
  simp [ExecStrict, execCall, memoryExpansion, expandMemory, readMemory,
    setReturnData, genericCall]
  all_goals (repeat' (first | (intro _) | apply And.intro))
  all_goals (try (apply call_lt _ (by assumption); simp only [Gas.accessCost, Gas.newAccount, Gas.callValue, Gas.callStipend, Gas.warmAccess, Gas.coldAccountAccess]; (repeat' split) <;> (try subst_vars) <;> simp <;> omega))
  all_goals (apply value_zero_of_low <;> first | assumption | (intro hx; simp only [hx, ite_false, false_or, Gas.callValue]; omega))

set_option maxHeartbeats 4000000 in
/-- **Strict gas and low-gas effects of every instruction.** -/
theorem exec_strict (op : Opcode) (m : Machine) : Wp (exec op) (ExecStrict m) m := by
  cases op
  case sstore => exact execSstore_strict m
  case selfdestruct => exact execSelfdestruct_strict m
  case create => exact execCreate_strict false m
  case create2 => exact execCreate_strict true m
  case call => exact execCall_strict_call m
  case callcode => exact execCall_strict_callcode m
  case delegatecall => exact execCall_strict_delegatecall m
  case staticcall => exact execCall_strict_staticcall m
  all_goals first
    | exact exec_strict_0 _ (by dsimp only [Opcode.ctorIdx]; decide) m |
      exact exec_strict_1 _ (by dsimp only [Opcode.ctorIdx]; decide) m |
      exact exec_strict_2 _ (by dsimp only [Opcode.ctorIdx]; decide) m |
      exact exec_strict_3 _ (by dsimp only [Opcode.ctorIdx]; decide) m |
      exact exec_strict_4 _ (by dsimp only [Opcode.ctorIdx]; decide) m |
      exact exec_strict_5 _ (by dsimp only [Opcode.ctorIdx]; decide) m |
      exact exec_strict_6 _ (by dsimp only [Opcode.ctorIdx]; decide) m |
      exact exec_strict_7 _ (by dsimp only [Opcode.ctorIdx]; decide) m
    | fail "exec_strict: no group"

end EvmLogic.Program.Reentrancy
