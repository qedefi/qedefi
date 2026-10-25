import EvmLogic.Step.Basic
import EvmLogic.State

/-!
# Step lemmas: transient storage (EIP-1153)

`TLOAD` and `TSTORE` cost a flat 100 gas (`Gas.warmAccess`) and touch no access set and no
refund counter. `TSTORE` changes `Machine.transient` only (never the world), and halts with
`writeInStaticContext` in a static frame (`step_tstore_static`). Transient storage is rolled back
with the frame's snapshot on failure and cleared after the transaction, which the interpreter
handles outside the step. The read-after-write lemmas (`getTransient_setTransient_self`, `…_ne`)
let the step tactics evaluate `TLOAD` after `TSTORE`.
-/

namespace EvmLean.Interpreter

/-! ## Transient storage reads and writes -/

@[simp] theorem getTransient_empty (a : Address) (k : Word) :
    getTransient (∅ : TransientStorage) a k = 0 := by
  simp [getTransient]

@[simp] theorem getTransient_setTransient_self (t : TransientStorage) (a : Address) (k v : Word) :
    getTransient (setTransient t a k v) a k = v := by
  unfold getTransient setTransient
  dsimp only
  split
  · rename_i h
    rw [Std.ExtTreeMap.getD_erase_self]
    have := Storage.get_set_self (t.getD a ∅) k v
    rw [Std.ExtTreeMap.isEmpty_iff] at h
    rw [h] at this
    simpa using this
  · rw [Std.ExtTreeMap.getD_insert_self, Storage.get_set_self]

/-- `getTransient` of a modified address: unchanged. -/
theorem getTransient_setTransient_ne_addr (t : TransientStorage) {a b : Address} (k v k' : Word)
    (h : b ≠ a) : getTransient (setTransient t a k v) b k' = getTransient t b k' := by
  have h' : ¬ a = b := fun e => h e.symm
  unfold getTransient setTransient
  dsimp only
  split <;> simp [Std.ExtTreeMap.getD_erase, Std.ExtTreeMap.getD_insert, h']

/-- `getTransient` of another key of the modified address: unchanged. -/
theorem getTransient_setTransient_ne_key (t : TransientStorage) (a : Address) {k k' : Word}
    (v : Word) (h : k' ≠ k) : getTransient (setTransient t a k v) a k' = getTransient t a k' := by
  unfold getTransient setTransient
  dsimp only
  split
  · rename_i he
    rw [Std.ExtTreeMap.getD_erase_self]
    have := Storage.get_set_ne (t.getD a ∅) v h
    rw [Std.ExtTreeMap.isEmpty_iff] at he
    rw [he] at this
    simpa using this
  · rw [Std.ExtTreeMap.getD_insert_self, Storage.get_set_ne _ _ h]

/-- Read-after-write for transient storage, in one equation. -/
theorem getTransient_setTransient (t : TransientStorage) (a : Address) (k v : Word) (b : Address)
    (k' : Word) :
    getTransient (setTransient t a k v) b k' =
      if b = a ∧ k' = k then v else getTransient t b k' := by
  by_cases hb : b = a
  · subst hb
    by_cases hk : k' = k
    · subst hk; simp
    · simp only [hk, and_false, ite_false]; exact getTransient_setTransient_ne_key t b v hk
  · simp only [hb, false_and, ite_false]; exact getTransient_setTransient_ne_addr t k v k' hb

/-- Writing the value already stored changes nothing observable. -/
theorem getTransient_setTransient_getTransient (t : TransientStorage) (a : Address) (k : Word)
    (b : Address) (k' : Word) :
    getTransient (setTransient t a k (getTransient t a k)) b k' = getTransient t b k' := by
  rw [getTransient_setTransient]
  split
  · rename_i h; obtain ⟨rfl, rfl⟩ := h; rfl
  · rfl

/-! ## `TLOAD` and `TSTORE` -/

variable {m : Machine} {x y : Word} {rest : List Word}

theorem decode_tload (fk : Fork) : Opcode.decode fk 0x5c = .tload := by cases fk <;> rfl

theorem decode_tstore (fk : Fork) : Opcode.decode fk 0x5d = .tstore := by cases fk <;> rfl

/-- **`TLOAD`**: pushes slot `x` of the executing account's transient storage, for 100 gas
(`Gas.warmAccess`). -/
theorem step_tload (hcode : m.frame.code[m.frame.pc]? = some 0x5c)
    (hstk : m.frame.stack = x :: rest) (hlen : rest.length < 1024)
    (hgas : 100 ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := getTransient m.transient m.frame.msg.currentTarget x :: rest,
      gasLeft := m.frame.gasLeft - 100,
      pc := m.frame.pc + 1 } } := by
  have hg : ¬ m.frame.gasLeft < Gas.warmAccess := Nat.not_lt.mpr hgas
  have hl : ¬ Gas.stackLimit ≤ rest.length := Nat.not_le.mpr hlen
  rw [step_eq_of_code hcode, decode_tload]
  simp only [exec, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind, hstk,
    StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, hg, hl, ite_false]
  rfl

/-- **`TSTORE`** in a non-static frame: writes `y` to slot `x` of the executing account's
transient storage, for 100 gas (`Gas.warmAccess`). Unlike `SSTORE` there is no stipend sentry
and no refund. -/
theorem step_tstore (hcode : m.frame.code[m.frame.pc]? = some 0x5d)
    (hstk : m.frame.stack = x :: y :: rest) (hstatic : m.frame.msg.isStatic = false)
    (hgas : 100 ≤ m.frame.gasLeft) :
    step m = .running { m with
      transient := setTransient m.transient m.frame.msg.currentTarget x y
      frame := { m.frame with
        stack := rest,
        gasLeft := m.frame.gasLeft - 100,
        pc := m.frame.pc + 1 } } := by
  have hg : ¬ m.frame.gasLeft < Gas.warmAccess := Nat.not_lt.mpr hgas
  rw [step_eq_of_code hcode, decode_tstore]
  simp only [exec, pop, charge, advance, getFrame, modifyFrame, StateT.run_bind, hstk,
    StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, hg, ite_false,
    requireNonStatic, hstatic, Bool.false_eq_true]
  rfl

/-- **`TSTORE` in a static frame** (with gas for its charge) halts with `writeInStaticContext`:
the frame ends exceptionally from the machine before the instruction. -/
theorem step_tstore_static (hcode : m.frame.code[m.frame.pc]? = some 0x5d)
    (hstk : m.frame.stack = x :: y :: rest) (hstatic : m.frame.msg.isStatic = true)
    (hgas : 100 ≤ m.frame.gasLeft) :
    step m = finishFrame m (.halt .writeInStaticContext) := by
  have hg : ¬ m.frame.gasLeft < Gas.warmAccess := Nat.not_lt.mpr hgas
  refine step_of_exec_error hcode ?_
  rw [decode_tstore]
  simp only [exec, pop, charge, getFrame, modifyFrame, StateT.run_bind, hstk,
    StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, hg, ite_false,
    requireNonStatic, hstatic, ite_true]
  rfl

/-- `TLOAD` with less than 100 gas halts out of gas. -/
theorem step_tload_oog (hcode : m.frame.code[m.frame.pc]? = some 0x5c)
    (hstk : m.frame.stack = x :: rest) (hgas : m.frame.gasLeft < 100) :
    step m = finishFrame m (.halt .outOfGas) := by
  have hg : m.frame.gasLeft < Gas.warmAccess := hgas
  refine step_of_exec_error hcode ?_
  rw [decode_tload]
  simp only [exec, pop, charge, getFrame, modifyFrame, StateT.run_bind, hstk,
    StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, hg, ite_true]
  rfl

/-- `TSTORE` with less than 100 gas halts out of gas (static or not: the charge comes first). -/
theorem step_tstore_oog (hcode : m.frame.code[m.frame.pc]? = some 0x5d)
    (hstk : m.frame.stack = x :: y :: rest) (hgas : m.frame.gasLeft < 100) :
    step m = finishFrame m (.halt .outOfGas) := by
  have hg : m.frame.gasLeft < Gas.warmAccess := hgas
  refine step_of_exec_error hcode ?_
  rw [decode_tstore]
  simp only [exec, pop, charge, getFrame, modifyFrame, StateT.run_bind, hstk,
    StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, hg, ite_true]
  rfl

end EvmLean.Interpreter
