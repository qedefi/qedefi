import EvmLogic.Program.Call
import EvmLogic.State

/-!
# `SELFDESTRUCT` (EIP-6780)

`SELFDESTRUCT` pops a beneficiary, warms it (EIP-2929), charges `5000` plus the cold access cost
plus `25000` when value moves to a dead account, and then, in a non-static frame:

* moves the executing account's whole balance to the beneficiary (`moveEther`; nothing is
  burnt when the beneficiary is the account itself, unless it was created in this transaction);
* **only if the account was created in this transaction** (EIP-6780): zeroes its balance and
  schedules it for deletion (`accountsToDelete`, applied at the end of the transaction);
  otherwise code and storage stay (`selfdestructWorld_of_not_created`,
  `selfdestructSub_accountsToDelete_of_not_created`);
* marks the beneficiary touched if it is empty (EIP-161);

and ends the frame successfully with empty output (`step_selfdestruct`). In a static frame it
halts with `writeInStaticContext` (`step_selfdestruct_static`).
-/

namespace EvmLogic.Program
open EvmLean EvmLean.Interpreter

/-- The cost of `SELFDESTRUCT` to `bene` from the frame of `m`. -/
def selfdestructCost (m : Machine) (bene : Address) : Nat :=
  Gas.selfdestructCost (m.frame.sub.accessedAddresses.contains bene)
    (isAccountAlive m.world bene) (m.world.balance m.frame.msg.currentTarget ≠ 0)

/-- The world after `SELFDESTRUCT` to `bene`: the balance moved, then zeroed if the account was
created in this transaction (EIP-6780). -/
def selfdestructWorld (m : Machine) (bene : Address) : World :=
  let self := m.frame.msg.currentTarget
  let w := moveEther m.world self bene (m.world.balance self)
  if m.createdAccounts.contains self then setAccountBalance w self 0 else w

/-- The substate after `SELFDESTRUCT` to `bene`: the beneficiary warm, the account scheduled
for deletion if created in this transaction, the beneficiary touched if empty. -/
def selfdestructSub (m : Machine) (bene : Address) : Substate :=
  let self := m.frame.msg.currentTarget
  let s := m.frame.sub.warmAddr bene
  let s := if m.createdAccounts.contains self then
    { s with accountsToDelete := s.accountsToDelete.insert self } else s
  if accountExistsAndIsEmpty (selfdestructWorld m bene) bene then
    { s with touchedAccounts := s.touchedAccounts.insert bene } else s

/-- The machine with which the frame ends. -/
def selfdestructMachine (m : Machine) (bene : Address) (rest : List Word) : Machine :=
  { m with
    world := selfdestructWorld m bene
    frame := { m.frame with
      stack := rest
      gasLeft := m.frame.gasLeft - selfdestructCost m bene
      sub := selfdestructSub m bene } }

theorem decode_selfdestruct (fk : Fork) : Opcode.decode fk 0xff = .selfdestruct := by
  cases fk <;> rfl

variable {m : Machine} {x : Word} {rest : List Word}

/-- **`SELFDESTRUCT`** in a non-static frame ends it successfully with empty output, after the
balance moves to the beneficiary `Word.toAddress x` (see the module docstring). -/
theorem step_selfdestruct (hcode : m.frame.code[m.frame.pc]? = some 0xff)
    (hstk : m.frame.stack = x :: rest) (hstatic : m.frame.msg.isStatic = false)
    (hgas : selfdestructCost m (Word.toAddress x) ≤ m.frame.gasLeft) :
    step m = finishFrame (selfdestructMachine m (Word.toAddress x) rest) (.success .empty) := by
  have hg : ¬ m.frame.gasLeft < selfdestructCost m (Word.toAddress x) := Nat.not_lt.mpr hgas
  simp only [selfdestructCost] at hg
  rw [step_eq_of_code hcode, decode_selfdestruct]
  simp only [exec, execSelfdestruct, popAddress, pop, getFrame, modifyFrame, StateT.run_bind,
    hstk, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind]
  rw [run_accessAddress]
  simp only [pure_bind, charge, getFrame, StateT.run_bind, StateT.run_get, StateT.run_pure,
    hg, ite_false, modifyFrame, StateT.run_modify, requireNonStatic, hstatic, Bool.false_eq_true,
    modifyWorld, modifySub]
  cases hc : m.createdAccounts.contains m.frame.msg.currentTarget <;>
  cases he : accountExistsAndIsEmpty (selfdestructWorld m (Word.toAddress x)) (Word.toAddress x) <;>
  simp only [selfdestructWorld, hc, Bool.false_eq_true, ite_false, ite_true] at he <;>
  simp only [he, Bool.false_eq_true, ite_false, ite_true, StateT.run_modify, StateT.run_bind,
    StateT.run_get, StateT.run_pure, pure_bind] <;>
  simp only [selfdestructMachine, selfdestructSub, selfdestructWorld, hc, he, Bool.false_eq_true,
    ite_false, ite_true] <;>
  rfl

/-- **`SELFDESTRUCT` in a static frame** (with gas for its charge) halts with
`writeInStaticContext`. -/
theorem step_selfdestruct_static (hcode : m.frame.code[m.frame.pc]? = some 0xff)
    (hstk : m.frame.stack = x :: rest) (hstatic : m.frame.msg.isStatic = true)
    (hgas : selfdestructCost m (Word.toAddress x) ≤ m.frame.gasLeft) :
    step m = finishFrame m (.halt .writeInStaticContext) := by
  have hg : ¬ m.frame.gasLeft < selfdestructCost m (Word.toAddress x) := Nat.not_lt.mpr hgas
  simp only [selfdestructCost] at hg
  refine step_of_exec_error hcode ?_
  rw [decode_selfdestruct]
  simp only [exec, execSelfdestruct, popAddress, pop, getFrame, modifyFrame, StateT.run_bind,
    hstk, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind]
  rw [run_accessAddress]
  simp only [pure_bind, charge, getFrame, StateT.run_bind, StateT.run_get, StateT.run_pure,
    hg, ite_false, modifyFrame, StateT.run_modify, requireNonStatic, hstatic, ite_true]
  rfl

/-- `SELFDESTRUCT` with less gas than its charge halts out of gas. -/
theorem step_selfdestruct_oog (hcode : m.frame.code[m.frame.pc]? = some 0xff)
    (hstk : m.frame.stack = x :: rest)
    (hgas : m.frame.gasLeft < selfdestructCost m (Word.toAddress x)) :
    step m = finishFrame m (.halt .outOfGas) := by
  simp only [selfdestructCost] at hgas
  refine step_of_exec_error hcode ?_
  rw [decode_selfdestruct]
  simp only [exec, execSelfdestruct, popAddress, pop, getFrame, modifyFrame, StateT.run_bind,
    hstk, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind]
  rw [run_accessAddress]
  simp only [pure_bind, charge, getFrame, StateT.run_bind, StateT.run_get, StateT.run_pure,
    hgas, ite_true]
  rfl

/-- The frame of `selfdestructMachine` is the frame of `m`. -/
theorem sameFrame_selfdestructMachine (m : Machine) (bene : Address) (rest : List Word) :
    SameFrame m (selfdestructMachine m bene rest) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## EIP-6780: what survives -/

/-- An account **not** created in this transaction keeps its code, storage and nonce: the
instruction only moves its balance. -/
theorem selfdestructWorld_of_not_created (m : Machine) (bene : Address)
    (h : m.createdAccounts.contains m.frame.msg.currentTarget = false) :
    selfdestructWorld m bene = moveEther m.world m.frame.msg.currentTarget bene
      (m.world.balance m.frame.msg.currentTarget) := by
  simp [selfdestructWorld, h]

/-- An account not created in this transaction is not scheduled for deletion. -/
theorem selfdestructSub_accountsToDelete_of_not_created (m : Machine) (bene : Address)
    (h : m.createdAccounts.contains m.frame.msg.currentTarget = false) :
    (selfdestructSub m bene).accountsToDelete = m.frame.sub.accountsToDelete := by
  simp only [selfdestructSub, h, Bool.false_eq_true, ite_false]
  split <;> rfl

/-- An account created in this transaction is scheduled for deletion. -/
theorem selfdestructSub_accountsToDelete_of_created (m : Machine) (bene : Address)
    (h : m.createdAccounts.contains m.frame.msg.currentTarget = true) :
    (selfdestructSub m bene).accountsToDelete =
      m.frame.sub.accountsToDelete.insert m.frame.msg.currentTarget := by
  simp only [selfdestructSub, h, ite_true]
  split <;> rfl

/-- After `SELFDESTRUCT` to another account, the executing account holds no ether. -/
theorem balance_selfdestructWorld_self (m : Machine) {bene : Address}
    (hne : m.frame.msg.currentTarget ≠ bene) :
    (selfdestructWorld m bene).balance m.frame.msg.currentTarget = 0 := by
  unfold selfdestructWorld
  dsimp only
  split
  · rw [setAccountBalance, balance_modifyState]; simp
  · rw [balance_moveEther _ _ hne]; simp

/-- After `SELFDESTRUCT` to another account, the beneficiary received the whole balance. -/
theorem balance_selfdestructWorld_bene (m : Machine) {bene : Address}
    (hne : m.frame.msg.currentTarget ≠ bene) :
    (selfdestructWorld m bene).balance bene =
      m.world.balance bene + m.world.balance m.frame.msg.currentTarget := by
  have hne' : bene ≠ m.frame.msg.currentTarget := fun e => hne e.symm
  unfold selfdestructWorld
  dsimp only
  split
  · simp [setAccountBalance, balance_modifyState, balance_moveEther _ _ hne, hne']
  · simp [balance_moveEther _ _ hne, hne']

end EvmLogic.Program
