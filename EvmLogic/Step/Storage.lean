import EvmLogic.Step.Basic
import EvmLogic.State

/-!
# Step lemmas: storage

`SLOAD` and `SSTORE` (EIP-2929 warm/cold accounting, EIP-2200/3529 costs and refunds), and
`TLOAD`/`TSTORE` (EIP-1153).

The accessed key is always added to the warm set (`addStorageKey`); adding a key that is
already warm changes nothing (`addStorageKey_of_warm`), so the lemmas need no case split
on warmness. The gas charged is stated exactly; `Gas.sstoreCostRefund` is at most
`2100 + 20000` (`sstoreCost_le`).
-/

namespace EvmLean.Interpreter

variable {m : Machine} {x y : Word} {rest : List Word}

/-- The substate with storage key `k` of `a` marked warm. -/
def Substate.warmKey (sub : Substate) (a : Address) (k : Word) : Substate :=
  { sub with accessedStorageKeys := addStorageKey sub.accessedStorageKeys a k }

/-- The substate with `r` added to the refund counter. -/
def Substate.addRefund (sub : Substate) (r : Int) : Substate :=
  { sub with refundCounter := sub.refundCounter + r }

/-- Marking a key warm twice is marking it once. -/
@[simp] theorem Substate.warmKey_warmKey (sub : Substate) (a : Address) (k : Word) :
    (sub.warmKey a k).warmKey a k = sub.warmKey a k := by
  simp only [Substate.warmKey]
  rw [addStorageKey_of_warm (storageKeyWarm_addStorageKey_self _ _ _)]

/-- The warm keys after `warmKey`. -/
@[simp] theorem Substate.accessedStorageKeys_warmKey (sub : Substate) (a : Address) (k : Word) :
    (sub.warmKey a k).accessedStorageKeys = addStorageKey sub.accessedStorageKeys a k := rfl

/-- The warm keys after `addRefund`. -/
@[simp] theorem Substate.accessedStorageKeys_addRefund (sub : Substate) (r : Int) :
    (sub.addRefund r).accessedStorageKeys = sub.accessedStorageKeys := rfl

/-- The original value of a slot of an account not created in this transaction. -/
@[simp] theorem getStorageOriginal_empty (o : World) (a : Address) (k : Word) :
    getStorageOriginal o ∅ a k = o.sload a k := by
  simp [getStorageOriginal]

/-- `accessStorageKey` marks the key warm and reports whether it already was. -/
theorem run_accessStorageKey (k : Word) :
    (accessStorageKey k).run m = pure
      (storageKeyWarm m.frame.sub.accessedStorageKeys m.frame.msg.currentTarget k,
       { m with frame := { m.frame with
          sub := m.frame.sub.warmKey m.frame.msg.currentTarget k } }) := by
  cases hw : storageKeyWarm m.frame.sub.accessedStorageKeys m.frame.msg.currentTarget k
  · simp only [accessStorageKey, getFrame, modifySub, modifyFrame, StateT.run_bind, hw,
      StateT.run_get, StateT.run_pure, pure_bind]
    rfl
  · simp only [accessStorageKey, getFrame, modifySub, modifyFrame, StateT.run_bind, hw,
      StateT.run_get, StateT.run_pure, pure_bind, Substate.warmKey, addStorageKey_of_warm hw]
    rfl

/-- The EIP-2929 cost of `SLOAD`. -/
def sloadCost (warm : Bool) : Nat := if warm then Gas.warmAccess else Gas.coldStorageAccess

/-- `SLOAD` costs at most 2100. -/
theorem sloadCost_le (warm : Bool) : sloadCost warm ≤ 2100 := by
  cases warm <;> decide

/-- `SLOAD` of slot `x` of the executing account. -/
theorem step_sload (hcode : m.frame.code[m.frame.pc]? = some 0x54)
    (hstk : m.frame.stack = x :: rest) (hlen : rest.length < 1024)
    (hgas : sloadCost (storageKeyWarm m.frame.sub.accessedStorageKeys
      m.frame.msg.currentTarget x) ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := m.world.sload m.frame.msg.currentTarget x :: rest,
      gasLeft := m.frame.gasLeft - sloadCost (storageKeyWarm m.frame.sub.accessedStorageKeys
        m.frame.msg.currentTarget x),
      sub := m.frame.sub.warmKey m.frame.msg.currentTarget x,
      pc := m.frame.pc + 1 } } := by
  have hg := Nat.not_lt.mpr hgas
  have hl : ¬ Gas.stackLimit ≤ rest.length := Nat.not_le.mpr hlen
  simp only [sloadCost] at hg
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x54 = .sload by
    cases m.ctx.fork <;> rfl]
  simp only [exec, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind, hstk,
    StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, run_accessStorageKey]
  simp only [hg, hl, ite_false, StateT.run_modify, pure_bind]
  rfl

/-- The `(cost, refund)` of `SSTORE x := y` in machine `m` (EIP-2200/2929/3529). -/
def sstoreCostRefund (m : Machine) (x y : Word) : Nat × Int :=
  let self := m.frame.msg.currentTarget
  Gas.sstoreCostRefund (getStorageOriginal m.originalWorld m.createdAccounts self x).toNat
    (m.world.sload self x).toNat y.toNat
    (storageKeyWarm m.frame.sub.accessedStorageKeys self x)

/-- `SSTORE` costs at most `2100 + 20000`. -/
theorem _root_.EvmLean.Gas.sstoreCostRefund_fst_le (o c n : Nat) (warm : Bool) :
    (Gas.sstoreCostRefund o c n warm).1 ≤ 22100 := by
  simp only [Gas.sstoreCostRefund]
  split <;> split <;> (try split) <;> simp [Gas.coldStorageAccess, Gas.storageSet,
    Gas.coldStorageWrite, Gas.warmAccess]

/-- `SSTORE` costs at most `2100 + 20000`. -/
theorem sstoreCost_le (m : Machine) (x y : Word) : (sstoreCostRefund m x y).1 ≤ 22100 :=
  Gas.sstoreCostRefund_fst_le _ _ _ _

/-- `SSTORE` of `y` to slot `x` of the executing account (non-static frame, more than the
2300-gas stipend left, enough gas for the cost). -/
theorem step_sstore (hcode : m.frame.code[m.frame.pc]? = some 0x55)
    (hstk : m.frame.stack = x :: y :: rest) (hstatic : m.frame.msg.isStatic = false)
    (hstipend : Gas.callStipend < m.frame.gasLeft)
    (hgas : (sstoreCostRefund m x y).1 ≤ m.frame.gasLeft) :
    step m = .running { m with
      world := m.world.sstore m.frame.msg.currentTarget x y
      frame := { m.frame with
        stack := rest,
        gasLeft := m.frame.gasLeft - (sstoreCostRefund m x y).1,
        sub := (m.frame.sub.warmKey m.frame.msg.currentTarget x).addRefund
          (sstoreCostRefund m x y).2,
        pc := m.frame.pc + 1 } } := by
  have hg := Nat.not_lt.mpr hgas
  have hs : ¬ m.frame.gasLeft ≤ Gas.callStipend := Nat.not_le.mpr hstipend
  simp only [sstoreCostRefund] at hg
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x55 = .sstore by
    cases m.ctx.fork <;> rfl]
  simp only [exec, execSstore, pop, getFrame, modifyFrame, StateT.run_bind, hstk,
    StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, hs, ite_false]
  simp only [run_accessStorageKey, StateT.run_bind, pure_bind, modifySub, modifyFrame,
    StateT.run_modify, charge, getFrame, StateT.run_get, StateT.run_pure]
  simp only [hg, ite_false, requireNonStatic, getFrame, StateT.run_bind, StateT.run_get,
    StateT.run_pure, pure_bind, hstatic, Bool.false_eq_true, modifyWorld, StateT.run_modify,
    advance, modifyFrame, setStorage]
  rfl

end EvmLean.Interpreter
