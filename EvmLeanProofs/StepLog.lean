import EvmLeanProofs.StepStack

/-!
# Step lemmas: `LOG0`–`LOG4`

`LOGn` pops `offset`, `size` and `n` topics, charges `375 + 8·size + 375·n` plus memory
expansion, and appends `{ address, topics, data := memory[offset, offset + size) }` to the
frame's logs. It halts in a static frame.
-/

namespace EvmLean.Interpreter

variable {m : Machine} {x y : Word} {rest : List Word}

/-- `popN` pops the listed words. -/
theorem run_popN (topics rest : List Word) (m : Machine)
    (hstk : m.frame.stack = topics ++ rest) :
    (popN topics.length).run m =
      pure (topics, { m with frame := { m.frame with stack := rest } }) := by
  induction topics generalizing m with
  | nil =>
    simp only [List.nil_append] at hstk
    simp only [List.length_nil, popN, StateT.run_pure]
    rw [← hstk]
  | cons t ts ih =>
    simp only [List.cons_append] at hstk
    simp only [List.length_cons, popN, pop, getFrame, modifyFrame, StateT.run_bind, hstk,
      StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind]
    rw [ih _ rfl]
    rfl

/-- The log entry appended by `LOGn` with topics `topics` reading `[x, x + y)`. -/
def logEntry (m : Machine) (x y : Word) (topics : List Word) : Log :=
  { address := m.frame.msg.currentTarget, topics := topics.toArray,
    data := readBytes (m.frame.memory.expand x.toNat y.toNat).bytes x.toNat y.toNat }

/-- `LOGn` (`n = topics.length`) in a non-static frame. -/
theorem step_log (n : Fin 5) (topics : List Word) (htop : topics.length = n.val)
    (hcode : m.frame.code[m.frame.pc]? = some (0xa0 + n.val).toUInt8)
    (hstk : m.frame.stack = x :: y :: (topics ++ rest)) (hstatic : m.frame.msg.isStatic = false)
    (hgas : Gas.logCost y.toNat n.val + (Gas.extendMemory m.frame.memory.size
      [(x.toNat, y.toNat)]).cost ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest,
      memory := m.frame.memory.expand x.toNat y.toNat,
      gasLeft := m.frame.gasLeft - (Gas.logCost y.toNat n.val + (Gas.extendMemory
        m.frame.memory.size [(x.toNat, y.toNat)]).cost),
      sub := { m.frame.sub with logs := m.frame.sub.logs.push (logEntry m x y topics) },
      pc := m.frame.pc + 1 } } := by
  have hg := Nat.not_lt.mpr hgas
  rw [step_eq_of_code hcode, decode_log]
  simp only [exec, execLog, popNat, pop, getFrame, modifyFrame, StateT.run_bind, hstk,
    StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ← htop]
  rw [run_popN topics rest _ rfl]
  simp only [pure_bind, memoryExpansion, charge, getFrame, StateT.run_bind, StateT.run_get,
    StateT.run_pure, pure_bind, hg, ite_false, StateT.run_modify, expandMemory, List.foldl,
    requireNonStatic, hstatic, Bool.false_eq_true, readMemory, modifySub, modifyFrame, advance,
    htop]
  rfl

/-- `LOG0`. -/
theorem step_log0 (hcode : m.frame.code[m.frame.pc]? = some 0xa0)
    (hstk : m.frame.stack = x :: y :: ([] ++ rest)) (hstatic : m.frame.msg.isStatic = false)
    (hgas : Gas.logCost y.toNat 0 + (Gas.extendMemory m.frame.memory.size
      [(x.toNat, y.toNat)]).cost ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest,
      memory := m.frame.memory.expand x.toNat y.toNat,
      gasLeft := m.frame.gasLeft - (Gas.logCost y.toNat 0 + (Gas.extendMemory
        m.frame.memory.size [(x.toNat, y.toNat)]).cost),
      sub := { m.frame.sub with logs := m.frame.sub.logs.push (logEntry m x y []) },
      pc := m.frame.pc + 1 } } :=
  step_log 0 [] rfl hcode hstk hstatic hgas

/-- `LOG1`. -/
theorem step_log1 {t0 : Word} (hcode : m.frame.code[m.frame.pc]? = some 0xa1)
    (hstk : m.frame.stack = x :: y :: ([t0] ++ rest)) (hstatic : m.frame.msg.isStatic = false)
    (hgas : Gas.logCost y.toNat 1 + (Gas.extendMemory m.frame.memory.size
      [(x.toNat, y.toNat)]).cost ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest,
      memory := m.frame.memory.expand x.toNat y.toNat,
      gasLeft := m.frame.gasLeft - (Gas.logCost y.toNat 1 + (Gas.extendMemory
        m.frame.memory.size [(x.toNat, y.toNat)]).cost),
      sub := { m.frame.sub with logs := m.frame.sub.logs.push (logEntry m x y [t0]) },
      pc := m.frame.pc + 1 } } :=
  step_log 1 [t0] rfl hcode hstk hstatic hgas

/-- `LOG2`. -/
theorem step_log2 {t0 t1 : Word} (hcode : m.frame.code[m.frame.pc]? = some 0xa2)
    (hstk : m.frame.stack = x :: y :: ([t0, t1] ++ rest)) (hstatic : m.frame.msg.isStatic = false)
    (hgas : Gas.logCost y.toNat 2 + (Gas.extendMemory m.frame.memory.size
      [(x.toNat, y.toNat)]).cost ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest,
      memory := m.frame.memory.expand x.toNat y.toNat,
      gasLeft := m.frame.gasLeft - (Gas.logCost y.toNat 2 + (Gas.extendMemory
        m.frame.memory.size [(x.toNat, y.toNat)]).cost),
      sub := { m.frame.sub with logs := m.frame.sub.logs.push (logEntry m x y [t0, t1]) },
      pc := m.frame.pc + 1 } } :=
  step_log 2 [t0, t1] rfl hcode hstk hstatic hgas

/-- `LOG3`. -/
theorem step_log3 {t0 t1 t2 : Word} (hcode : m.frame.code[m.frame.pc]? = some 0xa3)
    (hstk : m.frame.stack = x :: y :: ([t0, t1, t2] ++ rest)) (hstatic : m.frame.msg.isStatic = false)
    (hgas : Gas.logCost y.toNat 3 + (Gas.extendMemory m.frame.memory.size
      [(x.toNat, y.toNat)]).cost ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest,
      memory := m.frame.memory.expand x.toNat y.toNat,
      gasLeft := m.frame.gasLeft - (Gas.logCost y.toNat 3 + (Gas.extendMemory
        m.frame.memory.size [(x.toNat, y.toNat)]).cost),
      sub := { m.frame.sub with logs := m.frame.sub.logs.push (logEntry m x y [t0, t1, t2]) },
      pc := m.frame.pc + 1 } } :=
  step_log 3 [t0, t1, t2] rfl hcode hstk hstatic hgas

/-- `LOG4`. -/
theorem step_log4 {t0 t1 t2 t3 : Word} (hcode : m.frame.code[m.frame.pc]? = some 0xa4)
    (hstk : m.frame.stack = x :: y :: ([t0, t1, t2, t3] ++ rest)) (hstatic : m.frame.msg.isStatic = false)
    (hgas : Gas.logCost y.toNat 4 + (Gas.extendMemory m.frame.memory.size
      [(x.toNat, y.toNat)]).cost ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest,
      memory := m.frame.memory.expand x.toNat y.toNat,
      gasLeft := m.frame.gasLeft - (Gas.logCost y.toNat 4 + (Gas.extendMemory
        m.frame.memory.size [(x.toNat, y.toNat)]).cost),
      sub := { m.frame.sub with logs := m.frame.sub.logs.push (logEntry m x y [t0, t1, t2, t3]) },
      pc := m.frame.pc + 1 } } :=
  step_log 4 [t0, t1, t2, t3] rfl hcode hstk hstatic hgas

end EvmLean.Interpreter
