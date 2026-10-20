import EvmLogic.Solidity.Steps
import EvmLogic.Tactic.Patched

/-!
# `MCOPY` in the symbolic executors, and memory facts for dynamic data

Adds `MCOPY` to `pwp_step` (`pwp_mcopy`, `pwp_msteps`) and `psol_step` (`psol_mcopy`,
`psol_msteps`), whose step-lemma tables omit it, plus facts about `Memory.mcopy` and closed
forms of expansion costs for word-aligned memory, for accesses with symbolic lengths.
-/

section

namespace EvmLean.Memory
open EvmLogic EvmLean.Bytes

theorem getD_bytes_mcopy (mem : Memory) (dst src len j : Nat) :
    getD (mem.mcopy dst src len).bytes j =
      if dst ≤ j ∧ j < dst + len then getD mem.bytes (src + (j - dst)) else getD mem.bytes j := by
  simp only [mcopy, getD_bytes_write, size_read]
  split
  · rename_i h
    simp only [read, getD_readPadded, show j - dst < len by omega, ↓reduceIte, getD_bytes_expand]
  · simp only [getD_bytes_expand]

theorem read_mcopy (mem : Memory) (dst src len : Nat) :
    (mem.mcopy dst src len).read dst len = mem.read src len := by
  simp only [mcopy]
  rw [show (((mem.expand src len).expand dst len).read src len) =
    ((mem.expand src len).expand dst len).read src len from rfl]
  have h := read_write ((mem.expand src len).expand dst len) dst
    (((mem.expand src len).expand dst len).read src len)
  rw [size_read] at h
  rw [h, read_expand, read_expand]

theorem read_mcopy_of_disjoint (mem : Memory) (dst src len off n : Nat)
    (h : off + n ≤ dst ∨ dst + len ≤ off) :
    (mem.mcopy dst src len).read off n = mem.read off n := by
  simp only [mcopy]
  rw [read_write_of_disjoint _ _ _ _ _ (by rw [size_read]; exact h), read_expand, read_expand]

theorem loadWord_mcopy_of_disjoint (mem : Memory) (dst src len off : Nat)
    (h : off + 32 ≤ dst ∨ dst + len ≤ off) :
    (mem.mcopy dst src len).loadWord off = mem.loadWord off := by
  rw [loadWord, loadWord, read_mcopy_of_disjoint _ _ _ _ _ _ h]

theorem size_mcopy (mem : Memory) (dst src len : Nat) (h : len ≠ 0) :
    (mem.mcopy dst src len).size =
      max (max mem.size (32 * ((src + len + 31) / 32))) (32 * ((dst + len + 31) / 32)) := by
  simp only [mcopy, size_write, size_read, size_expand, wordsAfter, h, ↓reduceIte, words]
  omega

end EvmLean.Memory

namespace EvmLean.Gas
open EvmLogic

theorem memoryCost_mono {a b : Nat} (h : a ≤ b) : memoryCost a ≤ memoryCost b := by
  simp only [memoryCost, words, memoryPerWord]
  have h1 : (a + 31) / 32 ≤ (b + 31) / 32 := Nat.div_le_div_right (by omega)
  have h2 := Nat.mul_le_mul h1 h1
  have h3 := Nat.div_le_div_right (c := 512) h2
  omega

theorem extendMemory_one {s off len : Nat} (hlen : len ≠ 0) (hs : s % 32 = 0) :
    (extendMemory s [(off, len)]).cost =
      memoryCost (max s ((off + len + 31) / 32 * 32)) - memoryCost s := by
  simp only [extendMemory, List.foldl, hlen, ↓reduceIte, ceil32]
  have hc : (s + 31) / 32 * 32 = s := by omega
  simp only [hc]
  split
  · rename_i h
    rw [Nat.max_eq_left h, Nat.sub_self]
  · rename_i h
    rw [Nat.max_eq_right (by omega), Nat.zero_add]

theorem extendMemory_two {s a b len : Nat} (hlen : len ≠ 0) (hs : s % 32 = 0) :
    (extendMemory s [(a, len), (b, len)]).cost =
      memoryCost (max (max s ((a + len + 31) / 32 * 32)) ((b + len + 31) / 32 * 32)) -
        memoryCost s := by
  have hc : (s + 31) / 32 * 32 = s := by omega
  simp only [extendMemory, List.foldl, hlen, ↓reduceIte, ceil32]
  simp only [hc]
  generalize hA : (a + len + 31) / 32 * 32 = A
  generalize hB : (b + len + 31) / 32 * 32 = B
  have hBB : (B + 31) / 32 * 32 = B := by omega
  have hAA : (A + 31) / 32 * 32 = A := by omega
  by_cases h1 : A ≤ s
  · simp only [h1, ↓reduceIte, hc]
    by_cases h2 : B ≤ s
    · simp only [h2, ↓reduceIte, Nat.max_eq_left h1, Nat.max_eq_left h2, Nat.sub_self]
    · simp only [h2, ↓reduceIte, Nat.zero_add, Nat.max_eq_left h1,
        Nat.max_eq_right (Nat.le_of_lt (Nat.lt_of_not_le h2))]
  · simp only [h1, ↓reduceIte, hAA, Nat.zero_add]
    have hm1 := memoryCost_mono (show s ≤ A by omega)
    by_cases h2 : B ≤ A
    · simp only [h2, ↓reduceIte, show max (max s A) B = A by omega]
    · have hm2 := memoryCost_mono (show A ≤ B by omega)
      simp only [h2, ↓reduceIte, show max (max s A) B = B by omega]
      omega

end EvmLean.Gas

namespace EvmLean.Interpreter
open EvmLogic

theorem memoryCost_eq {m : Machine} {x : Word} {n s t : Nat} (hs : m.frame.memory.size = s)
    (hs32 : s % 32 = 0) (hn : n ≠ 0) (ht : max s ((x.toNat + n + 31) / 32 * 32) = t) :
    memoryCost m x n = Gas.memoryCost t - Gas.memoryCost s := by
  rw [memoryCost, hs, Gas.extendMemory_one hn hs32, ht]

theorem mcopyCost_eq {m : Machine} {x y : Word} {len s t : Nat} (hs : m.frame.memory.size = s)
    (hs32 : s % 32 = 0) (hlen : len ≠ 0)
    (ht : max (max s ((y.toNat + len + 31) / 32 * 32)) ((x.toNat + len + 31) / 32 * 32) = t) :
    mcopyCost m x y len = Gas.memoryCost t - Gas.memoryCost s := by
  rw [mcopyCost, hs, Gas.extendMemory_two hlen hs32, ht]

theorem memoryCost_of_le {m : Machine} {x : Word} {n : Nat} (h32 : m.frame.memory.size % 32 = 0)
    (h : x.toNat + n ≤ m.frame.memory.size) : memoryCost m x n = 0 := by
  by_cases hn : n = 0
  · subst hn; simp [memoryCost, Gas.extendMemory]
  · rw [memoryCost, Gas.extendMemory_one hn h32,
      Nat.max_eq_left (by omega), Nat.sub_self]

theorem outputCost_of_le {m : Machine} {x y : Word} (h32 : m.frame.memory.size % 32 = 0)
    (h : x.toNat + y.toNat ≤ m.frame.memory.size) : outputCost m x y = 0 := by
  by_cases hn : y.toNat = 0
  · simp [outputCost, Gas.extendMemory, hn]
  · rw [outputCost, Gas.extendMemory_one hn h32, Nat.max_eq_left (by omega), Nat.sub_self]

end EvmLean.Interpreter

namespace EvmLean.Memory
open EvmLogic

theorem expand_eq_self {mem : Memory} {off len : Nat} (h32 : mem.size % 32 = 0)
    (h : off + len ≤ mem.size) : mem.expand off len = mem := by
  apply EvmLean.Interpreter.Memory.expand_of_le
  simp only [wordsAfter, words]
  split <;> omega

end EvmLean.Memory

namespace EvmLogic.Program
open EvmLean Lean Elab Tactic EvmLogic.Tactic Meta EvmLean.Interpreter

/-- `wp_generalize_mem M h`: replace the memory of a `WP` goal's machine by a variable `M`
(`h : term = M`); after a copy of symbolic length, reason through facts about `M`. -/
elab "wp_generalize_mem " M:ident h:ident : tactic => withMainContext do
  let some m ← wpGoalMachine? (← getMainGoal) | throwError "wp_generalize_mem: not a WP goal"
  let fr ← whnfR (mkApp (mkConst ``Machine.frame) m)
  let mem ← whnfR (mkApp (mkConst ``Frame.memory) fr)
  let memS ← Term.exprToSyntax mem
  evalTactic (← `(tactic| generalize $h : $memS = $M))

/-- Add `hmcopy_size : (Memory.mcopy M d s l).size = …` for each new copy of numeral length,
so that `evm_gas` (`rw_mem_sizes`) can cost later accesses. -/
elab "mcopy_size_facts" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let found ← IO.mkRef (#[] : Array Expr)
  forEachExpr t fun e => do
    if e.isAppOfArity ``Memory.mcopy 4 then found.modify (·.push e)
  let mut known : Array Expr := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    if let some (_, lhs, _) := ty.eq? then
      if lhs.isAppOfArity ``Memory.size 1 then known := known.push lhs.appArg!
  for e in ← found.get do
    if known.contains e then continue
    let args := e.getAppArgs
    let some l ← (evalNat args[3]!).run | continue
    if l == 0 then continue
    known := known.push e
    let eS ← Term.exprToSyntax e
    let mS ← Term.exprToSyntax args[0]!
    let dS ← Term.exprToSyntax args[1]!
    let sS ← Term.exprToSyntax args[2]!
    let lS ← Term.exprToSyntax args[3]!
    evalTactic (← `(tactic| have hmcopy_size : Memory.size $eS = _ :=
      Memory.size_mcopy $mS $dS $sS $lS (by decide)))
    evalTactic (← `(tactic| try simp only [Memory.size_storeWord, Memory.size_expand,
      Memory.size_empty, Memory.wordsAfter, Memory.words, Nat.reduceAdd, Nat.reduceMul,
      Nat.reduceDiv, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.max_def,
      ↓reduceIte] at hmcopy_size))

/-- Discharge the length side condition `len ≠ 0` / `len = 0` of an `MCOPY` step. -/
macro "mcopy_len_disch" : tactic =>
  `(tactic| first | assumption | decide | (dsimp only; omega) | omega)

/-- Discharge the gas side condition of an `MCOPY` step. -/
macro "mcopy_gas_disch" : tactic =>
  `(tactic| first | assumption | (simp only [mcopyCost]; evm_gas) | omega)

/-- The normalization `pwp_step` applies to a new machine, with extra lemmas. -/
syntax "pwp_norm" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| pwp_norm $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| try evm_norm [List.set_cons_zero, List.set_cons_succ, Nat.sub_sub,
      Memory.loadWord_expand, Memory.read_expand, Memory.loadWord_storeWord,
      Memory.read_storeWord, Memory.loadWord_storeWord_of_disjoint,
      Memory.read_storeWord_of_disjoint, true_or, or_true, reduceClosedWord, Bytes.size_ofWord,
      Bytes.toWord_ofWord, $extra,*])

/-- Execute a non-empty `MCOPY` in a `WP` goal (literal or patched code). -/
syntax "pwp_mcopy" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| pwp_mcopy $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      apply WP.of_step
      case h =>
        apply EvmLean.Interpreter.step_mcopy
        case hcode => pcode_fact
        case hstk => exact rfl
        case hz => mcopy_len_disch
        case hgas => mcopy_gas_disch
      case hs => same_frame
      pwp_norm [EvmLean.Interpreter.mcopyCost, $extra,*]
      mcopy_size_facts))

/-- Execute an empty `MCOPY` in a `WP` goal (literal or patched code). -/
syntax "pwp_mcopy_zero" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| pwp_mcopy_zero $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      apply WP.of_step
      case h =>
        apply EvmLean.Interpreter.step_mcopy_zero
        case hcode => pcode_fact
        case hstk => exact rfl
        case hz => mcopy_len_disch
        case hgas => pwp_disch
      case hs => same_frame
      pwp_norm [$extra,*]))

/-- `pwp_steps` that also executes `MCOPY`. -/
syntax "pwp_msteps" (ppSpace num)? (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| pwp_msteps $[$n]? $[[$extra,*]]?) => do
    let extraA := (extra.map (·.getElems)).getD #[]
    let limit := (n.map (·.getNat)).getD 1000000
    let mut cfg : Option FastStep.Cfg := none
    for i in [0:limit] do
      if i == 1 then cfg ← pwpFastCfg extraA
      if ← pwpStepFast cfg extraA then continue
      if ← tryTac (evalTactic (← `(tactic| pwp_mcopy [$extraA,*]))) then continue
      if ← tryTac (evalTactic (← `(tactic| pwp_mcopy_zero [$extraA,*]))) then continue
      return

/-- Discharge `x.toNat + n ≤ size` / `size % 32 = 0` of a memory access using the facts `hs`. -/
syntax "mem_in_disch" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| mem_in_disch $[[$hs,*]]?) => do
    let hs := (hs.map (·.getElems)).getD #[]
    `(tactic| ((try dsimp only); (try simp only [BitVec.reduceToNat, $hs,*]); omega))

/-- One `MLOAD` inside memory of non-numeral size; the facts `hs` (size, offsets) discharge
the bounds and normalize the new machine. -/
syntax "pwp_mload_in" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| pwp_mload_in $[[$hs,*]]?) => do
    let hs := (hs.map (·.getElems)).getD #[]
    `(tactic| (
      apply WP.of_step
      case h =>
        apply EvmLean.Interpreter.step_mload
        case hcode => pcode_fact
        case hstk => exact rfl
        case hlen => simp only [List.length_cons]; omega
        case hgas =>
          rw [EvmLean.Interpreter.memoryCost_of_le (by mem_in_disch [$hs,*])
            (by mem_in_disch [$hs,*])]
          (try dsimp only); simp only [Gas.veryLow]; omega
      case hs => same_frame
      try dsimp only
      rw [EvmLean.Interpreter.memoryCost_of_le (by mem_in_disch [$hs,*])
        (by mem_in_disch [$hs,*]),
        EvmLean.Memory.expand_eq_self (by mem_in_disch [$hs,*]) (by mem_in_disch [$hs,*])]
      simp only [Gas.veryLow, Nat.add_zero, BitVec.reduceToNat, Nat.reduceAdd, Nat.sub_sub, $hs,*]))

/-- One `RETURN` of a range inside memory whose size is not a numeral (`outputCost_of_le`). -/
syntax "pwp_return_in" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| pwp_return_in $[[$hs,*]]?) => do
    let hs := (hs.map (·.getElems)).getD #[]
    `(tactic| (
      apply WP.halt_of_step
      case h =>
        apply EvmLean.Interpreter.step_return
        case hcode => pcode_fact
        case hstk => exact rfl
        case hgas =>
          rw [EvmLean.Interpreter.outputCost_of_le (by mem_in_disch [$hs,*])
            (by mem_in_disch [$hs,*])]
          omega
      case hs => same_frame
      simp only [outputData, outputMachine]
      rw [EvmLean.Memory.expand_eq_self (by mem_in_disch [$hs,*]) (by mem_in_disch [$hs,*])]
      simp only [readBytes_bytes, $hs,*]))

end EvmLogic.Program

namespace EvmLogic.Tactic.Patched
open EvmLean EvmLogic.Solidity

/-- Execute a non-empty `MCOPY` in a `run` goal (literal or patched code). -/
syntax "psol_mcopy" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| psol_mcopy $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      rw [EvmLean.Interpreter.run_succ_of_running ?h]
      case h =>
        apply EvmLean.Interpreter.step_mcopy
        case hcode => psol_disch
        case hstk => exact rfl
        case hz => mcopy_len_disch
        case hgas => mcopy_gas_disch
      try evm_norm [EvmLean.Interpreter.mcopyCost, EvmLogic.Tactic.Patched.reducePatchedRead,
        EvmLogic.Tactic.SolStep.reduceCodeImm, sol_norm, Nat.reduceMod, Nat.reducePow,
        Nat.reduceLT, $extra,*]
      mcopy_size_facts))

/-- Execute an empty `MCOPY` in a `run` goal (literal or patched code). -/
syntax "psol_mcopy_zero" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| psol_mcopy_zero $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      rw [EvmLean.Interpreter.run_succ_of_running ?h]
      case h =>
        apply EvmLean.Interpreter.step_mcopy_zero
        case hcode => psol_disch
        case hstk => exact rfl
        case hz => mcopy_len_disch
        case hgas => psol_disch
      try evm_norm [EvmLogic.Tactic.Patched.reducePatchedRead,
        EvmLogic.Tactic.SolStep.reduceCodeImm, sol_norm, Nat.reduceMod, Nat.reducePow,
        Nat.reduceLT, $extra,*]))

/-- `psol_steps` that also executes `MCOPY`. -/
syntax "psol_msteps" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| psol_msteps $[[$extra,*]]?) => do
    let extraA := (extra.map (·.getElems)).getD #[]
    let mut cfg : Option FastStep.Cfg := none
    for i in [0:1000000] do
      if i == 1 then cfg ← psolFastCfg extraA
      if let some c := cfg then
        if ← FastStep.fastRunStep c then continue
      if ← EvmLogic.Program.tryTac (Lean.Elab.Tactic.evalTactic (← `(tactic| psol_step [$extraA,*]))) then continue
      if ← EvmLogic.Program.tryTac (Lean.Elab.Tactic.evalTactic (← `(tactic| psol_mcopy [$extraA,*]))) then continue
      if ← EvmLogic.Program.tryTac (Lean.Elab.Tactic.evalTactic (← `(tactic| psol_mcopy_zero [$extraA,*]))) then continue
      return

end EvmLogic.Tactic.Patched

end
