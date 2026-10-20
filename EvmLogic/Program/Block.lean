import EvmLogic.Tactic.WpStep

/-!
# Basic blocks and jumps

`basicBlocks fork code` cuts code into basic blocks (`#eval` it to plan a proof). A **block
summary** is a lemma `∀ Q H, … → Q (exitMachine m) → WP m Q H`, proved once with
`wp_intro m; wp_run_to <exit pc>; wp_finish hQ` and reused at every visit of the block;
`WP.jump`/`WP.jumpi` connect blocks (destinations checked with `jdCheck`).
-/

namespace EvmLogic.Program
open EvmLean Lean Elab Tactic EvmLogic.Tactic Meta EvmLean.Interpreter

/-! ## Cutting code into blocks -/

/-- One decoded instruction: its pc, opcode, and (for `PUSHn`) the immediate value. -/
structure Instr where
  pc : Nat
  op : Opcode
  /-- The immediate of `PUSHn` (zero-padded past the end of the code), else zero. -/
  imm : Nat
  size : Nat
  deriving Repr, DecidableEq

/-- A basic block: its entry pc, its instructions, and the pc after the last one. -/
structure Block where
  start : Nat
  instrs : List Instr
  /-- The pc following the last instruction (the fall-through successor). -/
  next : Nat
  deriving Repr

/-- Does this byte end a basic block? `STOP`, `JUMP`, `JUMPI`, `RETURN`, `REVERT`, `INVALID`,
`SELFDESTRUCT`, and every byte that decodes to `INVALID` (undefined opcodes). -/
def endsBlock (fork : Fork) (b : UInt8) : Bool :=
  b == 0x00 || b == 0x56 || b == 0x57 || b == 0xf3 || b == 0xfd || b == 0xff ||
    Opcode.decode fork b == .invalid

def decodeAt (fork : Fork) (code : ByteArray) (pc : Nat) : Instr :=
  let b := code[pc]?.getD 0
  let op := Opcode.decode fork b
  let n := if 0x60 ≤ b ∧ b ≤ 0x7f then b.toNat - 0x5f else 0
  { pc, op, imm := Bytes.toNat (readBytes code (pc + 1) n), size := 1 + n }

/-- Cut `code` from `pc` into blocks; `cur` is the block being built (reversed), `fuel` bounds
the number of instructions. -/
def blocksLoop (fork : Fork) (code : ByteArray) :
    Nat → Nat → Nat → List Instr → List Block → List Block
  | 0, _, _, _, acc => acc.reverse
  | fuel + 1, pc, start, cur, acc =>
    if pc < code.size then
      let b := code[pc]?.getD 0
      let i := decodeAt fork code pc
      let pc' := pc + i.size
      -- A `JUMPDEST` starts a new block (closing a non-empty current one).
      let (start, cur, acc) :=
        if b == 0x5b && !cur.isEmpty then (pc, [], ⟨start, cur.reverse, pc⟩ :: acc)
        else (start, cur, acc)
      if endsBlock fork b then
        blocksLoop fork code fuel pc' pc' [] (⟨start, (i :: cur).reverse, pc'⟩ :: acc)
      else blocksLoop fork code fuel pc' start (i :: cur) acc
    else
      (if cur.isEmpty then acc else ⟨start, cur.reverse, pc⟩ :: acc).reverse

/-- The basic blocks of `code`, in order. -/
def basicBlocks (fork : Fork) (code : ByteArray) : List Block :=
  blocksLoop fork code (code.size + 1) 0 0 [] []

def blockStarts (fork : Fork) (code : ByteArray) : List Nat :=
  (basicBlocks fork code).map (·.start)

/-! ## Jumps -/

variable {m : Machine} {Q : Machine → Prop} {H : Machine → Outcome → Prop}

/-- **`JUMP`**: continue at the destination. -/
theorem WP.jump {d : Word} {rest : List Word} (hcode : m.frame.code[m.frame.pc]? = some 0x56)
    (hstk : m.frame.stack = d :: rest)
    (hdest : isValidJumpDest m.frame.jumpDests d.toNat = true)
    (hgas : Gas.mid ≤ m.frame.gasLeft)
    (h : WP { m with frame := { m.frame with
      stack := rest, gasLeft := m.frame.gasLeft - Gas.mid, pc := d.toNat } } Q H) : WP m Q H :=
  WP.of_step (step_jump hcode hstk hdest hgas) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h

/-- **`JUMPI`**: split on the condition `c`. If `c ≠ 0` execution continues at the (valid)
destination, else at the next instruction. -/
theorem WP.jumpi {d c : Word} {rest : List Word} (hcode : m.frame.code[m.frame.pc]? = some 0x57)
    (hstk : m.frame.stack = d :: c :: rest)
    (hdest : c ≠ 0 → isValidJumpDest m.frame.jumpDests d.toNat = true)
    (hgas : Gas.high ≤ m.frame.gasLeft)
    (htaken : c ≠ 0 → WP { m with frame := { m.frame with
      stack := rest, gasLeft := m.frame.gasLeft - Gas.high, pc := d.toNat } } Q H)
    (hfall : c = 0 → WP { m with frame := { m.frame with
      stack := rest, gasLeft := m.frame.gasLeft - Gas.high, pc := m.frame.pc + 1 } } Q H) :
    WP m Q H := by
  by_cases hc : c = 0
  · subst hc
    exact WP.of_step (step_jumpi_of_eq_zero hcode hstk hgas)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (hfall rfl)
  · exact WP.of_step (step_jumpi_of_ne_zero hcode hstk hc (hdest hc) hgas)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (htaken hc)

/-! ## Finishing a block summary -/

/-- Prove `m₁ = m₂` for two machines that are structure instances, field by field: fields that
agree after `dsimp` close by `rfl`, the rest (typically gas) by `omega`. -/
macro "machine_eq" : tactic => `(tactic| (
  simp only [Machine.mk.injEq, Frame.mk.injEq, true_and, and_true]
  all_goals first | rfl | omega | fail "machine_eq: cannot prove a field equality"))

/-- Close `WP m Q H` from `h : Q m'` where `m'` is the reached machine `m` up to the field
equalities `machine_eq` proves. -/
macro "wp_finish " h:term : tactic => `(tactic| (refine WP.ret_of_eq ?_ $h; machine_eq))

end EvmLogic.Program
