import EvmLogic.GasMono.Lockstep
import EvmLogic.GasMono.Pc
import EvmLogic.Program.Call
import EvmLogic.Tactic.SolStep
import EvmLogic.Tactic.WpStep

/-!
# Every gas at once: symbolic execution of a high-gas frame for all its lower-gas versions

The bytecode spec asks, below the exact gas `g₀`, that a frame fails or ends exactly as the
model says. WETH9's code has no final `INVALID`, so the region condition of the gas lockstep
(`EvmLogic.GasMono.RegionOk`) does not hold for it; and its one `CALL` (in `withdraw`) is reached
only for one selector, which an abstract interpretation cannot see. Instead the lockstep is run
along the symbolic execution itself, one instruction at a time:

`LowOK Hf M`: every machine `m` that `M` bumps (`bump d x ps m = M`: the same machine with `d`
less gas, any message gas and parents) ends its frame, failing only if it has less gas
(`0 < d`), or else as `Hf` says of the bumped end. With `d = 0` this is the exact result; with
`d > 0` the frame is a lower-gas version, which can only run out of gas earlier
(`EvmLogic.Program.Nested.exec_bump`: an instruction that does not read the gas and succeeds
with less gas succeeds identically with more).

The rules (`LowOK.step`, `LowOK.stop`, `LowOK.revert`, `LowOK.error`) take the high machine's
step, which the step lemmas give; `low_step`/`low_steps` drive them over literal code like
`sol_step` (same lemma table and side conditions).
-/

namespace Verified.WETH9.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
open EvmLogic.GasMono

/-! ## The judgement -/

/-- **All lower-gas versions of `M` end as `Hf` says**, or fail with strictly less gas. -/
def LowOK (Hf : Machine → Outcome → Prop) (M : Machine) : Prop :=
  ∀ m d x ps, bump d x ps m = M →
    Halts m (fun mf o => (0 < d ∧ Failed o) ∨ Hf (bump d x ps mf) o)

/-- A machine is the zero-gas bump of the machine it bumps by zero. -/
theorem bump_zero_inv (m : Machine) (x : Nat) (ps : List Frame) :
    bump 0 m.frame.msg.gas m.parents (bump 0 x ps m) = m := by
  obtain ⟨c, p, w, t, ow, cr, ⟨msg, code, jd, pc, st, mem, g, rd, sub, snap, k⟩, par⟩ := m
  rfl

theorem readsGasB_decode_false (fork : Fork) (b : UInt8)
    (h : b ≠ 0x5a ∧ b ≠ 0xf0 ∧ b ≠ 0xf1 ∧ b ≠ 0xf2 ∧ b ≠ 0xf4 ∧ b ≠ 0xf5 ∧ b ≠ 0xfa) :
    readsGasB (Opcode.decode fork b) = false := by
  cases hb : readsGasB (Opcode.decode fork b) with
  | false => rfl
  | true =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    rcases readsGas_decode fork b hb with h | h | h | h | h | h | h <;> contradiction

theorem not_readsGas {op : Opcode} (h : readsGasB op = false) : ¬ ReadsGas op := by
  rw [readsGas_iff, h]; simp

/-- With equal gas, a step that succeeds on the high machine succeeds on the low one. -/
theorem low_ok_of_zero {m : Machine} {x : Nat} {ps : List Frame} {op : Opcode}
    (hop : ¬ ReadsGas op) {a : Action} {M' : Machine}
    (hM : (exec op).run (bump 0 x ps m) = .ok (a, M')) :
    ∃ m', (exec op).run m = .ok (a, m') := by
  have := exec_bump op hop hM 0 m.frame.msg.gas m.parents
  rw [bump_zero_inv] at this
  exact ⟨_, this⟩

/-- A high step to `M'` in the same frame is an `Action.next` of the instruction. -/
theorem exec_next_of_step {M M' : Machine} {b : UInt8}
    (hb : M.frame.code[M.frame.pc]? = some b)
    (hng : readsGasB (Opcode.decode M.ctx.fork b) = false)
    (h : step M = .running M') (hs : SameFrame M M') :
    (exec (Opcode.decode M.ctx.fork b)).run M = .ok (.next, M') := by
  have hnc := exec_noChild _ hng M
  have hfr := exec_frame (Opcode.decode M.ctx.fork b) M
  cases hr : (exec (Opcode.decode M.ctx.fork b)).run M with
  | error e =>
    rw [step_of_exec_error hb hr] at h
    exact absurd (.of_same hs) (not_above_finishFrame (.refl M) h)
  | ok p =>
    obtain ⟨a, m'⟩ := p
    cases a with
    | next => rw [step_of_exec_next hb hr] at h; cases h; rfl
    | stop out =>
      rw [step_of_exec_stop hb hr] at h
      exact absurd (.of_same hs) (not_above_finishFrame (hfr.of_run hr).1.same h)
    | revert out =>
      rw [step_of_exec_revert hb hr] at h
      exact absurd (.of_same hs) (not_above_finishFrame (hfr.of_run hr).1.same h)
    | call req => exact (hnc.of_run hr).elim
    | create msg => exact (hnc.of_run hr).elim

/-! ## Rules -/

variable {Hf : Machine → Outcome → Prop} {M M' : Machine} {b : UInt8}

/-- **An instruction that continues the frame.** -/
theorem LowOK.step (hb : M.frame.code[M.frame.pc]? = some b)
    (hng : readsGasB (Opcode.decode M.ctx.fork b) = false)
    (h : step M = .running M') (hs : SameFrame M M') (k : LowOK Hf M') : LowOK Hf M := by
  have heM := exec_next_of_step hb hng h hs
  intro m d x ps hm
  subst hm
  have hb' : m.frame.code[m.frame.pc]? = some b := hb
  have hop : ¬ ReadsGas (Opcode.decode m.ctx.fork b) := not_readsGas hng
  cases hr : (exec (Opcode.decode m.ctx.fork b)).run m with
  | error e =>
    refine Halts.of_step (step_of_exec_error hb' hr) (.refl m) (.inl ⟨?_, fun out h => by cases h⟩)
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · obtain ⟨_, h0⟩ := low_ok_of_zero hop heM
      rw [hr] at h0; cases h0
    · exact hd
  | ok p =>
    obtain ⟨a, m'⟩ := p
    have hh := exec_bump _ hop hr d x ps
    have heM' : (exec (Opcode.decode m.ctx.fork b)).run (bump d x ps m) = .ok (.next, M') := heM
    rw [heM'] at hh
    cases hh
    have hfl := ((exec_frame _ m).of_run hr).1
    exact Halts.of_steps (Steps.of_step (step_of_exec_next hb' hr) hfl.same) (k m' d x ps rfl)

/-- **An instruction that ends the frame successfully** (`STOP`, `RETURN`). -/
theorem LowOK.stop {out : ByteArray} (hb : M.frame.code[M.frame.pc]? = some b)
    (hng : readsGasB (Opcode.decode M.ctx.fork b) = false)
    (he : (exec (Opcode.decode M.ctx.fork b)).run M = .ok (.stop out, M'))
    (hf : Hf M' (.success out)) : LowOK Hf M := by
  intro m d x ps hm
  subst hm
  have hb' : m.frame.code[m.frame.pc]? = some b := hb
  have hop : ¬ ReadsGas (Opcode.decode m.ctx.fork b) := not_readsGas hng
  cases hr : (exec (Opcode.decode m.ctx.fork b)).run m with
  | error e =>
    refine Halts.of_step (step_of_exec_error hb' hr) (.refl m) (.inl ⟨?_, fun out h => by cases h⟩)
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · obtain ⟨_, h0⟩ := low_ok_of_zero hop he
      rw [hr] at h0; cases h0
    · exact hd
  | ok p =>
    obtain ⟨a, m'⟩ := p
    have hh := exec_bump _ hop hr d x ps
    have he' : (exec (Opcode.decode m.ctx.fork b)).run (bump d x ps m) = .ok (.stop out, M') := he
    rw [he'] at hh
    cases hh
    have hfl := ((exec_frame _ m).of_run hr).1
    exact Halts.of_step (step_of_exec_stop hb' hr) hfl.same (.inr hf)

/-- **`REVERT`**: the lower-gas versions revert identically or fail earlier. -/
theorem LowOK.revert {out : ByteArray} (hb : M.frame.code[M.frame.pc]? = some b)
    (hng : readsGasB (Opcode.decode M.ctx.fork b) = false)
    (he : (exec (Opcode.decode M.ctx.fork b)).run M = .ok (.revert out, M'))
    (hf : Hf M' (.revert out)) : LowOK Hf M := by
  intro m d x ps hm
  subst hm
  have hb' : m.frame.code[m.frame.pc]? = some b := hb
  have hop : ¬ ReadsGas (Opcode.decode m.ctx.fork b) := not_readsGas hng
  cases hr : (exec (Opcode.decode m.ctx.fork b)).run m with
  | error e =>
    refine Halts.of_step (step_of_exec_error hb' hr) (.refl m) (.inl ⟨?_, fun out h => by cases h⟩)
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · obtain ⟨_, h0⟩ := low_ok_of_zero hop he
      rw [hr] at h0; cases h0
    · exact hd
  | ok p =>
    obtain ⟨a, m'⟩ := p
    have hh := exec_bump _ hop hr d x ps
    have he' : (exec (Opcode.decode m.ctx.fork b)).run (bump d x ps m) = .ok (.revert out, M') :=
      he
    rw [he'] at hh
    cases hh
    have hfl := ((exec_frame _ m).of_run hr).1
    exact Halts.of_step (step_of_exec_revert hb' hr) hfl.same (.inr hf)

/-- **An instruction that fails on the high machine** (a static `SSTORE`, `INVALID`): every
lower-gas version fails too. -/
theorem LowOK.error {e : ExceptionalHalt} (hb : M.frame.code[M.frame.pc]? = some b)
    (hng : readsGasB (Opcode.decode M.ctx.fork b) = false)
    (he : (exec (Opcode.decode M.ctx.fork b)).run M = .error e)
    (hf : ∀ e', Hf M (.halt e')) : LowOK Hf M := by
  intro m d x ps hm
  have hb' : m.frame.code[m.frame.pc]? = some b := by subst hm; exact hb
  have hop : ¬ ReadsGas (Opcode.decode m.ctx.fork b) := by subst hm; exact not_readsGas hng
  cases hr : (exec (Opcode.decode m.ctx.fork b)).run m with
  | error e' =>
    refine Halts.of_step (step_of_exec_error hb' hr) (.refl m) (.inr ?_)
    rw [hm]; exact hf e'
  | ok p =>
    obtain ⟨a, m'⟩ := p
    have hh := exec_bump _ hop hr d x ps
    subst hm
    have he' : (exec (Opcode.decode m.ctx.fork b)).run (bump d x ps m) = .error e := he
    rw [he'] at hh
    cases hh

/-! ## Exec equations of the halting instructions -/

theorem exec_return {m : Machine} {x y : Word} {rest : List Word}
    (hstk : m.frame.stack = x :: y :: rest) (hgas : outputCost m x y ≤ m.frame.gasLeft) :
    (exec (Opcode.decode m.ctx.fork 0xf3)).run m =
      .ok (.stop (outputData m x y), outputMachine m x y rest) := by
  rw [show Opcode.decode m.ctx.fork 0xf3 = .«return» by cases m.ctx.fork <;> rfl]
  simp only [exec, StateT.run_bind, run_readOutput hstk hgas]
  rfl

theorem exec_revert {m : Machine} {x y : Word} {rest : List Word}
    (hstk : m.frame.stack = x :: y :: rest) (hgas : outputCost m x y ≤ m.frame.gasLeft) :
    (exec (Opcode.decode m.ctx.fork 0xfd)).run m =
      .ok (.revert (outputData m x y), outputMachine m x y rest) := by
  rw [show Opcode.decode m.ctx.fork 0xfd = .revert by cases m.ctx.fork <;> rfl]
  simp only [exec, StateT.run_bind, run_readOutput hstk hgas]
  rfl

theorem exec_stop (m : Machine) :
    (exec (Opcode.decode m.ctx.fork 0x00)).run m = .ok (.stop .empty, m) := by
  rw [show Opcode.decode m.ctx.fork 0x00 = .stop by cases m.ctx.fork <;> rfl]
  rfl

/-! ## `BALANCE` -/

/-- **`BALANCE`**: pushes the balance of the address, charging the EIP-2929 access cost and
warming the address. -/
theorem step_balance {m : Machine} {x : Word} {rest : List Word}
    (hcode : m.frame.code[m.frame.pc]? = some 0x31)
    (hstk : m.frame.stack = x :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.accessCost (m.frame.sub.accessedAddresses.contains (Word.toAddress x)) ≤
      m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := m.world.balance (Word.toAddress x) :: rest,
      gasLeft := m.frame.gasLeft -
        Gas.accessCost (m.frame.sub.accessedAddresses.contains (Word.toAddress x)),
      sub := m.frame.sub.warmAddr (Word.toAddress x),
      pc := m.frame.pc + 1 } } := by
  have hg := Nat.not_lt.mpr hgas
  have hl : ¬ Gas.stackLimit ≤ rest.length := Nat.not_le.mpr hlen
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x31 = .balance by
    cases m.ctx.fork <;> rfl]
  simp only [exec, popAddress, pop, getFrame, modifyFrame, StateT.run_bind, hstk, StateT.run_get,
    StateT.run_pure, StateT.run_modify, pure_bind]
  rw [run_accessAddress]
  simp only [pure_bind, charge, push, advance, getFrame, modifyFrame, StateT.run_bind,
    StateT.run_get, StateT.run_pure, StateT.run_modify, hg, hl, ite_false]
  rfl

end Verified.WETH9.Spec
