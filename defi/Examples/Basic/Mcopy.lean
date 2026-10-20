import EvmLogic.Tactic.Mcopy

/-!
# `MCOPY` in the symbolic executors: examples

`copy42` stores 42, copies it with `MCOPY` and returns the copy; proved by `psol_msteps`
(a `run` goal) and `pwp_msteps` (a frame-local `WP` goal).
-/

namespace Examples.Basic.Mcopy
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program

/-- Store 42, copy it with `MCOPY`, return the copy. -/
def copy42 : ByteArray :=
  ⟨#[0x60, 0x2a, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0x60, 0x20, 0x5e, 0x60, 0x20, 0x60, 0x20, 0xf3]⟩

def copy42Machine (ctx : Context) (g : Nat) (msg : Message) (w : World) : Machine where
  ctx := ctx
  precompiles := PrecompileImpl.standard ctx
  world := w
  transient := ∅
  originalWorld := w
  createdAccounts := ∅
  parents := []
  frame := { msg, code := copy42, jumpDests := validJumpDests copy42, gasLeft := g, sub := {},
             snapshot := (w, ∅), kind := .call 0 0 }

/-- `copy42` returns the word 42 (`run` goal, `psol_msteps`). -/
theorem copy42_output (ctx : Context) (g : Nat) (hg : 100 ≤ g) (msg : Message) (w : World)
    (k : Nat) : ∃ r, run (k + 10) (copy42Machine ctx g msg w) = .ok r ∧
      Bytes.toWord r.output = 42 := by
  simp only [copy42Machine]
  psol_msteps
  refine ⟨_, rfl, ?_⟩
  simp only [topLevelResult_output, Memory.mcopy, Memory.read_expand, Memory.read_storeWord]
  rfl

/-- `copy42` returns the word 42 in any frame (`WP` goal, `pwp_msteps`). -/
theorem copy42_wp (m : Machine) (hc : m.frame.code = copy42) (hpc : m.frame.pc = 0)
    (hs : m.frame.stack = []) (hmem : m.frame.memory = {}) (hg : 100 ≤ m.frame.gasLeft) :
    WP m (fun _ => False) (fun _ o => ∃ out, o = .success out ∧ Bytes.toWord out = 42) := by
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hc hpc hs hmem
  pwp_msteps
  refine ⟨_, rfl, ?_⟩
  simp only [Memory.mcopy, Memory.read_expand, Memory.read_storeWord]
  rfl

end Examples.Basic.Mcopy
