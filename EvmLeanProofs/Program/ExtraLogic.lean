import EvmLeanProofs.Program.Logic

/-!
# Composing internal-function summaries

solc compiles an internal function as a code fragment entered by `JUMP` with the return
address on the stack. A summary of such a fragment is a `WP` from its entry pc whose running
postcondition is "back at the return address with the results on the stack", and whose
halting postcondition says how it may end the frame (e.g. a `revert`).

* `Machine.resumeAt m pc stack gas`: `m` with only pc, stack and gas changed — the shape of
  the machine after a pure internal function (no memory, storage or return-data effects).
* `WP.bind_mono`: sequencing with a summary whose halting postcondition is weaker than the
  caller's (the usual case: the caller's `H` mentions the whole call, the summary's only the
  fragment).
* `WP.of_false`: a summary that never halts (`H = False`) can be used under any `H`.
-/

namespace EvmLean.Program

open Interpreter

/-- `m` with pc, stack and gas replaced: where a pure internal function returns to. -/
def _root_.EvmLean.Interpreter.Machine.resumeAt (m : Machine) (pc : Nat) (stack : List Word)
    (gas : Nat) : Machine :=
  { m with frame := { m.frame with pc := pc, stack := stack, gasLeft := gas } }

namespace WP

variable {m : Machine} {Q Q₁ : Machine → Prop} {H H₁ : Machine → Outcome → Prop}

/-- **Sequencing with a summary.** Run the fragment summarised by `h` (reaching `Q₁` or ending
the frame with `H₁`, which implies the caller's `H`), then continue from any machine
satisfying `Q₁`. -/
theorem bind_mono (h : WP m Q₁ H₁) (hH : ∀ mf o, SameFrame m mf → H₁ mf o → H mf o)
    (k : ∀ m', SameFrame m m' → Q₁ m' → WP m' Q H) : WP m Q H :=
  (h.mono (fun _ _ h => h) hH).bind k

/-- A fragment that never ends the frame can be used under any halting postcondition. -/
theorem of_false (h : WP m Q (fun _ _ => False)) : WP m Q H :=
  h.mono (fun _ _ h => h) (fun _ _ _ h => h.elim)

end WP

end EvmLean.Program
