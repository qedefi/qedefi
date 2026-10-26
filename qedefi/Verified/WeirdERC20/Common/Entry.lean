import Verified.WeirdERC20.Common.Transport

/-!
# Function-body entries reached by a dispatcher

The symbolic runs of a dispatcher end at a function body's entry: `entryG mem m pc st g` is
the frame `m` at pc `pc` with stack `st`, memory `mem` (solc's prologue) and gas `g`; `entry`
spends `c` gas exactly. `dirtyRun_of` assembles a `DirtyRun` from the two runs a token proves
per entry point: the dirty frame reaches `entryG … g` at any gas (with `g` at most its gas),
and the clean frame (`clean D' G m`, with `G` large) reaches `entry … c` with the same stack.
-/

namespace Verified.WeirdERC20.Common
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.AbsInt
open Verified.Solmate.ERC20.Spec (CertT recorded)
open Verified.OpenZeppelin.ERC20.Spec (high hi setKind)

/-- The machine `m` at a function body's entry: pc `pc`, stack `st`, memory `mem`, gas `g`. -/
def entryG (mem : Memory) (m : Machine) (pc : Nat) (st : List Word) (g : Nat) : Machine :=
  { m with frame := { m.frame with pc := pc, stack := st, memory := mem, gasLeft := g } }

/-- The body entry after spending `c` gas. -/
def entry (mem : Memory) (m : Machine) (pc : Nat) (st : List Word) (c : Nat) : Machine :=
  entryG mem m pc st (m.frame.gasLeft - c)

theorem entry_clean (mem : Memory) (D' : ByteArray) (G : Nat) (m : Machine) (pc : Nat)
    (st : List Word) (c g : Nat) (hmG : m.frame.gasLeft ≤ G) (hg : g + c ≤ G) :
    entry mem (clean D' G m) pc st c =
      img D' (G - c - g) G [] (.call 0 0) (entryG mem m pc st g) := by
  obtain ⟨ctx, pre, w, tr, ow, cr, ⟨msg, code, jd, pc0, st0, mem0, gas, rd, sub, snap, kind⟩,
    ps⟩ := m
  simp only at hmG
  simp only [entry, entryG, clean, img, setData, high, hi, setKind,
    EvmLogic.Program.Nested.bump, Machine.mk.injEq, Frame.mk.injEq, true_and, and_true]
  omega

theorem steps_of_wp {m : Machine} {Q : Machine → Prop} (h : WP m Q (fun _ _ => False)) :
    ∃ s, Steps m s ∧ Q s := by
  rcases h with h | ⟨_, _, _, _, _, h⟩
  · exact h
  · exact h.elim

/-- **A `DirtyRun` from the two dispatcher runs.** -/
theorem dirtyRun_of {ρ : Nat → Address} {allowed : AVal → Bool} {code : ByteArray} {t : Tree}
    (hcert : CertT ρ allowed code t)
    (hsafe : ∀ q ∈ recorded t, dataSafeB (Bytes.getD code q) = true)
    {m : Machine} (hf : Fresh code m) {D' : ByteArray} (hD : D'.size < 2 ^ 64)
    {mem : Memory} {pc : Nat} {st : List Word} {g K c : Nat}
    (hst : Steps m (entryG mem m pc st g)) (hg : g ≤ m.frame.gasLeft) (hc : c ≤ K)
    (hclean : WP (clean D' (m.frame.gasLeft + K) m)
      (fun s => s = entry mem (clean D' (m.frame.gasLeft + K) m) pc st c) (fun _ _ => False))
    (hin : InCert ρ t (entryG mem m pc st g)) :
    DirtyRun code m D' := by
  refine ⟨hD, m.frame.gasLeft + K, m.frame.gasLeft + K - c - g, _, ρ, allowed, t, by omega,
    hst, rfl, ?_, hcert, hsafe, (hf.frame).1, hin⟩
  obtain ⟨s, hs, rfl⟩ := steps_of_wp hclean
  rw [entry_clean mem D' (m.frame.gasLeft + K) m pc st c g (by omega) (by omega)] at hs
  exact hs

end Verified.WeirdERC20.Common
