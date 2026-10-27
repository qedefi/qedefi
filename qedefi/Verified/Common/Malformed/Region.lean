import Verified.Common.Malformed.Pure
import Verified.Solmate.ERC20.Spec.SubCert

/-!
# Read-only regions of code

A *read-only region* is a table of abstract states (`CertT`, closed under the abstract step)
whose recorded pcs all hold pure instructions (`pureOpB`: no storage or transient write, no
log, no call or creation, no `SELFDESTRUCT`). `halts_pure`: a frame at a machine the table
describes ends, at any gas, with its world, transient storage and logs unchanged, whatever
the outcome. The getters of a token (`name()`, `balanceOf(a)`, …) are such regions from their
entries, with any calldata: their argument decoders and string loops only read.

`regionCert`: the exploration of a code from given abstract states (`regionCert_sound`).
-/

namespace Verified.Common.Malformed
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested
open EvmLogic.Program.Reentrancy EvmLogic.AbsInt EvmLogic.GasMono
open Verified.Solmate.ERC20.Spec (CertT inCertT_within inCert_recorded recorded)

/-- The instruction at a byte is pure (decoded as in the latest fork). -/
def pureByte (b : UInt8) : Bool := pureOpB (Opcode.decode .osaka b)

/-- `exec_pure` at a byte, in every fork (a byte decodes as in Osaka or to `INVALID`). -/
theorem exec_pure_byte (fork : Fork) {b : UInt8} (hb : pureByte b = true) (m : Machine) :
    Wp (exec (Opcode.decode fork b)) (PurePost m) m := by
  rcases decode_osaka_or_invalid fork b with h | h <;> rw [h]
  · exact exec_pure _ hb m
  · exact exec_pure .invalid rfl m

/-- The world, transient storage and logs at the end of the frame are those of `m`. -/
def Unchanged (m mf : Machine) : Prop :=
  mf.world = m.world ∧ mf.transient = m.transient ∧ mf.frame.sub.logs = m.frame.sub.logs

theorem getD_of_getElem? {code : ByteArray} {q : Nat} {b : UInt8} (h : code[q]? = some b) :
    Bytes.getD code q = b := by
  obtain ⟨hlt, he⟩ := getElem?_eq_some_iff.1 h
  rw [getD_eq_getElem hlt, he]

variable {ρ : Nat → Address} {allowed : AVal → Bool} {code : ByteArray} {t : Tree}

/-- **A read-only region changes nothing outside the frame**: from a machine described by a
closed table whose recorded pcs hold pure instructions, the frame ends (at any gas) with the
world, transient storage and logs it started with. -/
theorem halts_pure (hc : CertT ρ allowed code t)
    (hp : ∀ q ∈ recorded t, pureByte (Bytes.getD code q) = true) :
    ∀ m, m.frame.code = code → InCert ρ t m → Halts m fun mf _ => Unchanged m mf := by
  suffices ∀ n m, m.frame.gasLeft = n → m.frame.code = code → InCert ρ t m →
      Halts m fun mf _ => Unchanged m mf from fun m => this _ m rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m hn hcode hin
    obtain ⟨s, ⟨e, imm, ss, hf, hs⟩, hst⟩ := hin
    obtain ⟨b, hb, -, -⟩ := hc.ins.find hf
    rw [← hcode] at hb
    have hpb : pureByte b = true := by
      have := hp _ (inCert_recorded ⟨s, ⟨e, imm, ss, hf, hs⟩, hst⟩)
      rwa [← hcode, getD_of_getElem? hb] at this
    cases hrun : (exec (Opcode.decode m.ctx.fork b)).run m with
    | error err =>
      exact Halts.of_step (step_of_exec_error hb hrun) (.refl m) ⟨rfl, rfl, rfl⟩
    | ok p =>
      obtain ⟨a, m'⟩ := p
      have hpp := (exec_pure_byte m.ctx.fork hpb m).of_run hrun
      have hfr : InstrFrame m m' := ((exec_frame _ m).of_run hrun).1
      cases a with
      | next =>
        have hlt : m'.frame.gasLeft < m.frame.gasLeft :=
          ((exec_strict _ m).of_run hrun).1
        obtain ⟨hcode', hin'⟩ := inCertT_within hc hcode ⟨s, ⟨e, imm, ss, hf, hs⟩, hst⟩ hb hrun
          (.inl ⟨rfl, rfl⟩)
        refine Halts.of_steps (Steps.of_step (step_of_exec_next hb hrun) hfr.same)
          ((ih _ (hn ▸ hlt) m' rfl hcode' hin').mono fun mf _ _ h => ?_)
        obtain ⟨h1, h2, h3⟩ := hpp
        exact ⟨h.1.trans h1, h.2.1.trans h2, h.2.2.trans h3⟩
      | stop out => exact Halts.of_step (step_of_exec_stop hb hrun) hfr.same hpp
      | revert out => exact Halts.of_step (step_of_exec_revert hb hrun) hfr.same hpp
      | call req => exact hpp.elim
      | create msg => exact hpp.elim

/-! ## Explorations from given states -/

/-- Explore `code` from the abstract states `seeds` (no immutables). -/
def regionCert (code : ByteArray) (seeds : List (Nat × AStack)) (fuel : Nat) : Option Tree :=
  explore (fun _ => true) fuel (table code []) seeds

theorem regionCert_sound {seeds : List (Nat × AStack)} {fuel : Nat}
    (h : regionCert code seeds fuel = some t) :
    CertT ρ (fun _ => true) code t ∧ ∀ x ∈ seeds, InT t x.1 x.2 := by
  have hs : SymOk ρ code [] := fun q k h => by simp [symAt] at h
  obtain ⟨hA, hF, -⟩ := Tree.build_ok 64 (ascan code []).length _ (ascan_ok hs)
  have hI : ExInv (fun _ => true) (table code []) seeds := by
    intro q s ⟨e, imm, ss, hf, hm⟩
    rw [hF.find hf] at hm
    cases hm
  obtain ⟨hc, hm⟩ := explore_sound _ fuel _ _ t h hI
  exact ⟨⟨hc, explore_all fuel _ _ t h hA⟩, fun x hx => hm x.1 x.2 (.inr hx)⟩

/-- A machine at a seed `(q, [top])`: any one-word stack. -/
theorem inCert_top {m : Machine} {q : Nat} (h : InT t q [.top]) (hpc : m.frame.pc = q)
    {x : Word} (hs : m.frame.stack = [x]) : InCert ρ t m :=
  ⟨[.top], hpc ▸ h, by rw [hs]; exact ⟨trivial, trivial⟩⟩

end Verified.Common.Malformed
