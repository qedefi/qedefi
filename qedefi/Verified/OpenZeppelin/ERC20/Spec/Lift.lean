import Verified.OpenZeppelin.ERC20.Spec.LowGas
import QEDefi.ERC20.Spec.Bytecode

/-!
# The obligations below `g₀` from those above

For code without `GAS`, calls or creations (`NoGasCode`), each obligation of `ERC20Spec` follows
from the same obligation restricted to frames with at least `g₀` gas: a frame with less gas
fails or ends as the same frame with gas `g₀` at the top level (`lift`), and failing is allowed
below `g₀`. `Start` survives raising the gas (`start_high`), and every outcome predicate of the
spec reads the frame only through fields `high` keeps.
-/

namespace Verified.OpenZeppelin.ERC20.Spec
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.GasMono QEDefi.ERC20 QEDefi.ERC20.Spec
open EvmLogic.Solidity

variable {σ E : Type} {code : ByteArray} {abs : TokenAbs σ} {M : TokenModel σ Address E}
  {Act : Finset Address}

theorem start_high {m : Machine} (h : Start code abs M Act m) {G : Nat}
    (hG : m.frame.gasLeft ≤ G) : Start code abs M Act (high G m) :=
  ⟨fresh_high h.fresh hG, h.launched, h.value, h.size, h.caller, h.sound, h.wf⟩

theorem fails_of_failed {o : Outcome} (h : Failed o) : Fails o := by
  cases o with
  | success out => exact absurd rfl (h out)
  | revert _ => trivial
  | halt _ => trivial

theorem failed_of_fails {o : Outcome} (h : Fails o) : Failed o := by
  cases o with
  | success out => exact h.elim
  | revert _ => intro _ h'; cases h'
  | halt _ => intro _ h'; cases h'

/-- What a successful frame must satisfy for `Matches` of the result `res`, minus its created
accounts. -/
def MatchesOk (abs : TokenAbs σ) (Act : Finset Address) (m : Machine)
    (evs : List (Event Address)) : Result σ → SuccessPost
  | .ok s' ret => fun out W T L =>
    out = retBytes ret ∧ abs.read m.ctx.crypto Act W m.frame.msg.currentTarget = s' ∧
    FrameKeeps abs m.ctx.crypto Act m.frame.msg.currentTarget m.world W ∧
    T = m.transient ∧ L = m.frame.sub.logs ++ (evs.map (eventLog m.frame.msg.currentTarget)).toArray
  | .halt _ => fun _ _ _ _ => False

theorem matchesOk_of {m mf : Machine} {o : Outcome} {evs : List (Event Address)}
    {res : Result σ} (h : Matches abs Act m mf o evs res) :
    Failed o ∨ ∃ out, o = .success out ∧
      MatchesOk abs Act m evs res out mf.world mf.transient mf.frame.sub.logs := by
  cases res with
  | ok s' ret =>
    obtain ⟨ho, h1, h2, h3, -, h5⟩ := h
    exact .inr ⟨_, ho, rfl, h1, h2, h3, h5⟩
  | halt k =>
    cases k with
    | revert => obtain ⟨out, rfl⟩ := h; exact .inl fun _ h => by cases h
    | invalid => obtain ⟨e, rfl⟩ := h; exact .inl fun _ h => by cases h

theorem matches_of {m mf : Machine} {out : ByteArray} {evs : List (Event Address)}
    {res : Result σ} (h : MatchesOk abs Act m evs res out mf.world mf.transient mf.frame.sub.logs)
    (hc : mf.createdAccounts = m.createdAccounts) :
    Matches abs Act m mf (.success out) evs res := by
  cases res with
  | ok s' ret =>
    obtain ⟨rfl, h1, h2, h3, h5⟩ := h
    exact ⟨rfl, h1, h2, h3, hc, h5⟩
  | halt k => exact h.elim

/-- **`CallSpec` from the frames with at least `g₀` gas.** -/
theorem callSpec_of_high (hno : NoGasCode code) {g₀ : Nat} {c : Call Address}
    (h : ∀ Act m, Start code abs M Act m → c.Encodes m.frame.msg.data →
      (∀ a ∈ c.addrs, a ∈ Act) → g₀ ≤ m.frame.gasLeft →
      Halts m fun mf o =>
        Matches abs Act m mf o (M.events (pre abs Act m) m.frame.msg.caller c)
          (M.call (pre abs Act m) m.frame.msg.caller c) ∨
        (Fails o ∧ ¬ Normal g₀ m)) :
    CallSpec code abs M g₀ c := by
  intro Act m hS henc hadd
  by_cases hg : g₀ ≤ m.frame.gasLeft
  · exact h Act m hS henc hadd hg
  have hG : m.frame.gasLeft ≤ g₀ := by omega
  have hh := h Act (high g₀ m) (start_high hS hG) henc hadd (by rw [high_gasLeft hG])
  have hl := lift hno hS.fresh (G := g₀)
    (Q := MatchesOk abs Act m (M.events (pre abs Act m) m.frame.msg.caller c)
      (M.call (pre abs Act m) m.frame.msg.caller c)) (hh.mono fun mf o _ hp => by
        rcases hp with hm | ⟨hf, -⟩
        · exact matchesOk_of hm
        · exact .inl (failed_of_fails hf))
  refine hl.mono fun mf o _ hp => ?_
  rcases hp with hf | ⟨out, rfl, hq, hc⟩
  · exact .inr ⟨fails_of_failed hf, fun hn => hg hn.1⟩
  · exact .inl (matches_of hq hc)

/-- **`FallbackSpec` from the frames with at least `g₀` gas.** -/
theorem fallbackSpec_of_high (hno : NoGasCode code) {g₀ : Nat} {sel : List Nat}
    (h : ∀ Act m, Start code abs M Act m →
      (m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ sel) →
      g₀ ≤ m.frame.gasLeft →
      Halts m fun mf o =>
        Matches abs Act m mf o
          (M.events (pre abs Act m) m.frame.msg.caller (.other m.frame.msg.value.toNat))
          (M.call (pre abs Act m) m.frame.msg.caller (.other m.frame.msg.value.toNat)) ∨
        (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false))) :
    FallbackSpec code abs M g₀ sel := by
  intro Act m hS hsel
  by_cases hg : g₀ ≤ m.frame.gasLeft
  · exact h Act m hS hsel hg
  have hG : m.frame.gasLeft ≤ g₀ := by omega
  have hh := h Act (high g₀ m) (start_high hS hG) hsel (by rw [high_gasLeft hG])
  have hl := lift hno hS.fresh (G := g₀)
    (Q := MatchesOk abs Act m
      (M.events (pre abs Act m) m.frame.msg.caller (.other m.frame.msg.value.toNat))
      (M.call (pre abs Act m) m.frame.msg.caller (.other m.frame.msg.value.toNat)))
    (hh.mono fun mf o _ hp => by
        rcases hp with hm | ⟨hf, -⟩
        · exact matchesOk_of hm
        · exact .inl (failed_of_fails hf))
  refine hl.mono fun mf o _ hp => ?_
  rcases hp with hf | ⟨out, rfl, hq, hc⟩
  · exact .inr ⟨fails_of_failed hf, fun hn => hg hn.1⟩
  · exact .inl (matches_of hq hc)

/-- What a successful view must satisfy, minus its created accounts. -/
def ViewOk (M : TokenModel σ Address E) (s : σ) (v : View) (m : Machine) : SuccessPost :=
  fun out W T L => ∃ x : Word, out = Bytes.ofWord x ∧ x.toNat = v.value M s ∧ W = m.world ∧
    T = m.transient ∧ L = m.frame.sub.logs

/-- **`ViewSpec` from the frames with at least `g₀` gas.** -/
theorem viewSpec_of_high (hno : NoGasCode code) {g₀ : Nat} {v : View}
    (h : ∀ Act m, Start code abs M Act m → v.Encodes m.frame.msg.data →
      (∀ a ∈ v.addrs, a ∈ Act) → g₀ ≤ m.frame.gasLeft →
      Halts m fun mf o =>
        (∃ x : Word, o = .success (Bytes.ofWord x) ∧ x.toNat = v.value M (pre abs Act m) ∧
          mf.world = m.world ∧ mf.transient = m.transient ∧
          mf.createdAccounts = m.createdAccounts ∧ mf.frame.sub.logs = m.frame.sub.logs) ∨
        (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0))) :
    ViewSpec code abs M g₀ v := by
  intro Act m hS henc hadd
  by_cases hg : g₀ ≤ m.frame.gasLeft
  · exact h Act m hS henc hadd hg
  have hG : m.frame.gasLeft ≤ g₀ := by omega
  have hh := h Act (high g₀ m) (start_high hS hG) henc hadd (by rw [high_gasLeft hG])
  have hl := lift hno hS.fresh (G := g₀) (Q := ViewOk M (pre abs Act m) v m)
    (hh.mono fun mf o _ hp => by
        rcases hp with ⟨x, ho, h1, h2, h3, -, h5⟩ | ⟨hf, -⟩
        · exact .inr ⟨_, ho, x, rfl, h1, h2, h3, h5⟩
        · exact .inl (failed_of_fails hf))
  refine hl.mono fun mf o _ hp => ?_
  rcases hp with hf | ⟨out, rfl, ⟨x, rfl, h1, h2, h3, h5⟩, hc⟩
  · exact .inr ⟨fails_of_failed hf, fun hn => hg hn.1⟩
  · exact .inl ⟨x, rfl, h1, h2, h3, hc, h5⟩

/-- What a successful operation must satisfy, minus its created accounts. -/
def OpOk (abs : TokenAbs σ) (M : TokenModel σ Address E) (Act : Finset Address) (e : E)
    (m : Machine) : SuccessPost :=
  fun _ W T _ => match M.op (pre abs Act m) e with
    | some s' => abs.read m.ctx.crypto Act W m.frame.msg.currentTarget = s' ∧
      FrameKeeps abs m.ctx.crypto Act m.frame.msg.currentTarget m.world W ∧ T = m.transient
    | none => False

/-- **`OpSpec` from the frames with at least `g₀` gas.** -/
theorem opSpec_of_high (hno : NoGasCode code) {g₀ : Nat}
    {ops : Address → ByteArray → ℕ → Option E} {opAddrs : E → List Address}
    (h : ∀ Act m e, Start code abs M Act m →
      ops m.frame.msg.caller m.frame.msg.data m.frame.msg.value.toNat = some e →
      (∀ a ∈ opAddrs e, a ∈ Act) → g₀ ≤ m.frame.gasLeft →
      Halts m fun mf o =>
        OpMatches abs M Act e m mf o ∨
        (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false))) :
    OpSpec code abs M g₀ ops opAddrs := by
  intro Act m e hS hops hadd
  by_cases hg : g₀ ≤ m.frame.gasLeft
  · exact h Act m e hS hops hadd hg
  have hG : m.frame.gasLeft ≤ g₀ := by omega
  have hh := h Act (high g₀ m) e (start_high hS hG) hops hadd (by rw [high_gasLeft hG])
  have hl := lift hno hS.fresh (G := g₀) (Q := OpOk abs M Act e m)
    (hh.mono fun mf o _ hp => by
        rcases hp with hm | ⟨hf, -⟩
        · unfold OpMatches at hm
          unfold OpOk
          split at hm
          · obtain ⟨⟨out, ho⟩, h1, h2, h3, -⟩ := hm
            rename_i s' hs
            change M.op (pre abs Act m) e = some s' at hs
            exact .inr ⟨out, ho, by rw [hs]; exact ⟨h1, h2, h3⟩⟩
          · exact .inl (failed_of_fails hm)
        · exact .inl (failed_of_fails hf))
  refine hl.mono fun mf o _ hp => ?_
  rcases hp with hf | ⟨out, rfl, hq, hc⟩
  · exact .inr ⟨fails_of_failed hf, fun hn => hg hn.1⟩
  · left
    unfold OpOk at hq
    unfold OpMatches
    split at hq
    · rename_i s' hs
      rw [hs]
      exact ⟨⟨out, rfl⟩, hq.1, hq.2.1, hq.2.2, hc⟩
    · exact hq.elim

end Verified.OpenZeppelin.ERC20.Spec
