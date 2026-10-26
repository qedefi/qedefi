import Verified.WeirdERC20.Common.DataLockstep
import Verified.OpenZeppelin.ERC20.Spec.Lift
import Verified.Common.Malformed.Post

/-!
# Dirty calldata of a solc 0.4/0.5 token is the clean call

solc before 0.8 (ABI coder v1) masks an `address` argument to its low 160 bits and never
checks the high bits. So a frame whose calldata holds a dirty `address` word runs, once the
dispatcher has decoded its arguments, exactly as the frame with the clean ABI encoding of the
same call. `transport` turns this into a rule:

* the frame `m` (dirty calldata, any gas, any depth) reaches the entry `E` of a function body
  (or fails), and the clean frame — `m` at the top level, as a call, with the clean calldata
  `D'` and some gas `G` (`clean D' G m`) — reaches the image of `E` with at least as much gas
  (`img`; symbolic runs of the dispatcher);
* the body is a data-safe region (`data_lockstep`: no calldata read, no `GAS`, no child);
* the clean frame satisfies a summary `Q` (fails, or succeeds as `Q` says of its return data,
  world, transient storage and logs);

then `m` fails or succeeds as `Q` says, keeping its created accounts. At the top level a
`Halts` witness determines the frame's real exit (`exit_of_halts_top`), which the data
lockstep follows back to `m`.

`post_call_dirty`, `post_op_dirty`: the rules of `MalformedSpec`
(`Verified.Common.Malformed.MalPost`) for a frame whose clean counterpart is the ABI encoding
of an ERC-20 call (`CallSpec`) or an operation the decoder accepts (`OpSpec`), for the actors
extended by the accounts the call names.
-/

namespace Verified.WeirdERC20.Common
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested EvmLogic.GasMono
open EvmLogic.AbsInt QEDefi.ERC20 QEDefi.ERC20.Spec
open EvmLogic.Program.Reentrancy (halts_any)
open Verified.Solmate.ERC20.Spec (CertT recorded)
open Verified.OpenZeppelin.ERC20.Spec (SuccessPost top_success_inv fails_of_failed
  failed_of_fails MatchesOk matchesOk_of matches_of high fresh_high)
open Verified.Common.Malformed (MalPost start_extend)

variable {ρ : Nat → Address} {allowed : AVal → Bool} {code : ByteArray} {t : Tree}

theorem top_exit_shift {m m' mf : Machine} {N j : Nat} {o : Outcome} (hp : m.parents = [])
    (hex : Exit m N mf o) (hj : stepN j m = .running m') (hs : SameFrame m m') :
    Exit m' (N - j) mf o := by
  refine hex.shift hj hs ?_
  by_contra hlt
  have hfin := hex.finish
  rw [finishFrame_of_top _ (hfin.2.parents.trans hp)] at hfin
  have := stepN_add_of_done hfin.1 (j - (N + 1))
  rw [show N + 1 + (j - (N + 1)) = j by omega, hj] at this
  cases this

/-- **Dirty calldata runs as the clean call.** The dirty frame reaches `E`; the clean frame
`mc` (at the top level, as a call) reaches the image of `E` (calldata `D'`, `d` more gas,
message gas `x`). -/
theorem transport (hc : CertT ρ allowed code t)
    (hsafe : ∀ q ∈ recorded t, dataSafeB (Bytes.getD code q) = true)
    {m mc : Machine} {D' : ByteArray} {d x : Nat} {E : Machine}
    (hp : mc.parents = []) (hk : mc.frame.kind = .call 0 0)
    (hpd : Steps m E) (hEcr : E.createdAccounts = m.createdAccounts)
    (hpc : Steps mc (img D' d x [] (.call 0 0) E))
    (hEc : E.frame.code = code) (hEin : InCert ρ t E) {Q : SuccessPost}
    (hsum : Halts mc fun mf o =>
      Failed o ∨ ∃ out, o = .success out ∧ Q out mf.world mf.transient mf.frame.sub.logs) :
    Halts m fun mf o => Failed o ∨ ∃ out, o = .success out ∧
      Q out mf.world mf.transient mf.frame.sub.logs ∧ mf.createdAccounts = m.createdAccounts := by
  obtain ⟨N, X, oX, hex, mf', o', hH, hs', hfin⟩ := exit_of_halts_top hp hsum
  obtain ⟨j, hj, hsj⟩ := hpc
  have hexE := top_exit_shift hp hex hj hsj
  have hlow := data_lockstep hc hsafe D' d x [] (.call 0 0) (N - j) E X oX hEc hEin hexE
  refine Halts.of_steps hpd (hlow.mono fun mfl ol _ hp => ?_)
  rcases hp with hfl | ⟨rfl, rfl, hcr⟩
  · exact .inl hfl
  · cases ol with
    | success out =>
      right
      have hfh := hex.finish.2
      obtain ⟨ho, hw, htr, hl⟩ := top_success_inv (ko := 0) (ks := 0) (hfh.kind.trans hk)
        (hs'.kind.trans hk) (hfh.parents.trans hp) (hs'.parents.trans hp)
        (hs'.msg.trans hfh.msg.symm) hfin
      rcases hH with hF | ⟨out', ho', hQ⟩
      · exact absurd ho (hF out)
      · rw [ho] at ho'
        cases ho'
        refine ⟨out, rfl, ?_, hcr.trans hEcr⟩
        rw [hw, htr, hl] at hQ
        exact hQ
    | revert out => exact .inl (fun _ h => by cases h)
    | halt e => exact .inl (fun _ h => by cases h)

variable {σ E : Type} {abs : TokenAbs σ} {M : TokenModel σ Address E} {Act : Finset Address}

/-- **The clean frame**: `m` at the top level with gas `G`, as a call, with calldata `D'`. -/
def clean (D' : ByteArray) (G : Nat) (m : Machine) : Machine := setData D' (high G m)

theorem fresh_clean {m : Machine} (hf : Fresh code m) {G : Nat} (hG : m.frame.gasLeft ≤ G)
    (D' : ByteArray) : Fresh code (clean D' G m) := by
  obtain ⟨msg, kind, snap, hfr, hcode⟩ := fresh_high hf hG
  exact ⟨{ msg with data := D' }, kind, snap, by simp only [clean, setData, hfr, Frame.init],
    hcode⟩

/-- `Start` for the clean frame (every field `Start` reads is kept). -/
theorem start_clean {m : Machine} (h : Start code abs M Act m) {G : Nat}
    (hG : m.frame.gasLeft ≤ G) {D' : ByteArray} (hD : D'.size < 2 ^ 64) :
    Start code abs M Act (clean D' G m) :=
  ⟨fresh_clean h.fresh hG D', h.launched, h.value, h.precompiles, hD, h.caller, h.sound, h.wf,
    h.hasCode, h.codeBound⟩

variable {ops : Address → ByteArray → ℕ → Option E} {opAddrs : E → List Address}
  {rec : Option (Machine → ℕ → Address)}

/-- The symbolic data of a dirty frame `m`: it reaches a body entry `E` (keeping its created
accounts), the clean frame with calldata `D'` and some gas `G` reaches an image of `E`, and
the body is a data-safe region. -/
def DirtyRun (code : ByteArray) (m : Machine) (D' : ByteArray) : Prop :=
  D'.size < 2 ^ 64 ∧
    ∃ (G d : Nat) (E : Machine) (ρ : Nat → Address) (allowed : AVal → Bool) (t : Tree),
      m.frame.gasLeft ≤ G ∧ Steps m E ∧ E.createdAccounts = m.createdAccounts ∧
      Steps (clean D' G m) (img D' d G [] (.call 0 0) E) ∧
      CertT ρ allowed code t ∧ (∀ q ∈ recorded t, dataSafeB (Bytes.getD code q) = true) ∧
      E.frame.code = code ∧ InCert ρ t E

/-- `transport` from a `DirtyRun`, given the summary of every clean frame. -/
theorem transport' {m : Machine} {D' : ByteArray} (hr : DirtyRun code m D') {Q : SuccessPost}
    (hsum : ∀ G, m.frame.gasLeft ≤ G → Halts (clean D' G m) fun mf o =>
      Failed o ∨ ∃ out, o = .success out ∧ Q out mf.world mf.transient mf.frame.sub.logs) :
    Halts m fun mf o => Failed o ∨ ∃ out, o = .success out ∧
      Q out mf.world mf.transient mf.frame.sub.logs ∧ mf.createdAccounts = m.createdAccounts := by
  obtain ⟨-, G, d, E, ρ, allowed, t, hG, hpd, hEcr, hpc, hc, hsafe, hEc, hEin⟩ := hr
  exact transport hc hsafe rfl rfl hpd hEcr hpc hEc hEin (hsum G hG)

/-- **A dirty ERC-20 call** whose clean counterpart (calldata `D'`) is the encoding of the call
`c` ends as `CallSpec` says of `c`, for the actors and its accounts. -/
theorem post_call_dirty {g₀ : Nat} {c : Call Address}
    (hcs : CallSpec code abs M g₀ c) {m : Machine} (hS : Start code abs M Act m)
    {D' : ByteArray} (hr : DirtyRun code m D') (henc : c.Encodes D') (hex : Explains rec m c) :
    Halts m (MalPost abs M ops opAddrs rec Act m) := by
  by_cases h : abs.Sound m.ctx.crypto (Act ∪ c.addrs.toFinset) ∧
      M.wf (pre abs (Act ∪ c.addrs.toFinset) m)
  · have hsum : ∀ G, m.frame.gasLeft ≤ G → Halts (clean D' G m) fun mf o =>
        Failed o ∨ ∃ out, o = .success out ∧
          MatchesOk abs (Act ∪ c.addrs.toFinset) m
            (M.events (pre abs (Act ∪ c.addrs.toFinset) m) m.frame.msg.caller c)
            (M.call (pre abs (Act ∪ c.addrs.toFinset) m) m.frame.msg.caller c)
            out mf.world mf.transient mf.frame.sub.logs := fun G hG =>
      (hcs _ _ (start_extend (start_clean hS hG hr.1) _ h.1 h.2) henc
        fun a ha => Finset.mem_union_right _ (List.mem_toFinset.2 ha)).mono fun mf o _ hp => by
        rcases hp with hm | ⟨hfl, -⟩
        · exact matchesOk_of hm
        · exact .inl (failed_of_fails hfl)
    refine (transport' hr hsum).mono fun mf o _ hp => ?_
    rcases hp with hfl | ⟨out, rfl, hq, hcr⟩
    · exact .inl (fails_of_failed hfl)
    · exact .inr (.inr (.inl ⟨c, hex, fun _ _ => matches_of hq hcr⟩))
  · exact (halts_any hS.precompiles).mono fun _ _ _ _ =>
      .inr (.inr (.inl ⟨c, hex, fun hs hw => absurd ⟨hs, hw⟩ h⟩))

/-- What a successful frame must satisfy for `OpMatches` of an operation whose model outcome
is `s'`, minus its created accounts. -/
def OpOk (abs : TokenAbs σ) (Act : Finset Address) (m : Machine) (s' : σ) : SuccessPost :=
  fun _ W T _ => abs.read m.ctx.crypto Act W m.frame.msg.currentTarget = s' ∧
    FrameKeeps abs m.ctx.crypto Act m.frame.msg.currentTarget m.world W ∧ T = m.transient

/-- **A dirty operation** whose clean counterpart (calldata `D'`) the decoder accepts as `e`
ends as `OpSpec` says of `e`, for the actors and its accounts. -/
theorem post_op_dirty {g₀ : Nat} (hos : OpSpec code abs M g₀ ops opAddrs)
    {m : Machine} (hS : Start code abs M Act m) {D' : ByteArray} (hr : DirtyRun code m D')
    {e : E} (hops : ops m.frame.msg.caller D' m.frame.msg.value.toNat = some e) :
    Halts m (MalPost abs M ops opAddrs rec Act m) := by
  by_cases h : abs.Sound m.ctx.crypto (Act ∪ (opAddrs e).toFinset) ∧
      M.wf (pre abs (Act ∪ (opAddrs e).toFinset) m)
  · have hspec := fun G (hG : m.frame.gasLeft ≤ G) =>
      hos _ _ e (start_extend (start_clean hS hG hr.1) _ h.1 h.2) hops
        fun a ha => Finset.mem_union_right _ (List.mem_toFinset.2 ha)
    cases hop : M.op (pre abs (Act ∪ (opAddrs e).toFinset) m) e with
    | none =>
      have hsum : ∀ G, m.frame.gasLeft ≤ G → Halts (clean D' G m) fun mf o =>
          Failed o ∨ ∃ out, o = .success out ∧
            (fun (_ : ByteArray) (_ : World) (_ : TransientStorage) (_ : Array Log) => False)
              out mf.world mf.transient mf.frame.sub.logs := fun G hG =>
        (hspec G hG).mono fun mf o _ hp => by
          rcases hp with hm | ⟨hfl, -⟩
          · unfold OpMatches at hm
            have hop' : M.op (pre abs (Act ∪ (opAddrs e).toFinset) (clean D' G m)) e =
                none := hop
            rw [hop'] at hm
            exact .inl (failed_of_fails hm)
          · exact .inl (failed_of_fails hfl)
      refine (transport' hr (Q := fun _ _ _ _ => False) hsum).mono fun mf o _ hp => ?_
      rcases hp with hfl | ⟨out, rfl, hq, -⟩
      · exact .inl (fails_of_failed hfl)
      · exact hq.elim
    | some s' =>
      have hsum : ∀ G, m.frame.gasLeft ≤ G → Halts (clean D' G m) fun mf o =>
          Failed o ∨ ∃ out, o = .success out ∧
            OpOk abs (Act ∪ (opAddrs e).toFinset) m s' out mf.world mf.transient
              mf.frame.sub.logs := fun G hG =>
        (hspec G hG).mono fun mf o _ hp => by
          rcases hp with hm | ⟨hfl, -⟩
          · unfold OpMatches at hm
            have hop' : M.op (pre abs (Act ∪ (opAddrs e).toFinset) (clean D' G m)) e =
                some s' := hop
            rw [hop'] at hm
            obtain ⟨⟨out, ho⟩, h1, h2, h3, -⟩ := hm
            exact .inr ⟨out, ho, h1, h2, h3⟩
          · exact .inl (failed_of_fails hfl)
      refine (transport' hr hsum).mono fun mf o _ hp => ?_
      rcases hp with hfl | ⟨out, rfl, ⟨h1, h2, h3⟩, hcr⟩
      · exact .inl (fails_of_failed hfl)
      · refine .inr (.inr (.inr ⟨D', e, hops, fun _ _ => ⟨⟨s', hop⟩, ?_⟩⟩))
        unfold OpMatches
        rw [hop]
        exact ⟨⟨out, rfl⟩, h1, h2, h3, hcr⟩
  · exact (halts_any hS.precompiles).mono fun _ _ _ _ =>
      .inr (.inr (.inr ⟨D', e, hops, fun hs hw => absurd ⟨hs, hw⟩ h⟩))

end Verified.WeirdERC20.Common
