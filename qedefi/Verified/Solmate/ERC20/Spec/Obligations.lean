import Verified.Solmate.ERC20.Spec.Dispatch
import Verified.Solmate.ERC20.Spec.Ops
import Verified.Solmate.ERC20.Spec.Static

/-!
# Solmate's `ERC20` is `solmateModel`: the obligations of `ERC20Spec`

Each obligation for the deployed asset (`code ia`, any immutables), from gas `g₀ = 100000`:

* in a normal frame, the exact outcome (`Normal.lean`, `Ops.lean`);
* outside it, the frame *lifted* to gas `max gas g₀` under a dummy parent with empty code
  (`hi`) ends as the static, value or normal theorems say, and the frame itself fails or ends
  the same way (`lowGas`): the asset reads no gas on these paths, whatever the code at `0x01`
  (`noGasRead_of_steps`, `reaches_target`).

`solmate_erc20Spec`: the bundle.

Not proved: `ERC20Spec.Complete`. `PermitSpec` fails for this code, for every gas bound `gp`,
in frames whose gas is `2²⁵⁶` or more (`Start` does not bound it): `GAS` pushes the gas modulo
`2²⁵⁶`, which `permit` passes to the `STATICCALL` of `ecrecover`; with gas `2²⁵⁶·k + c` (`k`
large enough that the frame is `Normal`, `c` such that the pushed word is below the
precompile's 3000), the precompile runs out of gas, the call fails and `permit` reverts on a
valid signature the model accepts. The obligations above avoid this: their paths execute no
`GAS` (`noGasRead_of_steps`).
-/

namespace Verified.Solmate.ERC20.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity EvmLogic.GasMono
open EvmLogic.Program.Nested (bump)
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.Solmate
open Verified.Solmate.Contracts Verified.Solmate.ERC20 Verified.Solmate.ERC4626

/-- The gas from which the asset is exact. -/
def g₀ : Nat := 100000

/-! ## The lifted frame -/

/-- A parent frame with empty code (the frame of `m` with its code removed). -/
def p0 (m : Machine) : Frame := { m.frame with code := .empty }

/-- The frame of `m` with gas `G`, as a call under `p0 m`. -/
def hi (G : Nat) (m : Machine) : Machine := lift (G - m.frame.gasLeft) G [p0 m] (.call 0 0) m

variable {ia : SolmateAsset.Immutables} {Act : Finset Address} {m : Machine}

theorem hi_msg (G : Nat) (m : Machine) : (hi G m).frame.msg = { m.frame.msg with gas := G } :=
  rfl

theorem hi_fresh (hf : Fresh (code ia) m) {G : Nat} (hG : m.frame.gasLeft ≤ G) :
    Fresh (code ia) (hi G m) := by
  obtain ⟨msg, k, snap, hfr, hc⟩ := hf
  refine ⟨{ msg with gas := G }, .call 0 0, snap, ?_, hc⟩
  have hg : m.frame.gasLeft = msg.gas := by rw [hfr]; rfl
  simp only [hi, lift, setKind, bump, hfr, Frame.init, Frame.mk.injEq, and_true]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, ?_⟩
  omega

theorem hi_start (hS : Start (code ia) solmateAbs M Act m) {G : Nat}
    (hG : m.frame.gasLeft ≤ G) : Start (code ia) solmateAbs M Act (hi G m) where
  fresh := hi_fresh hS.fresh hG
  launched := hS.launched
  value := hS.value
  precompiles := hS.precompiles
  size := hS.size
  caller := hS.caller
  sound := hS.sound
  wf := hS.wf

theorem hi_gas {G : Nat} (hG : m.frame.gasLeft ≤ G) : (hi G m).frame.gasLeft = G := by
  simp only [hi, lift, setKind, bump]; omega

theorem failed_fails {o : Outcome} (h : Failed o) : Fails o := by
  cases o with
  | success out => exact absurd rfl (h out)
  | revert _ => trivial
  | halt _ => trivial

/-- **A frame of the asset ends as its lift does, or fails**, on the paths that read no gas. -/
theorem low (hS : Start (code ia) solmateAbs M Act m) {G : Nat} (hG : m.frame.gasLeft ≤ G)
    (hG' : 1000 ≤ G)
    (hc : m.frame.msg.value ≠ 0 ∨ m.frame.msg.data.size < 4 ∨
      Abi.selectorOf m.frame.msg.data ∉ assetSelectors ∨
      Abi.selectorOf m.frame.msg.data ∈ specSelectors)
    {P : ByteArray → Machine → Prop}
    (hP : ∀ out mf mf', mf'.world = mf.world → mf'.transient = mf.transient →
      mf'.createdAccounts = mf.createdAccounts → mf'.frame.sub.logs = mf.frame.sub.logs →
      P out mf → P out mf')
    (hhigh : Halts (hi G m) fun mf o => ∀ out, o = .success out → P out mf) :
    Halts m fun mf o => Fails o ∨ ∃ out, o = .success out ∧ P out mf := by
  have hf := hi_fresh hS.fresh hG
  obtain ⟨hcode, -, hpc, hst, -, -, -⟩ := hf.frame
  obtain ⟨mT, hT, hTpc⟩ := reaches_target (hi G m) hf hS.size (by rw [hi_gas hG]; exact hG') hc
  refine (lowGas (p0 := p0 m) (by rfl) hP hhigh fun N mfh oh hex =>
    noGasRead_of_steps rfl (by rfl) hcode hpc hst hT hTpc N mfh oh hex).mono
    fun mf o _ h => ?_
  rcases h with h | h
  · exact .inl (failed_fails h)
  · exact .inr h

theorem matches_congr {mf mf' : Machine} {o : Outcome} {evs : List (Event Address)}
    {r : Result (VState Address)} (hw : mf'.world = mf.world) (ht : mf'.transient = mf.transient)
    (hc : mf'.createdAccounts = mf.createdAccounts) (hl : mf'.frame.sub.logs = mf.frame.sub.logs)
    (h : Matches solmateAbs Act m mf o evs r) : Matches solmateAbs Act m mf' o evs r := by
  unfold Matches at h ⊢
  split
  · rename_i s' ret
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨h1, hw ▸ h2, hw ▸ h3, ht ▸ h4, hc ▸ h5, hl ▸ h6⟩
  · exact h
  · exact h

theorem sel_mem_spec {data : ByteArray} {s : Nat} {args : List Word} (h : Args data s args)
    (hs : s ∈ specSelectors) : Abi.selectorOf data ∈ specSelectors := h.selector ▸ hs

/-! ## The ERC-20 calls -/

theorem not_success_of_fails {o : Outcome} (h : Fails o) (out : ByteArray) :
    o ≠ .success out := by
  rintro rfl; exact h

/-- **`transfer`.** -/
theorem transfer_spec (dst : Address) (v : ℕ) :
    CallSpec (code ia) solmateAbs M g₀ (.transfer dst v) := by
  intro Act m hS hE hA
  have hdst : dst ∈ Act := hA dst (by simp [Call.addrs])
  by_cases hN : Normal g₀ m
  · exact (transfer_normal hS hE hdst hN.2.2 hN.2.1 (by have := hN.1; unfold g₀ at this; omega)).mono
      fun _ _ _ h => .inl h
  · have hsel := sel_mem_spec hE.2 (by simp [specSelectors])
    refine (low (P := fun out mf => Matches solmateAbs Act m mf (.success out)
        (M.events (pre solmateAbs Act m) m.frame.msg.caller (.transfer dst v))
        (M.call (pre solmateAbs Act m) m.frame.msg.caller (.transfer dst v)))
      hS (Nat.le_max_left _ g₀) (by unfold g₀; omega) (.inr (.inr (.inr hsel)))
      (fun out mf mf' hw ht hc hl h => matches_congr hw ht hc hl h) ?_).mono
      fun mf o _ h => ?_
    · have hS' := hi_start hS (Nat.le_max_left m.frame.gasLeft g₀)
      have hgG := hi_gas (m := m) (Nat.le_max_left m.frame.gasLeft g₀)
      by_cases hval : m.frame.msg.value = 0
      · by_cases hst : m.frame.msg.isStatic = false
        · exact (transfer_normal hS' hE hdst hval hst (by rw [hgG]; unfold g₀; omega)).mono
            fun mf o _ h out ho => by subst ho; exact h
        · exact (transfer_static (hi _ m) hS'.fresh hval (by rw [hi_msg]; simpa using hst)
            (twoWordCall_of_args hE.2) hS.size (by rw [hgG]; unfold g₀; omega)).mono
            fun mf o _ h out ho => absurd ho (not_success_of_fails h out)
      · exact (value_reverts (hi _ m) hS'.fresh hval (by rw [hgG]; unfold g₀; omega)).mono
          fun mf o _ ⟨r, hr⟩ out ho => by subst hr; cases ho
    · rcases h with h | ⟨out, rfl, h⟩
      · exact .inr ⟨h, hN⟩
      · exact .inl h

/-- **`transferFrom`.** -/
theorem transferFrom_spec (src dst : Address) (v : ℕ) :
    CallSpec (code ia) solmateAbs M g₀ (.transferFrom src dst v) := by
  intro Act m hS hE hA
  have hsrc : src ∈ Act := hA src (by simp [Call.addrs])
  have hdst : dst ∈ Act := hA dst (by simp [Call.addrs])
  by_cases hN : Normal g₀ m
  · exact (transferFrom_normal hS hE hsrc hdst hN.2.2 hN.2.1
      (by have := hN.1; unfold g₀ at this; omega)).mono fun _ _ _ h => .inl h
  · have hsel := sel_mem_spec hE.2 (by simp [specSelectors])
    refine (low (P := fun out mf => Matches solmateAbs Act m mf (.success out)
        (M.events (pre solmateAbs Act m) m.frame.msg.caller (.transferFrom src dst v))
        (M.call (pre solmateAbs Act m) m.frame.msg.caller (.transferFrom src dst v)))
      hS (Nat.le_max_left _ g₀) (by unfold g₀; omega) (.inr (.inr (.inr hsel)))
      (fun out mf mf' hw ht hc hl h => matches_congr hw ht hc hl h) ?_).mono
      fun mf o _ h => ?_
    · have hS' := hi_start hS (Nat.le_max_left m.frame.gasLeft g₀)
      have hgG := hi_gas (m := m) (Nat.le_max_left m.frame.gasLeft g₀)
      by_cases hval : m.frame.msg.value = 0
      · by_cases hst : m.frame.msg.isStatic = false
        · exact (transferFrom_normal hS' hE hsrc hdst hval hst
            (by rw [hgG]; unfold g₀; omega)).mono fun mf o _ h out ho => by subst ho; exact h
        · exact (transferFrom_static (hi _ m) hS'.fresh hval (by rw [hi_msg]; simpa using hst)
            (threeWordCall_of_args hE.2) hS.size (by rw [hgG]; unfold g₀; omega)).mono
            fun mf o _ h out ho => absurd ho (not_success_of_fails h out)
      · exact (value_reverts (hi _ m) hS'.fresh hval (by rw [hgG]; unfold g₀; omega)).mono
          fun mf o _ ⟨r, hr⟩ out ho => by subst hr; cases ho
    · rcases h with h | ⟨out, rfl, h⟩
      · exact .inr ⟨h, hN⟩
      · exact .inl h

/-- **`approve`.** -/
theorem approve_spec (sp : Address) (v : ℕ) :
    CallSpec (code ia) solmateAbs M g₀ (.approve sp v) := by
  intro Act m hS hE hA
  have hsp : sp ∈ Act := hA sp (by simp [Call.addrs])
  by_cases hN : Normal g₀ m
  · exact (approve_normal hS hE hsp hN.2.2 hN.2.1
      (by have := hN.1; unfold g₀ at this; omega)).mono fun _ _ _ h => .inl h
  · have hsel := sel_mem_spec hE.2 (by simp [specSelectors])
    refine (low (P := fun out mf => Matches solmateAbs Act m mf (.success out)
        (M.events (pre solmateAbs Act m) m.frame.msg.caller (.approve sp v))
        (M.call (pre solmateAbs Act m) m.frame.msg.caller (.approve sp v)))
      hS (Nat.le_max_left _ g₀) (by unfold g₀; omega) (.inr (.inr (.inr hsel)))
      (fun out mf mf' hw ht hc hl h => matches_congr hw ht hc hl h) ?_).mono
      fun mf o _ h => ?_
    · have hS' := hi_start hS (Nat.le_max_left m.frame.gasLeft g₀)
      have hgG := hi_gas (m := m) (Nat.le_max_left m.frame.gasLeft g₀)
      by_cases hval : m.frame.msg.value = 0
      · by_cases hst : m.frame.msg.isStatic = false
        · exact (approve_normal hS' hE hsp hval hst
            (by rw [hgG]; unfold g₀; omega)).mono fun mf o _ h out ho => by subst ho; exact h
        · exact (approve_static (hi _ m) hS'.fresh hval (by rw [hi_msg]; simpa using hst)
            (twoWordCall_of_args hE.2) hS.size (by rw [hgG]; unfold g₀; omega)).mono
            fun mf o _ h out ho => absurd ho (not_success_of_fails h out)
      · exact (value_reverts (hi _ m) hS'.fresh hval (by rw [hgG]; unfold g₀; omega)).mono
          fun mf o _ ⟨r, hr⟩ out ho => by subst hr; cases ho
    · rcases h with h | ⟨out, rfl, h⟩
      · exact .inr ⟨h, hN⟩
      · exact .inl h

/-- **The ERC-20 calls.** -/
theorem calls_spec : ∀ c, CallSpec (code ia) solmateAbs M g₀ c
  | .transfer dst v => transfer_spec dst v
  | .transferFrom src dst v => transferFrom_spec src dst v
  | .approve sp v => approve_spec sp v
  | .other _ => fun _ _ _ hE => hE.elim
  | .permit .. => fun _ _ _ hE => hE.elim

/-! ## Views -/

theorem view_sel (vw : View) {data : ByteArray} (h : vw.Encodes data) :
    Abi.selectorOf data ∈ specSelectors := by
  cases vw with
  | balanceOf a => exact sel_mem_spec (args := [_]) h (by simp [specSelectors])
  | allowance o sp => exact sel_mem_spec (args := [_, _]) h (by simp [specSelectors])
  | totalSupply => exact sel_mem_spec (args := []) h (by simp [specSelectors])

/-- **The views.** -/
theorem views_spec (vw : View) : ViewSpec (code ia) solmateAbs M g₀ vw := by
  intro Act m hS hE hA
  by_cases hN : g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0
  · exact (view_normal hS vw hE hA hN.2 (by have := hN.1; unfold g₀ at this; omega)).mono
      fun _ _ _ h => .inl h
  · refine (low (P := fun out mf => ∃ x : Word, Outcome.success out = .success (Bytes.ofWord x) ∧
        x.toNat = vw.value M (pre solmateAbs Act m) ∧ mf.world = m.world ∧
        mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
        mf.frame.sub.logs = m.frame.sub.logs)
      hS (Nat.le_max_left _ g₀) (by unfold g₀; omega) (.inr (.inr (.inr (view_sel vw hE))))
      (fun out mf mf' hw ht hc hl ⟨x, h1, h2, h3, h4, h5, h6⟩ =>
        ⟨x, h1, h2, hw ▸ h3, ht ▸ h4, hc ▸ h5, hl ▸ h6⟩) ?_).mono
      fun mf o _ h => ?_
    · have hS' := hi_start hS (Nat.le_max_left m.frame.gasLeft g₀)
      have hgG := hi_gas (m := m) (Nat.le_max_left m.frame.gasLeft g₀)
      by_cases hval : m.frame.msg.value = 0
      · exact (view_normal hS' vw hE hA hval (by rw [hgG]; unfold g₀; omega)).mono
          fun mf o _ h out ho => by subst ho; exact h
      · exact (value_reverts (hi _ m) hS'.fresh hval (by rw [hgG]; unfold g₀; omega)).mono
          fun mf o _ ⟨r, hr⟩ out ho => by subst hr; cases ho
    · rcases h with h | ⟨out, rfl, h⟩
      · exact .inr ⟨h, hN⟩
      · exact .inl h

/-! ## Unknown selectors -/

/-- **Unknown selectors and short calldata.** -/
theorem fallback_spec : FallbackSpec (code ia) solmateAbs M g₀ assetSelectors := by
  intro Act m hS hsel
  by_cases hN : g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false
  · exact (fallback_normal hS hsel (by have := hN.1; unfold g₀ at this; omega)).mono
      fun _ _ _ h => .inl h
  · refine (low (P := fun _ _ => False) hS (Nat.le_max_left _ g₀) (by unfold g₀; omega)
      (by rcases hsel with h | h
          · exact .inr (.inl h)
          · exact .inr (.inr (.inl h)))
      (fun _ _ _ _ _ _ _ h => h) ?_).mono fun mf o _ h => ?_
    · have hS' := hi_start hS (Nat.le_max_left m.frame.gasLeft g₀)
      have hgG := hi_gas (m := m) (Nat.le_max_left m.frame.gasLeft g₀)
      refine (fallback_normal hS' hsel (by rw [hgG]; unfold g₀; omega)).mono
        fun mf o _ h out ho => ?_
      subst ho
      simp only [M, solmateModel_call, call_other] at h
      obtain ⟨r, hr⟩ := h
      cases hr
    · rcases h with h | ⟨_, _, h⟩
      · exact .inr ⟨h, hN⟩
      · exact h.elim

/-! ## `mint` and `burn` -/

theorem opMatches_congr {e : Variant.Op Address} {mf mf' : Machine} {o : Outcome}
    (hw : mf'.world = mf.world) (ht : mf'.transient = mf.transient)
    (hc : mf'.createdAccounts = mf.createdAccounts)
    (h : OpMatches solmateAbs M Act e m mf o) : OpMatches solmateAbs M Act e m mf' o := by
  unfold OpMatches at h ⊢
  split
  · rename_i s' hs
    rw [hs] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    exact ⟨h1, hw ▸ h2, hw ▸ h3, ht ▸ h4, hc ▸ h5⟩
  · rename_i hs
    rw [hs] at h
    exact h

theorem word_toNat (v : Word) : word v.toNat = v := by simp [word]

/-- One of the two operations, in any frame (the high frame of the lifting included). -/
theorem op_high (hS : Start (code ia) solmateAbs M Act m) {e : Variant.Op Address}
    (he : (AddrAmount m.frame.msg.data 0x40c10f19 ∧ e = .mint m.frame.msg.caller
        (Word.toAddress (argWord m.frame.msg.data 0)) (argWord m.frame.msg.data 1).toNat) ∨
      (AddrAmount m.frame.msg.data 0x9dc29fac ∧ e = .burn m.frame.msg.caller
        (Word.toAddress (argWord m.frame.msg.data 0)) (argWord m.frame.msg.data 1).toNat))
    (hA : ∀ a ∈ solmateOpAddrs e, a ∈ Act) (hval : m.frame.msg.value = 0)
    (hg : 60000 ≤ m.frame.gasLeft) :
    Halts m fun mf o => (m.frame.msg.isStatic = false → OpMatches solmateAbs M Act e m mf o) ∧
      (m.frame.msg.isStatic = true → Fails o) := by
  rcases he with ⟨hd, rfl⟩ | ⟨hd, rfl⟩
  · have hd' := twoWordCall_of_addrAmount hd
    rw [word_toNat] at hd'
    have hdst := hA (Word.toAddress (argWord m.frame.msg.data 0)) (by simp [solmateOpAddrs])
    cases hst : m.frame.msg.isStatic
    · exact (mint_normal hS hd' hdst hval hst hg).mono fun _ _ _ h =>
        ⟨fun _ => h, fun h' => absurd h' (by simp)⟩
    · exact (mint_static m hS.fresh hval hst hd' hS.size hg).mono fun _ _ _ h =>
        ⟨fun h' => absurd h' (by simp), fun _ => h⟩
  · have hd' := twoWordCall_of_addrAmount hd
    rw [word_toNat] at hd'
    have hsrc := hA (Word.toAddress (argWord m.frame.msg.data 0)) (by simp [solmateOpAddrs])
    cases hst : m.frame.msg.isStatic
    · exact (burn_normal hS hd' hsrc hval hst hg).mono fun _ _ _ h =>
        ⟨fun _ => h, fun h' => absurd h' (by simp)⟩
    · exact (burn_static m hS.fresh hval hst hd' hS.size hg).mono fun _ _ _ h =>
        ⟨fun h' => absurd h' (by simp), fun _ => h⟩

/-- **The other entry points**: `mint` and `burn`. -/
theorem ops_spec : OpSpec (code ia) solmateAbs M g₀ solmateOps solmateOpAddrs := by
  intro Act m e hS hops hA
  obtain ⟨hv0, he⟩ := solmateOps_some hops
  have hval : m.frame.msg.value = 0 := by
    apply BitVec.eq_of_toNat_eq; simpa using hv0
  have hsel : Abi.selectorOf m.frame.msg.data ∈ specSelectors := by
    rcases he with ⟨⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ <;> rw [h] <;> simp [specSelectors]
  by_cases hN : g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false
  · exact (op_high hS he hA hval (by have := hN.1; unfold g₀ at this; omega)).mono
      fun _ _ _ h => .inl (h.1 hN.2)
  · refine (low (P := fun out mf => OpMatches solmateAbs M Act e m mf (.success out))
      hS (Nat.le_max_left _ g₀) (by unfold g₀; omega) (.inr (.inr (.inr hsel)))
      (fun out mf mf' hw ht hc _ h => opMatches_congr hw ht hc h) ?_).mono
      fun mf o _ h => ?_
    · have hS' := hi_start hS (Nat.le_max_left m.frame.gasLeft g₀)
      have hgG := hi_gas (m := m) (Nat.le_max_left m.frame.gasLeft g₀)
      refine (op_high hS' he hA hval (by rw [hgG]; unfold g₀; omega)).mono
        fun mf o _ h out ho => ?_
      subst ho
      cases hst : m.frame.msg.isStatic
      · exact h.1 hst
      · exact (h.2 hst).elim
    · rcases h with h | ⟨out, rfl, h⟩
      · exact .inr ⟨h, hN⟩
      · exact .inl h

/-! ## The bundle -/

/-- **Solmate's `ERC20` (the deployed `MockERC20`, any immutables) is `solmateModel`** through
`solmateAbs`, exactly from gas `100000`, with the asset's fourteen selectors and `mint`/`burn`
as its other entry points. -/
theorem solmate_erc20Spec (ia : SolmateAsset.Immutables) :
    ERC20Spec (SolmateAsset.runtimeCodeWith ia) solmateAbs solmateModel g₀ assetSelectors
      solmateOps solmateOpAddrs where
  calls := calls_spec
  views := views_spec
  fallback := fallback_spec
  ops := ops_spec

end Verified.Solmate.ERC20.Spec
