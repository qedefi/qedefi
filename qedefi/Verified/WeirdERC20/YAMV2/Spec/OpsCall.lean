import Verified.WeirdERC20.YAMV2.Spec.Decrease
import Verified.WeirdERC20.YAMV2.Spec.TransferCall

/-!
# YAMv2 under the spec: the other entry points

`mint(dst, x)` by the minter, `increaseAllowance(sp, x)` and `decreaseAllowance(sp, x)`, as
decoded by `ops`, against the model's `stepOp`: the code-level runs (`Ops.lean`,
`Decrease.lean`) through the abstraction. The supply bound (`Start.wf`) makes the minted
balance fit.
-/

namespace Verified.WeirdERC20.YAMV2.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.YAMV2.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

/-! ## The model -/

set_option linter.unusedSimpArgs false in
theorem yam_op_mint (s : VState Address) (c d : Address) (v : ℕ) :
    M.op s (.mint c d v) =
      if c = s.admin ∧ d ≠ 0 ∧ s.supply + v ≤ QEDefi.Math.MAX then
        some { s with supply := s.supply + v, bal := s.bal + Finsupp.single d v }
      else none := by
  simp only [M, QEDefi.ERC20.Spec.YAMV2.model, QEDefi.ERC20.Spec.YAMV2.stepOp]
  by_cases h1 : c = s.admin
  · by_cases h2 : d = 0
    · subst h2
      simp [h1, Variant.mint, QEDefi.ERC20.Spec.YAMV2.variant, Variant.standard, Auth.allows]
    · have h2' : ¬ d = 0#160 := h2
      by_cases h3 : s.supply + v ≤ QEDefi.Math.MAX
      · simp [h1, h2', h3, Variant.mint, QEDefi.ERC20.Spec.YAMV2.variant, Variant.standard,
          Auth.allows, Variant.units]
      · simp [h1, h2', h3, Variant.mint, QEDefi.ERC20.Spec.YAMV2.variant, Variant.standard,
          Auth.allows, Variant.units, lt_of_not_ge h3]
  · simp [h1]

set_option linter.unusedSimpArgs false in
theorem yam_op_increase (s : VState Address) (c sp : Address) (x : ℕ) :
    M.op s (.increaseAllowance c sp x) =
      if c ≠ 0 ∧ sp ≠ 0 ∧ s.allowance c sp + x ≤ QEDefi.Math.MAX then
        some (s.setAllowance c sp (s.allowance c sp + x))
      else none := by
  simp only [M, QEDefi.ERC20.Spec.YAMV2.model, QEDefi.ERC20.Spec.YAMV2.stepOp]
  by_cases h1 : c = 0
  · simp [h1]
  have h1' : ¬ c = 0#160 := h1
  by_cases h2 : sp = 0
  · subst h2
    simp [h1', Variant.adjustAllowance, QEDefi.ERC20.Spec.YAMV2.variant]
  have h2' : ¬ sp = 0#160 := h2
  by_cases h3 : s.allowance c sp + x ≤ QEDefi.Math.MAX
  · simp [h1', h2', h3, Variant.adjustAllowance, QEDefi.ERC20.Spec.YAMV2.variant]
  · simp [h1', h2', h3, Variant.adjustAllowance, QEDefi.ERC20.Spec.YAMV2.variant,
      lt_of_not_ge h3]

set_option linter.unusedSimpArgs false in
theorem yam_op_decrease (s : VState Address) (c sp : Address) (x : ℕ) :
    M.op s (.decreaseAllowance c sp x) =
      if c ≠ 0 ∧ sp ≠ 0 ∧ x ≤ s.allowance c sp then
        some (s.setAllowance c sp (s.allowance c sp - x))
      else none := by
  simp only [M, QEDefi.ERC20.Spec.YAMV2.model, QEDefi.ERC20.Spec.YAMV2.stepOp]
  by_cases h1 : c = 0
  · simp [h1]
  have h1' : ¬ c = 0#160 := h1
  by_cases h2 : sp = 0
  · subst h2
    simp [h1', Variant.adjustAllowance, QEDefi.ERC20.Spec.YAMV2.variant]
  have h2' : ¬ sp = 0#160 := h2
  by_cases h3 : x ≤ s.allowance c sp
  · simp [h1', h2', h3, Variant.adjustAllowance, QEDefi.ERC20.Spec.YAMV2.variant,
      Nat.not_lt.2 h3]
  · simp [h1', h2', h3, Variant.adjustAllowance, QEDefi.ERC20.Spec.YAMV2.variant,
      lt_of_not_ge h3]

/-! ## Decoding -/

/-- What `ops` decodes: no value, two clean argument words, one of the three selectors. -/
theorem ops_some {c : Address} {data : ByteArray} {value : ℕ} {e : QEDefi.ERC20.Spec.YAMV2.Op Address}
    (h : ops c data value = some e) :
    value = 0 ∧ ∃ a, Word.ofAddress a = argWord data 0 ∧
      ((Abi.selectorOf data = 0x40c10f19 ∧ Args data 0x40c10f19 [Word.ofAddress a, argWord data 1] ∧
          e = .mint c a (argWord data 1).toNat) ∨
        (Abi.selectorOf data = 0x39509351 ∧
          Args data 0x39509351 [Word.ofAddress a, argWord data 1] ∧
          e = .increaseAllowance c a (argWord data 1).toNat) ∨
        (Abi.selectorOf data = 0xa457c2d7 ∧
          Args data 0xa457c2d7 [Word.ofAddress a, argWord data 1] ∧
          e = .decreaseAllowance c a (argWord data 1).toNat)) := by
  unfold ops at h
  by_cases h1 : value ≠ 0 ∨ data.size < 4 + 32 * 2
  · rw [ite_pos' h1] at h; cases h
  rw [ite_neg' h1] at h
  simp only [not_or, not_lt, ne_eq, not_not] at h1
  obtain ⟨hv, hsz⟩ := h1
  refine ⟨hv, ?_⟩
  cases ha : addrArg data 0 with
  | none => rw [ha] at h; cases h
  | some a =>
    rw [ha] at h
    simp only at h
    simp only [addrArg] at ha
    by_cases hc : Word.ofAddress (Word.toAddress (argWord data 0)) = argWord data 0
    swap
    · rw [ite_neg' hc] at ha; cases ha
    rw [ite_pos' hc] at ha
    cases ha
    refine ⟨_, hc, ?_⟩
    have hargs : ∀ s, Abi.selectorOf data = s →
        Args data s [Word.ofAddress (Word.toAddress (argWord data 0)), argWord data 1] := by
      intro s hs
      refine ⟨hs, by simpa using hsz, fun i hi => ?_⟩
      match i, hi with
      | 0, _ => simpa [argWord] using hc.symm
      | 1, _ => rfl
    by_cases s1 : Abi.selectorOf data = 0x40c10f19
    · rw [ite_pos' s1] at h; cases h; exact .inl ⟨s1, hargs _ s1, rfl⟩
    rw [ite_neg' s1] at h
    by_cases s2 : Abi.selectorOf data = 0x39509351
    · rw [ite_pos' s2] at h; cases h; exact .inr (.inl ⟨s2, hargs _ s2, rfl⟩)
    rw [ite_neg' s2] at h
    by_cases s3 : Abi.selectorOf data = 0xa457c2d7
    · rw [ite_pos' s3] at h; cases h; exact .inr (.inr ⟨s3, hargs _ s3, rfl⟩)
    rw [ite_neg' s3] at h
    cases h

/-! ## The storage -/

theorem read_sstore_supply {crypto : Crypto} {Act : Finset Address} {w : World} {t : Address}
    (hS : abs.Sound crypto Act) (y : Word) :
    read crypto Act (w.sstore t 3#256 y) t = { read crypto Act w t with supply := y.toNat } := by
  simp only [read, VState.ofToken, show balancesSlot = 1#256 from rfl,
    show supplySlot = 3#256 from rfl, show allowancesSlot = 2#256 from rfl,
    show minterSlot = 0#256 from rfl]
  rw [BNB.Spec.readMap_sstore_fixed hS (by decide) (by decide),
    BNB.Spec.readMap2_sstore_fixed hS (by decide) (by decide),
    World.sload_sstore_ne_key _ _ _ (by decide : (0#256 : Word) ≠ 3#256)]
  simp [readSlot, World.sload_sstore_self]

/-! ## The obligations -/

theorem op_mint {Act : Finset Address} {m : Machine} (dst : Address) (x : Word)
    (hs : Start YAMV2.runtimeCode abs M Act m) (hv0 : m.frame.msg.value = 0)
    (hd : Args m.frame.msg.data 0x40c10f19 [Word.ofAddress dst, x]) (hdA : dst ∈ Act) :
    Halts m fun mf o =>
      OpMatches abs M Act (.mint m.frame.msg.caller dst x.toNat) m mf o ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)) := by
  refine halts_split' (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => mint_high m dst x hs.fresh hd hs.size hv0 hG.2 hG.1)
    (mint_low m dst x hs.fresh hd hs.size) ?_
  rintro mf o ⟨-, hrev, hok⟩
  left
  have hpre := pre_eq hs hv0
  have hwf := hs.wf
  rw [hpre] at hwf
  obtain ⟨htot, -⟩ := hwf
  unfold OpMatches
  rw [yam_op_mint, hpre]
  have hadm : (read m.ctx.crypto Act m.world m.frame.msg.currentTarget).admin =
      Word.toAddress (m.world.sload m.frame.msg.currentTarget 0#256) := rfl
  have hsup : (read m.ctx.crypto Act m.world m.frame.msg.currentTarget).supply =
      (m.world.sload m.frame.msg.currentTarget 3#256).toNat := rfl
  rw [hadm, hsup]
  have hSlt := BitVec.isLt (m.world.sload m.frame.msg.currentTarget 3#256)
  by_cases hr : m.frame.msg.caller = Word.toAddress (m.world.sload m.frame.msg.currentTarget 0#256) ∧
      dst ≠ 0 ∧ (m.world.sload m.frame.msg.currentTarget 3#256).toNat + x.toNat ≤ QEDefi.Math.MAX
  swap
  · rw [ite_neg' hr]
    obtain ⟨out, rfl⟩ := hrev (by
      simp only [not_and_or, not_not] at hr
      rcases hr with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · unfold QEDefi.Math.MAX at h; exact .inr (.inr (by omega)))
    exact trivial
  rw [ite_pos' hr]
  obtain ⟨hmin, hd0, hle⟩ := hr
  unfold QEDefi.Math.MAX at hle
  have hbal : (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat ≤
      (m.world.sload m.frame.msg.currentTarget 3#256).toNat := by
    have h1 := QEDefi.ERC20.Token.le_total
      (read m.ctx.crypto Act m.world m.frame.msg.currentTarget).bal dst
    simp only [read, VState.ofToken, show balancesSlot = 1#256 from rfl, readMap_of_mem hdA,
      readSlot, show supplySlot = 3#256 from rfl] at h1 htot
    exact h1.trans htot
  have hne : balSlot m.ctx.crypto dst ≠ 3#256 := fun e =>
    hs.sound.fixed1 1#256 (by decide) dst hdA (by simp only [balSlot] at e; rw [e]; decide)
  have hw1 : (m.world.sstore m.frame.msg.currentTarget 3#256
      (x + m.world.sload m.frame.msg.currentTarget 3#256)).sload m.frame.msg.currentTarget
        (balSlot m.ctx.crypto dst) = m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst) :=
    World.sload_sstore_ne_key _ _ _ hne
  obtain ⟨-, -, ho, hw, ht, hcr⟩ := hok hmin hd0 (by omega) (by rw [hw1]; omega)
  refine ⟨ho, ?_, ?_, ht, hcr⟩
  · show read _ _ _ _ = _
    rw [hw, mintWorld, read_sstore_bal hs.sound hdA, read_sstore_supply hs.sound, hw1]
    have e1 : (x + m.world.sload m.frame.msg.currentTarget 3#256).toNat =
        (m.world.sload m.frame.msg.currentTarget 3#256).toNat + x.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega
    have e2 : (read m.ctx.crypto Act m.world m.frame.msg.currentTarget).bal.update dst
        (x + m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat =
        (read m.ctx.crypto Act m.world m.frame.msg.currentTarget).bal +
          Finsupp.single dst x.toNat := by
      ext a
      simp only [Finsupp.update_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
      by_cases ha : a = dst
      · subst ha
        simp only [ite_true, read, VState.ofToken, readMap_of_mem hdA,
          show balancesSlot = 1#256 from rfl]
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
        simp only [balSlot] at *; omega
      · simp [ha, Ne.symm ha]
    rw [e1]
    dsimp only
    rw [e2]
    rfl
  · rw [hw, mintWorld]
    exact BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inl ⟨_, hdA, rfl⟩)))
      (BNB.Spec.FrameKeeps.sstore' (.inr (.inl rfl)) BNB.Spec.frameKeeps_refl')

theorem read_allowance {crypto : Crypto} {Act : Finset Address} {w : World} {t o sp : Address}
    (ho : o ∈ Act) (hsp : sp ∈ Act) :
    (read crypto Act w t).allowance o sp = (w.sload t (allowSlot crypto o sp)).toNat := by
  simp [read, VState.ofToken, readMap2, ho, hsp, allowancesSlot, allowSlot]

theorem op_increase {Act : Finset Address} {m : Machine} (sp : Address) (x : Word)
    (hs : Start YAMV2.runtimeCode abs M Act m) (hv0 : m.frame.msg.value = 0)
    (hd : Args m.frame.msg.data 0x39509351 [Word.ofAddress sp, x]) (hsA : sp ∈ Act) :
    Halts m fun mf o =>
      OpMatches abs M Act (.increaseAllowance m.frame.msg.caller sp x.toNat) m mf o ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)) := by
  refine halts_split' (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => increase_high m sp x hs.fresh hd hs.size hv0 hG.2 hG.1)
    (increase_low m sp x hs.fresh hd hs.size) ?_
  rintro mf o ⟨-, hrev, hok⟩
  left
  have hpre := pre_eq hs hv0
  unfold OpMatches
  rw [yam_op_increase, hpre, read_allowance hs.caller hsA]
  have hAlt := BitVec.isLt
    (m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto m.frame.msg.caller sp))
  by_cases hr : m.frame.msg.caller ≠ 0 ∧ sp ≠ 0 ∧ (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat + x.toNat ≤ QEDefi.Math.MAX
  swap
  · rw [ite_neg' hr]
    obtain ⟨out, rfl⟩ := hrev (by
      simp only [not_and_or, not_not] at hr
      rcases hr with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · unfold QEDefi.Math.MAX at h; exact .inr (.inr (by omega)))
    exact trivial
  rw [ite_pos' hr]
  obtain ⟨hc0, hs0, hle⟩ := hr
  unfold QEDefi.Math.MAX at hle
  obtain ⟨-, -, ho, hw, ht, hcr⟩ := hok hc0 hs0 (by omega)
  refine ⟨ho, ?_, ?_, ht, hcr⟩
  · show read _ _ _ _ = _
    rw [hw, read_sstore_allow hs.sound hs.caller hsA,
      BitVec.toNat_add, Nat.mod_eq_of_lt (by omega), Nat.add_comm]
  · rw [hw]
    exact BNB.Spec.FrameKeeps.sstore'
      (.inr (.inr (.inr ⟨_, hs.caller, _, hsA, rfl⟩))) BNB.Spec.frameKeeps_refl'

theorem op_decrease {Act : Finset Address} {m : Machine} (sp : Address) (x : Word)
    (hs : Start YAMV2.runtimeCode abs M Act m) (hv0 : m.frame.msg.value = 0)
    (hd : Args m.frame.msg.data 0xa457c2d7 [Word.ofAddress sp, x]) (hsA : sp ∈ Act) :
    Halts m fun mf o =>
      OpMatches abs M Act (.decreaseAllowance m.frame.msg.caller sp x.toNat) m mf o ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)) := by
  refine halts_split' (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => decrease_high m sp x hs.fresh hd hs.size hv0 hG.2 hG.1)
    (decrease_low m sp x hs.fresh hd hs.size) ?_
  rintro mf o ⟨-, hrev, hok⟩
  left
  have hpre := pre_eq hs hv0
  unfold OpMatches
  rw [yam_op_decrease, hpre, read_allowance hs.caller hsA]
  by_cases hr : m.frame.msg.caller ≠ 0 ∧ sp ≠ 0 ∧ x.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat
  swap
  · rw [ite_neg' hr]
    obtain ⟨out, rfl⟩ := hrev (by
      simp only [not_and_or, not_not, not_le] at hr
      rcases hr with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h))
    exact trivial
  rw [ite_pos' hr]
  obtain ⟨hc0, hs0, hle⟩ := hr
  obtain ⟨-, -, ho, hw, ht, hcr⟩ := hok hc0 hs0 hle
  refine ⟨ho, ?_, ?_, ht, hcr⟩
  · show read _ _ _ _ = _
    rw [hw, read_sstore_allow hs.sound hs.caller hsA,
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)]
  · rw [hw]
    exact BNB.Spec.FrameKeeps.sstore'
      (.inr (.inr (.inr ⟨_, hs.caller, _, hsA, rfl⟩))) BNB.Spec.frameKeeps_refl'

/-- **The other entry points**: `mint`, `increaseAllowance`, `decreaseAllowance`. -/
theorem ops_spec : OpSpec YAMV2.runtimeCode abs M g₀ ops opAddrs := by
  intro Act m e hs hops haddr
  obtain ⟨hv, a, -, hcase⟩ := ops_some hops
  have hv0 : m.frame.msg.value = 0 := BitVec.eq_of_toNat_eq (by simpa using hv)
  rcases hcase with ⟨-, hd, rfl⟩ | ⟨-, hd, rfl⟩ | ⟨-, hd, rfl⟩
  · exact op_mint a _ hs hv0 hd (haddr a (by simp [opAddrs]))
  · exact op_increase a _ hs hv0 hd (haddr a (by simp [opAddrs]))
  · exact op_decrease a _ hs hv0 hd (haddr a (by simp [opAddrs]))

end Verified.WeirdERC20.YAMV2.Spec
