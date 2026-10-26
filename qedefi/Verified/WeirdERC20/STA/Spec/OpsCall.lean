import Verified.WeirdERC20.STA.Spec.Ops

/-!
# STA under the spec: the obligation of the other entry points

The code-level runs (`Ops.lean`) against the model's `burn`, `burnFrom` and `adjustAllowance`.
The model's invariant (`Start.wf`: `basePercent = 100`, the actors' balances add up to the
supply) makes the supply cover any burn; the actors' distinct rows (`Start.sound`) keep the
reads after a write at their starting values.
-/

namespace Verified.WeirdERC20.STA.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.STA.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')

set_option linter.unusedSimpArgs false in
theorem sta_op_burn (s : VState Address) (c : Address) (v : ℕ) :
    M.op s (.burn c c v) = if v = 0 ∨ s.bal c < v then none
      else some { s with supply := s.supply - v, bal := s.bal - Finsupp.single c v } := by
  by_cases h1 : v = 0
  · simp [M, QEDefi.ERC20.Spec.STA.staModel, Variant.stepOp, Variant.burn, Variant.sta,
      Variant.standard, Auth.allows, h1]
  · by_cases h2 : s.bal c < v
    · simp [M, QEDefi.ERC20.Spec.STA.staModel, Variant.stepOp, Variant.burn, Variant.sta,
        Variant.standard, Auth.allows, Variant.units, h1, h2]
    · simp [M, QEDefi.ERC20.Spec.STA.staModel, Variant.stepOp, Variant.burn, Variant.sta,
        Variant.standard, Auth.allows, Variant.units, h1, h2]

set_option linter.unusedSimpArgs false in
theorem sta_op_burnFrom (s : VState Address) (c a : Address) (v : ℕ) :
    M.op s (.burnFrom c a v) = if s.allowance a c < v ∨ v = 0 ∨ s.bal a < v then none
      else some { s.setAllowance a c (s.allowance a c - v) with
        supply := s.supply - v
        bal := s.bal - Finsupp.single a v } := by
  by_cases h1 : s.allowance a c < v
  · simp [M, QEDefi.ERC20.Spec.STA.staModel, Variant.stepOp, Variant.burnFrom, Variant.sta,
      Variant.standard, h1]
  by_cases h2 : v = 0
  · simp [M, QEDefi.ERC20.Spec.STA.staModel, Variant.stepOp, Variant.burnFrom, Variant.sta,
      Variant.standard, h1, h2]
  by_cases h3 : s.bal a < v
  · simp [M, QEDefi.ERC20.Spec.STA.staModel, Variant.stepOp, Variant.burnFrom, Variant.sta,
      Variant.standard, Variant.units, h1, h2, h3]
  · simp [M, QEDefi.ERC20.Spec.STA.staModel, Variant.stepOp, Variant.burnFrom, Variant.sta,
      Variant.standard, Variant.units, h1, h2, h3, VState.setAllowance]

set_option linter.unusedSimpArgs false in
theorem sta_op_up (s : VState Address) (c sp : Address) (x : ℕ) :
    M.op s (.adjustAllowance c sp true x) =
      if sp = 0 ∨ QEDefi.Math.MAX < s.allowance c sp + x then none
      else some (s.setAllowance c sp (s.allowance c sp + x)) := by
  by_cases h1 : sp = 0
  · simp [M, QEDefi.ERC20.Spec.STA.staModel, Variant.stepOp, Variant.adjustAllowance,
      Variant.sta, Variant.standard, h1]
  · have h1' : ¬ sp = 0#160 := h1
    by_cases h2 : QEDefi.Math.MAX < s.allowance c sp + x
    · simp [M, QEDefi.ERC20.Spec.STA.staModel, Variant.stepOp, Variant.adjustAllowance,
        Variant.sta, Variant.standard, h1', h2]
    · simp [M, QEDefi.ERC20.Spec.STA.staModel, Variant.stepOp, Variant.adjustAllowance,
        Variant.sta, Variant.standard, h1', h2]

set_option linter.unusedSimpArgs false in
theorem sta_op_down (s : VState Address) (c sp : Address) (x : ℕ) :
    M.op s (.adjustAllowance c sp false x) =
      if sp = 0 ∨ s.allowance c sp < x then none
      else some (s.setAllowance c sp (s.allowance c sp - x)) := by
  by_cases h1 : sp = 0
  · simp [M, QEDefi.ERC20.Spec.STA.staModel, Variant.stepOp, Variant.adjustAllowance,
      Variant.sta, Variant.standard, h1]
  · have h1' : ¬ sp = 0#160 := h1
    by_cases h2 : s.allowance c sp < x
    · simp [M, QEDefi.ERC20.Spec.STA.staModel, Variant.stepOp, Variant.adjustAllowance,
        Variant.sta, Variant.standard, h1', h2]
    · simp [M, QEDefi.ERC20.Spec.STA.staModel, Variant.stepOp, Variant.adjustAllowance,
        Variant.sta, Variant.standard, h1', h2]

/-- `_destroy(a, v)` through the abstraction, from a world whose `basePercent` is 100. -/
theorem staRead_destroyWorld {crypto : Crypto} {Act : Finset Address} {w : World}
    {t a : Address} {v : Word} (hS : staSound crypto Act) (ha : a ∈ Act)
    (h6 : w.sload t 6#256 = 100#256)
    (hb : v.toNat ≤ (w.sload t (balSlot crypto a)).toNat) (hs : v.toNat ≤ (w.sload t 5#256).toNat) :
    staRead crypto Act (destroyWorld crypto w t a v) t =
      { staRead crypto Act w t with
        supply := (staRead crypto Act w t).supply - v.toNat
        bal := (staRead crypto Act w t).bal - Finsupp.single a v.toNat } := by
  have hb1 : (subW w t 5#256 v).sload t (balSlot crypto a) = w.sload t (balSlot crypto a) := by
    simp only [subW, balSlot]
    exact World.sload_sstore_ne_key _ _ _ (fun e => hS.fixed1 3#256 (by simp) a ha (by rw [e]; simp))
  have hsupp : (staRead crypto Act w t).supply = (w.sload t 5#256).toNat := by
    simp [staRead, readSlot, h6]
  have hbalc := readMap_of_mem (crypto := crypto) ha w t 3#256
  rw [destroyWorld, subW, hb1, staRead_sstore_bal hS ha, subW, staRead_sstore_supply hS h6]
  have h1 : (w.sload t (balSlot crypto a) - v).toNat = (w.sload t (balSlot crypto a)).toNat - v.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hb)
  have h2 : (w.sload t 5#256 - v).toNat = (w.sload t 5#256).toNat - v.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hs)
  rw [h1, h2, ← hsupp]
  dsimp only
  congr 1
  ext b
  simp only [Finsupp.update_apply, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
  by_cases hba : b = a
  · subst hba; simp only [ite_true, staRead]; rw [hbalc]
  · simp [hba, Ne.symm hba, staRead]

theorem sta_bal_le_supply {Act : Finset Address} {m : Machine}
    (hs : Start STA.runtimeCode staAbs M Act m) (hv : m.frame.msg.value = 0) {a : Address}
    (ha : a ∈ Act) :
    (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto a)).toNat ≤
      (m.world.sload m.frame.msg.currentTarget 5#256).toNat := by
  obtain ⟨-, htot⟩ := sta_wf_facts hs hv
  rw [← htot, ← readMap_of_mem (crypto := m.ctx.crypto) ha m.world m.frame.msg.currentTarget 3#256]
  exact QEDefi.ERC20.Token.le_total _ _

theorem op_destroy (Act : Finset Address) (m : Machine) (hs : Start STA.runtimeCode staAbs M Act m)
    (hval : m.frame.msg.value = 0) (hd : Args m.frame.msg.data 0x9d118770 [argWord m.frame.msg.data 0]) :
    Halts m fun mf o =>
      OpMatches staAbs M Act (.burn m.frame.msg.caller m.frame.msg.caller
        (argWord m.frame.msg.data 0).toNat) m mf o ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)) := by
  set v := argWord m.frame.msg.data 0
  have hS := hs.sound
  have hcA := hs.caller
  have hpre := pre_eq hs hval
  obtain ⟨h6, -⟩ := sta_wf_facts hs hval
  have hle := sta_bal_le_supply hs hval hcA
  refine halts_split' (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => destroy_high m v hs.fresh hd hs.size hval hG.2 hG.1)
    (destroy_low m v hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  left
  simp only [OpMatches]
  have hbc : (pre staAbs Act m).bal m.frame.msg.caller =
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat := by
    rw [hpre]; simp [staRead, hcA]
  have hv0 : v.toNat = 0 ↔ v = 0 := ⟨fun h => BitVec.eq_of_toNat_eq (by simp [h]), fun h => by simp [h]⟩
  rw [sta_op_burn, hbc]
  by_cases hr : v.toNat = 0 ∨
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat <
        v.toNat
  · rw [ite_pos' hr]
    exact hrev (by rcases hr with h | h; exact .inl (hv0.1 h); exact .inr h)
  rw [ite_neg' hr]
  simp only [not_or, not_lt] at hr
  obtain ⟨hz, hb⟩ := hr
  have hb1 : (subW m.world m.frame.msg.currentTarget 5#256 v).sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller) =
      m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller) := by
    simp only [subW, balSlot]
    exact World.sload_sstore_ne_key _ _ _
      (fun e => hS.fixed1 3#256 (by simp) _ hcA (by rw [e]; simp))
  obtain ⟨ho, hw, ht, hcr⟩ := hok (fun h => hz (hv0.2 h)) hb (by omega) (by rw [hb1]; exact hb)
  refine ⟨ho, ?_, ?_, ht, hcr⟩
  · show staRead _ _ _ _ = _
    rw [hw, staRead_destroyWorld hS hcA h6 hb (by omega), ← hpre]
  · rw [hw, destroyWorld, subW, subW]
    exact BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inl ⟨_, hcA, rfl⟩)))
      (BNB.Spec.FrameKeeps.sstore' (.inl rfl) BNB.Spec.frameKeeps_refl')

/-- Lowering an actor's allowance row leaves the fixed slots and the balance rows. -/
theorem sload_subW_allow {crypto : Crypto} {Act : Finset Address} {w : World}
    {t o sp : Address} {v : Word} (hS : staSound crypto Act) (ho : o ∈ Act) (hsp : sp ∈ Act)
    {k : Word} (hk : k = 5#256 ∨ k = 6#256 ∨ ∃ a ∈ Act, k = balSlot crypto a) :
    (subW w t (allowSlot crypto o sp) v).sload t k = w.sload t k := by
  simp only [subW, allowSlot]
  apply World.sload_sstore_ne_key
  rcases hk with rfl | rfl | ⟨a, ha, rfl⟩
  · exact fun e => hS.fixed2 4#256 (by simp) o ho sp hsp (by rw [← e]; simp)
  · exact fun e => hS.fixed2 4#256 (by simp) o ho sp hsp (by rw [← e]; simp)
  · exact hS.disj 3#256 (by simp) 4#256 (by simp) a ha o ho sp hsp

theorem op_destroyFrom (Act : Finset Address) (m : Machine)
    (hs : Start STA.runtimeCode staAbs M Act m) (a : Address) (haA : a ∈ Act)
    (hval : m.frame.msg.value = 0)
    (hd : Args m.frame.msg.data 0x33393efa [Word.ofAddress a, argWord m.frame.msg.data 1]) :
    Halts m fun mf o =>
      OpMatches staAbs M Act (.burnFrom m.frame.msg.caller a (argWord m.frame.msg.data 1).toNat)
        m mf o ∨ (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)) := by
  set v := argWord m.frame.msg.data 1
  have hS := hs.sound
  have hcA := hs.caller
  have hpre := pre_eq hs hval
  obtain ⟨h6, -⟩ := sta_wf_facts hs hval
  have hle := sta_bal_le_supply hs hval haA
  refine halts_split' (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => destroyFrom_high m a v hs.fresh hd hs.size hval hG.2 hG.1)
    (destroyFrom_low m a v hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  left
  simp only [OpMatches]
  have hW5 := sload_subW_allow (w := m.world) (t := m.frame.msg.currentTarget) (v := v) hS haA hcA
    (k := 5#256) (.inl rfl)
  have hW6 := sload_subW_allow (w := m.world) (t := m.frame.msg.currentTarget) (v := v) hS haA hcA
    (k := 6#256) (.inr (.inl rfl))
  have hWb := sload_subW_allow (w := m.world) (t := m.frame.msg.currentTarget) (v := v) hS haA hcA
    (k := balSlot m.ctx.crypto a) (.inr (.inr ⟨a, haA, rfl⟩))
  simp only [hW5, hWb] at hrev hok
  have hba : (pre staAbs Act m).bal a =
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto a)).toNat := by
    rw [hpre]; simp [staRead, haA]
  have hal : (pre staAbs Act m).allowance a m.frame.msg.caller =
      (m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto a m.frame.msg.caller)).toNat := by
    rw [hpre]; simp [staRead, readMap2, haA, hcA]
  have hv0 : v.toNat = 0 ↔ v = 0 := ⟨fun h => BitVec.eq_of_toNat_eq (by simp [h]), fun h => by simp [h]⟩
  rw [sta_op_burnFrom, hba, hal]
  by_cases hr : (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto a m.frame.msg.caller)).toNat < v.toNat ∨ v.toNat = 0 ∨
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto a)).toNat < v.toNat
  · rw [ite_pos' hr]
    exact hrev (by
      rcases hr with h | h | h
      · exact .inl h
      · exact .inr (.inl (hv0.1 h))
      · exact .inr (.inr h))
  rw [ite_neg' hr]
  simp only [not_or, not_lt] at hr
  obtain ⟨ha, hz, hb⟩ := hr
  have hb1 : (subW (subW m.world m.frame.msg.currentTarget (allowSlot m.ctx.crypto a m.frame.msg.caller)
      v) m.frame.msg.currentTarget 5#256 v).sload m.frame.msg.currentTarget (balSlot m.ctx.crypto a) =
      m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto a) := by
    rw [← hWb]
    simp only [subW, balSlot]
    exact World.sload_sstore_ne_key _ _ _
      (fun e => hS.fixed1 3#256 (by simp) _ haA (by rw [e]; simp))
  obtain ⟨ho, hw, ht, hcr⟩ := hok ha (fun h => hz (hv0.2 h)) hb (by omega) (by rw [hb1]; exact hb)
  refine ⟨ho, ?_, ?_, ht, hcr⟩
  · show staRead _ _ _ _ = _
    rw [hw, staRead_destroyWorld hS haA (by rw [hW6]; exact h6) (by rw [hWb]; exact hb)
      (by rw [hW5]; omega)]
    rw [subW, allowSlot, staRead_sstore_allow hS haA hcA, ← hpre]
    have h1 : (m.world.sload m.frame.msg.currentTarget
        (mappingSlot2 m.ctx.crypto (Word.ofAddress a) (Word.ofAddress m.frame.msg.caller) 4#256) -
          v).toNat = (pre staAbs Act m).allowance a m.frame.msg.caller - v.toNat := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact ha), hal]
    rw [h1, hal]
    rfl
  · rw [hw, destroyWorld, subW, subW, subW]
    exact BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inl ⟨_, haA, rfl⟩)))
      (BNB.Spec.FrameKeeps.sstore' (.inl rfl)
        (BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inr ⟨_, haA, _, hcA, rfl⟩)))
          BNB.Spec.frameKeeps_refl'))

theorem op_up (Act : Finset Address) (m : Machine)
    (hs : Start STA.runtimeCode staAbs M Act m) (sp : Address) (hsA : sp ∈ Act)
    (hval : m.frame.msg.value = 0)
    (hd : Args m.frame.msg.data 0xe5981a42 [Word.ofAddress sp, argWord m.frame.msg.data 1]) :
    Halts m fun mf o =>
      OpMatches staAbs M Act (.adjustAllowance m.frame.msg.caller sp true
        (argWord m.frame.msg.data 1).toNat) m mf o ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)) := by
  set x := argWord m.frame.msg.data 1
  have hS := hs.sound
  have hcA := hs.caller
  have hpre := pre_eq hs hval
  refine halts_split' (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => up_high m sp x hs.fresh hd hs.size hval hG.2 hG.1)
    (up_low m sp x hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  left
  simp only [OpMatches]
  have hal : (pre staAbs Act m).allowance m.frame.msg.caller sp =
      (m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat := by
    rw [hpre]; simp [staRead, readMap2, hsA, hcA]
  rw [sta_op_up, hal]
  by_cases hr : sp = 0 ∨ 2 ^ 256 ≤ x.toNat + (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat
  · rw [ite_pos' (by
      rcases hr with h | h
      · exact .inl h
      · exact .inr (by unfold QEDefi.Math.MAX; omega))]
    exact hrev hr
  rw [ite_neg' (by
    simp only [not_or, not_le] at hr ⊢
    exact ⟨hr.1, by unfold QEDefi.Math.MAX; omega⟩)]
  simp only [not_or, not_le] at hr
  obtain ⟨hs0, hfit⟩ := hr
  obtain ⟨ho, hw, ht, hcr⟩ := hok hs0 hfit
  refine ⟨ho, ?_, ?_, ht, hcr⟩
  · show staRead _ _ _ _ = _
    rw [hw, allowSlot, staRead_sstore_allow hS hcA hsA, ← hpre, BitVec.toNat_add,
      Nat.mod_eq_of_lt hfit, ← allowSlot, ← hal, Nat.add_comm]
  · rw [hw]
    exact BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inr ⟨_, hcA, _, hsA, rfl⟩)))
      BNB.Spec.frameKeeps_refl'

theorem op_down (Act : Finset Address) (m : Machine)
    (hs : Start STA.runtimeCode staAbs M Act m) (sp : Address) (hsA : sp ∈ Act)
    (hval : m.frame.msg.value = 0)
    (hd : Args m.frame.msg.data 0xdf401a96 [Word.ofAddress sp, argWord m.frame.msg.data 1]) :
    Halts m fun mf o =>
      OpMatches staAbs M Act (.adjustAllowance m.frame.msg.caller sp false
        (argWord m.frame.msg.data 1).toNat) m mf o ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)) := by
  set x := argWord m.frame.msg.data 1
  have hS := hs.sound
  have hcA := hs.caller
  have hpre := pre_eq hs hval
  refine halts_split' (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => down_high m sp x hs.fresh hd hs.size hval hG.2 hG.1)
    (down_low m sp x hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  left
  simp only [OpMatches]
  have hal : (pre staAbs Act m).allowance m.frame.msg.caller sp =
      (m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat := by
    rw [hpre]; simp [staRead, readMap2, hsA, hcA]
  rw [sta_op_down, hal]
  by_cases hr : sp = 0 ∨ (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat < x.toNat
  · rw [ite_pos' hr]
    exact hrev hr
  rw [ite_neg' hr]
  simp only [not_or, not_lt] at hr
  obtain ⟨hs0, hle⟩ := hr
  obtain ⟨ho, hw, ht, hcr⟩ := hok hs0 hle
  refine ⟨ho, ?_, ?_, ht, hcr⟩
  · show staRead _ _ _ _ = _
    rw [hw, subW, allowSlot, staRead_sstore_allow hS hcA hsA, ← hpre,
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hle), ← allowSlot, ← hal]
  · rw [hw, subW]
    exact BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inr ⟨_, hcA, _, hsA, rfl⟩)))
      BNB.Spec.frameKeeps_refl'

theorem ofAddress_toAddress {x : Word} (h : x.toNat < 2 ^ 160) :
    Word.ofAddress x.toAddress = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [Word.ofAddress, Word.toAddress, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]

/-- The decoder's arguments are the ABI arguments it read. -/
theorem args_of_ops {data : ByteArray} {sel : Nat} {a : Address} (hsel : Abi.selectorOf data = sel)
    (hsz : ¬ data.size < 68) (ha : addrArg (argWord data 0) = some a) :
    Args data sel [Word.ofAddress a, argWord data 1] := by
  unfold addrArg at ha
  split at ha
  · rename_i hlt
    cases ha
    refine ⟨hsel, by simp; omega, ?_⟩
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · simp only [List.getElem_cons_zero]; rw [ofAddress_toAddress hlt]; rfl
    · rfl
  · cases ha

theorem args_one {data : ByteArray} {k : Nat} (hsel : Abi.selectorOf data = k)
    (hsz : ¬ data.size < 36) : Args data k [argWord data 0] := by
  refine ⟨hsel, by simp; omega, ?_⟩
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0) with rfl
  rfl

/-- **The other entry points**: `destroy`, `destroyFrom`, `upAllowance`, `downAllowance`. -/
theorem ops_spec : OpSpec STA.runtimeCode staAbs M g₀ staOps staOpAddrs := by
  intro Act m e hs hops haddr
  simp only [staOps] at hops
  split at hops
  · cases hops
  rename_i hvs
  have hval : m.frame.msg.value = 0 := by
    have : m.frame.msg.value.toNat = 0 := by simp only [not_or] at hvs; omega
    exact BitVec.eq_of_toNat_eq this
  have hsz : ¬ m.frame.msg.data.size < 36 := fun h => hvs (.inr h)
  split at hops
  · rename_i hsel
    cases hops
    exact op_destroy Act m hs hval (args_one hsel hsz)
  split at hops
  · cases hops
  rename_i hsz2
  split at hops
  · rename_i _ hsel
    cases ha : addrArg (argWord m.frame.msg.data 0) with
    | none => simp [ha] at hops
    | some a =>
      simp only [ha, Option.map_some, Option.some.injEq] at hops
      subst hops
      exact op_destroyFrom Act m hs a (haddr a (by simp [staOpAddrs])) hval (args_of_ops hsel hsz2 ha)
  split at hops
  · rename_i _ _ hsel
    cases ha : addrArg (argWord m.frame.msg.data 0) with
    | none => simp [ha] at hops
    | some a =>
      simp only [ha, Option.map_some, Option.some.injEq] at hops
      subst hops
      exact op_up Act m hs a (haddr a (by simp [staOpAddrs])) hval (args_of_ops hsel hsz2 ha)
  split at hops
  · rename_i _ _ _ hsel
    cases ha : addrArg (argWord m.frame.msg.data 0) with
    | none => simp [ha] at hops
    | some a =>
      simp only [ha, Option.map_some, Option.some.injEq] at hops
      subst hops
      exact op_down Act m hs a (haddr a (by simp [staOpAddrs])) hval (args_of_ops hsel hsz2 ha)
  · cases hops

end Verified.WeirdERC20.STA.Spec
