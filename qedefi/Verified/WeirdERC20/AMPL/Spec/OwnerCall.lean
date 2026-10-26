import Verified.WeirdERC20.AMPL.Spec.Rebase
import Verified.WeirdERC20.AMPL.Spec.OpsCall

/-!
# AMPL under the spec: the owner's and the monetary policy's entry points

The code-level runs (`Owner.lean`, `Rebase.lean`) against the model's `setMonetaryPolicy`,
`transferOwnership`, `renounceOwnership` and `rebase` (`amplOp`), and `OpSpec` for every
decoded entry point (`ops_spec`).
-/

namespace Verified.WeirdERC20.AMPL.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.AMPL.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open QEDefi.ERC20.Spec.AMPL (AState AState.setAllowance liftR AmplOp amplOp rebaseOp rebaseSupply)

/-- The model's `rebaseSupply` on the stored supply and the `int256` delta is the code's
`rebaseW`. -/
theorem rebaseSupply_eq (S d : Word) :
    rebaseSupply S.toNat d.toInt = (rebaseW S d).map BitVec.toNat := by
  have hd := d.isLt
  have hS := S.isLt
  unfold rebaseSupply rebaseW
  by_cases hn : 2 ^ 255 ≤ d.toNat
  · have hi : d.toInt = (d.toNat : ℤ) - 2 ^ 256 := by
      rw [BitVec.toInt_eq_toNat_cond]; split <;> push_cast <;> omega
    have hneg : (0#256 - d).toNat = 2 ^ 256 - d.toNat := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.zero_mod]; omega
    rw [hi, ite_pos' (by omega), ite_pos' hn]
    by_cases hm : d.toNat = 2 ^ 255
    · rw [ite_pos' (by omega), ite_pos' hm]; rfl
    rw [ite_neg' (by omega), ite_neg' hm]
    have habs : ((d.toNat : ℤ) - 2 ^ 256).natAbs = (0#256 - d).toNat := by omega
    rw [habs]
    by_cases hs : S.toNat < (0#256 - d).toNat
    · rw [ite_pos' hs, ite_pos' hs]; rfl
    rw [ite_neg' hs, ite_neg' hs]
    simp only [Option.map_some, Option.some.injEq]
    have hsub : (S - (0#256 - d)).toNat = S.toNat - (0#256 - d).toNat := by
      rw [BitVec.toNat_sub S (0#256 - d)]
      omega
    rw [hsub]
  · have hi : d.toInt = (d.toNat : ℤ) := by
      rw [BitVec.toInt_eq_toNat_cond]; split <;> push_cast <;> omega
    rw [hi, ite_neg' (by omega), ite_neg' hn]
    simp only [Int.toNat_natCast]
    unfold QEDefi.Math.MAX
    by_cases hf : 2 ^ 256 ≤ d.toNat + S.toNat
    · rw [ite_pos' (by omega), ite_pos' hf]; rfl
    rw [ite_neg' (by omega), ite_neg' hf]
    simp only [Option.map_some, Option.some.injEq, BitVec.toNat_add]
    omega

/-- A write to a fixed slot (`155`–`157`, `0`, `104`) leaves the actors' rows. -/
theorem amplRead_sstore_fixed {crypto : Crypto} {Act : Finset Address} {w : World} {t : Address}
    {k x : Word} (hS : amplSound crypto Act)
    (hk : k ∈ [155#256, 156#256, 157#256, 0#256, 104#256]) :
    amplRead crypto Act (w.sstore t k x) t = { amplRead crypto Act w t with
      supply := if Live (w.sstore t k x) t then readSlot (w.sstore t k x) t 156#256 else 0
      scale := readSlot (w.sstore t k x) t 157#256
      admin := ((w.sstore t k x).sload t 155#256).toAddress
      owner := ((w.sstore t k x).sload t 104#256).toAddress } := by
  simp only [amplRead]
  rw [BNB.Spec.readMap_sstore_fixed (base := 158#256) hS hk (by simp),
    BNB.Spec.readMap_sstore_fixed (base := 160#256) hS hk (by simp),
    BNB.Spec.readMap2_sstore_fixed (base := 159#256) hS hk (by simp), World.balance_sstore]

theorem ampl_op_setMP (s : AState Address) (c p : Address) :
    M.op s (.setMonetaryPolicy c p) = if c = s.owner then some { s with admin := p } else none :=
  rfl

theorem ampl_op_transferOwnership (s : AState Address) (c a : Address) :
    M.op s (.transferOwnership c a) =
      if c = s.owner ∧ a ≠ 0 then some { s with owner := a } else none :=
  rfl

theorem ampl_op_renounce (s : AState Address) (c : Address) :
    M.op s (.renounceOwnership c) = if c = s.owner then some { s with owner := 0 } else none :=
  rfl

theorem ampl_op_rebase (s : AState Address) (c : Address) (d : ℤ) :
    M.op s (.rebase c d) = rebaseOp s c d :=
  rfl

/-- **`setMonetaryPolicy(p)`**: by the owner, the monetary policy becomes `p`. -/
theorem op_setMP (Act : Finset Address) (m : Machine)
    (hs : Start AMPL.runtimeCode amplAbs M Act m) (p : Address)
    (hval : m.frame.msg.value = 0) (hd : Args m.frame.msg.data 0x8b5a6a08 [Word.ofAddress p]) :
    Halts m fun mf o =>
      OpMatches amplAbs M Act (.setMonetaryPolicy m.frame.msg.caller p) m mf o ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)) := by
  have hS := hs.sound
  have hpre := pre_eq hs hval
  refine halts_split' (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => setMP_high m p hs.fresh hd hs.size hval hG.2 hG.1)
    (setMP_low m p hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  left
  simp only [OpMatches]
  rw [ampl_op_setMP, hpre]
  rw [show (amplRead m.ctx.crypto Act m.world m.frame.msg.currentTarget).owner =
    (m.world.sload m.frame.msg.currentTarget 104#256).toAddress from rfl]
  by_cases hown : m.frame.msg.caller = (m.world.sload m.frame.msg.currentTarget 104#256).toAddress
  swap
  · rw [ite_neg' hown]
    exact hrev hown
  rw [ite_pos' hown]
  obtain ⟨ho, hw, ht, hcr⟩ := hok hown
  refine ⟨ho, ?_, ?_, ht, hcr⟩
  · show amplRead _ _ _ _ = _
    rw [hw, amplRead_sstore_fixed hS (by simp)]
    simp only [Live, readSlot, World.sload_sstore_self,
      World.sload_sstore_ne_key _ _ _ (by decide : (0#256 : Word) ≠ 155#256),
      World.sload_sstore_ne_key _ _ _ (by decide : (104#256 : Word) ≠ 155#256),
      World.sload_sstore_ne_key _ _ _ (by decide : (156#256 : Word) ≠ 155#256),
      World.sload_sstore_ne_key _ _ _ (by decide : (157#256 : Word) ≠ 155#256),
      toAddress_or_and_hi]
    rfl
  · rw [hw]
    exact BNB.Spec.FrameKeeps.sstore' (.inl rfl) BNB.Spec.frameKeeps_refl'

/-- **`transferOwnership(a)`**: by the owner, `a ≠ 0`, the owner becomes `a`. -/
theorem op_transferOwnership (Act : Finset Address) (m : Machine)
    (hs : Start AMPL.runtimeCode amplAbs M Act m) (a : Address)
    (hval : m.frame.msg.value = 0) (hd : Args m.frame.msg.data 0xf2fde38b [Word.ofAddress a]) :
    Halts m fun mf o =>
      OpMatches amplAbs M Act (.transferOwnership m.frame.msg.caller a) m mf o ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)) := by
  have hS := hs.sound
  have hpre := pre_eq hs hval
  refine halts_split' (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => transferOwnership_high m a hs.fresh hd hs.size hval hG.2 hG.1)
    (transferOwnership_low m a hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  left
  simp only [OpMatches]
  rw [ampl_op_transferOwnership, hpre]
  rw [show (amplRead m.ctx.crypto Act m.world m.frame.msg.currentTarget).owner =
    (m.world.sload m.frame.msg.currentTarget 104#256).toAddress from rfl]
  by_cases hown : m.frame.msg.caller = (m.world.sload m.frame.msg.currentTarget 104#256).toAddress
    ∧ a ≠ 0
  swap
  · rw [ite_neg' hown]
    exact hrev (by
      by_cases h1 : m.frame.msg.caller =
          (m.world.sload m.frame.msg.currentTarget 104#256).toAddress
      · exact .inr (Classical.not_not.1 fun h2 => hown ⟨h1, h2⟩)
      · exact .inl h1)
  rw [ite_pos' hown]
  obtain ⟨ho, hw, ht, hcr⟩ := hok hown.1 hown.2
  refine ⟨ho, ?_, ?_, ht, hcr⟩
  · show amplRead _ _ _ _ = _
    rw [hw, amplRead_sstore_fixed hS (by simp)]
    simp only [Live, readSlot, World.sload_sstore_self,
      World.sload_sstore_ne_key _ _ _ (by decide : (0#256 : Word) ≠ 104#256),
      World.sload_sstore_ne_key _ _ _ (by decide : (155#256 : Word) ≠ 104#256),
      World.sload_sstore_ne_key _ _ _ (by decide : (156#256 : Word) ≠ 104#256),
      World.sload_sstore_ne_key _ _ _ (by decide : (157#256 : Word) ≠ 104#256),
      toAddress_or_hi_and]
    rfl
  · rw [hw]
    exact BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl)))))))
      BNB.Spec.frameKeeps_refl'

/-- **`renounceOwnership()`**: by the owner, the owner becomes `0`. -/
theorem op_renounce (Act : Finset Address) (m : Machine)
    (hs : Start AMPL.runtimeCode amplAbs M Act m)
    (hval : m.frame.msg.value = 0) (hsel : Abi.selectorOf m.frame.msg.data = 0x715018a6)
    (h4 : 4 ≤ m.frame.msg.data.size) :
    Halts m fun mf o =>
      OpMatches amplAbs M Act (.renounceOwnership m.frame.msg.caller) m mf o ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)) := by
  have hS := hs.sound
  have hpre := pre_eq hs hval
  refine halts_split' (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => renounce_high m hs.fresh hsel h4 hs.size hval hG.2 hG.1)
    (renounce_low m hs.fresh hsel h4 hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  left
  simp only [OpMatches]
  rw [ampl_op_renounce, hpre]
  rw [show (amplRead m.ctx.crypto Act m.world m.frame.msg.currentTarget).owner =
    (m.world.sload m.frame.msg.currentTarget 104#256).toAddress from rfl]
  by_cases hown : m.frame.msg.caller = (m.world.sload m.frame.msg.currentTarget 104#256).toAddress
  swap
  · rw [ite_neg' hown]
    exact hrev hown
  rw [ite_pos' hown]
  obtain ⟨ho, hw, ht, hcr⟩ := hok hown
  refine ⟨ho, ?_, ?_, ht, hcr⟩
  · show amplRead _ _ _ _ = _
    rw [hw, amplRead_sstore_fixed hS (by simp)]
    simp only [Live, readSlot, World.sload_sstore_self,
      World.sload_sstore_ne_key _ _ _ (by decide : (0#256 : Word) ≠ 104#256),
      World.sload_sstore_ne_key _ _ _ (by decide : (155#256 : Word) ≠ 104#256),
      World.sload_sstore_ne_key _ _ _ (by decide : (156#256 : Word) ≠ 104#256),
      World.sload_sstore_ne_key _ _ _ (by decide : (157#256 : Word) ≠ 104#256),
      toAddress_hi_and]
    rfl
  · rw [hw]
    exact BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl)))))))
      BNB.Spec.frameKeeps_refl'

theorem gonsW_toNat : gonsW.toNat = Variant.amplTotalGons := by
  unfold Variant.amplTotalGons QEDefi.Math.MAX; rfl

theorem toInt_eq_zero {d : Word} : d.toInt = 0 ↔ d = 0 := by
  constructor
  · intro h; exact BitVec.eq_of_toInt_eq (by rw [h]; rfl)
  · rintro rfl; rfl

/-- **`rebase(epoch, Δ)`**: by the monetary policy, the supply moves by the `int256` `Δ` as the
code computes it (`rebaseW`, `rebaseSupply_eq`), capped, and `gonsPerFragment` follows. -/
theorem op_rebase (Act : Finset Address) (m : Machine)
    (hs : Start AMPL.runtimeCode amplAbs M Act m) (hval : m.frame.msg.value = 0)
    (hd : Args m.frame.msg.data 0x7a43e23f
      [argWord m.frame.msg.data 0, argWord m.frame.msg.data 1]) :
    Halts m fun mf o =>
      OpMatches amplAbs M Act (.rebase m.frame.msg.caller (argWord m.frame.msg.data 1).toInt)
        m mf o ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)) := by
  set d := argWord m.frame.msg.data 1
  have hS := hs.sound
  have hpre := pre_eq hs hval
  have hL : Live m.world m.frame.msg.currentTarget := live_of_wf (by rw [← hpre]; exact hs.wf)
  refine halts_split' (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => rebase_high m _ d hs.fresh hd hs.size hval hG.2 hG.1)
    (rebase_low m _ d hs.fresh hd hs.size) ?_
  rintro mf o ⟨h1, h2, h3, h4⟩
  left
  simp only [OpMatches]
  rw [ampl_op_rebase, hpre]
  unfold rebaseOp
  rw [show (amplRead m.ctx.crypto Act m.world m.frame.msg.currentTarget).admin =
    (m.world.sload m.frame.msg.currentTarget 155#256).toAddress from rfl,
    show (amplRead m.ctx.crypto Act m.world m.frame.msg.currentTarget).supply =
    (m.world.sload m.frame.msg.currentTarget 156#256).toNat by simp [amplRead, hL, readSlot]]
  by_cases hown : m.frame.msg.caller = (m.world.sload m.frame.msg.currentTarget 155#256).toAddress
  swap
  · rw [ite_pos' hown]
    exact h1 hown
  rw [ite_neg' (not_not.2 hown)]
  by_cases hd0 : d = 0
  · rw [ite_pos' (toInt_eq_zero.2 hd0)]
    obtain ⟨ho, hw, ht, hc⟩ := h2 hown hd0
    refine ⟨ho, ?_, ?_, ht, hc⟩
    · show amplRead _ _ _ _ = _
      rw [hw]
    · rw [hw]
      exact BNB.Spec.frameKeeps_refl'
  rw [ite_neg' (fun h => hd0 (toInt_eq_zero.1 h)), rebaseSupply_eq]
  cases hW : rebaseW (m.world.sload m.frame.msg.currentTarget 156#256) d with
  | none => exact h3 hown hd0 hW
  | some S1 =>
    simp only [Option.map_some]
    obtain ⟨hz, hnz⟩ := h4 hown hd0 S1 hW
    rw [show (Variant.ampl : Variant Address).maxSupply = 2 ^ 128 - 1 from rfl]
    by_cases h0 : min S1.toNat (2 ^ 128 - 1) = 0
    · rw [ite_pos' h0]
      exact hz h0
    rw [ite_neg' h0]
    obtain ⟨ho, ⟨w1, X, S2, hw1, hS2, hmin, hw⟩, ht, hc⟩ := hnz h0
    have hL' : Live mf.world m.frame.msg.currentTarget := by
      unfold Live at hL ⊢
      rw [hw, World.sload_sstore_ne_key _ _ _ (by decide)]
      rcases hw1 with rfl | rfl
      · rw [World.sload_sstore_ne_key _ _ _ (by decide)]; exact hL
      · rw [World.sload_sstore_ne_key _ _ _ (by decide), World.sload_sstore_ne_key _ _ _ (by decide)]
        exact hL
    refine ⟨ho, ?_, ?_, ht, hc⟩
    · show amplRead _ _ _ _ = _
      have hsup : (mf.world.sload m.frame.msg.currentTarget 156#256).toNat =
          min S1.toNat (2 ^ 128 - 1) := by
        rw [hw, World.sload_sstore_ne_key _ _ _ (by decide), hS2, hmin]
      have hsc : (mf.world.sload m.frame.msg.currentTarget 157#256).toNat =
          Variant.amplTotalGons / min S1.toNat (2 ^ 128 - 1) := by
        rw [hw, World.sload_sstore_self, ← hmin, Word.div, BitVec.toNat_udiv, gonsW_toNat]
      have h155 : mf.world.sload m.frame.msg.currentTarget 155#256 =
          m.world.sload m.frame.msg.currentTarget 155#256 := by
        rw [hw, World.sload_sstore_ne_key _ _ _ (by decide)]
        rcases hw1 with rfl | rfl
        · rw [World.sload_sstore_ne_key _ _ _ (by decide)]
        · rw [World.sload_sstore_ne_key _ _ _ (by decide), World.sload_sstore_ne_key _ _ _ (by decide)]
      have h104 : mf.world.sload m.frame.msg.currentTarget 104#256 =
          m.world.sload m.frame.msg.currentTarget 104#256 := by
        rw [hw, World.sload_sstore_ne_key _ _ _ (by decide)]
        rcases hw1 with rfl | rfl
        · rw [World.sload_sstore_ne_key _ _ _ (by decide)]
        · rw [World.sload_sstore_ne_key _ _ _ (by decide), World.sload_sstore_ne_key _ _ _ (by decide)]
      have hrows : amplRead m.ctx.crypto Act mf.world m.frame.msg.currentTarget =
          { amplRead m.ctx.crypto Act m.world m.frame.msg.currentTarget with
            supply := if Live mf.world m.frame.msg.currentTarget then
              readSlot mf.world m.frame.msg.currentTarget 156#256 else 0
            scale := readSlot mf.world m.frame.msg.currentTarget 157#256
            admin := (mf.world.sload m.frame.msg.currentTarget 155#256).toAddress
            owner := (mf.world.sload m.frame.msg.currentTarget 104#256).toAddress } := by
        rw [hw, amplRead_sstore_fixed hS (by simp)]
        rcases hw1 with rfl | rfl
        · rw [amplRead_sstore_fixed hS (by simp)]
        · rw [amplRead_sstore_fixed hS (by simp), amplRead_sstore_fixed hS (by simp)]
      rw [hrows]
      simp only [readSlot, hsup, hsc, h155, h104, hL', ite_true]
      rfl
    · rw [hw]
      refine BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inl rfl))) ?_
      rcases hw1 with rfl | rfl
      · exact BNB.Spec.FrameKeeps.sstore' (.inr (.inl rfl)) BNB.Spec.frameKeeps_refl'
      · exact BNB.Spec.FrameKeeps.sstore' (.inr (.inl rfl))
          (BNB.Spec.FrameKeeps.sstore' (.inr (.inl rfl)) BNB.Spec.frameKeeps_refl')

theorem args_ww {data : ByteArray} {sel : Nat} (hsel : Abi.selectorOf data = sel)
    (hsz : ¬ data.size < 68) :
    Args data sel [argWord data 0, argWord data 1] := by
  refine ⟨hsel, by simp; omega, ?_⟩
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl

/-- **The other entry points**: `renounceOwnership`, `transferAll`, `setMonetaryPolicy`,
`transferOwnership`, `transferAllFrom`, `increaseAllowance`, `decreaseAllowance`, `rebase`. -/
theorem ops_spec : OpSpec AMPL.runtimeCode amplAbs M g₀ amplOps amplOpAddrs := by
  intro Act m e hs hops haddr
  unfold amplOps at hops
  by_cases hvs : m.frame.msg.value.toNat ≠ 0 ∨ m.frame.msg.data.size < 4
  · rw [ite_pos' hvs] at hops; cases hops
  rw [ite_neg' hvs] at hops
  have hval : m.frame.msg.value = 0 := by
    have : m.frame.msg.value.toNat = 0 := by simp only [not_or] at hvs; omega
    exact BitVec.eq_of_toNat_eq this
  have h4 : 4 ≤ m.frame.msg.data.size := by simp only [not_or] at hvs; omega
  by_cases hr : Abi.selectorOf m.frame.msg.data = 0x715018a6
  · rw [ite_pos' hr] at hops
    cases hops
    exact op_renounce Act m hs hval hr h4
  rw [ite_neg' hr] at hops
  by_cases hsz : m.frame.msg.data.size < 36
  · rw [ite_pos' hsz] at hops; cases hops
  rw [ite_neg' hsz] at hops
  by_cases hs1 : Abi.selectorOf m.frame.msg.data = 0xa3a7e7f3
  · rw [ite_pos' hs1] at hops
    cases ha : addrArg (argWord m.frame.msg.data 0) with
    | none => rw [ha] at hops; cases hops
    | some a =>
      rw [ha] at hops
      cases hops
      exact op_transferAll Act m hs a (haddr a (by simp [amplOpAddrs])) hval (args_a hs1 hsz ha)
  rw [ite_neg' hs1] at hops
  by_cases hs2 : Abi.selectorOf m.frame.msg.data = 0x8b5a6a08
  · rw [ite_pos' hs2] at hops
    cases ha : addrArg (argWord m.frame.msg.data 0) with
    | none => rw [ha] at hops; cases hops
    | some a =>
      rw [ha] at hops
      cases hops
      exact op_setMP Act m hs a hval (args_a hs2 hsz ha)
  rw [ite_neg' hs2] at hops
  by_cases hs3 : Abi.selectorOf m.frame.msg.data = 0xf2fde38b
  · rw [ite_pos' hs3] at hops
    cases ha : addrArg (argWord m.frame.msg.data 0) with
    | none => rw [ha] at hops; cases hops
    | some a =>
      rw [ha] at hops
      cases hops
      exact op_transferOwnership Act m hs a hval (args_a hs3 hsz ha)
  rw [ite_neg' hs3] at hops
  by_cases hsz2 : m.frame.msg.data.size < 68
  · rw [ite_pos' hsz2] at hops; cases hops
  rw [ite_neg' hsz2] at hops
  by_cases hs4 : Abi.selectorOf m.frame.msg.data = 0x84d4b410
  · rw [ite_pos' hs4] at hops
    cases ha : addrArg (argWord m.frame.msg.data 0) with
    | none => rw [ha] at hops; cases hops
    | some a =>
      cases hb : addrArg (argWord m.frame.msg.data 1) with
      | none => rw [ha, hb] at hops; cases hops
      | some b =>
        rw [ha, hb] at hops
        cases hops
        exact op_transferAllFrom Act m hs a b (haddr a (by simp [amplOpAddrs]))
          (haddr b (by simp [amplOpAddrs])) hval (args_aa hs4 hsz2 ha hb)
  rw [ite_neg' hs4] at hops
  by_cases hs5 : Abi.selectorOf m.frame.msg.data = 0x39509351
  · rw [ite_pos' hs5] at hops
    cases ha : addrArg (argWord m.frame.msg.data 0) with
    | none => rw [ha] at hops; cases hops
    | some a =>
      rw [ha] at hops
      cases hops
      exact op_inc Act m hs a (haddr a (by simp [amplOpAddrs])) hval (args_aw hs5 hsz2 ha)
  rw [ite_neg' hs5] at hops
  by_cases hs6 : Abi.selectorOf m.frame.msg.data = 0xa457c2d7
  · rw [ite_pos' hs6] at hops
    cases ha : addrArg (argWord m.frame.msg.data 0) with
    | none => rw [ha] at hops; cases hops
    | some a =>
      rw [ha] at hops
      cases hops
      exact op_dec Act m hs a (haddr a (by simp [amplOpAddrs])) hval (args_aw hs6 hsz2 ha)
  rw [ite_neg' hs6] at hops
  by_cases hs7 : Abi.selectorOf m.frame.msg.data = 0x7a43e23f
  · rw [ite_pos' hs7] at hops
    cases hops
    exact op_rebase Act m hs hval (args_ww hs7 hsz2)
  rw [ite_neg' hs7] at hops
  cases hops

end Verified.WeirdERC20.AMPL.Spec
