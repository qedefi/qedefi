import QEDefi.ERC20.Spec.Storage
import EvmLogic.State
import Verified.Solady.Spec.Rows

/-!
# Writes to Solidity mapping rows, read for the actors

What one `SSTORE` to an actor's row of a nested mapping does to `readMap`, `readMap2` and
`readSlot`, under `ActorRows` (the actors' rows are pairwise distinct and avoid the fixed
slots). Used by the BNB, STA and AMPL obligations.
-/

namespace Verified.WeirdERC20.BNB.Spec
open EvmLean EvmLogic EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec
open Verified.Solady.Spec (ite_pos' ite_neg')

variable {crypto : Crypto} {Act : Finset Address} {b1 b2 fixed : List Word} {w : World}
  {t : Address} {o sp : Address} {x : Word}

theorem readMap_sstore_map2 (hS : ActorRows crypto Act b1 b2 fixed) {base base2 : Word}
    (hb : base ∈ b1) (hb2 : base2 ∈ b2) (ho : o ∈ Act) (hs : sp ∈ Act) :
    readMap crypto Act
        (w.sstore t (mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) base2) x) t base =
      readMap crypto Act w t base := by
  ext a
  by_cases ha : a ∈ Act
  · rw [readMap_of_mem ha, readMap_of_mem ha,
      World.sload_sstore_ne_key _ _ _ (hS.disj base hb base2 hb2 a ha o ho sp hs)]
  · rw [readMap_of_not_mem ha, readMap_of_not_mem ha]

theorem readSlot_sstore_map2 (hS : ActorRows crypto Act b1 b2 fixed) {k base2 : Word}
    (hk : k ∈ fixed) (hb2 : base2 ∈ b2) (ho : o ∈ Act) (hs : sp ∈ Act) :
    readSlot (w.sstore t (mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) base2) x) t k =
      readSlot w t k := by
  simp only [readSlot]
  rw [World.sload_sstore_ne_key _ _ _ (fun e => hS.fixed2 base2 hb2 o ho sp hs (by rw [← e]; exact hk))]

theorem sload_sstore_map2 (hS : ActorRows crypto Act b1 b2 fixed) {k base2 : Word}
    (hk : k ∈ fixed) (hb2 : base2 ∈ b2) (ho : o ∈ Act) (hs : sp ∈ Act) :
    (w.sstore t (mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) base2) x).sload t k =
      w.sload t k :=
  World.sload_sstore_ne_key _ _ _ (fun e => hS.fixed2 base2 hb2 o ho sp hs (by rw [← e]; exact hk))

/-- **Writing a nested row of two actors** sets that entry of `readMap2`. -/
theorem readMap2_sstore (hS : ActorRows crypto Act b1 b2 fixed) {base : Word} (hb : base ∈ b2)
    (ho : o ∈ Act) (hs : sp ∈ Act) :
    readMap2 crypto Act
        (w.sstore t (mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) base) x) t base =
      Function.update (readMap2 crypto Act w t base) o
        (Function.update (readMap2 crypto Act w t base o) sp x.toNat) := by
  funext o' sp'
  simp only [Function.update_apply]
  by_cases he : o' = o ∧ sp' = sp
  · obtain ⟨rfl, rfl⟩ := he
    simp [readMap2, ho, hs]
  · have hrhs : (if o' = o then Function.update (readMap2 crypto Act w t base o) sp x.toNat
        else readMap2 crypto Act w t base o') sp' = readMap2 crypto Act w t base o' sp' := by
      by_cases h1 : o' = o
      · subst h1; simp [show sp' ≠ sp from fun e => he ⟨rfl, e⟩]
      · simp [h1]
    rw [hrhs]
    simp only [readMap2]
    split
    · rename_i hm
      have hne : mappingSlot2 crypto (Word.ofAddress o') (Word.ofAddress sp') base ≠
          mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) base := fun e => by
        obtain ⟨h1, h2, -⟩ := hS.inj2 base hb base hb o' hm.1 sp' hm.2 o ho sp hs e
        exact he ⟨h1, h2⟩
      rw [World.sload_sstore_ne_key _ _ _ hne]
    · rfl

/-- **Writing a one-level row of an actor** sets that entry of `readMap`. -/
theorem readMap_sstore (hS : ActorRows crypto Act b1 b2 fixed) {base : Word} (hb : base ∈ b1)
    {a : Address} (ha : a ∈ Act) :
    readMap crypto Act (w.sstore t (mappingSlot crypto (Word.ofAddress a) base) x) t base =
      (readMap crypto Act w t base).update a x.toNat := by
  ext c
  rw [Finsupp.update_apply]
  by_cases hca : c = a
  · subst hca; rw [readMap_of_mem ha, ite_pos' rfl, World.sload_sstore_self]
  · rw [ite_neg' hca]
    by_cases hc : c ∈ Act
    · rw [readMap_of_mem hc, readMap_of_mem hc, World.sload_sstore_ne_key _ _ _ (fun e => hca
        (hS.inj1 base hb base hb c hc a ha e).1)]
    · rw [readMap_of_not_mem hc, readMap_of_not_mem hc]

/-- A write to a one-level row leaves the other one-level mappings. -/
theorem readMap_sstore_other (hS : ActorRows crypto Act b1 b2 fixed) {base base' : Word}
    (hb : base ∈ b1) (hb' : base' ∈ b1) (hne : base' ≠ base) {a : Address} (ha : a ∈ Act) :
    readMap crypto Act (w.sstore t (mappingSlot crypto (Word.ofAddress a) base) x) t base' =
      readMap crypto Act w t base' := by
  ext c
  by_cases hc : c ∈ Act
  · rw [readMap_of_mem hc, readMap_of_mem hc, World.sload_sstore_ne_key _ _ _ (fun e => hne
      (hS.inj1 base' hb' base hb c hc a ha e).2)]
  · rw [readMap_of_not_mem hc, readMap_of_not_mem hc]

/-- A write to a one-level row leaves the nested mappings. -/
theorem readMap2_sstore_map (hS : ActorRows crypto Act b1 b2 fixed) {base base2 : Word}
    (hb : base ∈ b1) (hb2 : base2 ∈ b2) {a : Address} (ha : a ∈ Act) :
    readMap2 crypto Act (w.sstore t (mappingSlot crypto (Word.ofAddress a) base) x) t base2 =
      readMap2 crypto Act w t base2 := by
  funext o' sp'
  simp only [readMap2]
  split
  · rename_i hm
    rw [World.sload_sstore_ne_key _ _ _ (fun e => hS.disj base hb base2 hb2 a ha o' hm.1 sp' hm.2
      e.symm)]
  · rfl

/-- A write to a one-level row leaves the fixed slots. -/
theorem sload_sstore_map (hS : ActorRows crypto Act b1 b2 fixed) {k base : Word}
    (hk : k ∈ fixed) (hb : base ∈ b1) {a : Address} (ha : a ∈ Act) :
    (w.sstore t (mappingSlot crypto (Word.ofAddress a) base) x).sload t k = w.sload t k :=
  World.sload_sstore_ne_key _ _ _ (fun e => hS.fixed1 base hb a ha (by rw [← e]; exact hk))

/-- A write to a fixed slot leaves the one-level rows. -/
theorem readMap_sstore_fixed (hS : ActorRows crypto Act b1 b2 fixed) {k base : Word}
    (hk : k ∈ fixed) (hb : base ∈ b1) :
    readMap crypto Act (w.sstore t k x) t base = readMap crypto Act w t base := by
  ext c
  by_cases hc : c ∈ Act
  · rw [readMap_of_mem hc, readMap_of_mem hc,
      World.sload_sstore_ne_key _ _ _ (fun e => hS.fixed1 base hb c hc (by rw [e]; exact hk))]
  · rw [readMap_of_not_mem hc, readMap_of_not_mem hc]

/-- A write to a fixed slot leaves the nested rows. -/
theorem readMap2_sstore_fixed (hS : ActorRows crypto Act b1 b2 fixed) {k base : Word}
    (hk : k ∈ fixed) (hb : base ∈ b2) :
    readMap2 crypto Act (w.sstore t k x) t base = readMap2 crypto Act w t base := by
  funext o' sp'
  simp only [readMap2]
  split
  · rename_i hm
    rw [World.sload_sstore_ne_key _ _ _ (fun e => hS.fixed2 base hb o' hm.1 sp' hm.2 (by rw [e]; exact hk))]
  · rfl

theorem frameKeeps_refl' {σ : Type} {abs : TokenAbs σ} : FrameKeeps abs crypto Act t w w :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- A write to a slot of the footprint keeps `FrameKeeps`, for any abstraction. -/
theorem FrameKeeps.sstore' {σ : Type} {abs : TokenAbs σ} {w' : World} {k v : Word}
    (hk : abs.footprint crypto Act k) (h : FrameKeeps abs crypto Act t w w') :
    FrameKeeps abs crypto Act t w (w'.sstore t k v) where
  own k' hk' := by
    have hne : k' ≠ k := fun e => hk' (by rw [e]; exact hk)
    rw [World.sload_sstore_ne_key _ _ _ hne]
    exact h.own k' hk'
  code := by rw [World.code_sstore]; exact h.code
  nonce := by
    simp only [World.sstore, World.account_modify_self]; exact h.nonce
  balance := by rw [World.balance_sstore]; exact h.balance
  others b hb := by
    simp only [World.sstore, World.account_modify_ne _ _ hb]; exact h.others b hb

end Verified.WeirdERC20.BNB.Spec
