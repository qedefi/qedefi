import Verified.WETH9.Spec.Abs
import EvmLogic.State

/-!
# Writes to WETH9's storage, read through `weth9Abs`

Under `ActorRows crypto Act [3] [4] []` (`weth9Abs.Sound`): writing an actor's `balanceOf` row
changes only that actor's balance (`readMap_sstore_bal`) and no allowance
(`readMap2_sstore_bal`); writing the `allowance` row of a pair of actors changes only that
allowance (`readMap2_sstore_allow`) and no balance (`readMap_sstore_allow`). A write to a
footprint slot keeps everything `FrameKeeps` asks (`frameKeeps_sstore`), and `FrameKeeps`
composes (`FrameKeeps.trans`).
-/

namespace Verified.WETH9.Spec
open EvmLean EvmLogic EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec

variable {crypto : Crypto} {Act : Finset Address} {w : World} {token : Address}

theorem account_sstore_ne {w : World} {a b : Address} (k v : Word) (h : b ≠ a) :
    (w.sstore a k v).account b = w.account b :=
  World.account_modify_ne _ _ h

theorem nonce_sstore (w : World) (a : Address) (k v : Word) :
    ((w.sstore a k v).account a).nonce = (w.account a).nonce := by
  simp [World.sstore, World.account_modify_self]

section
variable (hR : ActorRows crypto Act [3] [4] [])
include hR

theorem balSlot_inj {a b : Address} (ha : a ∈ Act) (hb : b ∈ Act)
    (h : mappingSlot crypto (Word.ofAddress a) 3 = mappingSlot crypto (Word.ofAddress b) 3) : a = b :=
  (hR.inj1 3 (by simp) 3 (by simp) a ha b hb h).1

theorem allowSlot_inj {o sp o' sp' : Address} (ho : o ∈ Act) (hsp : sp ∈ Act) (ho' : o' ∈ Act)
    (hsp' : sp' ∈ Act) (h : mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) 4 = mappingSlot2 crypto (Word.ofAddress o') (Word.ofAddress sp') 4) : o = o' ∧ sp = sp' :=
  let h' := hR.inj2 4 (by simp) 4 (by simp) o ho sp hsp o' ho' sp' hsp' h
  ⟨h'.1, h'.2.1⟩

theorem balSlot_ne_allowSlot {a o sp : Address} (ha : a ∈ Act) (ho : o ∈ Act) (hsp : sp ∈ Act) :
    mappingSlot crypto (Word.ofAddress a) 3 ≠ mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) 4 :=
  hR.disj 3 (by simp) 4 (by simp) a ha o ho sp hsp

/-- **Writing `balanceOf[b]`** changes the actors' balances only at `b`. -/
theorem readMap_sstore_bal {b : Address} (hb : b ∈ Act) (x : Word) (a : Address) :
    readMap crypto Act (w.sstore token (mappingSlot crypto (Word.ofAddress b) 3) x) token 3 a =
      if a = b then x.toNat else readMap crypto Act w token 3 a := by
  by_cases ha : a ∈ Act
  · rw [readMap_of_mem ha, readMap_of_mem ha]
    by_cases hab : a = b
    · subst hab; rw [World.sload_sstore_self]; simp
    · have : mappingSlot crypto (Word.ofAddress a) 3 ≠ mappingSlot crypto (Word.ofAddress b) 3 :=
        fun h => hab (balSlot_inj hR ha hb h)
      rw [World.sload_sstore_ne_key _ _ _ this]; simp [hab]
  · have hab : a ≠ b := fun h => ha (h ▸ hb)
    simp [readMap_of_not_mem ha, hab]

/-- Writing `balanceOf[b]` changes no allowance of the actors. -/
theorem readMap2_sstore_bal {b : Address} (hb : b ∈ Act) (x : Word) :
    readMap2 crypto Act (w.sstore token (mappingSlot crypto (Word.ofAddress b) 3) x) token 4 =
      readMap2 crypto Act w token 4 := by
  funext o sp
  simp only [readMap2]
  split
  · rename_i h
    rw [World.sload_sstore_ne_key _ _ _ (Ne.symm (balSlot_ne_allowSlot hR hb h.1 h.2))]
  · rfl

/-- **Writing `allowance[o][sp]`** changes the actors' allowances only at `(o, sp)`. -/
theorem readMap2_sstore_allow {o sp : Address} (ho : o ∈ Act) (hsp : sp ∈ Act) (x : Word)
    (p q : Address) :
    readMap2 crypto Act (w.sstore token (mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) 4) x) token 4 p q =
      if p = o ∧ q = sp then x.toNat else readMap2 crypto Act w token 4 p q := by
  simp only [readMap2]
  by_cases hpq : p ∈ Act ∧ q ∈ Act
  · simp only [hpq, and_self, ↓reduceIte]
    by_cases he : p = o ∧ q = sp
    · obtain ⟨rfl, rfl⟩ := he; rw [World.sload_sstore_self]; simp
    · have : mappingSlot2 crypto (Word.ofAddress p) (Word.ofAddress q) 4 ≠
          mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) 4 :=
        fun h => he (allowSlot_inj hR hpq.1 hpq.2 ho hsp h)
      rw [World.sload_sstore_ne_key _ _ _ this]; simp [he]
  · have he : ¬ (p = o ∧ q = sp) := fun h => hpq ⟨h.1 ▸ ho, h.2 ▸ hsp⟩
    simp [hpq, he]

/-- Writing `allowance[o][sp]` changes no balance of the actors. -/
theorem readMap_sstore_allow {o sp : Address} (ho : o ∈ Act) (hsp : sp ∈ Act) (x : Word) :
    readMap crypto Act (w.sstore token (mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) 4) x) token 3 =
      readMap crypto Act w token 3 := by
  ext a
  by_cases ha : a ∈ Act
  · rw [readMap_of_mem ha, readMap_of_mem ha,
      World.sload_sstore_ne_key _ _ _ (balSlot_ne_allowSlot hR ha ho hsp)]
  · simp [readMap_of_not_mem ha]

end

/-! ## What a write keeps -/

theorem FrameKeeps.refl {σ : Type} (abs : TokenAbs σ) (crypto : Crypto) (Act : Finset Address)
    (token : Address) (w : World) : FrameKeeps abs crypto Act token w w :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem FrameKeeps.trans {σ : Type} {abs : TokenAbs σ} {crypto : Crypto} {Act : Finset Address}
    {token : Address} {w₁ w₂ w₃ : World} (h₁ : FrameKeeps abs crypto Act token w₁ w₂)
    (h₂ : FrameKeeps abs crypto Act token w₂ w₃) : FrameKeeps abs crypto Act token w₁ w₃ :=
  ⟨fun k hk => (h₂.own k hk).trans (h₁.own k hk), h₂.code.trans h₁.code,
    h₂.nonce.trans h₁.nonce, h₂.balance.trans h₁.balance,
    fun b hb => (h₂.others b hb).trans (h₁.others b hb)⟩

/-- **A write to a footprint slot** keeps what `FrameKeeps` asks. -/
theorem frameKeeps_sstore {k : Word} (hk : weth9Footprint crypto Act k) (x : Word) :
    FrameKeeps weth9Abs crypto Act token w (w.sstore token k x) where
  own _ hk' := World.sload_sstore_ne_key _ _ _ (fun h => hk' (h ▸ hk))
  code := World.code_sstore _ _ _ _ _
  nonce := nonce_sstore _ _ _ _
  balance := World.balance_sstore _ _ _ _ _
  others _ hb := account_sstore_ne _ _ hb

theorem footprint_bal {a : Address} (ha : a ∈ Act) : weth9Footprint crypto Act (mappingSlot crypto (Word.ofAddress a) 3) :=
  .inl ⟨a, ha, rfl⟩

theorem footprint_allow {o sp : Address} (ho : o ∈ Act) (hsp : sp ∈ Act) :
    weth9Footprint crypto Act (mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) 4) :=
  .inr ⟨o, ho, sp, hsp, rfl⟩

end Verified.WETH9.Spec
