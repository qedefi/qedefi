import Verified.Solady.Spec.Abs
import EvmLogic.State

/-!
# Solady `ERC20` under the spec: writes through the abstraction

What one `SSTORE` to an actor's row (or the supply slot) does to `read`, under
`SoladySound`, and that such writes keep `FrameKeeps`.
-/

namespace Verified.Solady.Spec
open EvmLean EvmLogic QEDefi.ERC20 QEDefi.ERC20.Spec

variable {crypto : Crypto} {Act : Finset Address} {token : Address} {w w' : World}

theorem frameKeeps_refl : FrameKeeps soladyAbs crypto Act token w w :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- A write to a slot of the footprint keeps `FrameKeeps`. -/
theorem FrameKeeps.sstore {k v : Word} (hk : Footprint crypto Act k)
    (h : FrameKeeps soladyAbs crypto Act token w w') :
    FrameKeeps soladyAbs crypto Act token w (w'.sstore token k v) where
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

theorem bal_mem (a : Address) (ha : a ∈ Act) : Footprint crypto Act (balSlot crypto a) :=
  .inr (.inl ⟨a, ha, rfl⟩)

theorem allow_mem (o sp : Address) (ho : o ∈ Act) (hs : sp ∈ Act) :
    Footprint crypto Act (allowSlot crypto o sp) :=
  .inr (.inr (.inl ⟨o, ho, sp, hs, rfl⟩))

theorem supply_mem : Footprint crypto Act supplySlot := .inl rfl

/-- **Writing an allowance row** of two actors sets that allowance. -/
theorem read_sstore_allow (hS : SoladySound crypto Act) {o sp : Address} (ho : o ∈ Act)
    (hs : sp ∈ Act) (x : Word) :
    read crypto Act (w.sstore token (allowSlot crypto o sp) x) token =
      (read crypto Act w token).setAllowance o sp x.toNat := by
  have hb : balances crypto Act (w.sstore token (allowSlot crypto o sp) x) token =
      balances crypto Act w token := by
    ext a; simp only [balances, Finsupp.onFinset_apply]
    split
    · rename_i ha
      rw [World.sload_sstore_ne_key _ _ _ (hS.allow_bal o ho sp hs a ha).symm]
    · rfl
  have hn : nonceMap crypto Act (w.sstore token (allowSlot crypto o sp) x) token =
      nonceMap crypto Act w token := by
    ext a; simp only [nonceMap, Finsupp.onFinset_apply]
    split
    · rename_i ha
      rw [World.sload_sstore_ne_key _ _ _ (hS.allow_nonce o ho sp hs a ha).symm]
    · rfl
  have hsup : readSlot (w.sstore token (allowSlot crypto o sp) x) token supplySlot =
      readSlot w token supplySlot := by
    simp only [readSlot]
    rw [World.sload_sstore_ne_key _ _ _ (hS.allow_supply o ho sp hs).symm]
  have ha : allowances crypto Act (w.sstore token (allowSlot crypto o sp) x) token =
      Function.update (allowances crypto Act w token) o
        (Function.update (allowances crypto Act w token o) sp x.toNat) := by
    funext o' sp'
    simp only [Function.update_apply]
    by_cases he : o' = o ∧ sp' = sp
    · obtain ⟨rfl, rfl⟩ := he
      simp [allowances, ho, hs]
    · have hrhs : (if o' = o then Function.update (allowances crypto Act w token o) sp x.toNat
          else allowances crypto Act w token o') sp' = allowances crypto Act w token o' sp' := by
        by_cases h1 : o' = o
        · subst h1; simp [show sp' ≠ sp from fun e => he ⟨rfl, e⟩]
        · simp [h1]
      rw [hrhs]
      simp only [allowances]
      split
      · rename_i hm
        have hne : allowSlot crypto o' sp' ≠ allowSlot crypto o sp := fun e =>
          he (hS.allow_inj o' hm.1 sp' hm.2 o ho sp hs e)
        rw [World.sload_sstore_ne_key _ _ _ hne]
      · rfl
  simp only [read, hb, hn, hsup, ha, World.balance_sstore, VState.setAllowance]

/-- **Writing a balance row** of an actor sets that balance. -/
theorem read_sstore_bal (hS : SoladySound crypto Act) {a : Address} (ha : a ∈ Act) (x : Word) :
    read crypto Act (w.sstore token (balSlot crypto a) x) token =
      { read crypto Act w token with
        bal := (balances crypto Act w token).update a x.toNat } := by
  have hb : balances crypto Act (w.sstore token (balSlot crypto a) x) token =
      (balances crypto Act w token).update a x.toNat := by
    ext b
    simp only [balances, Finsupp.onFinset_apply, Finsupp.update_apply]
    by_cases hba : b = a
    · subst hba; simp [ha]
    · simp only [hba, ↓reduceIte]
      split
      · rename_i hbA
        rw [World.sload_sstore_ne_key _ _ _ (fun e => hba (hS.bal_inj b hbA a ha e))]
      · rfl
  have hn : nonceMap crypto Act (w.sstore token (balSlot crypto a) x) token =
      nonceMap crypto Act w token := by
    ext b; simp only [nonceMap, Finsupp.onFinset_apply]
    split
    · rename_i hb
      rw [World.sload_sstore_ne_key _ _ _ (hS.bal_nonce a ha b hb).symm]
    · rfl
  have hsup : readSlot (w.sstore token (balSlot crypto a) x) token supplySlot =
      readSlot w token supplySlot := by
    simp only [readSlot]
    rw [World.sload_sstore_ne_key _ _ _ (hS.bal_supply a ha).symm]
  have hal : allowances crypto Act (w.sstore token (balSlot crypto a) x) token =
      allowances crypto Act w token := by
    funext o sp; simp only [allowances]
    split
    · rename_i hm
      rw [World.sload_sstore_ne_key _ _ _ (hS.allow_bal o hm.1 sp hm.2 a ha)]
    · rfl
  simp only [read, hb, hn, hsup, hal, World.balance_sstore]

/-- **Writing the supply slot** sets the supply. -/
theorem read_sstore_supply (hS : SoladySound crypto Act) (x : Word) :
    read crypto Act (w.sstore token supplySlot x) token =
      { read crypto Act w token with supply := x.toNat } := by
  have hb : balances crypto Act (w.sstore token supplySlot x) token =
      balances crypto Act w token := by
    ext a; simp only [balances, Finsupp.onFinset_apply]
    split
    · rename_i ha; rw [World.sload_sstore_ne_key _ _ _ (hS.bal_supply a ha)]
    · rfl
  have hn : nonceMap crypto Act (w.sstore token supplySlot x) token =
      nonceMap crypto Act w token := by
    ext a; simp only [nonceMap, Finsupp.onFinset_apply]
    split
    · rename_i ha; rw [World.sload_sstore_ne_key _ _ _ (hS.nonce_supply a ha)]
    · rfl
  have hal : allowances crypto Act (w.sstore token supplySlot x) token =
      allowances crypto Act w token := by
    funext o sp; simp only [allowances]
    split
    · rename_i hm; rw [World.sload_sstore_ne_key _ _ _ (hS.allow_supply o hm.1 sp hm.2)]
    · rfl
  simp only [read, hb, hn, hal, World.balance_sstore, readSlot, World.sload_sstore_self]

end Verified.Solady.Spec
