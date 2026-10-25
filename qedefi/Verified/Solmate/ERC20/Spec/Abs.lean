import QEDefi.ERC20.Spec.Storage
import QEDefi.ERC20.Spec.Instances.Solmate

/-!
# Solmate's `ERC20` storage as a model state

`solmateAbs`: the storage abstraction of Solmate's `ERC20` (`MockERC20`, the `SolmateAsset`
contract) for a set of actors `Act`, with the layout of
`contracts/artifacts/SolmateAsset/storageLayout.json`: `totalSupply` at slot 2, `balanceOf` at
3, `allowance` at 4, `nonces` at 5 (`name` and `symbol` at 0 and 1 are not model state). The
fields of `VState` that Solmate has no storage for are constants: no fee, unit scale, nothing
paused, blacklisted or frozen; `self` is the token and `ether` its balance.

`Sound crypto Act` is `ActorRows crypto Act [3, 5] [4] [2]`: the actors' rows of `balanceOf`,
`nonces` and `allowance` are pairwise distinct and none is the `totalSupply` slot. These are
the slots the token writes, so they are the hypotheses its writes need.
-/

namespace Verified.Solmate.ERC20.Spec
open EvmLean EvmLogic EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec

/-- The model state of the token at `token` in `w`, for the actors `Act`. -/
noncomputable def solmateRead (crypto : Crypto) (Act : Finset Address) (w : World)
    (token : Address) : VState Address where
  self := token
  bal := readMap crypto Act w token 3#256
  supply := readSlot w token 2#256
  allowance := readMap2 crypto Act w token 4#256
  scale := 1
  admin := 0
  paused := false
  blacklisted := fun _ => false
  feeBps := 0
  feeMax := 0
  ether := (w.balance token).toNat
  frozen := 0
  nonces := readMap crypto Act w token 5#256

/-- The slots `solmateRead` reads: `totalSupply` and the actors' rows. -/
def solmateFootprint (crypto : Crypto) (Act : Finset Address) (k : Word) : Prop :=
  k = 2#256 ∨ MapSlots crypto Act 3#256 k ∨ Map2Slots crypto Act 4#256 k ∨
    MapSlots crypto Act 5#256 k

/-- The hash hypotheses: the actors' rows are distinct and avoid the `totalSupply` slot. -/
def SolmateSound (crypto : Crypto) (Act : Finset Address) : Prop :=
  ActorRows crypto Act [3#256, 5#256] [4#256] [2#256]

theorem solmateRead_congr (crypto : Crypto) (Act : Finset Address) (w w' : World)
    (token : Address)
    (h : ∀ k, solmateFootprint crypto Act k → w'.sload token k = w.sload token k)
    (hb : w'.balance token = w.balance token) :
    solmateRead crypto Act w' token = solmateRead crypto Act w token := by
  unfold solmateRead
  rw [readMap_congr (fun k hk => h k (.inr (.inl hk))),
    readMap2_congr (fun k hk => h k (.inr (.inr (.inl hk)))),
    readMap_congr (fun k hk => h k (.inr (.inr (.inr hk)))),
    readSlot_congr (h _ (.inl rfl)), hb]

/-- **The storage abstraction of Solmate's `ERC20`.** -/
noncomputable def solmateAbs : TokenAbs (VState Address) where
  read := solmateRead
  footprint := solmateFootprint
  read_congr := solmateRead_congr
  Sound := SolmateSound

end Verified.Solmate.ERC20.Spec

/-! ## Reading after a write -/

namespace Verified.Solmate.ERC20.Spec
open EvmLean EvmLogic EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec

variable {crypto : Crypto} {Act : Finset Address} {w : World} {token : Address} {v : Word}

theorem if_pos' {p : Prop} [Decidable p] {α : Type} {a b : α} (h : p) : (if p then a else b) = a := by
  simp [h]

theorem if_neg' {p : Prop} [Decidable p] {α : Type} {a b : α} (h : ¬ p) : (if p then a else b) = b := by
  simp [h]

theorem sload_sstore_token (w : World) (token : Address) (k v k' : Word) :
    (w.sstore token k v).sload token k' = if k' = k then v else w.sload token k' := by
  rw [World.sload_sstore]; simp

theorem readMap_sstore_other {b k : Word}
    (hk : ∀ a ∈ Act, k ≠ mappingSlot crypto (Word.ofAddress a) b) :
    readMap crypto Act (w.sstore token k v) token b = readMap crypto Act w token b := by
  ext a
  by_cases ha : a ∈ Act
  · rw [readMap_of_mem ha, readMap_of_mem ha, World.sload_sstore_ne_key _ _ _ (hk a ha).symm]
  · rw [readMap_of_not_mem ha, readMap_of_not_mem ha]

theorem readMap2_sstore_other {b k : Word}
    (hk : ∀ o ∈ Act, ∀ sp ∈ Act, k ≠ mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) b) :
    readMap2 crypto Act (w.sstore token k v) token b = readMap2 crypto Act w token b := by
  funext o sp
  simp only [readMap2]
  split
  · rename_i h; rw [World.sload_sstore_ne_key _ _ _ (hk o h.1 sp h.2).symm]
  · rfl

theorem readMap_sstore_row {b : Word} (hb : b ∈ [3#256, 5#256]) (hS : SolmateSound crypto Act)
    {c : Address} (hc : c ∈ Act) :
    readMap crypto Act (w.sstore token (mappingSlot crypto (Word.ofAddress c) b) v) token b =
      (readMap crypto Act w token b).update c v.toNat := by
  ext a
  rw [Finsupp.update_apply]
  by_cases ha : a ∈ Act
  · rw [readMap_of_mem ha, sload_sstore_token]
    by_cases hac : a = c
    · subst hac; simp
    · have : mappingSlot crypto (Word.ofAddress a) b ≠ mappingSlot crypto (Word.ofAddress c) b :=
        fun e => hac (hS.inj1 b hb b hb a ha c hc e).1
      simp [this, hac, readMap_of_mem ha]
  · have hac : a ≠ c := fun e => ha (e ▸ hc)
    simp [readMap_of_not_mem ha, hac]

theorem readMap2_sstore_row (hS : SolmateSound crypto Act) {o sp : Address} (ho : o ∈ Act)
    (hsp : sp ∈ Act) :
    readMap2 crypto Act (w.sstore token
        (mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) 4#256) v) token 4#256 =
      Function.update (readMap2 crypto Act w token 4#256) o
        (Function.update (readMap2 crypto Act w token 4#256 o) sp v.toNat) := by
  funext o' sp'
  simp only [readMap2, Function.update_apply]
  by_cases h : o' ∈ Act ∧ sp' ∈ Act
  · rw [if_pos' h, sload_sstore_token]
    by_cases he : o' = o ∧ sp' = sp
    · obtain ⟨rfl, rfl⟩ := he; simp
    · have hne : mappingSlot2 crypto (Word.ofAddress o') (Word.ofAddress sp') 4#256 ≠
          mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) 4#256 := by
        intro e
        obtain ⟨h1, h2, -⟩ := hS.inj2 _ (by simp) _ (by simp) o' h.1 sp' h.2 o ho sp hsp e
        exact he ⟨h1, h2⟩
      rw [if_neg' hne]
      by_cases ho' : o' = o
      · subst ho'
        have hsp' : sp' ≠ sp := fun e => he ⟨rfl, e⟩
        simp [hsp', h, readMap2]
      · simp [ho', h, readMap2]
  · rw [if_neg' h]
    have he : ¬ (o' = o ∧ sp' = sp) := fun e => h ⟨e.1 ▸ ho, e.2 ▸ hsp⟩
    by_cases ho' : o' = o
    · subst ho'
      have hsp' : sp' ≠ sp := fun e => he ⟨rfl, e⟩
      have : ¬ (o' ∈ Act ∧ sp' ∈ Act) := h
      simp [hsp', this, readMap2]
    · simp [ho', h, readMap2]

theorem readSlot_sstore_other {k : Word} (hk : k ≠ 2#256) :
    readSlot (w.sstore token k v) token 2#256 = readSlot w token 2#256 := by
  simp only [readSlot, World.sload_sstore_ne_key _ _ _ (Ne.symm hk)]

/-- **A balance row written**: `balanceOf[c] = v` for an actor `c`. -/
theorem read_sstore_bal (hS : SolmateSound crypto Act) {c : Address} (hc : c ∈ Act) :
    solmateRead crypto Act (w.sstore token (mappingSlot crypto (Word.ofAddress c) 3#256) v)
        token =
      { solmateRead crypto Act w token with
        bal := (solmateRead crypto Act w token).bal.update c v.toNat } := by
  simp only [solmateRead, VState.mk.injEq, true_and, World.balance_sstore]
  refine ⟨readMap_sstore_row (by simp) hS hc, readSlot_sstore_other ?_, readMap2_sstore_other ?_,
    readMap_sstore_other ?_⟩
  · exact fun e => hS.fixed1 3#256 (by simp) c hc (by simp [e])
  · exact fun o ho sp hsp => hS.disj _ (by simp) _ (by simp) c hc o ho sp hsp
  · intro a ha e
    have := (hS.inj1 _ (by simp) _ (by simp) c hc a ha e).2
    exact absurd this (by decide)

/-- **A nonce row written**: `nonces[c] = v` for an actor `c`. -/
theorem read_sstore_nonce (hS : SolmateSound crypto Act) {c : Address} (hc : c ∈ Act) :
    solmateRead crypto Act (w.sstore token (mappingSlot crypto (Word.ofAddress c) 5#256) v)
        token =
      { solmateRead crypto Act w token with
        nonces := (solmateRead crypto Act w token).nonces.update c v.toNat } := by
  simp only [solmateRead, VState.mk.injEq, true_and, World.balance_sstore]
  refine ⟨readMap_sstore_other ?_, readSlot_sstore_other ?_, readMap2_sstore_other ?_,
    readMap_sstore_row (by simp) hS hc⟩
  · intro a ha e
    have := (hS.inj1 _ (by simp) _ (by simp) c hc a ha e).2
    exact absurd this (by decide)
  · exact fun e => hS.fixed1 5#256 (by simp) c hc (by simp [e])
  · exact fun o ho sp hsp => hS.disj _ (by simp) _ (by simp) c hc o ho sp hsp

/-- **An allowance row written**: `allowance[o][sp] = v` for actors `o`, `sp`. -/
theorem read_sstore_allowance (hS : SolmateSound crypto Act) {o sp : Address} (ho : o ∈ Act)
    (hsp : sp ∈ Act) :
    solmateRead crypto Act (w.sstore token
        (mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) 4#256) v) token =
      (solmateRead crypto Act w token).setAllowance o sp v.toNat := by
  simp only [solmateRead, VState.setAllowance, VState.mk.injEq, true_and, World.balance_sstore]
  refine ⟨readMap_sstore_other ?_, readSlot_sstore_other ?_, readMap2_sstore_row hS ho hsp,
    readMap_sstore_other ?_⟩
  · exact fun a ha e => hS.disj _ (by simp) _ (by simp) a ha o ho sp hsp e.symm
  · exact fun e => hS.fixed2 4#256 (by simp) o ho sp hsp (by simp [e])
  · exact fun a ha e => hS.disj _ (by simp) _ (by simp) a ha o ho sp hsp e.symm

/-- **The supply slot written.** -/
theorem read_sstore_supply (hS : SolmateSound crypto Act) :
    solmateRead crypto Act (w.sstore token 2#256 v) token =
      { solmateRead crypto Act w token with supply := v.toNat } := by
  simp only [solmateRead, VState.mk.injEq, true_and, World.balance_sstore]
  refine ⟨readMap_sstore_other ?_, by simp [readSlot], readMap2_sstore_other ?_,
    readMap_sstore_other ?_⟩
  · exact fun a ha e => hS.fixed1 3#256 (by simp) a ha (by simp [← e])
  · exact fun o ho sp hsp e => hS.fixed2 4#256 (by simp) o ho sp hsp (by simp [← e])
  · exact fun a ha e => hS.fixed1 5#256 (by simp) a ha (by simp [← e])

/-! ## What a write keeps -/

theorem frameKeeps_refl (crypto : Crypto) (Act : Finset Address) (token : Address) (w : World) :
    FrameKeeps solmateAbs crypto Act token w w :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- A write into the footprint keeps what `FrameKeeps` keeps. -/
theorem FrameKeeps.sstore {w w₁ : World} {k : Word}
    (h : FrameKeeps solmateAbs crypto Act token w w₁) (hk : solmateFootprint crypto Act k) :
    FrameKeeps solmateAbs crypto Act token w (w₁.sstore token k v) where
  own k' hk' := by
    have hne : k' ≠ k := fun e => hk' (e ▸ hk)
    rw [World.sload_sstore_ne_key _ _ _ hne]; exact h.own k' hk'
  code := by rw [World.code_sstore]; exact h.code
  nonce := by
    simp only [World.sstore, World.account_modify_self]; exact h.nonce
  balance := by rw [World.balance_sstore]; exact h.balance
  others b hb := by
    simp only [World.sstore, World.account_modify_ne _ _ hb]; exact h.others b hb

theorem footprint_bal {c : Address} (hc : c ∈ Act) :
    solmateFootprint crypto Act (mappingSlot crypto (Word.ofAddress c) 3#256) :=
  .inr (.inl ⟨c, hc, rfl⟩)

theorem footprint_nonce {c : Address} (hc : c ∈ Act) :
    solmateFootprint crypto Act (mappingSlot crypto (Word.ofAddress c) 5#256) :=
  .inr (.inr (.inr ⟨c, hc, rfl⟩))

theorem footprint_allowance {o sp : Address} (ho : o ∈ Act) (hsp : sp ∈ Act) :
    solmateFootprint crypto Act (mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) 4#256) :=
  .inr (.inr (.inl ⟨o, ho, sp, hsp, rfl⟩))

theorem footprint_supply : solmateFootprint crypto Act 2#256 := .inl rfl

end Verified.Solmate.ERC20.Spec
