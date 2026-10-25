import Verified.WeirdERC20.USDT.Spec.Basic

/-!
# USDT: the abstraction after the code's writes

`FrameKeeps` for writes inside the footprint (`frameKeeps_sstore`), and the abstraction after
writing one of the actors' rows (under `ActorRows`): an `allowed` row is `setAllowance`
(`read_sstore_allow`), a `balances` row updates `bal` (`read_sstore_bal`). Fixed slots and the
other rows keep their values, so the scope (`Live`) is unchanged.
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open Verified.WeirdERC20.USDT.Contracts
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.Math

/-! ## What a write may change -/

theorem frameKeeps_refl (crypto : Crypto) (Act : Finset Address) (token : Address) (w : World) :
    FrameKeeps usdtAbs crypto Act token w w :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem nonce_sstore (w : World) (a : Address) (k v : Word) (b : Address) :
    ((w.sstore a k v).account b).nonce = (w.account b).nonce := by
  by_cases h : b = a
  · subst h; simp [World.sstore, World.account_modify_self]
  · simp only [World.sstore, World.account_modify_ne _ _ h]

/-- A write of the token inside the footprint keeps `FrameKeeps`. -/
theorem FrameKeeps.sstore {crypto : Crypto} {Act : Finset Address} {token : Address}
    {w w' : World} (h : FrameKeeps usdtAbs crypto Act token w w') {k : Word}
    (hk : footprint crypto Act k) (x : Word) :
    FrameKeeps usdtAbs crypto Act token w (w'.sstore token k x) where
  own k' hk' := by
    rw [World.sload_sstore_ne_key _ _ _ (fun e => hk' (by rw [e]; exact hk))]
    exact h.own k' hk'
  code := by rw [World.code_sstore]; exact h.code
  nonce := by rw [nonce_sstore]; exact h.nonce
  balance := by rw [World.balance_sstore]; exact h.balance
  others b hb := by
    simp only [World.sstore, World.account_modify_ne _ _ hb]
    exact h.others b hb

/-! ## Reading after a write -/

/-- The fixed slots, as a set of words. -/
theorem mem_fixedSlots {k : Word} :
    k ∈ fixedSlots ↔ k = 0 ∨ k = 1 ∨ k = 3 ∨ k = 4 ∨ k = 9 ∨ k = 10 := by
  simp [fixedSlots, supplySlot, bpsSlot, maxFeeSlot, decimalsSlot]

/-- `readState` after writes that keep every fixed slot, the ether and the rows of the three
mappings read as stated. -/
theorem readState_eq {crypto : Crypto} {Act : Finset Address} {w w' : World} {token : Address}
    (hf : ∀ k ∈ fixedSlots, w'.sload token k = w.sload token k)
    (hb : w'.balance token = w.balance token)
    (hblack : ∀ a ∈ Act, w'.sload token (mappingSlot crypto (Word.ofAddress a) blackSlot) =
      w.sload token (mappingSlot crypto (Word.ofAddress a) blackSlot)) :
    readState crypto Act w' token =
      { readState crypto Act w token with
        bal := readMap crypto Act w' token balancesSlot
        allowance := readMap2 crypto Act w' token allowedSlot } := by
  have h0 := hf 0 (by simp [fixedSlots])
  have hbl : blacklistedOf crypto Act w' token = blacklistedOf crypto Act w token := by
    funext a
    simp only [blacklistedOf]
    by_cases ha : a ∈ Act
    · rw [hblack a ha]
    · simp [ha]
  simp only [readState, ownerOf, pausedOf, h0, hbl, hb,
    readSlot_congr (hf supplySlot (by simp [fixedSlots])),
    readSlot_congr (hf bpsSlot (by simp [fixedSlots])),
    readSlot_congr (hf maxFeeSlot (by simp [fixedSlots]))]

theorem read_eq_of_live {crypto : Crypto} {Act : Finset Address} {w : World} {token : Address}
    (h : Live Act w token) : read crypto Act w token = readState crypto Act w token := by
  simp [read, h]

/-- **After writing `allowed[o][sp] := x`** (actors), the abstraction is `setAllowance`. -/
theorem read_sstore_allow {crypto : Crypto} {Act : Finset Address} {w : World} {token : Address}
    (hs : usdtAbs.Sound crypto Act) {o sp : Address} (ho : o ∈ Act) (hsp : sp ∈ Act)
    (hl : Live Act w token) (x : Word) :
    Live Act (w.sstore token (mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp)
        allowedSlot) x) token ∧
    read crypto Act (w.sstore token (mappingSlot2 crypto (Word.ofAddress o)
        (Word.ofAddress sp) allowedSlot) x) token =
      (read crypto Act w token).setAllowance o sp x.toNat := by
  have hs' : ActorRows crypto Act [balancesSlot, blackSlot] [allowedSlot] fixedSlots := hs
  have hfix : ∀ k ∈ fixedSlots, (w.sstore token (mappingSlot2 crypto (Word.ofAddress o)
      (Word.ofAddress sp) allowedSlot) x).sload token k = w.sload token k :=
    fun k hk => World.sload_sstore_ne_key _ _ _ (fun e => hs'.fixed2 allowedSlot (by simp) o ho sp
      hsp (by rw [← e]; exact hk))
  have hl' := (live_congr (Act := Act) hfix).2 hl
  refine ⟨hl', ?_⟩
  rw [read_eq_of_live hl', read_eq_of_live hl, readState_eq hfix (World.balance_sstore _ _ _ _ _)
    (fun a ha => World.sload_sstore_ne_key _ _ _ (hs'.disj blackSlot (by simp) allowedSlot
      (by simp) a ha o ho sp hsp))]
  have hbal : readMap crypto Act (w.sstore token (mappingSlot2 crypto (Word.ofAddress o)
      (Word.ofAddress sp) allowedSlot) x) token balancesSlot =
      readMap crypto Act w token balancesSlot :=
    readMap_congr fun k ⟨a, ha, hk⟩ => by
      subst hk
      exact World.sload_sstore_ne_key _ _ _ (hs'.disj balancesSlot (by simp) allowedSlot
        (by simp) a ha o ho sp hsp)
  rw [hbal]
  simp only [VState.setAllowance, readState]
  congr 1
  funext a b
  simp only [Function.update_apply]
  have hne : ∀ a' b', a' ∈ Act → b' ∈ Act → ¬ (a' = o ∧ b' = sp) →
      mappingSlot2 crypto (Word.ofAddress a') (Word.ofAddress b') allowedSlot ≠
        mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) allowedSlot := by
    intro a' b' ha hb hn e
    obtain ⟨h1, h2, -⟩ := hs'.inj2 allowedSlot (by simp) allowedSlot (by simp) a' ha b' hb o ho
      sp hsp e
    exact hn ⟨h1, h2⟩
  by_cases hao : a = o
  · subst hao
    by_cases hbs : b = sp
    · subst hbs
      simp [readMap2, ho, hsp]
    · simp only [↓reduceIte]
      rw [Function.update_of_ne hbs]
      simp only [readMap2]
      split_ifs with hab
      · rw [World.sload_sstore_ne_key _ _ _ (hne a b hab.1 hab.2 (fun h => hbs h.2))]
      · rfl
  · simp only [hao, ↓reduceIte, readMap2]
    split_ifs with hab
    · rw [World.sload_sstore_ne_key _ _ _ (hne a b hab.1 hab.2 (fun h => hao h.1))]
    · rfl

end Verified.WeirdERC20.USDT.Spec
