import Verified.WeirdERC20.USDT.Spec.OpHigh
import Verified.WeirdERC20.USDT.Spec.Transfer

/-!
# USDT's admin entry points: the abstraction after their writes

A write of `totalSupply`, `basisPointsRate` or `maximumFee` (`write_fixed`) or of an actor's
`isBlackListed` row (`write_black`) keeps the scope (`Live`) and changes only that field of the
abstraction. With `write_bal` (`read_bal_write`), these are the writes of the admin entry points.
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open Verified.WeirdERC20.USDT.Contracts
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.Math QEDefi.ERC4626

section Writes

variable {crypto : Crypto} {Act : Finset Address} {w : World} {t : Address}

theorem blackKey_eq (crypto : Crypto) (a : Address) :
    blackKey crypto a = mappingSlot crypto (Word.ofAddress a) blackSlot := rfl

theorem ownerA_eq (w : World) (t : Address) : ownerA w t = ownerOf w t := rfl

/-- **A write of a fixed slot other than the owner's, `decimals` and `deprecated`**: the scope
is kept and only `supply`, `feeBps` or `feeMax` changes. -/
theorem write_fixed (hs : usdtAbs.Sound crypto Act) (hl : Live Act w t) {k : Word}
    (hk : k = 1 ∨ k = 3 ∨ k = 4) (x : Word) :
    Live Act (w.sstore t k x) t ∧
    readState crypto Act (w.sstore t k x) t =
      { readState crypto Act w t with
        supply := if k = 1 then x.toNat else (readState crypto Act w t).supply
        feeBps := if k = 3 then x.toNat else (readState crypto Act w t).feeBps
        feeMax := if k = 4 then x.toNat else (readState crypto Act w t).feeMax } := by
  have hs' : ActorRows crypto Act [balancesSlot, blackSlot] [allowedSlot] fixedSlots := hs
  have hkf : k ∈ fixedSlots := by
    rw [mem_fixedSlots]; rcases hk with h | h | h <;> simp [h]
  have hne : ∀ j : Word, j = 0 ∨ j = 9 ∨ j = 10 →
      (w.sstore t k x).sload t j = w.sload t j := by
    intro j hj
    apply World.sload_sstore_ne_key
    rcases hk with h | h | h <;> rcases hj with h' | h' | h' <;> subst h h' <;> decide
  have h0 := hne 0 (.inl rfl)
  have h9 := hne 9 (.inr (.inl rfl))
  have h10 := hne 10 (.inr (.inr rfl))
  have hrow1 : ∀ b ∈ [balancesSlot, blackSlot], ∀ a ∈ Act,
      (w.sstore t k x).sload t (mappingSlot crypto (Word.ofAddress a) b) =
        w.sload t (mappingSlot crypto (Word.ofAddress a) b) :=
    fun b hb a ha => World.sload_sstore_ne_key _ _ _
      (fun e => hs'.fixed1 b hb a ha (by rw [e]; exact hkf))
  refine ⟨?_, ?_⟩
  · unfold Live ownerOf at hl ⊢
    rw [h0, h10, show decimalsSlot = 9 from rfl, h9]
    exact hl
  · have hbal : readMap crypto Act (w.sstore t k x) t balancesSlot =
        readMap crypto Act w t balancesSlot :=
      readMap_congr fun k' ⟨a, ha, e⟩ => by subst e; exact hrow1 _ (by simp) a ha
    have hal : readMap2 crypto Act (w.sstore t k x) t allowedSlot =
        readMap2 crypto Act w t allowedSlot :=
      readMap2_congr fun k' ⟨o, ho, sp, hsp, e⟩ => by
        subst e
        exact World.sload_sstore_ne_key _ _ _
          (fun e => hs'.fixed2 allowedSlot (by simp) o ho sp hsp (by rw [e]; exact hkf))
    have hbl : blacklistedOf crypto Act (w.sstore t k x) t = blacklistedOf crypto Act w t := by
      funext a
      simp only [blacklistedOf]
      by_cases ha : a ∈ Act
      · rw [hrow1 blackSlot (by simp) a ha]
      · simp [ha]
    have hslot : ∀ j : Word, readSlot (w.sstore t k x) t j =
        if j = k then x.toNat else readSlot w t j := by
      intro j
      by_cases hj : j = k
      · subst hj; simp [readSlot]
      · simp only [readSlot, hj, ↓reduceIte, World.sload_sstore_ne_key _ _ _ hj]
    simp only [readState, ownerOf, pausedOf, h0, hbal, hal, hbl, World.balance_sstore, hslot]
    rcases hk with h | h | h <;> subst h <;>
      simp [supplySlot, bpsSlot, maxFeeSlot]

/-- **A write of an actor's `isBlackListed` row**: the scope is kept and only that actor's flag
changes, to the row's low byte. -/
theorem write_black (hs : usdtAbs.Sound crypto Act) (hl : Live Act w t) {u : Address}
    (hu : u ∈ Act) (x : Word) :
    Live Act (w.sstore t (blackKey crypto u) x) t ∧
    readState crypto Act (w.sstore t (blackKey crypto u) x) t =
      { readState crypto Act w t with
        blacklisted := Function.update (readState crypto Act w t).blacklisted u
          (rowBool.get x != 0) } := by
  have hs' : ActorRows crypto Act [balancesSlot, blackSlot] [allowedSlot] fixedSlots := hs
  rw [blackKey_eq]
  have hfix : ∀ k ∈ fixedSlots, (w.sstore t (mappingSlot crypto (Word.ofAddress u) blackSlot)
      x).sload t k = w.sload t k :=
    fun k hk => World.sload_sstore_ne_key _ _ _ (fun e => hs'.fixed1 blackSlot (by simp) u hu
      (by rw [← e]; exact hk))
  have hl' := (live_congr (Act := Act) hfix).2 hl
  refine ⟨hl', ?_⟩
  have hbal : readMap crypto Act (w.sstore t (mappingSlot crypto (Word.ofAddress u) blackSlot) x)
      t balancesSlot = readMap crypto Act w t balancesSlot :=
    readMap_congr fun k' ⟨a, ha, e⟩ => by
      subst e
      exact World.sload_sstore_ne_key _ _ _ (fun e => by
        have := (hs'.inj1 balancesSlot (by simp) blackSlot (by simp) a ha u hu e).2
        exact absurd this (by decide))
  have hal : readMap2 crypto Act (w.sstore t (mappingSlot crypto (Word.ofAddress u) blackSlot) x)
      t allowedSlot = readMap2 crypto Act w t allowedSlot :=
    readMap2_congr fun k' ⟨o, ho, sp, hsp, e⟩ => by
      subst e
      exact World.sload_sstore_ne_key _ _ _ (fun e => hs'.disj blackSlot (by simp) allowedSlot
        (by simp) u hu o ho sp hsp e.symm)
  have hbl : blacklistedOf crypto Act
      (w.sstore t (mappingSlot crypto (Word.ofAddress u) blackSlot) x) t =
      Function.update (blacklistedOf crypto Act w t) u (rowBool.get x != 0) := by
    funext a
    by_cases hau : a = u
    · subst hau
      simp [blacklistedOf, hu]
    · rw [Function.update_of_ne hau]
      simp only [blacklistedOf]
      by_cases ha : a ∈ Act
      · rw [World.sload_sstore_ne_key _ _ _ (fun e => hau
          (hs'.inj1 blackSlot (by simp) blackSlot (by simp) a ha u hu e).1)]
      · simp [ha]
  simp only [readState, ownerOf, pausedOf, hfix 0 (by simp [fixedSlots]), hbal, hal, hbl,
    World.balance_sstore, readSlot_congr (hfix supplySlot (by simp [fixedSlots])),
    readSlot_congr (hfix bpsSlot (by simp [fixedSlots])),
    readSlot_congr (hfix maxFeeSlot (by simp [fixedSlots]))]

end Writes

end Verified.WeirdERC20.USDT.Spec
