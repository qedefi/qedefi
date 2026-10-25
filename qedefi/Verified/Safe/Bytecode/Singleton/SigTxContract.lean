import Verified.Safe.Bytecode.Singleton.SigTx

/-!
# The signature loop of `execTransaction`: contract signatures

From the copy of a contract signature into the `isValidSignature` calldata (pc `17648`) to the
loop head: the length is bounded by the signatures' (`contract_bounds`), the copy keeps the memory
below the calldata, `EXTCODESIZE` of the owner is nonzero (so it is not idle, so a signer).
-/

namespace Verified.Safe.Guard

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested
open Verified.Safe.Contracts Verified.Safe.MiniSafe

namespace Dep

variable (D : Dep) {O T : Finset Address} {thr : Nat} {h₀ : Word} {msg : Message}
  {ctx : Context} {w : World} {m : Machine}

/-- The bounds `checkNSignatures` checks on a contract signature at offset `s` of length `ln`
(no overflow of `s + 32` nor of `s + 32 + ln`, and within the signatures' length `L`). -/
theorem contract_bounds {s ln L : Word}
    (h1 : ((s + 32#256).lt s).iszero ≠ 0) (h2 : ((s + 32#256 + ln).lt (s + 32#256)).iszero ≠ 0)
    (h3 : ((s + 32#256 + ln).gt L).iszero ≠ 0) :
    (s + 32#256).toNat = s.toNat + 32 ∧ s.toNat + 32 + ln.toNat ≤ L.toNat := by
  rw [iszero_ne_zero, lt_eq_zero] at h1 h2
  rw [iszero_ne_zero, gt_eq_zero] at h3
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h1 h2 h3 ⊢
  have := s.isLt; have := ln.isLt
  omega

theorem toNat_add3 {a b c : Word} (h : a.toNat + b.toNat + c.toNat < 2 ^ 256) :
    (a + b + c).toNat = a.toNat + b.toNat + c.toNat := by
  simp only [BitVec.toNat_add]; omega

set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
/-- **A contract signature**, from the head of the copy into the `isValidSignature` calldata
(pc `17648`; the calldata at the free pointer `p`, the copy's destination `dst = p + 100`, the
signature's length `len` at most `2 ^ 32`, the call's target `tgt` the owner `a`): the owner has
code (else `EXTCODESIZE` reverts), so it is not idle, so a signer; back at the loop head with it
counted. The stack is generic (variables), so that the lemma applies to the explored state by
first-order unification. -/
theorem tx_contract {rest : List Word} {req sig dh ex ret L : Word} {P0 : Nat}
    {i sv rv vv a last p src dst len x5 x6 x7 x8 x9 x10 x11 tgt x13 x14 x15 x16 x17 x18 x19 :
      Word} {M : Memory}
    (hC : D.SgCtx O T thr h₀ msg ctx)
    (hs0 : 128 ≤ sig.toNat) (hp0 : 128 ≤ p.toNat) (hpP : p.toNat ≤ P0 + 256 * i.toNat)
    (hsig : sig.toNat + 32 + L.toNat ≤ p.toNat)
    (hcnt : i.toNat ≤ cnt (O ∩ T) (amask &&& last)) (hpb : p.toNat < 2 ^ 200)
    (hF : Fr (fix msg ctx) m 17648 (0#256 :: src :: dst :: len :: len :: x5 :: x6 :: x7 :: x8 ::
      x9 :: x10 :: x11 :: tgt :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: 6958#256 :: i ::
      sv :: rv :: vv :: a :: last :: req :: sig :: dh :: ex :: ret :: rest) M w)
    (htgt : tgt = amask &&& a) (hx6 : x6 = dst) (hdst : dst.toNat = 100 + p.toNat) (hlen : len.toNat ≤ 2 ^ 32)
    (hM64 : M.loadWord 64 = p) (hMsig : M.loadWord sig.toNat = L) :
    OwnB True (fun _ => True) (D.Rsf ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork)
      (Own.SstoreOk (Kw ctx.crypto)) D.Csf Dsim Doomed (fun y => TxL msg ctx O T rest req sig dh ex
        ret L P0 y ∨ D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork y) m := by
  subst htgt x6
  refine copy_17648 _ _ _ _ _ _ _ _ _ hF rfl (by omega) fun i' mem' m hF hpres => ?_
  sg_explore [6820]
  all_goals try sg_side
  all_goals try exact absurd hc7675 hc7525
  all_goals try exact absurd (iszero_ne_zero.1 hc7730) hc7675
  all_goals
    have hq : mem'.loadWord 64 = p := (hpres 64 (by omega)).trans hM64
    have hqs : mem'.loadWord sig.toNat = L := (hpres _ (by omega)).trans hMsig
    have hpad : 100 + p.toNat ≤ (len + dst - (31#256 &&& len)).toNat := by
      have := Nat.and_le_right (n := 31) (m := len.toNat)
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat,
        Nat.reducePow, Nat.reduceMod]
      omega
    have hO := D.owner_mem hR7617 hC.target hc7675
    have hT : Word.toAddress a ∈ T := by
      obtain ⟨m₀, hw, hR⟩ := hR17738
      have hsz : (w.code (Word.toAddress a)).size ≠ 0 := by
        have h := iszero_eq_zero.1 (iszero_ne_zero.1 hc17745)
        rw [amask_and, Word.toAddress_ofAddress] at h
        intro h0; rw [h0] at h; exact h rfl
      by_contra hT
      have := (hR.2.1 _ (.inr ⟨hO, hT⟩)).1
      rw [hw] at this
      exact hsz this
    have hcnt' := step_cnt hO hT hc7525 hcnt
    have hi1 : (1#256 + i).toNat = 1 + i.toNat := by
      have := cnt_le (O ∩ T) (amask &&& last); have := card_le (O ∩ T)
      rw [toNat_add_of_lt (by simp only [BitVec.reduceToNat]; omega)]; rfl
    refine .leaf (.inl ⟨1#256 + i, _, _, _, _, _, _, w', p, hF, ?_, ?_, hp0, by omega, hsig, hcnt'⟩)
    · simp (disch := omega) only [Memory.loadWord_expand, Memory.loadWord_storeWord',
        Memory.loadWord_storeWord_of_disjoint, loadWord_returnMemory_of_disjoint, hq]
    · simp (disch := omega) only [Memory.loadWord_expand, Memory.loadWord_storeWord',
        Memory.loadWord_storeWord_of_disjoint, loadWord_returnMemory_of_disjoint, hq, hqs]

end Dep

end Verified.Safe.Guard
