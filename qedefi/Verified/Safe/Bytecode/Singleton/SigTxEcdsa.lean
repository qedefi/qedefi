import Verified.Safe.Bytecode.Singleton.SigTx

/-!
# The signature loop of `execTransaction`: `ecrecover` signatures

From the two `ecrecover` calls of the loop (plain ECDSA at pc `7440`, `eth_sign` at pc `7333`),
to the loop head: the recovered owner is above `lastOwner`, an owner, and (by `Signers`) in `T`.
These are tactic scripts (`tx_ecdsa_close`, `tx_ethSign_close`), run by `tx_loop` on the
explored states at the two calls: they name the hypotheses of that context (`hC`, `hdh`, `hL`,
`hF`, …), so they are not hygienic. Stating the states as lemmas would require restating
expressions of several kilobytes, whose unification against the explored states is slow.
-/

namespace Verified.Safe.Guard

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested
open Verified.Safe.Contracts Verified.Safe.MiniSafe

set_option hygiene false in
/-- **A plain ECDSA signature**: from the `ecrecover` call at pc `7440`, back at the loop head
with one more owner of `T` counted, or the frame ends. -/
macro "tx_ecdsa_close" : tactic => `(tactic| (
    sg_explore [6820] using [hL, toNat_add_of_lt, Memory.loadWord_storeWord]
    all_goals try sg_side
    all_goals try exact absurd hc7675 hc7525
    all_goals try exact absurd (iszero_ne_zero.1 hc7730) hc7675
    obtain ⟨g, hsucc, hmem⟩ := hres (iszero_eq_zero.1 (iszero_ne_zero.1 hc7447))
    have e1 : (32#256 + p - 32#256) = p := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have e2 : 32#256 + (32#256 + (32#256 + (32#256 + (32#256 + p)))) - (32#256 + p) = 128#256 := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    simp only [e1, e2] at hsucc hmem
    simp only [BitVec.reduceToNat] at hsucc hmem
    simp (disch := (try simp only [BitVec.reduceToNat]); omega) only [toNat_add_of_lt] at hsucc hmem
    simp (disch := omega) only [BitVec.reduceToNat, readBytes_bytes, Memory.read_expand,
      Memory.read_128', Memory.read_storeWord_of_disjoint, Memory.read_storeWord'] at hsucc hmem
    rw [run_ecrecover] at hsucc hmem
    by_cases hg : 3000 ≤ g
    swap
    · simp [hg, Precompile.fail] at hsucc
    simp only [hg, ↓reduceIte, returnMemory_ecrecoverOutput] at hmem
    have hpb' : p.toNat < 2 ^ 200 := hpb
    have h32p : (32#256 + p).toNat = 32 + p.toNat := by
      rw [toNat_add_of_lt (by simp only [BitVec.reduceToNat]; omega)]; rfl
    obtain ⟨sh, hsh, hdh'⟩ := hdh
    split at hmem
    · rename_i a hrec
      have h64 : mem'.loadWord 64 = 32#256 + p := by
        subst hmem
        simp (disch := omega) only [Memory.loadWord_expand, Memory.loadWord_storeWord,
          Memory.loadWord_storeWord_of_disjoint]
      have hx : mem'.loadWord p.toNat = Word.ofAddress a := by
        subst hmem
        simp (disch := omega) only [Memory.loadWord_expand, Memory.loadWord_storeWord,
          Memory.loadWord_storeWord_of_disjoint]
      have hsL : mem'.loadWord sig.toNat = L := by
        subst hmem
        simp (disch := omega) only [Memory.loadWord_expand, Memory.loadWord_storeWord,
          Memory.loadWord_storeWord_of_disjoint, hL]
      simp only [h64, e1, hx] at hF hc7525 hc7675
      have hO := D.owner_mem hR7617 hC.target hc7675
      rw [Word.toAddress_ofAddress] at hO
      have hT : a ∈ T := hC.signers.ecdsa sh _ _ _ a hsh (hdh' ▸ hrec) hO
      have hcnt' := step_cnt (x := Word.ofAddress a) (by rw [Word.toAddress_ofAddress]; exact hO)
        (by rw [Word.toAddress_ofAddress]; exact hT) hc7525 hcnt
      have hi1 : (1#256 + i).toNat = 1 + i.toNat := by
        have := cnt_le (O ∩ T) (amask &&& last); have := card_le (O ∩ T)
        rw [toNat_add_of_lt (by simp only [BitVec.reduceToNat]; omega)]; rfl
      refine .leaf (.inl ⟨1#256 + i, _, _, _, _, _, _, w, 32#256 + p, hF, ?_, ?_, ?_, ?_, ?_, hcnt'⟩)
      · simp (disch := omega) only [Memory.loadWord_expand, Memory.loadWord_storeWord,
          Memory.loadWord_storeWord_of_disjoint, h64]
      · simp (disch := omega) only [Memory.loadWord_expand, Memory.loadWord_storeWord,
          Memory.loadWord_storeWord_of_disjoint, hsL]
      · omega
      · omega
      · omega
    · exfalso
      have hx : mem'.loadWord p.toNat = 0#256 := by
        subst hmem
        simp (disch := omega) only [Memory.loadWord_expand, Memory.loadWord_storeWord,
          Memory.loadWord_storeWord_of_disjoint]
      have h64 : mem'.loadWord 64 = 32#256 + p := by
        subst hmem
        simp (disch := omega) only [Memory.loadWord_expand, Memory.loadWord_storeWord,
          Memory.loadWord_storeWord_of_disjoint]
      simp only [h64, e1, hx] at hc7525
      rw [iszero_eq_zero, gt_ne_zero] at hc7525
      simp at hc7525))

set_option hygiene false in
/-- **An `eth_sign` signature**: from the `ecrecover` call at pc `7333` (on the `eth_sign` digest
hashed at `p + 32`), back at the loop head with one more owner of `T` counted. -/
macro "tx_ethSign_close" : tactic => `(tactic| (
    have hlen : BitVec.toNat (32#256 + (28#256 + (32#256 + p)) - p - 32#256) = 60 := by
      have : 32#256 + (28#256 + (32#256 + p)) - p - 32#256 = 60#256 := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      rw [this]; rfl
    simp only [hlen, Memory.read_ethSign] at hF
    sg_explore [6820] using [hL, toNat_add_of_lt, Memory.loadWord_storeWord]
    all_goals try sg_side
    all_goals try exact absurd hc7675 hc7525
    all_goals try exact absurd (iszero_ne_zero.1 hc7730) hc7675
    obtain ⟨g, hsucc, hmem⟩ := hres (iszero_eq_zero.1 (iszero_ne_zero.1 hc7340))
    have hpb' : p.toNat < 2 ^ 200 := hpb
    generalize hq : 32#256 + (28#256 + (32#256 + p)) = q at hsucc hmem hc7525 hc7675 hF
    have hqn : q.toNat = 92 + p.toNat := by
      rw [← hq]; apply Eq.trans (toNat_add_of_lt ?_) ?_ <;> simp only [BitVec.toNat_add,
        BitVec.toNat_ofNat] <;> omega
    have e1 : (32#256 + q - 32#256) = q := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have e2 : 32#256 + (32#256 + (32#256 + (32#256 + (32#256 + q)))) - (32#256 + q) = 128#256 := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h32q : (32#256 + q).toNat = 32 + q.toNat := by
      rw [toNat_add_of_lt (by simp only [BitVec.reduceToNat]; omega)]; rfl
    simp only [e1, e2, h32q, BitVec.reduceToNat] at hsucc hmem
    simp (disch := omega) only [BitVec.reduceToNat, readBytes_bytes, Memory.read_expand,
      Memory.read_128', Memory.read_storeWord_of_disjoint, Memory.read_storeWord'] at hsucc hmem
    rw [run_ecrecover] at hsucc hmem
    by_cases hg : 3000 ≤ g
    swap
    · simp [hg, Precompile.fail] at hsucc
    simp only [hg, ↓reduceIte, returnMemory_ecrecoverOutput] at hmem
    obtain ⟨sh, hsh, hdh'⟩ := hdh
    have hq' : q.toNat = 32 + (28 + (32 + p.toNat)) := by omega
    split at hmem
    · rename_i a hrec
      have h64 : mem'.loadWord 64 = 32#256 + q := by
        subst hmem
        simp (disch := omega) only [Memory.loadWord_expand, Memory.loadWord_storeWord',
          Memory.loadWord_storeWord_of_disjoint]
      have hx : mem'.loadWord q.toNat = Word.ofAddress a := by
        subst hmem
        simp (disch := omega) only [Memory.loadWord_expand, Memory.loadWord_storeWord',
          Memory.loadWord_storeWord_of_disjoint]
      have hsL : mem'.loadWord sig.toNat = L := by
        subst hmem
        simp (disch := omega) only [Memory.loadWord_expand, Memory.loadWord_storeWord',
          Memory.loadWord_storeWord_of_disjoint, hL]
      simp only [h64, e1, hx] at hF hc7525 hc7675
      have hO := D.owner_mem hR7617 hC.target hc7675
      rw [Word.toAddress_ofAddress] at hO
      have hT : a ∈ T := hC.signers.ethSign sh _ _ _ a hsh (by rw [ethSignDigest, ← hdh']; exact hrec) hO
      have hcnt' := step_cnt (x := Word.ofAddress a) (by rw [Word.toAddress_ofAddress]; exact hO)
        (by rw [Word.toAddress_ofAddress]; exact hT) hc7525 hcnt
      have hi1 : (1#256 + i).toNat = 1 + i.toNat := by
        have := cnt_le (O ∩ T) (amask &&& last); have := card_le (O ∩ T)
        rw [toNat_add_of_lt (by simp only [BitVec.reduceToNat]; omega)]; rfl
      refine .leaf (.inl ⟨1#256 + i, _, _, _, _, _, _, w, 32#256 + q, hF, ?_, ?_, ?_, ?_, ?_, hcnt'⟩)
      · simp (disch := omega) only [Memory.loadWord_expand, Memory.loadWord_storeWord',
          Memory.loadWord_storeWord_of_disjoint, h64]
      · simp (disch := omega) only [Memory.loadWord_expand, Memory.loadWord_storeWord',
          Memory.loadWord_storeWord_of_disjoint, hsL]
      · omega
      · omega
      · omega
    · exfalso
      have hx : mem'.loadWord q.toNat = 0#256 := by
        subst hmem
        simp (disch := omega) only [Memory.loadWord_expand, Memory.loadWord_storeWord',
          Memory.loadWord_storeWord_of_disjoint]
      have h64 : mem'.loadWord 64 = 32#256 + q := by
        subst hmem
        simp (disch := omega) only [Memory.loadWord_expand, Memory.loadWord_storeWord',
          Memory.loadWord_storeWord_of_disjoint]
      simp only [h64, e1, hx] at hc7525
      rw [iszero_eq_zero, gt_ne_zero] at hc7525
      simp at hc7525))

end Verified.Safe.Guard
