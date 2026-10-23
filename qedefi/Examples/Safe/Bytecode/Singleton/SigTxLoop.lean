import Examples.Safe.Bytecode.Singleton.SigTxEcdsa
import Examples.Safe.Bytecode.Singleton.SigTxContract

/-!
# The signature loop of `execTransaction`: no exit

`tx_loop`: from every loop state (`TxL`), the frame judgment. Each pass that does not end the
frame counts one more owner of `T` (an `ecrecover`, contract or approved-hash signature), so the
counter stays at most `|O ∩ T| < thr`, and the exit `i ≥ thr` is never taken.
-/

namespace Examples.Safe.Guard

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested
open Examples.Safe.Contracts Examples.Actor.MiniSafeOwn

namespace Dep

variable (D : Dep) {O T : Finset Address} {thr : Nat} {h₀ : Word} {msg : Message}
  {ctx : Context} {w : World} {m : Machine}

set_option maxHeartbeats 0 in
/-- **No exit**: from the loop states of `execTransaction`'s check, the frame judgment. -/
theorem tx_loop {rest : List Word} {req sig dh ex ret L : Word} {P0 : Nat}
    (hC : D.SgCtx O T thr h₀ msg ctx) (hreq : req = BitVec.ofNat 256 thr)
    (hdh : ∃ sh : ByteArray, sh.size = 32 ∧ dh = safeDigest ctx.crypto ctx.block.chainId D.sf sh)
    (hex : ex = Word.ofAddress msg.caller) (hL32 : L.toNat ≤ 2 ^ 32) (hP0 : P0 < 2 ^ 40)
    (hs0 : 128 ≤ sig.toNat) :
    ∀ x, TxL msg ctx O T rest req sig dh ex ret L P0 x →
      D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork x := by
  refine OwnG.coind _ ?_
  rintro x ⟨i, sv, rv, vv, cur, last, mem, w, p, hF, hp, hL, hp0, hpP, hsig, hcnt⟩
  have hit := D.cnt_lt_thr hC hcnt
  have hpb : p.toNat < 2 ^ 200 := by
    have := card_le (O ∩ T); have := cnt_le (O ∩ T) (amask &&& last); omega
  refine OwnB.jumpdestStep hF (by own_code) (Own.sstoreOk_of_ne (b := 0x5b) hF (by own_code)
    (by decide)) fun m hF => ?_
  sg_explore [6820, 17648, 7333, 7440] using [hp, hL, toNat_add_of_lt, Memory.loadWord_storeWord]
  -- The exit: `i < thr` always.
  all_goals try
    (rw [iszero_ne_zero, ← not_ne_iff, lt_ne_zero, hreq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hC.thr_lt] at hc6828; exact absurd hit hc6828)
  -- Infeasible: `currentOwner > lastOwner` both held and failed.
  all_goals try exact absurd hc7675 hc7525
  all_goals try exact absurd (iszero_ne_zero.1 hc7730) hc7675
  -- Approved hashes (`v = 1`): by `msg.sender`, or approved before.
  all_goals try
    (guard_hyp hF : Fr _ _ 6820 _ _ _
     obtain ⟨sh, hsh, hdh'⟩ := hdh
     have hO := D.owner_mem hR7617 hC.target hc7675
     have hT := by first
       | exact D.approval_T hR7116 hC.target hsh hdh' hO hc7123
       | exact D.executor_T hC hex hO hc7032
     have hcnt' := step_cnt hO hT hc7525 hcnt
     have hi1 : (1#256 + i).toNat = 1 + i.toNat := by
       have := cnt_le (O ∩ T) (amask &&& last); have := card_le (O ∩ T)
       rw [toNat_add_of_lt (by simp only [BitVec.reduceToNat]; omega)]; rfl
     exact .leaf (.inl ⟨1#256 + i, _, _, _, _, _, _, w, p, hF,
       by simp (disch := omega) only [Memory.loadWord_expand,
            Memory.loadWord_storeWord_of_disjoint, hp],
       by simp (disch := omega) only [Memory.loadWord_expand,
            Memory.loadWord_storeWord_of_disjoint, hL],
       hp0, by omega, hsig, hcnt'⟩))
  -- The rest, in the order of the exploration: two contract signatures (the threshold
  -- checked `≠ 0` with and without the overflow check), `eth_sign`, plain ECDSA.
  all_goals try
    (guard_hyp hF : Fr _ _ 7333 _ _ _
     tx_ethSign_close)
  all_goals try
    (guard_hyp hF : Fr _ _ 7440 _ _ _
     tx_ecdsa_close)
  all_goals
    obtain ⟨-, hle⟩ := contract_bounds (by assumption) hc21112 hc17469
    refine D.tx_contract hC hs0 hp0 hpP hsig hcnt hpb hF rfl rfl ?_ ?_ ?_ ?_
    · simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · simp (disch := (try simp only [BitVec.reduceToNat]); omega) only [toNat_add3,
        BitVec.reduceToNat, Memory.loadWord_expand, Memory.loadWord_storeWord_of_disjoint] at hle ⊢
      omega
    · simp (disch := omega) only [Memory.loadWord_expand, Memory.loadWord_storeWord_of_disjoint, hp]
    · simp (disch := omega) only [Memory.loadWord_expand, Memory.loadWord_storeWord_of_disjoint, hL]

end Dep

end Examples.Safe.Guard
