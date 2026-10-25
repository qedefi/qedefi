import Verified.Safe.Bytecode.Singleton.SigTxLoop
import Verified.Safe.Bytecode.Singleton.Frame

/-!
# The singleton: `execTransaction`

From the entry of `execTransaction` (pc `2590`): the calldata decoding (the signatures copied to
`0x80`, their length at most `2 ^ 32`), the nonce increment (key `5`, allowed by `Kw`),
`getTransactionHash` (`tx_hash`: a digest of this Safe), `checkSignatures` reading the
threshold, and the loop head of `checkNSignatures` in a state of `TxL`; then `tx_loop`.
-/

namespace Verified.Safe.Guard

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested
open Verified.Safe.Contracts Verified.Safe.MiniSafe

namespace Dep

variable (D : Dep) {O T : Finset Address} {thr : Nat} {h₀ : Word} {msg : Message}
  {ctx : Context} {w : World} {m : Machine}

set_option maxHeartbeats 0 in
/-- **`execTransaction`**: from its entry, the frame judgment; the frame never reaches the call
when fewer than `thr` owners sign. -/
theorem sg_execTransaction (hC : D.SgCtx O T thr h₀ msg ctx) : D.SgExec O T thr h₀ msg ctx := by
  intro w m s hF
  sg_explore [12738]
  case key9575 => exact .inl rfl
  generalize hL : Bytes.toWord (readBytes msg.data
    (BitVec.toNat (4#256 + Bytes.toWord (readBytes msg.data 292 32))) 32) = L at hF hc2923
  have hL32 : L.toNat ≤ 2 ^ 32 := by
    have h := gt_eq_zero.1 (BitVec.or_eq_zero_iff.1 (iszero_ne_zero.1 hc2923)).1
    exact h
  have hpn : (128#256 + (32#256 + Word.div (31#256 + L) 32#256 * 32#256)).toNat =
      160 + (31 + L.toNat) / 32 * 32 := by
    have h1 : (31#256 + L).toNat = 31 + L.toNat := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
    have h2 : (Word.div (31#256 + L) 32#256).toNat = (31 + L.toNat) / 32 := by
      simp only [Word.div, BitVec.toNat_udiv, h1]; rfl
    have h3 : (Word.div (31#256 + L) 32#256 * 32#256).toNat = (31 + L.toNat) / 32 * 32 := by
      rw [BitVec.toNat_mul, h2]; simp only [BitVec.toNat_ofNat]; omega
    rw [BitVec.toNat_add, BitVec.toNat_add, h3]; simp only [BitVec.toNat_ofNat]; omega
  have h160 : (160#256 + L).toNat = 160 + L.toNat := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  refine D.tx_hash (p := 128#256 + (32#256 + Word.div (31#256 + L) 32#256 * 32#256)) hC.target
    ?hp (by omega) (by omega) hF fun m dh mem' hF hdh h64 hpres => ?_
  case hp =>
    simp (disch := first | omega | simp) only [Memory.loadWord_expand,
      Memory.loadWord_storeWord_of_disjoint, Own.loadWord_copyIn_of_disjoint,
      Memory.loadWord_storeWord]
  have h128 : mem'.loadWord 128 = L := by
    rw [hpres 128 (by omega) (by omega)]
    simp (disch := first | omega | simp) only [Memory.loadWord_expand,
      Memory.loadWord_storeWord_of_disjoint, Own.loadWord_copyIn_of_disjoint,
      Memory.loadWord_storeWord]
  sg_explore [6820] using [h64, h128]
  -- The threshold read as zero and as nonzero.
  · exact absurd hc17247 hc16112
  obtain ⟨m₀, hw0, hG0, -⟩ := hR16101
  have hreq := hG0.2.2.threshold
  rw [hw0, ← hC.target] at hreq
  obtain ⟨q, hq⟩ : ∃ q, mem'.loadWord 64 = q := ⟨_, rfl⟩
  have hqn : q.toNat = 160 + (31 + L.toNat) / 32 * 32 + 128 := by
    rw [← hq, h64, BitVec.toNat_add, hpn]; simp only [BitVec.toNat_ofNat]; omega
  have h64' : (mem'.expand 128 32).loadWord 64 = q := by rw [Memory.loadWord_expand, hq]
  have h128' : (mem'.expand 128 32).loadWord (128#256 : Word).toNat = L := by
    rw [show (128#256 : Word).toNat = 128 from rfl, Memory.loadWord_expand, h128]
  exact .leaf (D.tx_loop (P0 := q.toNat) hC hreq hdh rfl hL32 (by omega) (by decide) _
    ⟨0#256, 0#256, 0#256, 0#256, 0#256, 0#256, _, _, q, hF, h64', h128', by omega,
      by simp, by simp only [BitVec.reduceToNat]; omega, Nat.zero_le _⟩)

end Dep

end Verified.Safe.Guard
