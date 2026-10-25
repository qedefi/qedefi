import EvmLogic.Tactic.Mcopy
import EvmLogic.Solidity.Strings
import Verified.Solmate.ERC4626.StringsCommon
import Verified.MathlibDeps
import Verified.Solmate.ERC4626.MulDiv
import QEDefi.Math.Arith

/-!
# Long strings of `Verified.Solmate.ERC4626.StringsCode`

The long-string (copy loop) part of the `name()`/`symbol()` getter proofs, split off
`StringsCode` so that its kernel checks run in parallel with the short-string part.
-/

section

/-!
## Long strings

The getter copies the words at `keccak256(slot) + j` with a loop (`0x056e`–`0x0581`), then the
encoder (`0x1148`) copies again with `MCOPY`. Memory expansion is tracked through the potential
`gasLeft + Gas.memoryCost size` (`VaultCopy.gas`), so the expansion terms telescope.
-/

namespace Verified.Solmate.ERC4626
open Verified.Solmate.ERC20 QEDefi.ERC4626

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts EvmLean.Bytes

/-- The copy loop's state after `k` words at pc `pc`: `dst = 0xa0 + 32 k`, `ptr = h + k`,
`end = 0xa0 + L`; the first `k` data words at `0xa0`; the gas potential covers the rest. -/
structure VaultCopy (i : SolmateVault.Immutables) (w : World) (a : Address) (h : Word)
    (L n R : Nat) (fmp : Word) (tl : List Word) (k pc : Nat) (m : Machine) : Prop where
  code : m.frame.code = SolmateVault.runtimeCodeWith i
  jd : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i)
  pcEq : m.frame.pc = pc
  world : m.world = w
  target : m.frame.msg.currentTarget = a
  stack : ∃ dst ptr endw, m.frame.stack = dst :: ptr :: endw :: tl ∧
    dst.toNat = 160 + 32 * k ∧ ptr = h + BitVec.ofNat 256 k ∧ endw.toNat = 160 + L
  size : m.frame.memory.size = 160 + 32 * k
  fmpEq : m.frame.memory.loadWord 64 = fmp
  len : m.frame.memory.read 128 32 = ofWord (BitVec.ofNat 256 L)
  data : m.frame.memory.read 160 (32 * k) = Str.wordsFrom (w.sload a) h k
  /-- Gas, as a potential. -/
  gas : R + 2300 * (n - k) + Gas.memoryCost (256 + 64 * n) ≤
    m.frame.gasLeft + Gas.memoryCost (160 + 32 * k)

set_option maxHeartbeats 0 in
theorem vaultCopyBody_wp {i : SolmateVault.Immutables} {w : World} {a : Address} {h fmp : Word}
    {L n R k : Nat} {tl : List Word} (m : Machine)
    (hst : VaultCopy i w a h L n R fmp tl k 0x56e m) (hkn : k < n) (hn : n = (L + 31) / 32)
    (hL : 32 ≤ L) (hL' : L < 2 ^ 64) (htl : tl.length ≤ 1010) :
    WP m (fun m' => (k + 1 < n ∧ VaultCopy i w a h L n R fmp tl (k + 1) 0x56e m') ∨
      (k + 1 = n ∧ VaultCopy i w a h L n R fmp tl (k + 1) 0x582 m')) (fun _ _ => False) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨hc, hj, hpc, hw, ha, ⟨dst, ptr, endw, hs, hdst, hptr, hend⟩, hsize, hfmp, hlen, hdata,
    hg⟩ := hst
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc hw ha
  have hm1 := Gas.memoryCost_mono (show 160 + 32 * k ≤ 160 + 32 * (k + 1) by omega)
  have hm2 := Gas.memoryCost_mono (show 160 + 32 * (k + 1) ≤ 256 + 64 * n by omega)
  have hcost : (Gas.extendMemory (160 + 32 * k) [(160 + 32 * k, 32)]).cost =
      Gas.memoryCost (160 + 32 * (k + 1)) - Gas.memoryCost (160 + 32 * k) := by
    rw [Gas.extendMemory_one (by omega) (by omega),
      show max (160 + 32 * k) ((160 + 32 * k + 32 + 31) / 32 * 32) = 160 + 32 * (k + 1) by omega]
  generalize hc0 : Gas.memoryCost (160 + 32 * k) = c0 at *
  generalize hc1 : Gas.memoryCost (160 + 32 * (k + 1)) = c1 at *
  generalize hcF : Gas.memoryCost (256 + 64 * n) = cF at *
  generalize hQ : (fun m' : Machine => k + 1 < n ∧ VaultCopy i m_world m_msg.currentTarget h L n R fmp tl (k + 1) 1390 m' ∨
        k + 1 = n ∧ VaultCopy i m_world m_msg.currentTarget h L n R fmp tl (k + 1) 1410 m') = Q
  pwp_steps
  have hsl := sloadCost_le (storageKeyWarm m_sub.accessedStorageKeys m_msg.currentTarget ptr)
  apply WP.of_step
  case h =>
    apply step_mstore
    case hcode => pcode_fact
    case hstk => exact rfl
    case hgas =>
      simp only [memoryCost, hsize, hdst, hcost, Gas.veryLow]
      omega
  case hs => same_frame
  dsimp only
  simp only [memoryCost, hsize, hdst, hcost, Gas.veryLow]
  have hptr' : 1#256 + ptr = h + BitVec.ofNat 256 (k + 1) := by rw [hptr, add_one_ptr]
  have hdst' : (32#256 + dst).toNat = 160 + 32 * (k + 1) := by
    rw [Str.toNat_add_of_lt (by rw [hdst]; simp only [BitVec.reduceToNat]; omega), hdst]
    simp only [BitVec.reduceToNat]; omega
  by_cases hk1 : k + 1 < n
  · pwp_run_to 1390 [Str.gt_eq_one (show (32#256 + dst).toNat < endw.toNat by omega)]
    have hM'size : ((m_memory.expand (160 + 32 * k) 32).storeWord (160 + 32 * k)
        (m_world.sload m_msg.currentTarget ptr)).size = 160 + 32 * (k + 1) := by
      rw [Memory.size_storeWord, Memory.size_expand, hsize]
      simp only [Memory.wordsAfter, Memory.words, hsize, Nat.reduceEqDiff, ↓reduceIte]
      omega
    have hM'fmp : ((m_memory.expand (160 + 32 * k) 32).storeWord (160 + 32 * k)
        (m_world.sload m_msg.currentTarget ptr)).loadWord 64 = fmp := by
      rw [Memory.loadWord_storeWord_of_disjoint _ _ _ _ (by omega), Memory.loadWord_expand, hfmp]
    have hM'len : ((m_memory.expand (160 + 32 * k) 32).storeWord (160 + 32 * k)
        (m_world.sload m_msg.currentTarget ptr)).read 128 32 = ofWord (BitVec.ofNat 256 L) := by
      rw [Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand, hlen]
    have hM'data : ((m_memory.expand (160 + 32 * k) 32).storeWord (160 + 32 * k)
        (m_world.sload m_msg.currentTarget ptr)).read 160 (32 * (k + 1)) =
        Str.wordsFrom (m_world.sload m_msg.currentTarget) h (k + 1) := by
      rw [show 32 * (k + 1) = 32 * k + 32 by omega, Memory.read_add,
        Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand, hdata,
        show 160 + 32 * k = 160 + 32 * k from rfl, Memory.read_storeWord, Str.wordsFrom_succ, hptr]
    subst hQ
    refine WP.ret (.inl ⟨hk1, rfl, hj, rfl, rfl, rfl, ⟨_, _, _, rfl, hdst', hptr', hend⟩,
      hM'size, hM'fmp, hM'len, hM'data, ?_⟩)
    dsimp only
    rw [hc1, hcF]
    generalize sloadCost _ = sl at *
    omega
  · pwp_run_to 1410 [Str.gt_eq_zero (show endw.toNat ≤ (32#256 + dst).toNat by omega)]
    have hM'size : ((m_memory.expand (160 + 32 * k) 32).storeWord (160 + 32 * k)
        (m_world.sload m_msg.currentTarget ptr)).size = 160 + 32 * (k + 1) := by
      rw [Memory.size_storeWord, Memory.size_expand, hsize]
      simp only [Memory.wordsAfter, Memory.words, hsize, Nat.reduceEqDiff, ↓reduceIte]
      omega
    have hM'fmp : ((m_memory.expand (160 + 32 * k) 32).storeWord (160 + 32 * k)
        (m_world.sload m_msg.currentTarget ptr)).loadWord 64 = fmp := by
      rw [Memory.loadWord_storeWord_of_disjoint _ _ _ _ (by omega), Memory.loadWord_expand, hfmp]
    have hM'len : ((m_memory.expand (160 + 32 * k) 32).storeWord (160 + 32 * k)
        (m_world.sload m_msg.currentTarget ptr)).read 128 32 = ofWord (BitVec.ofNat 256 L) := by
      rw [Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand, hlen]
    have hM'data : ((m_memory.expand (160 + 32 * k) 32).storeWord (160 + 32 * k)
        (m_world.sload m_msg.currentTarget ptr)).read 160 (32 * (k + 1)) =
        Str.wordsFrom (m_world.sload m_msg.currentTarget) h (k + 1) := by
      rw [show 32 * (k + 1) = 32 * k + 32 by omega, Memory.read_add,
        Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand, hdata,
        show 160 + 32 * k = 160 + 32 * k from rfl, Memory.read_storeWord, Str.wordsFrom_succ, hptr]
    subst hQ
    refine WP.ret (.inr ⟨by omega, rfl, hj, rfl, rfl, rfl, ⟨_, _, _, rfl, hdst', hptr', hend⟩,
      hM'size, hM'fmp, hM'len, hM'data, ?_⟩)
    dsimp only
    rw [hc1, hcF]
    generalize sloadCost _ = sl at *
    omega

/-- **The copy loop**: from its head with `k < n` words copied to its exit with all `n`. -/
theorem vaultCopyLoop_wp {i : SolmateVault.Immutables} {w : World} {a : Address} {h fmp : Word}
    {L n R k : Nat} {tl : List Word} (m : Machine)
    (hst : VaultCopy i w a h L n R fmp tl k 0x56e m) (hkn : k < n) (hn : n = (L + 31) / 32)
    (hL : 32 ≤ L) (hL' : L < 2 ^ 64) (htl : tl.length ≤ 1010) :
    WP m (VaultCopy i w a h L n R fmp tl n 0x582) (fun _ _ => False) := by
  refine WP.loop_nat (fun j m => ∃ k, j = n - k ∧ k < n ∧ VaultCopy i w a h L n R fmp tl k 0x56e m)
    ⟨k, rfl, hkn, hst⟩ ?_
  rintro j m ⟨k, rfl, hkn, hst⟩
  refine (vaultCopyBody_wp m hst hkn hn hL hL' htl).mono_left ?_
  rintro m' (⟨hk1, h'⟩ | ⟨hk1, h'⟩)
  · exact .inl ⟨n - (k + 1), by omega, k + 1, rfl, hk1, h'⟩
  · exact .inr (hk1 ▸ h')

end Verified.Solmate.ERC4626

namespace Verified.Solmate.ERC4626
open Verified.Solmate.ERC20 QEDefi.ERC4626

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts EvmLean.Bytes

set_option maxHeartbeats 0 in
theorem vaultLongTail_wp {i : SolmateVault.Immutables} {w : World} {a : Address} {h slot : Word}
    {L n R : Nat} {rest : List Word} (m : Machine)
    (hst : VaultCopy i w a h L n R (BitVec.ofNat 256 (160 + 32 * n))
      (BitVec.ofNat 256 L :: slot :: 128#256 :: 504#256 :: rest) n 0x582 m)
    (hn : n = (L + 31) / 32) (hL : 32 ≤ L) (hL' : L < 2 ^ 64) (htl : rest.length ≤ 1000)
    (hR : 500 + 3 * n ≤ R) :
    WP m (fun _ => False)
      (fun mf o => mf.world = w ∧ o = .success (Abi.encodeString (Str.longData (w.sload a) h L))) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨hc, hj, hpc, hw, ha, ⟨dst, ptr, endw, hs, hdst, hptr, hend⟩, hsize, hfmp, hlen, hdata,
    hg⟩ := hst
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc hw ha
  clear hdst hptr hend
  simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero] at hg
  have hn1 : 1 ≤ n := by omega
  have hnL : L ≤ 32 * n := by omega
  have hnL' : 32 * n < L + 32 := by omega
  have hn64 : n < 2 ^ 60 := by omega
  have hhead : (BitVec.ofNat 256 (160 + 32 * n)).toNat = 160 + 32 * n :=
    Str.toNat_ofNat_of_lt (by omega)
  have hLn : (BitVec.ofNat 256 L).toNat = L := Str.toNat_ofNat_of_lt (by omega)
  have hm1 := Gas.memoryCost_mono (show 160 + 32 * n ≤ 192 + 32 * n by omega)
  have hm2 := Gas.memoryCost_mono (show 192 + 32 * n ≤ 224 + 32 * n by omega)
  have hm3 := Gas.memoryCost_mono (show 224 + 32 * n ≤ 224 + 64 * n by omega)
  have hm4 := Gas.memoryCost_mono (show 224 + 64 * n ≤ 256 + 64 * n by omega)
  have hcost1 : (Gas.extendMemory (160 + 32 * n) [(160 + 32 * n, 32)]).cost =
      Gas.memoryCost (192 + 32 * n) - Gas.memoryCost (160 + 32 * n) := by
    rw [Gas.extendMemory_one (by omega) (by omega),
      show max (160 + 32 * n) ((160 + 32 * n + 32 + 31) / 32 * 32) = 192 + 32 * n by omega]
  have hcost2 : (Gas.extendMemory (192 + 32 * n) [(192 + 32 * n, 32)]).cost =
      Gas.memoryCost (224 + 32 * n) - Gas.memoryCost (192 + 32 * n) := by
    rw [Gas.extendMemory_one (by omega) (by omega),
      show max (192 + 32 * n) ((192 + 32 * n + 32 + 31) / 32 * 32) = 224 + 32 * n by omega]
  have hcost3 : (Gas.extendMemory (224 + 32 * n) [(160, L), (224 + 32 * n, L)]).cost =
      Gas.memoryCost (224 + 64 * n) - Gas.memoryCost (224 + 32 * n) := by
    rw [Gas.extendMemory_two (by omega) (by omega),
      show max (max (224 + 32 * n) ((160 + L + 31) / 32 * 32)) ((224 + 32 * n + L + 31) / 32 * 32)
        = 224 + 64 * n by omega]
  have hcost4 : (Gas.extendMemory (224 + 64 * n) [(224 + 32 * n + L, 32)]).cost =
      Gas.memoryCost (256 + 64 * n) - Gas.memoryCost (224 + 64 * n) := by
    rw [Gas.extendMemory_one (by omega) (by omega),
      show max (224 + 64 * n) ((224 + 32 * n + L + 32 + 31) / 32 * 32) = 256 + 64 * n by omega]
  generalize Gas.memoryCost (160 + 32 * n) = c0 at *
  generalize Gas.memoryCost (192 + 32 * n) = c1 at *
  generalize Gas.memoryCost (224 + 32 * n) = c2 at *
  generalize Gas.memoryCost (224 + 64 * n) = c3 at *
  generalize Gas.memoryCost (256 + 64 * n) = cF at *
  -- the getter's epilogue, the return to `0x01f8`, `mload(0x40)`, the call of the encoder
  pwp_steps
  pwp_mload_in [hsize, hfmp]
  pwp_steps [hfmp]
  -- `mstore(head, 0x20)`
  apply WP.of_step
  case h =>
    apply step_mstore
    case hcode => pcode_fact
    case hstk => exact rfl
    case hgas => simp only [memoryCost, hsize, hhead, hcost1, Gas.veryLow]; omega
  case hs => same_frame
  dsimp only
  simp only [memoryCost, hsize, hhead, hcost1, Gas.veryLow]
  wp_generalize_gas g1 hg1
  wp_generalize_mem M1 hM1
  have hM1s : M1.size = 192 + 32 * n := by
    subst hM1; rw [Memory.size_storeWord, Memory.size_expand, hsize]
    simp only [Memory.wordsAfter, Memory.words, hsize, Nat.reduceEqDiff, ↓reduceIte]; omega
  have hM1w : M1.loadWord 128 = BitVec.ofNat 256 L := by
    subst hM1
    rw [Memory.loadWord, Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega),
      Memory.read_expand, hlen, toWord_ofWord]
  have hM1f : M1.loadWord 64 = BitVec.ofNat 256 (160 + 32 * n) := by
    subst hM1
    rw [Memory.loadWord_storeWord_of_disjoint _ _ _ _ (by omega), Memory.loadWord_expand, hfmp]
  have hM1d : M1.read 160 (32 * n) = Str.wordsFrom (m_world.sload m_msg.currentTarget) h n := by
    subst hM1; rw [Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand, hdata]
  have hM1h : M1.read (160 + 32 * n) 32 = ofWord 32#256 := by
    subst hM1; rw [Memory.read_storeWord]
  clear hM1 hsize hfmp hlen hdata
  pwp_steps
  pwp_mload_in [hM1s, hM1w]
  pwp_steps
  -- `mstore(head + 32, len)`
  have hx2 : (BitVec.ofNat 256 (160 + 32 * n) + 32#256).toNat = 192 + 32 * n := by
    simp only [BitVec.toNat_add, hhead, BitVec.reduceToNat]; omega
  apply WP.of_step
  case h =>
    apply step_mstore
    case hcode => pcode_fact
    case hstk => exact rfl
    case hgas => simp only [memoryCost, hM1s, hx2, hcost2, Gas.veryLow]; omega
  case hs => same_frame
  dsimp only
  simp only [memoryCost, hM1s, hx2, hcost2, Gas.veryLow]
  wp_generalize_gas g2 hg2
  wp_generalize_mem M2 hM2
  have hM2s : M2.size = 224 + 32 * n := by
    subst hM2; rw [Memory.size_storeWord, Memory.size_expand, hM1s]
    simp only [Memory.wordsAfter, Memory.words, hM1s, Nat.reduceEqDiff, ↓reduceIte]; omega
  have hM2f : M2.loadWord 64 = BitVec.ofNat 256 (160 + 32 * n) := by
    subst hM2
    rw [Memory.loadWord_storeWord_of_disjoint _ _ _ _ (by omega), Memory.loadWord_expand, hM1f]
  have hM2d : M2.read 160 L = (Str.wordsFrom (m_world.sload m_msg.currentTarget) h n).extract 0 L := by
    subst hM2
    rw [Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand,
      Memory.read_prefix _ hnL, hM1d]
  have hM2h : M2.read (160 + 32 * n) 64 = ofWord 32#256 ++ ofWord (BitVec.ofNat 256 L) := by
    subst hM2
    rw [Memory.read_64, Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand,
      hM1h, show 160 + 32 * n + 32 = 192 + 32 * n by omega, Memory.read_storeWord]
  clear hM2 hM1s hM1w hM1f hM1d hM1h
  pwp_steps
  -- `mcopy(head + 64, 0xa0, len)`
  have hx3 : (BitVec.ofNat 256 (160 + 32 * n) + 64#256).toNat = 224 + 32 * n := by
    simp only [BitVec.toNat_add, hhead, BitVec.reduceToNat]; omega
  apply WP.of_step
  case h =>
    apply step_mcopy
    case hcode => pcode_fact
    case hstk => exact rfl
    case hz => rw [hLn]; omega
    case hgas =>
      simp only [mcopyCost, hM2s, hx3, hLn, BitVec.reduceToNat, hcost3]
      rw [show (L + 31) / 32 = n by omega]
      omega
  case hs => same_frame
  dsimp only
  simp only [mcopyCost, hM2s, hx3, hLn, BitVec.reduceToNat, hcost3,
    show (L + 31) / 32 = n by omega]
  wp_generalize_gas g3 hg3
  wp_generalize_mem M3 hM3
  have hM3s : M3.size = 224 + 64 * n := by
    subst hM3; rw [Memory.size_mcopy _ _ _ _ (by omega), hM2s]; omega
  have hM3f : M3.loadWord 64 = BitVec.ofNat 256 (160 + 32 * n) := by
    subst hM3; rw [Memory.loadWord_mcopy_of_disjoint _ _ _ _ _ (by omega), hM2f]
  have hM3h : M3.read (160 + 32 * n) (64 + L) =
      ofWord 32#256 ++ ofWord (BitVec.ofNat 256 L) ++
        (Str.wordsFrom (m_world.sload m_msg.currentTarget) h n).extract 0 L := by
    subst hM3
    rw [Memory.read_add, Memory.read_mcopy_of_disjoint _ _ _ _ _ _ (by omega), hM2h,
      show 160 + 32 * n + 64 = 224 + 32 * n by omega, Memory.read_mcopy, hM2d]
  clear hM3 hM2s hM2f hM2d hM2h
  pwp_steps
  -- `mstore(head + 64 + len, 0)`
  have hx4 : (BitVec.ofNat 256 (160 + 32 * n) + BitVec.ofNat 256 L + 64#256).toNat =
      224 + 32 * n + L := by
    simp only [BitVec.toNat_add, hhead, hLn, BitVec.reduceToNat]
    omega
  apply WP.of_step
  case h =>
    apply step_mstore
    case hcode => pcode_fact
    case hstk => exact rfl
    case hgas => simp only [memoryCost, hM3s, hx4, hcost4, Gas.veryLow]; omega
  case hs => same_frame
  dsimp only
  simp only [memoryCost, hM3s, hx4, hcost4, Gas.veryLow]
  wp_generalize_gas g4 hg4
  wp_generalize_mem M4 hM4
  have hM4s : M4.size = 256 + 64 * n := by
    subst hM4; rw [Memory.size_storeWord, Memory.size_expand, hM3s]
    simp only [Memory.wordsAfter, Memory.words, hM3s, Nat.reduceEqDiff, ↓reduceIte]; omega
  have hM4f : M4.loadWord 64 = BitVec.ofNat 256 (160 + 32 * n) := by
    subst hM4
    rw [Memory.loadWord_storeWord_of_disjoint _ _ _ _ (by omega), Memory.loadWord_expand, hM3f]
  have hM4r : M4.read (160 + 32 * n) (64 + 32 * n) =
      Abi.encodeString (Str.longData (m_world.sload m_msg.currentTarget) h L) := by
    subst hM4
    rw [show 64 + 32 * n = (64 + L) + (32 * n - L) by omega, Memory.read_add,
      Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand, hM3h,
      show 160 + 32 * n + (64 + L) = 224 + 32 * n + L by omega,
      Memory.read_storeWord_prefix (hn := by omega), extract_ofWord_zero (by omega)]
    simp only [Abi.encodeString, Str.longData, ← hn, ByteArray.size_extract, Str.size_wordsFrom,
      show min L (32 * n) - 0 = L by omega, show n * 32 - L = 32 * n - L by omega,
      ByteArray.append_assoc]
  clear hM4 hM3s hM3f hM3h
  have hround : (L + 31) / 32 * 32 = 32 * n := by omega
  pwp_steps [Str.and_notMask31 (show L < 2 ^ 255 by omega), hround]
  pwp_mload_in [hM4s, hM4f]
  pwp_steps
  have hsz : (BitVec.ofNat 256 (160 + 32 * n) + BitVec.ofNat 256 (32 * n) + 64#256 -
      BitVec.ofNat 256 (160 + 32 * n)).toNat = 64 + 32 * n := by
    rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def]; simp only [BitVec.toNat_add, hhead, BitVec.toNat_ofNat]
      omega)]
    simp only [BitVec.toNat_add, hhead, BitVec.toNat_ofNat]
    omega
  pwp_return_in [hM4s, hhead, hsz, hM4r]
  exact ⟨trivial, trivial⟩

end Verified.Solmate.ERC4626

namespace Verified.Solmate.ERC4626
open Verified.Solmate.ERC20 QEDefi.ERC4626

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts EvmLean.Bytes

set_option maxHeartbeats 0 in
theorem vaultStringLong_wp {i : SolmateVault.Immutables} (m : Machine) {S slot : Word}
    {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hpc : m.frame.pc = 0x1339)
    (hs : m.frame.stack = S :: 1300#256 :: slot :: 504#256 :: rest)
    (hS : m.world.sload m.frame.msg.currentTarget slot = S) (hodd : S.toNat % 2 = 1)
    (hmem : m.frame.memory = initMemory)
    (hlen : rest.length ≤ 1000)
    (hg : 5000 + 2400 * ((Str.slotLen S + 31) / 32) +
      Gas.memoryCost (256 + 64 * ((Str.slotLen S + 31) / 32)) ≤ m.frame.gasLeft)
    (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun _ => False)
      (StringPost m (Str.decode m.ctx.crypto (m.world.sload m.frame.msg.currentTarget) slot)) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc hmem
  have hL := Str.slotLen_lt S
  by_cases hlong : 32 ≤ Str.slotLen S
  · have hdec : Str.decode m_ctx.crypto (m_world.sload m_msg.currentTarget) slot =
        some (Str.longData (m_world.sload m_msg.currentTarget)
          (arrayDataSlot m_ctx.crypto slot) (Str.slotLen S)) := by
      simp [Str.decode, hS, Str.slotOk, hodd, hlong]
    rw [hdec]
    generalize hn : (Str.slotLen S + 31) / 32 = n at hg
    have hmono := Gas.memoryCost_mono (show 160 ≤ 256 + 64 * n by omega)
    have hn64 : Str.slotLen S < 2 ^ 64 := by
      have := Gas.memoryCost_mono (show 0 ≤ 256 + 64 * n by omega); omega
    pwp_run_to 1390 [initMemory, hS, Str.and_one_of_odd hodd, Str.shr_one_of_odd hodd,
      Str.lt_32_of_ge hlong (by omega),
      Str.iszero_of_ne (show Str.slotLen S ≠ 0 by omega) (by omega),
      Str.div_32_mul_32 hL, Str.lt_31_of_gt (show 31 < Str.slotLen S by omega) (by omega)]
    wp_generalize_mem M0 hM0
    have hM0s : M0.size = 160 := by
      subst hM0; simp [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words]
    have hM0f : M0.loadWord 64 = BitVec.ofNat 256 (160 + 32 * n) := by
      subst hM0
      simp (disch := omega) only [Memory.loadWord_storeWord_of_disjoint, Memory.loadWord_expand,
        Memory.loadWord_storeWord]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (128 : Word).toNat = 128 from rfl]
      omega
    have hM0l : M0.read 128 32 = ofWord (BitVec.ofNat 256 (Str.slotLen S)) := by
      subst hM0
      simp (disch := omega) only [Memory.read_storeWord_of_disjoint, Memory.read_expand,
        Memory.read_storeWord]
    have hM0d : M0.read 160 (32 * 0) = Str.wordsFrom (m_world.sload m_msg.currentTarget)
        (m_ctx.crypto.keccak256 (ofWord slot)) 0 := Memory.read_zero_len _ _
    refine WP.bind_mono (vaultCopyLoop_wp (k := 0) (n := n) (R := 500 + 3 * n)
      (fmp := BitVec.ofNat 256 (160 + 32 * n)) _
      ⟨rfl, hj, rfl, rfl, rfl, ⟨_, _, _, rfl, rfl, (BitVec.add_zero _).symm, ?_⟩, hM0s, hM0f,
        hM0l, hM0d, ?_⟩ (by omega) hn.symm hlong hn64 (by simp only [List.length_cons]; omega))
      (fun _ _ _ h => h.elim) ?_
    · simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · dsimp only
      simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero]
      generalize Gas.memoryCost (256 + 64 * n) = cF at *
      generalize Gas.memoryCost 160 = c0 at *
      evm_gas
    · intro m' _ hst
      refine (vaultLongTail_wp m' hst hn.symm hlong hn64 (by omega) (by omega)).mono
        (fun _ _ h => h.elim) ?_
      rintro mf o - ⟨hw, ho⟩
      exact ⟨hw, ho⟩
  · have hdec : Str.decode m_ctx.crypto (m_world.sload m_msg.currentTarget) slot = none := by
      simp [Str.decode, hS, Str.slotOk, hodd, hlong]
    rw [hdec]
    pwp_steps [initMemory, hS, Str.and_one_of_odd hodd, Str.shr_one_of_odd hodd,
      Str.lt_32_of_lt (Nat.lt_of_not_le hlong)]
    exact ⟨rfl, _, rfl⟩

end Verified.Solmate.ERC4626

end
