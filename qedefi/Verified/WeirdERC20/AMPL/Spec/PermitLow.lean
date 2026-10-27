import Verified.WeirdERC20.AMPL.Spec.PermitTail
import Verified.WeirdERC20.AMPL.Spec.PermitLoop

/-!
# AMPL's `permit` at any gas

`permit_low`: a `permit` frame with all seven argument words, at any gas, value, depth and
staticness, fails or succeeds as `PermitLow` says. That is, it succeeds only when `PermitOk`
holds, and then ends as `PermitDone`. The run goes through the dispatcher and the deadline
check, hashes the struct, calls `name()` (an empty name, a short one, or a long one copied by
the loop, `loop_low`), and ends with `tail_low`.
-/

set_option linter.unusedSimpArgs false

namespace Verified.WeirdERC20.AMPL.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open EvmLogic.Program.Nested
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC4626 Verified.WeirdERC20.AMPL.Contracts
open Verified.WeirdERC20.AMPL.Spec Verified.Solady.Spec.AnyGas
open Verified.Solady.Spec (LowHalts ite_neg' ite_pos')

theorem lenWord_eq (S : Word) :
    (S &&& (S &&& 1#256).iszero * 256#256 +
      115792089237316195423570985008687907853269984665640564039457584007913129639935#256).div
        2#256 = BitVec.ofNat 256 (nameLen07 S) := by
  apply BitVec.eq_of_toNat_eq
  have hS := S.isLt
  by_cases h : S.toNat % 2 = 0
  · have h1 : (S &&& 1#256).iszero = 1#256 := by
      rw [Str.and_one_of_even h]; rfl
    rw [h1]
    have hm : (1#256 * 256#256 +
        115792089237316195423570985008687907853269984665640564039457584007913129639935#256) =
        255#256 := by decide
    rw [hm]
    simp only [Word.div, BitVec.toNat_udiv, BitVec.toNat_and, BitVec.toNat_ofNat, nameLen07, h,
      ite_true]
    rw [show (255 : Nat) % 2 ^ 256 = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    norm_num
    omega
  · have h1 : (S &&& 1#256).iszero = 0#256 := by
      rw [Str.and_one_of_odd (by omega)]; rfl
    rw [h1]
    have hm : (0#256 * 256#256 +
        115792089237316195423570985008687907853269984665640564039457584007913129639935#256) =
        BitVec.allOnes 256 := by decide
    rw [hm, BitVec.and_allOnes]
    simp only [Word.div, BitVec.toNat_udiv, BitVec.toNat_ofNat, nameLen07, h, ite_false]
    norm_num
    omega

theorem nameLen07_lt (S : Word) : nameLen07 S < 2 ^ 255 := by
  have := S.isLt
  unfold nameLen07; split <;> omega

/-- The free memory pointer after `name()` copied `L` bytes from pointer `352`. -/
theorem free_eq {L : Nat} (hL : L < 2 ^ 255) :
    32#256 + (352#256 + 32#256 * Word.div (BitVec.ofNat 256 L + 31#256) 32#256) =
      BitVec.ofNat 256 (384 + 32 * ((L + 31) / 32)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Word.div, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_udiv, BitVec.toNat_ofNat]
  norm_num
  omega


theorem nonce_ok {n : Word} (h : (Word.lt (1#256 + n) n).iszero ≠ 0) : n.toNat + 1 < 2 ^ 256 := by
  by_contra hc
  apply h
  have hn := n.isLt
  have he : n.toNat = 2 ^ 256 - 1 := by omega
  have h0 : 1#256 + n = 0#256 := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, he]; norm_num
  rw [h0]
  have : BitVec.ult 0#256 n = true := by simp [BitVec.ult, he]
  simp [Word.lt, Word.ofBool, this, Word.iszero]

theorem and255_idem (x : Word) : 255#256 &&& (x &&& 255#256) = x &&& 255#256 := by
  rw [BitVec.and_comm, BitVec.and_assoc, BitVec.and_self]

theorem len_le31 {L : Nat} (hL : L < 2 ^ 255) (h : Word.lt 31#256 (BitVec.ofNat 256 L) = 0) :
    L ≤ 31 := by
  have := (Word.lt_eq_zero_iff _ _).1 h
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega)] at this
  omega

theorem len_ne0 {L : Nat} (hL : L < 2 ^ 255) (h : Word.iszero (BitVec.ofNat 256 L) = 0) :
    L ≠ 0 := by
  intro h0
  subst h0
  exact absurd h (by decide)

theorem len_eq0 {L : Nat} (hL : L < 2 ^ 255) (h : Word.iszero (BitVec.ofNat 256 L) ≠ 0) :
    L = 0 := by
  have := Verified.Solady.Spec.eq_zero_of_iszero_ne h
  have h2 := congrArg BitVec.toNat this
  simp only [BitVec.toNat_ofNat] at h2
  rw [Nat.mod_eq_of_lt (by omega)] at h2
  simpa using h2

theorem len_gt31 {L : Nat} (hL : L < 2 ^ 255) (h : Word.lt 31#256 (BitVec.ofNat 256 L) ≠ 0) :
    31 < L := by
  by_contra hc
  apply h
  rw [Word.lt_eq_zero_iff]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem read_prefix (M : Memory) (off L n : Nat) (h : L ≤ n) :
    (M.read off n).extract 0 L = M.read off L := by
  apply Bytes.ext_getD (by simp [Memory.read, Bytes.size_readPadded]; omega)
  intro j hj
  simp only [ByteArray.size_extract, Memory.read, Bytes.size_readPadded] at hj
  rw [Bytes.getD_extract, Memory.read, Memory.read, Bytes.getD_readPadded, Bytes.getD_readPadded]
  simp only [Nat.zero_add, show j < n by omega, show j < L by omega, ite_true]

theorem loopMem_loadWord_below (sl : Word → Word) (k : Nat) (M : Memory) (dst p : Word)
    (off : Nat) (h : off + 32 ≤ dst.toNat) (hb : dst.toNat + 32 * k < 2 ^ 256) :
    (loopMem sl M dst p k).loadWord off = M.loadWord off := by
  simp only [Memory.loadWord]
  rw [loopMem_read_below sl k M dst p off 32 h hb]

theorem read_loopMem' (sl : Word → Word) (k : Nat) (M : Memory) (dst p : Word) (off : Nat)
    (h : dst.toNat = off) (hb : off + 32 * k < 2 ^ 256) :
    (loopMem sl M dst p k).read off (32 * k) = Str.wordsFrom sl p k := by
  subst h; exact read_loopMem sl k M dst p hb

theorem read_zero (M : Memory) (off : Nat) : M.read off 0 = ByteArray.empty :=
  eqEmpty (by simp [Memory.read, Bytes.size_readPadded])

theorem div_mul_256 (S : Word) :
    Word.div S 256#256 * 256#256 = BitVec.ofNat 256 (S.toNat / 256 * 256) := by
  apply BitVec.eq_of_toNat_eq
  have := S.isLt
  simp only [Word.div, BitVec.toNat_mul, BitVec.toNat_udiv, BitVec.toNat_ofNat]

/-- **`PermitOk` from the facts of a successful run.** -/
theorem permitOk_of (m : Machine) (nb' : ByteArray)
    (hv : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hd : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hts : (ofNat m.ctx.block.timestamp).toNat ≤ (argWord m.frame.msg.data 3).toNat)
    (hnb : nb' = nameBytes07 m.ctx.crypto (m.world.sload m.frame.msg.currentTarget))
    (hr : (ecrecoverAddress? m.ctx.crypto (digest m.ctx.crypto
        (m.ctx.crypto.keccak256 (Bytes.ofWord DOMAIN_TYPEHASH ++
          (Bytes.ofWord (m.ctx.crypto.keccak256 nb') ++ (Bytes.ofWord VERSION_HASH ++
            (Bytes.ofWord (ofNat m.ctx.block.chainId) ++
              Bytes.ofWord (Word.ofAddress m.frame.msg.currentTarget))))))
        (structHash m.ctx.crypto (pOwner m.frame.msg.data) (pSpender m.frame.msg.data)
          (argWord m.frame.msg.data 2)
          (m.world.sload m.frame.msg.currentTarget
            (nonceSlot m.ctx.crypto (pOwner m.frame.msg.data)))
          (argWord m.frame.msg.data 3)))
        (255#256 &&& (argWord m.frame.msg.data 4 &&& 255#256)) (argWord m.frame.msg.data 5)
        (argWord m.frame.msg.data 6)).getD 0 = pOwner m.frame.msg.data)
    (hn : (Word.lt (1#256 + m.world.sload m.frame.msg.currentTarget
      (nonceSlot m.ctx.crypto (pOwner m.frame.msg.data)))
      (m.world.sload m.frame.msg.currentTarget
        (nonceSlot m.ctx.crypto (pOwner m.frame.msg.data)))).iszero ≠ 0) :
    PermitOk m := by
  refine ⟨hv, hst, hd, hts, ?_, nonce_ok hn⟩
  unfold amplRec amplDigest amplDs
  rw [ite_neg' (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq, ← hnb]
  rw [and255_idem] at hr
  exact hr

/-- **`PermitDone` from the end of a successful run.** -/
theorem permitDone_of (m mf : Machine)
    (hw : mf.world = (m.world.sstore m.frame.msg.currentTarget
          (m.ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress (pOwner m.frame.msg.data)) ++
            Bytes.ofWord 160#256))
          (1#256 + m.world.sload m.frame.msg.currentTarget
            (nonceSlot m.ctx.crypto (pOwner m.frame.msg.data)))).sstore m.frame.msg.currentTarget
        (m.ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress (pSpender m.frame.msg.data)) ++
          Bytes.ofWord (m.ctx.crypto.keccak256
            (Bytes.ofWord (Word.ofAddress (pOwner m.frame.msg.data)) ++ Bytes.ofWord 159#256))))
        (argWord m.frame.msg.data 2))
    (ht : mf.transient = m.transient) (hc : mf.createdAccounts = m.createdAccounts)
    (hl : mf.frame.sub.logs = m.frame.sub.logs.push (approvalLog m.frame.msg.currentTarget
      (pOwner m.frame.msg.data) (pSpender m.frame.msg.data) (argWord m.frame.msg.data 2))) :
    PermitDone m mf := by
  refine ⟨?_, ht, hc, hl⟩
  rw [hw, BitVec.add_comm 1#256]
  rfl

set_option maxHeartbeats 0 in
theorem permit_low (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xd505accf) (h228 : 228 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none) :
    LowHalts m (PermitLow m) := by
  intro H hF hok
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 224) (by omega) hsz
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps stop_at [4891] [hsel', hz, hl, Abi.shr_calldataload_zero, and_mask_lit, mask_lit_and]
  refine wp_timestamp hF (by pcode_fact) fun _ _ => ?_
  dsimp only
  hwp_steps stop_at [2648] [hsel', hz, hl, Abi.shr_calldataload_zero, and_mask_lit, mask_lit_and,
    Word.toAddress_ofAddress]
  refine wp_chainid hF (by pcode_fact) fun _ _ => ?_
  dsimp only
  hwp_steps stop_at [1911, 2689] [hsel', hz, hl, Abi.shr_calldataload_zero, and_mask_lit,
    mask_lit_and, Word.toAddress_ofAddress, lenWord_eq]
  · refine tail_low hF _ (384 + 32 * ((nameLen07 (m_world.sload m_msg.currentTarget 51#256) + 31) / 32)) (BitVec.ofNat 256 (nameLen07 (m_world.sload m_msg.currentTarget 51#256)))
      _ _ _ _ _ _ _ _ _ rfl hj rfl rfl ?_ ?_ (by omega) (by have := nameLen07_lt (m_world.sload m_msg.currentTarget 51#256); omega)
      hstd hdel ?_
    · simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord,
        Memory.loadWord_storeWord_of_disjoint]
    · simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord,
        Memory.loadWord_storeWord_of_disjoint]
      exact free_eq (nameLen07_lt _)
    · intro mf hd hst hr hn hw ht hcr hlg
      apply hok
      refine ⟨rfl, ?_, ?_⟩
      · dsimp only [dsOfMem] at hd hst hr
        have hL := nameLen07_lt (m_world.sload m_msg.currentTarget 51#256)
        have hL31 := len_le31 hL ‹Word.lt (31#256) _ = 0›
        have hL0 := len_ne0 hL ‹Word.iszero _ = 0›
        simp (disch := omega) only [Memory.read_expand, Memory.read_storeWord_of_disjoint,
          read_storeWord_prefix_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, Memory.read_192,
          read32_storeWord_eq, extract_ofWord_32, div_mul_256] at hr
        refine permitOk_of _ _ (Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›) hst hd
          (Verified.Solady.Spec.le_of_iszero_gt ‹_›) ?_ hr hn
        simp only [nameBytes07, hL0, hL31, ite_false, ite_true]
      · exact permitDone_of _ _ hw ht hcr (by rw [hlg]; simp only [warmKey_logs]; rfl)
  · have hL := nameLen07_lt (m_world.sload m_msg.currentTarget 51#256)
    have hL0 := len_ne0 hL ‹Word.iszero _ = 0›
    have hL32 := len_gt31 hL ‹Word.lt (31#256) _ ≠ 0›
    have hL' : nameLen07 (m_world.sload m_msg.currentTarget 51#256) < 2 ^ 256 := by omega
    have he : (384#256 + BitVec.ofNat 256 (nameLen07 (m_world.sload m_msg.currentTarget 51#256))).toNat
        = 384 + nameLen07 (m_world.sload m_msg.currentTarget 51#256) := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    have h384 : (384#256 : Word).toNat = 384 := rfl
    refine loop_low hF ((nameLen07 (m_world.sload m_msg.currentTarget 51#256) + 31) / 32 - 1) _
      384#256 _ _ _ rfl hj rfl rfl (by rw [h384]; omega) (by rw [h384, he]; omega)
      (by rw [h384, he]; omega) fun g sb hsb => ?_
    dsimp only
    hwp_steps stop_at [2689] [hsel', hz, hl, Abi.shr_calldataload_zero, and_mask_lit,
      mask_lit_and, Word.toAddress_ofAddress, lenWord_eq]
    refine tail_low hF _ (384 + 32 * ((nameLen07 (m_world.sload m_msg.currentTarget 51#256) + 31) / 32)) (BitVec.ofNat 256 (nameLen07 (m_world.sload m_msg.currentTarget 51#256)))
      _ _ _ _ _ _ _ _ _ rfl hj rfl rfl ?_ ?_ (by omega) (by omega) hstd hdel ?_
    · rw [loopMem_loadWord_below _ _ _ _ _ _ (by rw [h384]) (by rw [h384]; omega)]
      simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord,
        Memory.loadWord_storeWord_of_disjoint]
    · rw [loopMem_loadWord_below _ _ _ _ _ _ (by rw [h384]; omega) (by rw [h384]; omega)]
      simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord,
        Memory.loadWord_storeWord_of_disjoint]
      exact free_eq hL
    · intro mf hd hst hr hn hw ht hcr hlg
      apply hok
      refine ⟨rfl, ?_, ?_⟩
      · dsimp only [dsOfMem] at hd hst hr
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL'] at hr
        rw [← read_prefix _ 384 _ (32 * ((nameLen07 (m_world.sload m_msg.currentTarget 51#256)
          + 31) / 32 - 1 + 1)) (by omega), read_loopMem' _ _ _ _ _ _ h384 (by omega)] at hr
        simp (disch := omega) only [Memory.read_expand, Memory.read_storeWord_of_disjoint,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt, Memory.read_192,
          read32_storeWord_eq, extract_ofWord_32] at hr
        refine permitOk_of _ _ (Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›) hst hd
          (Verified.Solady.Spec.le_of_iszero_gt ‹_›) ?_ hr hn
        simp only [nameBytes07, hL0, ite_false, show ¬ nameLen07 (m_world.sload m_msg.currentTarget
          51#256) ≤ 31 by omega, Str.longData]
        congr 2
        omega
      · exact permitDone_of _ _ hw ht hcr (by rw [hlg]; simp only [warmKey_logs]; rw [hsb]; rfl)
  · refine tail_low hF _ (384 + 32 * ((nameLen07 (m_world.sload m_msg.currentTarget 51#256) + 31) / 32)) (BitVec.ofNat 256 (nameLen07 (m_world.sload m_msg.currentTarget 51#256)))
      _ _ _ _ _ _ _ _ _ rfl hj rfl rfl ?_ ?_ (by omega) (by have := nameLen07_lt (m_world.sload m_msg.currentTarget 51#256); omega)
      hstd hdel ?_
    · simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord,
        Memory.loadWord_storeWord_of_disjoint]
    · simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord,
        Memory.loadWord_storeWord_of_disjoint]
      exact free_eq (nameLen07_lt _)
    · intro mf hd hst hr hn hw ht hcr hlg
      apply hok
      refine ⟨rfl, ?_, ?_⟩
      · dsimp only [dsOfMem] at hd hst hr
        have hL := nameLen07_lt (m_world.sload m_msg.currentTarget 51#256)
        have hL0 := len_eq0 hL ‹Word.iszero _ ≠ 0›
        simp (disch := omega) only [Memory.read_expand, Memory.read_storeWord_of_disjoint,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt, Memory.read_192, hL0, read_zero,
          read32_storeWord_eq, extract_ofWord_32] at hr
        refine permitOk_of _ _ (Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›) hst hd
          (Verified.Solady.Spec.le_of_iszero_gt ‹_›) ?_ hr hn
        simp only [nameBytes07, hL0, ite_true]
      · exact permitDone_of _ _ hw ht hcr (by rw [hlg]; simp only [warmKey_logs]; rfl)

end Verified.WeirdERC20.AMPL.Spec.Malformed
