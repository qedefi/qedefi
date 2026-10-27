import Verified.WeirdERC20.AMPL.Spec.PermitHigh

/-!
# AMPL's `permit` from enough gas: `permit_high`

`permit_high`: in a frame with no value, not static, with at least `150000` gas (and less than
`2⁶⁴`), whose name has at most 31 bytes, `permit` succeeds exactly when `PermitOk` holds, ending
as `PermitDone`, and reverts otherwise (no exceptional halt): `permit_high_late` past the
deadline, `permit_high_empty` and `permit_high_short` before it, through the tails of
`PermitHigh`.
-/

set_option linter.unusedSimpArgs false

namespace Verified.WeirdERC20.AMPL.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open EvmLogic.Program.Nested
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC4626 Verified.WeirdERC20.AMPL.Contracts
open Verified.WeirdERC20.AMPL.Spec Verified.Solady.Spec.AnyGas
open Verified.Solady.Spec (ite_neg' ite_pos')

/-- `permit`'s end from enough gas: success exactly when `PermitOk`, else a revert. -/
def PermitHigh (m mf : Machine) (o : Outcome) : Prop :=
  (PermitOk m → o = .success .empty ∧ PermitDone m mf) ∧ (¬ PermitOk m → ∃ out, o = .revert out)

/-- `PermitOk` from the facts of a successful run (the nonce bound as a number). -/
theorem permitOk_of' (m : Machine) (nb' : ByteArray)
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
    (hno : (m.world.sload m.frame.msg.currentTarget
        (nonceSlot m.ctx.crypto (pOwner m.frame.msg.data))).toNat + 1 < 2 ^ 256) :
    PermitOk m := by
  refine ⟨hv, hst, hd, hts, ?_, hno⟩
  unfold amplRec amplDigest amplDs
  rw [ite_neg' (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq, ← hnb]
  rw [and255_idem] at hr
  exact hr

/-- The recovery `PermitOk` asks for, in the form the run computes it. -/
theorem rec_of_permitOk (m : Machine) (nb' : ByteArray)
    (hnb : nb' = nameBytes07 m.ctx.crypto (m.world.sload m.frame.msg.currentTarget))
    (hok : PermitOk m) :
    (ecrecoverAddress? m.ctx.crypto (digest m.ctx.crypto
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
        (argWord m.frame.msg.data 6)).getD 0 = pOwner m.frame.msg.data := by
  have h := hok.2.2.2.2.1
  have hd := hok.2.2.1
  unfold amplRec amplDigest amplDs at h
  rw [ite_neg' (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq, ← hnb] at h
  rw [and255_idem]
  exact h

set_option maxHeartbeats 0 in
/-- `permit` past its deadline reverts. -/
theorem permit_high_late (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xd505accf) (h228 : 228 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hst : m.frame.msg.isStatic = false) (hg : 150000 ≤ m.frame.gasLeft)
    (hgl : m.frame.gasLeft < 2 ^ 64)
    (hshort : nameLen07 (m.world.sload m.frame.msg.currentTarget 51#256) ≤ 31)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hdl : ¬ (ofNat m.ctx.block.timestamp).toNat ≤ (argWord m.frame.msg.data 3).toNat) :
    Halts m (PermitHigh m) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 224) (by omega) hsz
  apply WP.halts_of_false
  have hgt : Word.gt (ofNat m.ctx.block.timestamp) (Bytes.toWord (readBytes m.frame.msg.data 100 32)) =
      1#256 := Str.gt_eq_one (by simp only [argWord, Nat.reduceMul, Nat.reduceAdd] at hdl; omega)
  solady_fresh_intro
  pwp_xsteps [hval, hst, hsel', hz, hl, hgt, Abi.shr_calldataload_zero, and_mask_lit, mask_lit_and,
    Word.toAddress_ofAddress, Memory.read_64]
  exact ⟨fun hok => absurd hok.2.2.2.1 hdl, fun _ => ⟨_, rfl⟩⟩

set_option maxHeartbeats 0 in
/-- `permit` before its deadline, with an empty `name`. -/
theorem permit_high_empty (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xd505accf) (h228 : 228 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hst : m.frame.msg.isStatic = false) (hg : 150000 ≤ m.frame.gasLeft)
    (hgl : m.frame.gasLeft < 2 ^ 64)
    (hshort : nameLen07 (m.world.sload m.frame.msg.currentTarget 51#256) ≤ 31)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hdl : (ofNat m.ctx.block.timestamp).toNat ≤ (argWord m.frame.msg.data 3).toNat)
    (hL0 : nameLen07 (m.world.sload m.frame.msg.currentTarget 51#256) = 0) :
    Halts m (PermitHigh m) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 224) (by omega) hsz
  apply WP.halts_of_false
  have hge : Word.gt (ofNat m.ctx.block.timestamp) (Bytes.toWord (readBytes m.frame.msg.data 100 32)) =
      0#256 := Str.gt_eq_zero (by simp only [argWord, Nat.reduceMul, Nat.reduceAdd] at hdl; omega)
  solady_fresh_intro
  pwp_run_to 2689 [hval, hst, hsel', hz, hl, hge, hL0, lenWord_eq, Abi.shr_calldataload_zero,
    and_mask_lit, mask_lit_and, Word.toAddress_ofAddress, Memory.read_64]
  refine tail_high_empty _ (nameLen07 (m_world.sload m_msg.currentTarget 51#256))
    _ _ _ _ _ _ _ _ _ rfl hj rfl rfl ?_ ?_ ?_ hL0 hst ?_ ?_ hstd hdel ?_ ?_
  · dsimp only
    simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord,
      Memory.loadWord_storeWord_of_disjoint, hL0]
  · dsimp only
    simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord,
      Memory.loadWord_storeWord_of_disjoint, hL0]
  · dsimp only
    simp [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words,
      Nat.max_def]
  · dsimp only; evm_gas
  · dsimp only; omega
  · intro mf hd hr hno hw ht hcr hlg
    dsimp only [dsOfMem] at hd hr hno hw ht hcr hlg
    simp (disch := omega) only [Memory.read_expand, Memory.read_storeWord_of_disjoint,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt, Memory.read_192, hL0, read_zero,
      read32_storeWord_eq, extract_ofWord_32] at hr
    refine ⟨fun _ => ⟨rfl, permitDone_of _ _ hw ht hcr ?_⟩, fun hn => absurd ?_ hn⟩
    · rw [hlg]; simp only [warmKey_logs]; rfl
    · exact permitOk_of' _ _ hval hst hd hdl (by simp only [nameBytes07, hL0, ite_true]) hr hno
  · intro mf out hnc
    refine ⟨fun hok => absurd ⟨hok.2.2.1, ?_, hok.2.2.2.2.2⟩ hnc, fun _ => ⟨out, rfl⟩⟩
    dsimp only [dsOfMem]
    simp (disch := omega) only [Memory.read_expand, Memory.read_storeWord_of_disjoint,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt, Memory.read_192, hL0, read_zero,
      read32_storeWord_eq, extract_ofWord_32]
    have h := (rec_of_permitOk _ _ rfl hok :)
    simp only [nameBytes07, hL0, ite_true] at h
    exact h

set_option maxHeartbeats 0 in
/-- `permit` before its deadline, with a `name` of 1 to 31 bytes. -/
theorem permit_high_short (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xd505accf) (h228 : 228 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hst : m.frame.msg.isStatic = false) (hg : 150000 ≤ m.frame.gasLeft)
    (hgl : m.frame.gasLeft < 2 ^ 64)
    (hshort : nameLen07 (m.world.sload m.frame.msg.currentTarget 51#256) ≤ 31)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hdl : (ofNat m.ctx.block.timestamp).toNat ≤ (argWord m.frame.msg.data 3).toNat)
    (hL0 : ¬ nameLen07 (m.world.sload m.frame.msg.currentTarget 51#256) = 0) :
    Halts m (PermitHigh m) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 224) (by omega) hsz
  have hLlt := nameLen07_lt (m.world.sload m.frame.msg.currentTarget 51#256)
  apply WP.halts_of_false
  have hge : Word.gt (ofNat m.ctx.block.timestamp) (Bytes.toWord (readBytes m.frame.msg.data 100 32)) =
      0#256 := Str.gt_eq_zero (by simp only [argWord, Nat.reduceMul, Nat.reduceAdd] at hdl; omega)
  have hLw0 : Word.iszero (BitVec.ofNat 256 (nameLen07 (m.world.sload m.frame.msg.currentTarget
      51#256))) = 0#256 := Str.iszero_of_ne hL0 (by omega)
  have hLw31 := Str.lt_31_of_le hshort
  have h416 : 384 + 32 * ((nameLen07 (m.world.sload m.frame.msg.currentTarget 51#256) + 31) / 32)
      = 416 := by omega
  solady_fresh_intro
  pwp_run_to 2689 [hval, hst, hsel', hz, hl, hge, hLw0, hLw31, lenWord_eq, Abi.shr_calldataload_zero,
    and_mask_lit, mask_lit_and, Word.toAddress_ofAddress, Memory.read_64]
  refine tail_high_short _ (nameLen07 (m_world.sload m_msg.currentTarget 51#256))
    _ _ _ _ _ _ _ _ _ rfl hj rfl rfl ?_ ?_ ?_ (Nat.pos_of_ne_zero hL0) hshort hst ?_ ?_ hstd hdel
    ?_ ?_
  · dsimp only
    simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord,
      Memory.loadWord_storeWord_of_disjoint]
  · dsimp only
    simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord,
      Memory.loadWord_storeWord_of_disjoint]
    rw [free_eq (nameLen07_lt _), h416]
  · dsimp only
    simp [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words,
      Nat.max_def]
  · dsimp only; evm_gas
  · dsimp only; omega
  · intro mf hd hr hno hw ht hcr hlg
    dsimp only [dsOfMem] at hd hr hno hw ht hcr hlg
    simp (disch := omega) only [Memory.read_expand, Memory.read_storeWord_of_disjoint,
      read_storeWord_prefix_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, Memory.read_192,
      read32_storeWord_eq, extract_ofWord_32, div_mul_256] at hr
    refine ⟨fun _ => ⟨rfl, permitDone_of _ _ hw ht hcr ?_⟩, fun hn => absurd ?_ hn⟩
    · rw [hlg]; simp only [warmKey_logs]; rfl
    · exact permitOk_of' _ _ hval hst hd hdl (by simp only [nameBytes07, hL0, hshort, ite_false, ite_true]) hr hno
  · intro mf out hnc
    refine ⟨fun hok => absurd ⟨hok.2.2.1, ?_, hok.2.2.2.2.2⟩ hnc, fun _ => ⟨out, rfl⟩⟩
    dsimp only [dsOfMem]
    simp (disch := omega) only [Memory.read_expand, Memory.read_storeWord_of_disjoint,
      read_storeWord_prefix_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, Memory.read_192,
      read32_storeWord_eq, extract_ofWord_32, div_mul_256]
    have h := (rec_of_permitOk _ _ rfl hok :)
    simp only [nameBytes07, hL0, hshort, ite_false, ite_true] at h
    exact h

/-- **`permit` from enough gas, for a name of at most 31 bytes.** -/
theorem permit_high (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xd505accf) (h228 : 228 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hst : m.frame.msg.isStatic = false) (hg : 150000 ≤ m.frame.gasLeft)
    (hgl : m.frame.gasLeft < 2 ^ 64)
    (hshort : nameLen07 (m.world.sload m.frame.msg.currentTarget 51#256) ≤ 31)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none) :
    Halts m (PermitHigh m) := by
  by_cases hdl : (ofNat m.ctx.block.timestamp).toNat ≤ (argWord m.frame.msg.data 3).toNat
  · by_cases hL0 : nameLen07 (m.world.sload m.frame.msg.currentTarget 51#256) = 0
    · exact permit_high_empty m hf hsel h228 hsz hval hst hg hgl hshort hstd hdel hdl hL0
    · exact permit_high_short m hf hsel h228 hsz hval hst hg hgl hshort hstd hdel hdl hL0
  · exact permit_high_late m hf hsel h228 hsz hval hst hg hgl hshort hstd hdel hdl

end Verified.WeirdERC20.AMPL.Spec.Malformed
