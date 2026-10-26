import Verified.Solmate.ERC20.Spec.PermitLongGas
import Verified.Solmate.ERC20.Spec.PermitModel
import Verified.Solmate.ERC4626.StringsCommon

namespace Verified.Solmate.ERC20.Spec
open QEDefi.ERC4626 Verified.Solmate.ERC20.Permit
open Verified.Solmate.ERC20.Spec.PermitLongGas

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts

/-- The memory size in the copy loop of `0x0a66` after `k` words: `96` before the first. -/
def plSz (k : Nat) : Nat := if k = 0 then 96 else 128 + 32 * k

/-- The stack of the copy loop of `0x0a66` (head `0x0ad2`) after `k` words. -/
def plStk (d Lw S : Word) (tl : List Word) (k : Nat) : List Word :=
  BitVec.ofNat 256 (32 * k) :: (d + BitVec.ofNat 256 k) :: 1#256 :: 1#256 :: Lw :: S :: 0#256 ::
    0#256 :: 128#256 :: 0#256 :: tl

/-- **The copy loop of `0x0a66` after `k` words**, in the frame of `b` (where
`DOMAIN_SEPARATOR()` was entered): `name`'s first `k` data words copied to `0x80`; the gas covers
`R`, 2300 per remaining word and the final memory, and `b`'s gas is at most what is left plus
3000, 2300 per copied word and the memory paid. -/
def PlCopy (ia : SolmateAsset.Immutables) (b : Machine) (d Lw S : Word) (n R : Nat)
    (tl : List Word) (k pc : Nat) (m : Machine) : Prop :=
  b.frame.code = SolmateAsset.runtimeCodeWith ia ∧
  JumpTable b.frame.jumpDests (SolmateAsset.runtimeCodeWith ia) ∧
  ∃ mem g sub, m = b.resumeWith pc (plStk d Lw S tl k) mem g b.frame.returnData sub ∧
    mem.size = plSz k ∧ mem.loadWord 64 = 128#256 ∧
    mem.read 128 (32 * k) = Str.wordsFrom (b.world.sload b.frame.msg.currentTarget) d k ∧
    R + 2300 * (n - k) + Gas.memoryCost (128 + 32 * n) ≤ g + Gas.memoryCost (plSz k) ∧
    b.frame.gasLeft ≤ g + 3000 + 2300 * k + Gas.memoryCost (plSz k) ∧ g ≤ b.frame.gasLeft ∧
    sub.logs = b.frame.sub.logs

theorem plSz_succ (k : Nat) : plSz (k + 1) = 160 + 32 * k := by
  simp only [plSz]; split <;> omega

theorem plSz_le (k : Nat) : plSz k ≤ 128 + 32 * k := by
  simp only [plSz]; split <;> omega

theorem plSz_mod (k : Nat) : plSz k % 32 = 0 := by
  simp only [plSz]; split <;> omega

theorem plSz_ge (k : Nat) : 96 ≤ plSz k := by
  simp only [plSz]; split <;> omega

set_option maxHeartbeats 0 in
/-- One word of the copy loop. -/
theorem plCopy_body {ia : SolmateAsset.Immutables} {b : Machine} {d Lw S : Word} {n R L k : Nat}
    {tl : List Word} (m : Machine) (hst : PlCopy ia b d Lw S n R tl k 2770 m) (hkn : k < n)
    (hn : n = (L + 31) / 32) (hLw : Lw.toNat = L) (hL2 : L < 2 ^ 255) (htl : tl.length ≤ 1010) :
    WP m (fun m' => (k + 1 < n ∧ PlCopy ia b d Lw S n R tl (k + 1) 2770 m') ∨
      (k + 1 = n ∧ PlCopy ia b d Lw S n R tl (k + 1) 2798 m')) (fun _ _ => False) := by
  have hagree := assetJumpDestsAgree ia
  obtain ⟨hc, hj, mem, g, sub, rfl, hsize, hfmp, hdata, hg, hgb, hgu, hlog⟩ := hst
  obtain ⟨b_ctx, b_pre, b_world, b_transient, b_originalWorld, b_created,
    ⟨b_msg, b_code, b_jumpDests, b_pc, b_stack, b_memory, b_gasLeft, b_returnData, b_sub,
      b_snapshot, b_kind⟩, b_parents⟩ := b
  dsimp only [Machine.resumeWith, plStk] at *
  subst hc
  have hL : 32 * k < L := by omega
  have hL' : L < 2 ^ 256 := hLw ▸ Lw.isLt
  have hlt : Word.lt (BitVec.ofNat 256 (32 * k)) Lw = 1#256 :=
    (Word.lt_eq_one_iff _ _).2 (by rw [hLw, Str.toNat_ofNat_of_lt (by omega)]; omega)
  have hm1 := Gas.memoryCost_mono (show plSz k ≤ 160 + 32 * k by have := plSz_le k; omega)
  have hm2 := Gas.memoryCost_mono (show 160 + 32 * k ≤ 128 + 32 * n by omega)
  have hcost : (Gas.extendMemory (plSz k) [(128 + 32 * k, 32)]).cost =
      Gas.memoryCost (160 + 32 * k) - Gas.memoryCost (plSz k) := by
    have := plSz_le k
    have := plSz_ge k
    rw [Gas.extendMemory_one (by omega) (plSz_mod k),
      show max (plSz k) ((128 + 32 * k + 32 + 31) / 32 * 32) = 160 + 32 * k by omega]
  have hx : (BitVec.ofNat 256 (32 * k) + 128#256).toNat = 128 + 32 * k := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  generalize hc0 : Gas.memoryCost (plSz k) = c0 at *
  generalize hc1 : Gas.memoryCost (160 + 32 * k) = c1 at *
  generalize hcF : Gas.memoryCost (128 + 32 * n) = cF at *
  pwp_steps [hlt]
  have hsl := sloadCost_le (storageKeyWarm sub.accessedStorageKeys b_msg.currentTarget
    (d + BitVec.ofNat 256 k))
  apply WP.of_step
  case h =>
    apply step_mstore
    case hcode => pcode_fact
    case hstk => exact rfl
    case hgas =>
      simp only [memoryCost, hsize, hx, hcost, Gas.veryLow]
      omega
  case hs => same_frame
  dsimp only
  simp only [memoryCost, hsize, hx, hcost, Gas.veryLow]
  have hptr' : d + BitVec.ofNat 256 k + 1#256 = d + BitVec.ofNat 256 (k + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hi' : 32#256 + BitVec.ofNat 256 (32 * k) = BitVec.ofNat 256 (32 * (k + 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hM'size : ((mem.expand (128 + 32 * k) 32).storeWord (128 + 32 * k)
      (b_world.sload b_msg.currentTarget (d + BitVec.ofNat 256 k))).size = plSz (k + 1) := by
    rw [Memory.size_storeWord, Memory.size_expand, hsize, plSz_succ]
    have := plSz_le k
    simp only [Memory.wordsAfter, Memory.words, hsize, Nat.reduceEqDiff, ↓reduceIte]
    omega
  have hM'fmp : ((mem.expand (128 + 32 * k) 32).storeWord (128 + 32 * k)
      (b_world.sload b_msg.currentTarget (d + BitVec.ofNat 256 k))).loadWord 64 = 128#256 := by
    rw [Memory.loadWord_storeWord_of_disjoint _ _ _ _ (by omega), Memory.loadWord_expand, hfmp]
  have hM'data : ((mem.expand (128 + 32 * k) 32).storeWord (128 + 32 * k)
      (b_world.sload b_msg.currentTarget (d + BitVec.ofNat 256 k))).read 128 (32 * (k + 1)) =
      Str.wordsFrom (b_world.sload b_msg.currentTarget) d (k + 1) := by
    rw [show 32 * (k + 1) = 32 * k + 32 by omega, Memory.read_add,
      Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand, hdata,
      Memory.read_storeWord, Str.wordsFrom_succ]
  by_cases hk1 : k + 1 < n
  · have hlt' : Word.lt (BitVec.ofNat 256 (32 * (k + 1))) Lw = 1#256 :=
      (Word.lt_eq_one_iff _ _).2 (by rw [hLw, Str.toNat_ofNat_of_lt (by omega)]; omega)
    pwp_run_to 2770 [hptr', hi']
    refine WP.ret (.inl ⟨hk1, rfl, hj, _, _, _, rfl, hM'size, hM'fmp, hM'data, ?_, ?_, ?_, hlog⟩)
    · rw [plSz_succ, hc1]; generalize sloadCost _ = sl at *; omega
    · dsimp only; rw [plSz_succ, hc1]; generalize sloadCost _ = sl at *; omega
    · try dsimp only
      generalize sloadCost _ = sl at *; omega
  · have hge : Word.lt (BitVec.ofNat 256 (32 * (k + 1))) Lw = 0#256 :=
      (Word.lt_eq_zero_iff _ _).2 (by rw [hLw, Str.toNat_ofNat_of_lt (by omega)]; omega)
    pwp_run_to 2798 [hptr', hi', hge]
    refine WP.ret (.inr ⟨by omega, rfl, hj, _, _, _, rfl, hM'size, hM'fmp, hM'data, ?_, ?_, ?_,
      hlog⟩)
    · rw [plSz_succ, hc1]; generalize sloadCost _ = sl at *; omega
    · dsimp only; rw [plSz_succ, hc1]; generalize sloadCost _ = sl at *; omega
    · try dsimp only
      generalize sloadCost _ = sl at *; omega


/-- **The copy loop of `0x0a66`**, from any word before the last to its exit. -/
theorem plCopy_loop {ia : SolmateAsset.Immutables} {b : Machine} {d Lw S : Word} {n R L k : Nat}
    {tl : List Word} (m : Machine) (hst : PlCopy ia b d Lw S n R tl k 2770 m) (hkn : k < n)
    (hn : n = (L + 31) / 32) (hLw : Lw.toNat = L) (hL2 : L < 2 ^ 255) (htl : tl.length ≤ 1010) :
    WP m (PlCopy ia b d Lw S n R tl n 2798) (fun _ _ => False) := by
  refine WP.loop_nat (fun j m => ∃ k, j = n - k ∧ k < n ∧ PlCopy ia b d Lw S n R tl k 2770 m)
    ⟨k, rfl, hkn, hst⟩ ?_
  rintro j m ⟨k, rfl, hkn, hst⟩
  refine (plCopy_body m hst hkn hn hLw hL2 htl).mono_left ?_
  rintro m' (⟨hk1, h'⟩ | ⟨hk1, h'⟩)
  · exact .inl ⟨n - (k + 1), by omega, k + 1, rfl, hk1, h'⟩
  · exact .inr (hk1 ▸ h')

theorem version_hash_eq : Permit.VERSION_HASH =
    90743482286830539503240959006302832933333810038750515972785732718729991261126#256 := rfl

theorem domain_typehash_eq : Permit.DOMAIN_TYPEHASH =
    63076024560530113402979550242307453568063438748328787417531900361828837441551#256 := rfl

/-- The `DOMAIN_SEPARATOR()` memory after a long `name`: free pointer `0x140`, the copied name
below it, any size from `320`. -/
def PlDsPost (b : Machine) (r : Word) (rest : List Word) (L n : Nat) (m' : Machine) : Prop :=
  ∃ mem g sub, m' = b.resumeWith r.toNat
      (dsOfName b.ctx.crypto (Str.longData (b.world.sload b.frame.msg.currentTarget)
        (arrayDataSlot b.ctx.crypto 0#256) L) (ofNat b.ctx.block.chainId)
        b.frame.msg.currentTarget :: rest) mem g b.frame.returnData sub ∧
    mem.loadWord 64 = 320#256 ∧ mem.size = max 320 (128 + 32 * n) ∧
    b.frame.gasLeft ≤ g + 5000 + 2400 * n + Gas.memoryCost (128 + 32 * n) ∧
    g ≤ b.frame.gasLeft ∧ sub.logs = b.frame.sub.logs

set_option maxHeartbeats 0 in
/-- From the exit of the copy loop to the return of `DOMAIN_SEPARATOR()`: the hash of the copied
name, the domain separator's encoding at the free pointer `0x80`, which moves to `0x140`. -/
theorem pl_ds_tail {ia : SolmateAsset.Immutables} {b : Machine} {Lw S r : Word}
    {n R L : Nat} {rest : List Word} (m : Machine)
    (hst : PlCopy ia b (arrayDataSlot b.ctx.crypto 0#256) Lw S n R
      (1913#256 :: 63076024560530113402979550242307453568063438748328787417531900361828837441551#256
        :: 0#256 :: 1108#256 :: 0#256 :: r :: rest) n 2798 m)
    (hn : n = (L + 31) / 32) (hLw : Lw.toNat = L) (h32 : 32 ≤ L) (hL2 : L < 2 ^ 255)
    (hlen : rest.length ≤ 1000) (hR : 1000 + 6 * n ≤ R)
    (hr : isValidJumpDest b.frame.jumpDests r.toNat = true) :
    WP m (PlDsPost b r rest L n) (fun _ _ => False) := by
  have hagree := assetJumpDestsAgree ia
  obtain ⟨hc, hj, mem, g, sub, rfl, hsize, hfmp, hdata, hg, hgb, hgu, hlog⟩ := hst
  obtain ⟨b_ctx, b_pre, b_world, b_transient, b_originalWorld, b_created,
    ⟨b_msg, b_code, b_jumpDests, b_pc, b_stack, b_memory, b_gasLeft, b_returnData, b_sub,
      b_snapshot, b_kind⟩, b_parents⟩ := b
  dsimp only [Machine.resumeWith, plStk, PlDsPost] at *
  subst hc
  have hn1 : n ≠ 0 := by omega
  simp only [plSz, hn1, ↓reduceIte] at hsize hg hgb
  have hMsz : mem.size = 160 + 32 * (n - 1) := by omega
  have hxm : ∀ off len, off + len ≤ 160 → mem.expand off len = mem :=
    fun _ _ h => bg_expand hMsz (by decide) h
  plwp_steps [hfmp, hMsz, hxm]
  have hLnL : L ≤ 32 * n := by omega
  have hext : Gas.extendMemory mem.size [(128, L)] = { cost := 0, newSize := mem.size } :=
    extend_of_le (by omega) _ (by simp; omega)
  have hxL : mem.expand 128 L = mem := Memory.expand_eq_self_of_le (by omega) (by omega)
  have hname : mem.read 128 L = Str.longData (b_world.sload b_msg.currentTarget)
      (arrayDataSlot b_ctx.crypto 0#256) L := by
    rw [Verified.Solmate.ERC4626.Memory.read_prefix _ hLnL, hdata, Str.longData, hn]
  refine WP.of_step (step_keccak256 (by pcode_fact) rfl (by simp; omega) ?_) (by same_frame) ?_
  · dsimp only
    simp only [Word.add_sub_cancel_left', hLw, BitVec.reduceToNat, hext]
    simp only [Gas.keccak256Cost, Gas.keccak256Base, Gas.keccak256PerWord, Gas.words]
    omega
  dsimp only
  simp only [Word.add_sub_cancel_left', hLw, BitVec.reduceToNat, hext, hxL, readBytes_bytes,
    hname]
  simp only [Gas.keccak256Cost,
    Gas.keccak256Base, Gas.keccak256PerWord, Gas.words]
  generalize hnh : b_ctx.crypto.keccak256 (Str.longData (b_world.sload b_msg.currentTarget)
    (arrayDataSlot b_ctx.crypto 0#256) L) = nh
  wp_generalize_gas g1 hg1
  have hg1' : g ≤ g1 + 106 + 6 * n := by subst hg1; omega
  have hg1'' : g1 + 106 + 6 * n ≤ g := by subst hg1; omega
  clear hg1
  by_cases h6 : 6 ≤ n
  · have hMsz : mem.size = 320 + 32 * (n - 6) := by omega
    have hxm : ∀ off len, off + len ≤ 320 → mem.expand off len = mem :=
      fun _ _ h => bg_expand hMsz (by decide) h
    plwp_steps [hfmp, hMsz, hxm]
    simp (disch := decide) only [Memory.read_160, Memory.read_storeWord,
      Memory.read_storeWord_of_disjoint]
    apply WP.ret
    simp only [PlDsPost, dsOfName, hnh, version_hash_eq, domain_typehash_eq, Machine.resumeWith]
    refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, hlog⟩
    · simp (disch := decide) only [Memory.loadWord_storeWord]
    · simp only [Memory.size_storeWord, hMsz]; omega
    · omega
    · omega
  · have hn5 : n ≤ 5 := by omega
    have hn1' : 1 ≤ n := by omega
    clear hMsz hxm
    obtain rfl | rfl | rfl | rfl | rfl : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    all_goals
      simp only [Nat.reduceMul, Nat.reduceAdd] at hsize
      pwp_steps [hfmp, hsize, permit_norm]
      simp (disch := decide) only [Memory.read_160, Memory.read_storeWord, Memory.read_expand,
        Memory.read_storeWord_of_disjoint]
      apply WP.ret
      simp only [PlDsPost, dsOfName, hnh, version_hash_eq, domain_typehash_eq, Machine.resumeWith]
      refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, hlog⟩
      · simp (disch := decide) only [Memory.loadWord_storeWord, Memory.loadWord_expand]
      · simp only [permit_norm, hsize]
      · omega
      · omega


set_option maxHeartbeats 0 in
/-- **`DOMAIN_SEPARATOR()` (entry `0x0424`) off the deployment chain with a long `name`**: the
slot word `S` of `name` is odd (long form) and encodes `L ≥ 32` bytes; the function copies the
`⌈L/32⌉` data words to `0x80`, hashes the `L` bytes and returns `dsOfName` of them, leaving free
pointer `0x140` and memory of `max 320 (128 + 32⌈L/32⌉)` bytes. -/
theorem pl_ds_long {ia : SolmateAsset.Immutables} (m : Machine) {r : Word} {rest : List Word}
    (hc : m.frame.code = SolmateAsset.runtimeCodeWith ia)
    (hj : JumpTable m.frame.jumpDests (SolmateAsset.runtimeCodeWith ia))
    (hpc : m.frame.pc = 1060) (hs : m.frame.stack = r :: rest) (hlen : rest.length ≤ 1000)
    (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hfmp : m.frame.memory.loadWord 64 = 128#256) (hsize : m.frame.memory.size = 96)
    (hne : ofNat m.ctx.block.chainId ≠ ia.initialChainId)
    (hodd : m.world.sload m.frame.msg.currentTarget 0#256 &&& 1#256 = 1#256)
    (hL : 32 ≤ (Word.shr 1#256 (m.world.sload m.frame.msg.currentTarget 0#256)).toNat)
    (hg : 10000 + Str.getterGas
      (Word.shr 1#256 (m.world.sload m.frame.msg.currentTarget 0#256)).toNat ≤
      m.frame.gasLeft) :
    WP m (PlDsPost m r rest (Word.shr 1#256 (m.world.sload m.frame.msg.currentTarget 0#256)).toNat
      (((Word.shr 1#256 (m.world.sload m.frame.msg.currentTarget 0#256)).toNat + 31) / 32))
      (fun _ _ => False) := by
  generalize hLdef : (Word.shr 1#256 (m.world.sload m.frame.msg.currentTarget 0#256)).toNat = L
    at hL hg ⊢
  generalize hndef : (L + 31) / 32 = n
  have hagree := assetJumpDestsAgree ia
  have hL2 : L < 2 ^ 255 := by
    rw [← hLdef, Str.shr_one]; simp only [BitVec.toNat_ofNat]
    have := (m.world.sload m.frame.msg.currentTarget 0#256).isLt; omega
  have hn1 : 1 ≤ n := by omega
  have hm := Gas.memoryCost_mono (show 128 + 32 * n ≤ 256 + 64 * n by omega)
  have hgg : 10000 + (8000 + 2400 * n + Gas.memoryCost (256 + 64 * n)) ≤ m.frame.gasLeft := by
    rw [← hndef]; exact hg
  refine WP.bind_mono (Q₁ := PlCopy ia m (arrayDataSlot m.ctx.crypto 0#256)
      (Word.shr 1#256 (m.world.sload m.frame.msg.currentTarget 0#256))
      (m.world.sload m.frame.msg.currentTarget 0#256) n (1000 + 6 * n)
      (1913#256 :: 63076024560530113402979550242307453568063438748328787417531900361828837441551#256
        :: 0#256 :: 1108#256 :: 0#256 :: r :: rest) 0 2770) ?_ (fun _ _ _ h => h) ?_
  · obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
      ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
        m_snapshot, m_kind⟩, m_parents⟩ := m
    dsimp only at *
    subst hpc hs
    subst hc
    have hne' : Word.eq (ofNat m_ctx.block.chainId) ia.initialChainId = 0#256 := eq_of_ne hne
    generalize hS : m_world.sload m_msg.currentTarget 0#256 = S at hodd hLdef ⊢
    have hlt : Word.lt (Word.shr 1#256 S) 32#256 = 0#256 :=
      (Word.lt_eq_zero_iff _ _).2 (by rw [hLdef]; simpa using hL)
    pwp_run_to 2770 [hne', readBytes_asset_chainId, hfmp, hsize, hS, hodd, hlt, permit_norm]
    apply WP.ret
    have h0 : BitVec.ofNat 256 0 = (0 : Word) := rfl
    simp only [PlCopy, plStk, Machine.resumeWith, Nat.mul_zero, h0, add_zero,
      arrayDataSlot]
    refine ⟨trivial, hj, _, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [permit_norm, hsize, plSz]
    · simp (disch := decide) only [Memory.loadWord_storeWord_of_disjoint, Memory.loadWord_expand,
        hfmp]
    · apply EvmLean.Bytes.ext_getD (by rw [Memory.size_read, Str.size_wordsFrom])
      intro j hj; rw [Memory.size_read] at hj; omega
    · have := sloadCost_le (storageKeyWarm m_sub.accessedStorageKeys m_msg.currentTarget 0#256)
      simp only [plSz, ↓reduceIte, Nat.sub_zero]
      generalize sloadCost _ = sl at *
      generalize Gas.memoryCost (128 + 32 * n) = c1 at *
      have h96 : Gas.memoryCost 96 = 9 := by decide
      omega
    · have := sloadCost_le (storageKeyWarm m_sub.accessedStorageKeys m_msg.currentTarget 0#256)
      simp only [plSz, ↓reduceIte]
      generalize sloadCost _ = sl at *
      omega
    · omega
    · rfl
  · intro m₁ _ h
    refine (plCopy_loop m₁ h (by omega) hndef.symm (by rw [hLdef]) hL2 (by simp; omega)).bind
      fun m₂ _ h₂ => ?_
    exact pl_ds_tail (L := L) m₂ h₂ hndef.symm (by rw [hLdef]) hL hL2 hlen (by omega) hr


theorem and_one_cases (S : Word) : S &&& 1#256 = 0#256 ∨ S &&& 1#256 = 1#256 := by
  rcases Nat.mod_two_eq_zero_or_one S.toNat with h | h
  · exact .inl (Str.and_one_of_even h)
  · exact .inr (Str.and_one_of_odd h)

set_option maxHeartbeats 0 in
/-- **`DOMAIN_SEPARATOR()` off the deployment chain with an inconsistent slot word** (a short
form of 32 bytes or more, or a long one below 32: `nameBytes` is `none`): the packed encoder
`0x0a66` reverts with `Panic(0x22)`. -/
theorem pl_ds_panic {ia : SolmateAsset.Immutables} (m : Machine) {r : Word} {rest : List Word}
    (hc : m.frame.code = SolmateAsset.runtimeCodeWith ia)
    (hj : JumpTable m.frame.jumpDests (SolmateAsset.runtimeCodeWith ia))
    (hpc : m.frame.pc = 1060) (hs : m.frame.stack = r :: rest) (hlen : rest.length ≤ 1000)
    (hfmp : m.frame.memory.loadWord 64 = 128#256) (hsize : m.frame.memory.size = 96)
    (hne : ofNat m.ctx.block.chainId ≠ ia.initialChainId)
    (hnone : nameBytes m.ctx.crypto (m.world.sload m.frame.msg.currentTarget) = none)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun _ => False) (fun _ o => ∃ out, o = .revert out) := by
  have hagree := assetJumpDestsAgree ia
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hc hpc hs
  have hne' : Word.eq (ofNat m_ctx.block.chainId) ia.initialChainId = 0#256 := eq_of_ne hne
  unfold nameBytes at hnone
  generalize hS : m_world.sload m_msg.currentTarget 0#256 = S at hnone
  rcases and_one_cases S with h0 | h1
  · -- short form, length from 32
    simp only [h0, ↓reduceIte] at hnone
    have hl : ¬ (Permit.shortLength S).toNat < 32 := by
      intro h; simp [h] at hnone
    have hlt : Word.lt (Word.shr 1#256 S &&& 127#256) 32#256 = 0#256 :=
      (Word.lt_eq_zero_iff _ _).2 (by simp only [Permit.shortLength] at hl; simpa using hl)
    pwp_steps [hne', readBytes_asset_chainId, hfmp, hsize, hS, h0, hlt, permit_norm]
    exact ⟨_, rfl⟩
  · -- long form, length below 32
    have h10 : ¬ (1#256 : Word) = 0#256 := by decide
    simp only [h1, h10, ↓reduceIte] at hnone
    have hl : (Word.shr 1#256 S).toNat < 32 := by
      by_contra h; simp [Nat.le_of_not_lt h] at hnone
    have hlt : Word.lt (Word.shr 1#256 S) 32#256 = 1#256 := (Word.lt_eq_one_iff _ _).2 (by simpa)
    pwp_steps [hne', readBytes_asset_chainId, hfmp, hsize, hS, h1, hlt, permit_norm]
    exact ⟨_, rfl⟩

end Verified.Solmate.ERC20.Spec
