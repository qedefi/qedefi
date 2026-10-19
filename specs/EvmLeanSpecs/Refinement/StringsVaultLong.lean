import EvmLeanSpecs.Refinement.StringsVault

/-!
# `name()` / `symbol()` of the compiled vault: long strings

A long string (32 bytes or more) is stored as `2 · length + 1` in its slot and its data in the
slots `keccak256(slot) + j`. The getter copies those words into memory with a loop
(`0x056e`–`0x0581`: `mstore(dst, sload(ptr)); ptr += 1; dst += 32` while `dst < end`); then
the ABI encoder (`0x1148`) writes the head and copies the data again with `MCOPY`.

Memory grows with the length, so the gas bound is a function of it: `Str.getterGas L`.
Memory-expansion costs are tracked through the *potential*
`gasLeft + Gas.memoryCost size` (`VaultCopy.gas`): every memory access then costs only its
static part, the expansion terms telescoping (`Gas.extendMemory_one`, `memoryCost_mono`).

* `vaultCopyLoop_wp`: the loop, by `WP.loop_nat` on the number of words left, from the
  invariant `VaultCopy … k` at the loop head to the same state at the loop exit (`0x0582`)
  with all `n = ⌈L / 32⌉` words copied.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts Bytes

/-- The state of the copy loop of the vault's string getter after `k` words, at pc `pc`:
`dst = 0xa0 + 32 k`, `ptr = h + k` (`h` the first data slot), `end = 0xa0 + L` on the stack;
memory of `0xa0 + 32 k` bytes holding the free pointer `fmp`, the length at `0x80` and the
first `k` data words at `0xa0`; the gas potential covers `R`, the rest of the copy
(`2300` per word) and the final memory (`256 + 64 n` bytes). -/
structure VaultCopy (i : SolmateVault.Immutables) (w : World) (a : Address) (h : Word)
    (L n R : Nat) (fmp : Word) (tl : List Word) (k pc : Nat) (m : Machine) : Prop where
  /-- The vault's code. -/
  code : m.frame.code = SolmateVault.runtimeCodeWith i
  /-- Its jump table. -/
  jd : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i)
  /-- The program counter. -/
  pcEq : m.frame.pc = pc
  /-- The world (read only). -/
  world : m.world = w
  /-- The executing account. -/
  target : m.frame.msg.currentTarget = a
  /-- The loop variables. -/
  stack : ∃ dst ptr endw, m.frame.stack = dst :: ptr :: endw :: tl ∧
    dst.toNat = 160 + 32 * k ∧ ptr = h + BitVec.ofNat 256 k ∧ endw.toNat = 160 + L
  /-- Memory size. -/
  size : m.frame.memory.size = 160 + 32 * k
  /-- The free memory pointer. -/
  fmpEq : m.frame.memory.loadWord 64 = fmp
  /-- The length word of the `string memory`. -/
  len : m.frame.memory.read 128 32 = ofWord (BitVec.ofNat 256 L)
  /-- The words copied so far. -/
  data : m.frame.memory.read 160 (32 * k) = Str.wordsFrom (w.sload a) h k
  /-- Gas, as a potential. -/
  gas : R + 2300 * (n - k) + Gas.memoryCost (256 + 64 * n) ≤
    m.frame.gasLeft + Gas.memoryCost (160 + 32 * k)

/-- `h + k + 1`, as the loop computes it. -/
theorem add_one_ptr (h : Word) (k : Nat) :
    1#256 + (h + BitVec.ofNat 256 k) = h + BitVec.ofNat 256 (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

set_option maxHeartbeats 0 in
/-- **One iteration of the copy loop**: from the loop head with `k < n` words copied, back to
the head with `k + 1`, or to the exit when `k + 1 = n`. -/
theorem vaultCopyBody_wp {i : SolmateVault.Immutables} {w : World} {a : Address} {h fmp : Word}
    {L n R k : Nat} {tl : List Word} (m : Machine)
    (hst : VaultCopy i w a h L n R fmp tl k 0x56e m) (hkn : k < n) (hn : n = (L + 31) / 32)
    (hL : 32 ≤ L) (hL' : L < 2 ^ 64) (htl : tl.length ≤ 1000) :
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
    -- memory after the store
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
    -- memory after the store
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
    (hL : 32 ≤ L) (hL' : L < 2 ^ 64) (htl : tl.length ≤ 1000) :
    WP m (VaultCopy i w a h L n R fmp tl n 0x582) (fun _ _ => False) := by
  refine WP.loop_nat (fun j m => ∃ k, j = n - k ∧ k < n ∧ VaultCopy i w a h L n R fmp tl k 0x56e m)
    ⟨k, rfl, hkn, hst⟩ ?_
  rintro j m ⟨k, rfl, hkn, hst⟩
  refine (vaultCopyBody_wp m hst hkn hn hL hL' htl).mono_left ?_
  rintro m' (⟨hk1, h'⟩ | ⟨hk1, h'⟩)
  · exact .inl ⟨n - (k + 1), by omega, k + 1, rfl, hk1, h'⟩
  · exact .inr (hk1 ▸ h')

end EvmLeanSpecs.Refinement
