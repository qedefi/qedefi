import Examples.Solmate.ERC4626.Views
import EvmLogic.Tactic.Mcopy
import EvmLogic.Solidity.Strings
import Examples.Solmate.ERC4626.ViewsSpec

/-!
# `name()` / `symbol()` of the compiled vault: the string copy

Solmate's `ERC20` declares `string public name; string public symbol;` (slots 0 and 1). The
compiled getters of the vault (`SolmateVault.runtimeCodeWith i`, any immutables) load the
slot word and call `extract_byte_array_length` (entry `0x1339`), allocate a `string memory`
at the free pointer `0x80`, copy the data (the slot word with its length byte cleared for a
short string; the words at `keccak256(slot) + j` for a long one), and return it through the
ABI encoder at `0x1148`, which copies the bytes into the return buffer with `MCOPY`.

* `vaultEncodeShort_wp`: the encoder from its `MCOPY` (`0x115f`) to the `RETURN`, for a
  string of 1–31 bytes already in memory at `0xa0` (two copies of symbolic length, handled
  with `step_mcopy`, `mcopyCost_eq`, `memoryCost_eq` and `wp_generalize_mem`).
* `vaultStringShort_wp`: from the entry of `extract_byte_array_length` with the slot word
  `S` of a short (even) slot on the stack, in any frame: the call returns
  `Abi.encodeString` of the decoded string, or panics if the slot is inconsistent
  (`Str.decode`); the world is unchanged (`StringPost`).
-/

section

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 Defi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic Examples.Solmate.Contracts EvmLean.Bytes

/-- What a `string` getter ends with: the world unchanged, and the ABI encoding of the string
`s` when the slot decodes to `some s`, a revert when it is inconsistent. -/
def StringPost (m : Machine) (r : Option ByteArray) (mf : Machine) (o : Outcome) : Prop :=
  mf.world = m.world ∧
    match r with
    | some s => o = .success (Abi.encodeString s)
    | none => ∃ out, o = .revert out

/-- The return buffer of a short string, from the memory the encoder starts with: the head
(offset and length words) and the data are where the encoder wrote them, and the bytes after
the data are the word of zeros it stores there. -/
theorem read_encodeShort (M : Memory) {L : Nat} {data : ByteArray} (hL1 : 1 ≤ L) (hL : L ≤ 31)
    (hd : M.read 160 L = data)
    (hh : M.read 192 64 = ofWord 32#256 ++ ofWord (BitVec.ofNat 256 L)) :
    (((M.mcopy 256 160 L).expand (L + 256) 32).storeWord (L + 256) 0#256).read 192 96 =
      Abi.encodeString data := by
  have hsz : data.size = L := by rw [← hd, Memory.size_read]
  generalize hM2 : ((M.mcopy 256 160 L).expand (L + 256) 32).storeWord (L + 256) 0#256 = M2
  have e1 : M2.read 192 96 = M2.read 192 64 ++ (M2.read 256 L ++ M2.read (L + 256) (32 - L)) := by
    rw [show (96 : Nat) = 64 + (L + (32 - L)) by omega, Memory.read_add, Memory.read_add,
      show 192 + 64 = 256 from rfl, show 256 + L = L + 256 by omega]
  rw [e1, ← hM2, Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega),
    Memory.read_expand, Memory.read_mcopy_of_disjoint _ _ _ _ _ _ (by omega), hh,
    Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand, Memory.read_mcopy,
    hd, Memory.read_storeWord_prefix (hn := by omega), extract_ofWord_zero (by omega)]
  simp only [Abi.encodeString, hsz, show (L + 31) / 32 * 32 - L = 32 - L by omega,
    ByteArray.append_assoc]

set_option maxHeartbeats 0 in
/-- **The vault's string encoder from its `MCOPY`, for a short string** (1–31 bytes at
`0xa0`, its length at `0x80`, the head at the free pointer `0xc0`). -/
theorem vaultEncodeShort_wp {i : SolmateVault.Immutables} (m : Machine) {L : Nat}
    {rest : List Word} {data : ByteArray}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hpc : m.frame.pc = 0x115f)
    (hs : m.frame.stack = 256#256 :: 160#256 :: BitVec.ofNat 256 L :: BitVec.ofNat 256 L ::
      0#256 :: 192#256 :: 128#256 :: 487#256 :: rest)
    (hL1 : 1 ≤ L) (hL2 : L ≤ 31) (hsize : m.frame.memory.size = 256)
    (h40 : m.frame.memory.loadWord 64 = 192#256) (hd : m.frame.memory.read 160 L = data)
    (hh : m.frame.memory.read 192 64 = ofWord 32#256 ++ ofWord (BitVec.ofNat 256 L))
    (hlen : rest.length ≤ 1005) (hg : 200 ≤ m.frame.gasLeft) :
    WP m (fun _ => False)
      (fun mf o => mf.world = m.world ∧ o = .success (Abi.encodeString data)) := by
  have hagree := Shares.jumpDestsAgree i
  have hLn : (BitVec.ofNat 256 L).toNat = L := Str.toNat_ofNat_of_lt (by omega)
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  have hcost1 : (Gas.extendMemory 256 [(160, L), (256, L)]).cost = 3 := by
    rw [Gas.extendMemory_two (by omega) (by decide),
      show max (max 256 ((160 + L + 31) / 32 * 32)) ((256 + L + 31) / 32 * 32) = 288 by omega]
    rfl
  apply WP.of_step
  case h =>
    apply step_mcopy
    case hcode => pcode_fact
    case hstk => exact rfl
    case hz => omega
    case hgas => simp only [mcopyCost, hsize, hLn, BitVec.reduceToNat, hcost1]; omega
  case hs => same_frame
  dsimp only
  simp only [mcopyCost, hsize, hLn, BitVec.reduceToNat, hcost1]
  wp_generalize_mem M1 hM1
  have hM1s : M1.size = 288 := by
    subst hM1; rw [Memory.size_mcopy _ _ _ _ (by omega), hsize]; omega
  have hM1f : M1.loadWord 64 = 192#256 := by
    subst hM1; rw [Memory.loadWord_mcopy_of_disjoint _ _ _ _ _ (by omega), h40]
  pwp_steps [hM1s, hM1f]
  have hx : (192#256 + BitVec.ofNat 256 L + 64#256).toNat = L + 256 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, hLn]; simp only [BitVec.reduceToNat]; omega
  have hx' : ((192 : Word) + BitVec.ofNat 256 L + (64 : Word)).toNat = L + 256 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, hLn]; simp only [BitVec.reduceToNat]; omega
  wp_generalize_gas g1 hg1
  have hcost2 : (Gas.extendMemory 288 [(L + 256, 32)]).cost = 3 := by
    rw [Gas.extendMemory_one (by omega) (by decide),
      show max 288 ((L + 256 + 32 + 31) / 32 * 32) = 320 by omega]
    rfl
  apply WP.of_step
  case h =>
    apply step_mstore
    case hcode => pcode_fact
    case hstk => exact rfl
    case hgas => simp only [memoryCost, hM1s, hx, hcost2, Gas.veryLow]; omega
  case hs => same_frame
  dsimp only
  simp only [memoryCost, hM1s, hx, hcost2]
  wp_generalize_mem M2 hM2
  have hM2s : M2.size = 320 := by
    subst hM2; rw [Memory.size_storeWord, Memory.size_expand, hM1s]
    simp only [Memory.wordsAfter, Memory.words, hM1s, Nat.reduceEqDiff, ↓reduceIte]; omega
  have hM2f : M2.loadWord 64 = 192#256 := by
    subst hM2; rw [Memory.loadWord_storeWord_of_disjoint _ _ _ _ (by omega),
      Memory.loadWord_expand, hM1f]
  have hM2r : M2.read 192 96 = Abi.encodeString data := by
    subst hM2 hM1; exact read_encodeShort m_memory hL1 hL2 hd hh
  have hround : (L + 31) / 32 * 32 = 32 := by omega
  pwp_steps [hM2s, hM2f, Str.and_notMask31 (show L < 2 ^ 255 by omega), hround, hM2r]
  exact ⟨rfl, trivial⟩

end Examples.Solmate.ERC4626

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 Defi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic Examples.Solmate.Contracts EvmLean.Bytes

set_option maxHeartbeats 0 in
/-- **The vault's string getter, short (even) slot word**, from the entry of
`extract_byte_array_length` (`0x1339`, called from the getter with return address `0x0514`). -/
theorem vaultStringShort_wp {i : SolmateVault.Immutables} (m : Machine) {S slot : Word}
    {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hpc : m.frame.pc = 0x1339)
    (hs : m.frame.stack = S :: 1300#256 :: slot :: 504#256 :: rest)
    (hS : m.world.sload m.frame.msg.currentTarget slot = S) (hev : S.toNat % 2 = 0)
    (hmem : m.frame.memory = initMemory)
    (hlen : rest.length ≤ 1000) (hg : 5000 ≤ m.frame.gasLeft) :
    WP m (fun _ => False)
      (StringPost m (Str.decode m.ctx.crypto (m.world.sload m.frame.msg.currentTarget) slot)) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc hmem
  have hL := Str.slotLen_lt S
  by_cases hshort : Str.slotLen S < 32
  · have hdec : Str.decode m_ctx.crypto (m_world.sload m_msg.currentTarget) slot =
        some ((ofWord S).extract 0 (Str.slotLen S)) := by
      simp [Str.decode, hS, Str.slotOk, hev, hshort]
    rw [hdec]
    by_cases hz : Str.slotLen S = 0
    · rw [hz]
      pwp_msteps [initMemory, hS, Str.and_one_of_even hev, Str.shr_one_and_127 hev, hz]
      refine ⟨rfl, ?_⟩
      simp only
      rw [Abi.encodeString_of_size_zero (by simp), Memory.read_64]
      simp (disch := omega) only [Memory.read_storeWord_of_disjoint, Memory.read_expand,
        Memory.read_storeWord]
    · have hround : (Str.slotLen S + 31) / 32 * 32 = 32 := by omega
      pwp_steps [initMemory, hS, Str.and_one_of_even hev, Str.shr_one_and_127 hev,
        Str.lt_32_of_lt hshort, Str.iszero_of_ne hz (by omega), Str.div_32_mul_32 hL, hround,
        Str.lt_31_of_le (show Str.slotLen S ≤ 31 by omega), Str.div_256_mul_256 S]
      wp_generalize_mem M0 hM0
      have hM0s : M0.size = 256 := by
        subst hM0; simp [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words]
      have hM0f : M0.loadWord 64 = 192#256 := by
        subst hM0
        simp (disch := omega) only [Memory.loadWord_storeWord_of_disjoint, Memory.loadWord_expand,
          Memory.loadWord_storeWord]
      have hM0d : M0.read 160 (Str.slotLen S) = (ofWord S).extract 0 (Str.slotLen S) := by
        subst hM0
        simp (disch := omega) only [Memory.read_storeWord_of_disjoint, Memory.read_expand]
        rw [Memory.read_storeWord_prefix (hn := by omega), extract_ofWord_div256 _ (by omega)]
      have hM0h : M0.read 192 64 = ofWord 32#256 ++ ofWord (BitVec.ofNat 256 (Str.slotLen S)) := by
        subst hM0
        rw [Memory.read_64]
        simp (disch := omega) only [Memory.read_storeWord_of_disjoint, Memory.read_expand,
          Memory.read_storeWord]
      refine WP.mono (vaultEncodeShort_wp _ (L := Str.slotLen S) rfl hj rfl rfl (by omega)
        (by omega) hM0s hM0f hM0d
        hM0h (by simp only [List.length_cons]; omega) (by dsimp only; evm_gas))
        (fun _ _ h => h.elim) ?_
      rintro mf o - ⟨hw, ho⟩
      exact ⟨hw, ho⟩
  · have hdec : Str.decode m_ctx.crypto (m_world.sload m_msg.currentTarget) slot = none := by
      simp [Str.decode, hS, Str.slotOk, hev, hshort]
    rw [hdec]
    pwp_steps [initMemory, hS, Str.and_one_of_even hev, Str.shr_one_and_127 hev,
      Str.lt_32_of_ge (Nat.le_of_not_lt hshort) (by omega)]
    exact ⟨rfl, _, rfl⟩

end Examples.Solmate.ERC4626

end

section

/-!
## `name()` / `symbol()` of the compiled vault: long strings

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

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 Defi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic Examples.Solmate.Contracts EvmLean.Bytes

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
    (hL : 32 ≤ L) (hL' : L < 2 ^ 64) (htl : tl.length ≤ 1010) :
    WP m (VaultCopy i w a h L n R fmp tl n 0x582) (fun _ _ => False) := by
  refine WP.loop_nat (fun j m => ∃ k, j = n - k ∧ k < n ∧ VaultCopy i w a h L n R fmp tl k 0x56e m)
    ⟨k, rfl, hkn, hst⟩ ?_
  rintro j m ⟨k, rfl, hkn, hst⟩
  refine (vaultCopyBody_wp m hst hkn hn hL hL' htl).mono_left ?_
  rintro m' (⟨hk1, h'⟩ | ⟨hk1, h'⟩)
  · exact .inl ⟨n - (k + 1), by omega, k + 1, rfl, hk1, h'⟩
  · exact .inr (hk1 ▸ h')

end Examples.Solmate.ERC4626

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 Defi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic Examples.Solmate.Contracts EvmLean.Bytes

/-- A prefix of a read is a shorter read. -/
theorem Memory.read_prefix (M : Memory) {off a b : Nat} (h : a ≤ b) :
    M.read off a = (M.read off b).extract 0 a := by
  apply ext_getD (by simp only [Memory.size_read, ByteArray.size_extract]; omega)
  intro j hj
  rw [Memory.size_read] at hj
  simp only [Memory.read, getD_readPadded, getD_extract, hj, ↓reduceIte, Nat.zero_add,
    show j < b by omega]

set_option maxHeartbeats 0 in
/-- **The end of the getter for a long string**: from the loop exit with all `n` words copied
(`0x0582`) through the ABI encoder (`0x1148`, with the head at the free pointer
`0xa0 + 32 n`) to the `RETURN`: the call returns `Abi.encodeString` of the first `L` bytes of
the copied words. -/
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
  -- the gas potential: the memory costs at the successive sizes
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

end Examples.Solmate.ERC4626

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 Defi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic Examples.Solmate.Contracts EvmLean.Bytes

set_option maxHeartbeats 0 in
/-- **The vault's string getter, long (odd) slot word**, from the entry of
`extract_byte_array_length` (`0x1339`): with enough gas for the copy, the call returns
`Abi.encodeString` of the decoded string, or panics if the slot is inconsistent. -/
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

end Examples.Solmate.ERC4626

end

section

/-!
## `name()` / `symbol()` of the compiled vault refine the storage strings

Solmate's `ERC20` stores `name` at slot 0 and `symbol` at slot 1 (`string public`). For the
compiled vault (`SolmateVault.runtimeCodeWith i`, any immutables):

* `vaultName_refines`, `vaultSymbol_refines` (any frame, `Halts`): from a fresh frame of the
  vault's code with `NoArgCall` calldata and enough gas (`StringPre`: `Str.getterGas` of the
  length the slot encodes), the call returns `Abi.encodeString s` where
  `stringAt crypto world vault slot = some s`, or reverts (`Panic(0x22)`) when the slot is
  inconsistent (`none`); the world is unchanged (`StringPost`).
* `vaultName_call`, `vaultSymbol_call`: the same for a top-level transaction
  (`processMessageCall`) on a `Deployed` vault (`StringResult`).

Both short (≤ 31 bytes, in the slot) and long strings (data at `keccak256(slot) + j`) are
covered, for every `Crypto`: the long-string data slots are whatever `arrayDataSlot` gives, so
no hypothesis on Keccak is needed to *read*.
-/

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 Defi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic Examples.Solmate.Contracts EvmLean.Bytes

/-- The start of a call frame of a string getter: fresh frame of `code`, no value, enough gas
for the string at `slot` of the executing account (`Str.getterGas`, below `2⁶⁴`), calldata
shorter than `2⁶⁴` bytes. -/
structure StringPre (code : ByteArray) (slot : Word) (m : Machine) : Prop where
  /-- A fresh frame of the code. -/
  fresh : Fresh code m
  /-- No value is sent (the getters are not payable). -/
  value : m.frame.msg.value = 0
  /-- Enough gas for the copy. -/
  gas : Str.getterGas (Str.slotLen (m.world.sload m.frame.msg.currentTarget slot)) ≤
    m.frame.gasLeft
  /-- Gas fits 64 bits. -/
  gasLt : m.frame.gasLeft < 2 ^ 64
  /-- Calldata length fits 64 bits. -/
  sizeLt : m.frame.msg.data.size < 2 ^ 64

set_option maxHeartbeats 0 in
/-- **The vault's string getter** from the entry of `extract_byte_array_length` (`0x1339`),
any slot word. -/
theorem vaultString_wp {i : SolmateVault.Immutables} (m : Machine) {S slot : Word}
    {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hpc : m.frame.pc = 0x1339)
    (hs : m.frame.stack = S :: 1300#256 :: slot :: 504#256 :: rest)
    (hS : m.world.sload m.frame.msg.currentTarget slot = S)
    (hmem : m.frame.memory = initMemory) (hlen : rest.length ≤ 1000)
    (hg : 5000 + 2400 * ((Str.slotLen S + 31) / 32) +
      Gas.memoryCost (256 + 64 * ((Str.slotLen S + 31) / 32)) ≤ m.frame.gasLeft)
    (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun _ => False)
      (StringPost m (Str.decode m.ctx.crypto (m.world.sload m.frame.msg.currentTarget) slot)) := by
  rcases Nat.mod_two_eq_zero_or_one S.toNat with hev | hodd
  · exact vaultStringShort_wp m hc hj hpc hs hS hev hmem hlen (by omega)
  · exact vaultStringLong_wp m hc hj hpc hs hS hodd hmem hlen hg hg'

/-- The gas of `StringPre` covers the getter after the dispatcher. -/
theorem getterGas_le {L g : Nat} (h : Str.getterGas L ≤ g) (c : Nat) (hc : c ≤ 3000) :
    5000 + 2400 * ((L + 31) / 32) + Gas.memoryCost (256 + 64 * ((L + 31) / 32)) ≤ g - c := by
  unfold Str.getterGas at h; omega

set_option maxHeartbeats 0 in
/-- **`name()` of the vault refines the storage string at slot 0**, in any frame. -/
theorem vaultName_refines {i : SolmateVault.Immutables} (m : Machine)
    (h : StringPre (SolmateVault.runtimeCodeWith i) 0#256 m)
    (hd : NoArgCall m.frame.msg.data 0x06fdde03) :
    Halts m (StringPost m (stringAt m.ctx.crypto m.world m.frame.msg.currentTarget 0#256)) := by
  obtain ⟨hf, hval, hg, hg', hsz'⟩ := h
  obtain ⟨hsel, hsz4⟩ := hd
  have hsel' := Dispatch.selector_eq hsel
  apply WP.halts_of_false
  have hagree := Shares.jumpDestsAgree i
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsz4 (by omega)
  have hg0 : 8000 ≤ m.frame.gasLeft := by unfold Str.getterGas at hg; omega
  fresh_intro
  pwp_run_to 0x1339 [hval, hsel', hlt, Abi.shr_calldataload_zero]
  refine WP.mono (vaultString_wp _ rfl hj rfl rfl rfl rfl (by simp) ?_ (by dsimp only; omega))
    (fun _ _ h => h.elim) (fun _ _ _ h => h)
  have hsl := sloadCost_le (storageKeyWarm m_sub.accessedStorageKeys m_msg.currentTarget 0#256)
  dsimp only
  generalize sloadCost _ = sl at *
  exact getterGas_le hg _ (by omega)

set_option maxHeartbeats 0 in
/-- **`symbol()` of the vault refines the storage string at slot 1**, in any frame. -/
theorem vaultSymbol_refines {i : SolmateVault.Immutables} (m : Machine)
    (h : StringPre (SolmateVault.runtimeCodeWith i) 1#256 m)
    (hd : NoArgCall m.frame.msg.data 0x95d89b41) :
    Halts m (StringPost m (stringAt m.ctx.crypto m.world m.frame.msg.currentTarget 1#256)) := by
  obtain ⟨hf, hval, hg, hg', hsz'⟩ := h
  obtain ⟨hsel, hsz4⟩ := hd
  have hsel' := Dispatch.selector_eq hsel
  apply WP.halts_of_false
  have hagree := Shares.jumpDestsAgree i
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsz4 (by omega)
  have hg0 : 8000 ≤ m.frame.gasLeft := by unfold Str.getterGas at hg; omega
  fresh_intro
  pwp_run_to 0x1339 [hval, hsel', hlt, Abi.shr_calldataload_zero]
  refine WP.mono (vaultString_wp _ rfl hj rfl rfl rfl rfl (by simp) ?_ (by dsimp only; omega))
    (fun _ _ h => h.elim) (fun _ _ _ h => h)
  have hsl := sloadCost_le (storageKeyWarm m_sub.accessedStorageKeys m_msg.currentTarget 1#256)
  dsimp only
  generalize sloadCost _ = sl at *
  exact getterGas_le hg _ (by omega)

end Examples.Solmate.ERC4626

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 Defi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic Examples.Solmate.Contracts EvmLean.Bytes

/-! ## Top-level transactions -/

/-- What a top-level call of a string getter returns: success with `Abi.encodeString s` for
`some s`, a revert for `none`. -/
def StringResult (res : MessageResult) (r : Option ByteArray) : Prop :=
  match r with
  | some s => res.success = true ∧ res.output = Abi.encodeString s
  | none => res.success = false ∧ res.reverted = true

variable {ctx : Context} {w : World} {tr : TransientStorage} {vault asset caller : Address}
  {data : ByteArray} {gas : Nat} {wa : AddressSet} {wk : StorageKeySet}

/-- A string-getter summary of the start machine of a top-level call gives the result of
`processMessageCall`: the world is unchanged and the result is `StringResult`. -/
theorem string_call {code : ByteArray} {a : Address} {r : Option ByteArray}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hdel : delegatedAddress? code = none) (hpre : Precompile.isPrecompile ctx.fork a = false)
    (h : Halts (startMachine ctx w tr (callMsg code a caller data gas wa wk))
      (StringPost (startMachine ctx w tr (callMsg code a caller data gas wa wk)) r)) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg code a caller data gas wa wk) = .ok res ∧ res.world = w ∧ StringResult res r := by
  obtain ⟨n, hn⟩ := processMessageCall_of_halts (a := a)
    (msg := callMsg code a caller data gas wa wk) hdeleg hdel rfl rfl hpre rfl rfl h
  refine ⟨n, fun fuel hle => ?_⟩
  obtain ⟨mf, o, ⟨hw, ho⟩, hs, hrun⟩ := hn fuel hle
  have hk : mf.frame.kind = .call 0 0 := hs.kind
  refine ⟨_, hrun, ?_⟩
  cases r with
  | some v =>
    simp only at ho
    subst ho
    obtain ⟨h1, h2, h3, -⟩ := topLevelResult_success_call
      (t := (callMsg code a caller data gas wa wk).target) (out := Abi.encodeString v) hk
    exact ⟨h3.trans hw, h1, h2⟩
  | none =>
    obtain ⟨out, ho⟩ := ho
    subst ho
    have hsnap : mf.frame.snapshot.1 = w := by rw [hs.snapshot]; rfl
    simp only [frameResult_revert, topLevelResult_world, topLevelResult_success,
      topLevelResult_reverted, StringResult, ChildResult.success, hsnap]
    decide

/-- The start of a top-level call satisfies `StringPre` when the gas covers the string. -/
theorem stringPre_start {code : ByteArray} {a : Address} {slot : Word}
    (hgas : Str.getterGas (Str.slotLen (w.sload a slot)) ≤ gas) (hgas' : gas < 2 ^ 64)
    (hsize : data.size < 2 ^ 64) :
    StringPre code slot (startMachine ctx w tr (callMsg code a caller data gas wa wk)) where
  fresh := fresh_startMachine ctx w tr (callMsg code a caller data gas wa wk)
  value := rfl
  gas := hgas
  gasLt := hgas'
  sizeLt := hsize

/-- **`name()` as a top-level transaction** on the deployed vault: the string at slot 0. -/
theorem vaultName_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hgas : Str.getterGas (Str.slotLen (w.sload vault 0#256)) ≤ gas) (hgas' : gas < 2 ^ 64) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller (Abi.encodeCall 0x06fdde03 []) gas wa wk) = .ok res ∧
      res.world = w ∧ StringResult res (stringAt ctx.crypto w vault 0#256) := by
  obtain ⟨i, -, hcode⟩ := hdep.vaultCode
  rw [hcode]
  exact string_call hdeleg (Shares.delegatedAddress?_code i) (hdep.vaultNotPrecompile _)
    (vaultName_refines _ (stringPre_start hgas hgas' (by rw [Abi.size_encodeCall]; simp))
      (noArgCall_encodeCall (by decide)))

/-- **`symbol()` as a top-level transaction** on the deployed vault: the string at slot 1. -/
theorem vaultSymbol_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hgas : Str.getterGas (Str.slotLen (w.sload vault 1#256)) ≤ gas) (hgas' : gas < 2 ^ 64) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller (Abi.encodeCall 0x95d89b41 []) gas wa wk) = .ok res ∧
      res.world = w ∧ StringResult res (stringAt ctx.crypto w vault 1#256) := by
  obtain ⟨i, -, hcode⟩ := hdep.vaultCode
  rw [hcode]
  exact string_call hdeleg (Shares.delegatedAddress?_code i) (hdep.vaultNotPrecompile _)
    (vaultSymbol_refines _ (stringPre_start hgas hgas' (by rw [Abi.size_encodeCall]; simp))
      (noArgCall_encodeCall (by decide)))

end Examples.Solmate.ERC4626

end
