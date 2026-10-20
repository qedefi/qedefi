import Examples.Solmate.ERC4626.VaultViewsMax
import EvmLogic.Tactic.Mcopy
import EvmLogic.Solidity.StringsWord

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

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts Bytes

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

end EvmLeanSpecs.Refinement

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts Bytes

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

end EvmLeanSpecs.Refinement
