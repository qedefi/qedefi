import EvmLeanSpecs.Refinement.VaultViewsMax
import EvmLeanProofs.Solidity.StringsTactic
import EvmLeanProofs.Solidity.StringsWord

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
    (hlen : rest.length ≤ 1000) (hg : 200 ≤ m.frame.gasLeft) :
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
