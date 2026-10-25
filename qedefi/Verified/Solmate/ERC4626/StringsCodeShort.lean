import EvmLogic.Tactic.Mcopy
import EvmLogic.Solidity.Strings
import Verified.Solmate.ERC4626.StringsCommon
import Verified.MathlibDeps
import Verified.Solmate.ERC4626.SharesBase
import QEDefi.Math.Arith

/-!
# Short strings of `Verified.Solmate.ERC4626.StringsCode`

The short-string (≤ 31 bytes) part of the `name()`/`symbol()` getter proofs, split off
`StringsCode` so that its kernel checks run in parallel with the long-string part.
-/

section

namespace Verified.Solmate.ERC4626
open Verified.Solmate.ERC20 QEDefi.ERC4626

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts EvmLean.Bytes

set_option maxHeartbeats 0 in
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

end Verified.Solmate.ERC4626

namespace Verified.Solmate.ERC4626
open Verified.Solmate.ERC20 QEDefi.ERC4626

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts EvmLean.Bytes

set_option maxHeartbeats 0 in
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

end Verified.Solmate.ERC4626

end
