import EvmLogic.Tactic.WpStep
import EvmLogic.Program.Summary
import EvmLogic.Solidity.Word
import Verified.Solmate.Contracts.SolmateVault
import EvmLogic.Tactic.Patched
import Verified.Solmate.ERC4626.SharesBase

/-!
# Solmate `mulDivDown` / `mulDivUp` in the compiled vault

Summaries of the two internal `mulDiv` functions (entries `0x0e62`, `0x0e7d`; stack
`denominator :: y :: x :: return :: rest`) for any immutables: on success they return to
`return` with the `Nat` mirror's value (`mulDivDownN`/`mulDivUpN`), else `revert(0, 0)`.
-/

namespace Verified.Solmate.ERC4626

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts

/-- `type(uint256).max`. -/
def MAXN : Nat := 2 ^ 256 - 1

/-- Solmate `mulDivDown(x, y, denominator)` on naturals: reverts (`none`) iff
`denominator = 0` or `y ≠ 0 ∧ x > MAX / y`, else `⌊x · y / denominator⌋`. -/
def mulDivDownN (x y d : Nat) : Option Nat :=
  if d = 0 ∨ (y ≠ 0 ∧ MAXN / y < x) then none else some (x * y / d)

/-- Solmate `mulDivUp(x, y, denominator)` on naturals: the same revert condition, else
`⌈x · y / denominator⌉` (as `ceilDivN`: floor plus one if the remainder is non-zero). -/
def mulDivUpN (x y d : Nat) : Option Nat :=
  if d = 0 ∨ (y ≠ 0 ∧ MAXN / y < x) then none else some (ceilDivN (x * y) d)

/-- What a reverting `mulDiv` leaves: `revert(0, 0)` with the world unchanged. -/
def MulDivRevert (m mf : Machine) (o : Outcome) : Prop :=
  o = .revert .empty ∧ mf.world = m.world

theorem Memory.read_zero_len (mem : Memory) (off : Nat) : mem.read off 0 = .empty := by
  rw [Memory.read, ← readBytes_eq_readPadded, readBytes_zero]

set_option maxHeartbeats 0 in
/-- **`mulDivDown` summary** (entry `0x0e62`, stack `d :: y :: x :: r :: rest`). -/
theorem mulDivDown_wp {i : SolmateVault.Immutables} (m : Machine) {d y x r : Word} {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hpc : m.frame.pc = 0xe62) (hs : m.frame.stack = d :: y :: x :: r :: rest)
    (hlen : rest.length ≤ 1010) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hg : 100 ≤ m.frame.gasLeft) :
    WP m (fun m' => ∃ v, mulDivDownN x.toNat y.toNat d.toNat = some v ∧
        m' = m.resumeAt r.toNat (BitVec.ofNat 256 v :: rest) (m.frame.gasLeft - 81))
      (fun mf o => mulDivDownN x.toNat y.toNat d.toNat = none ∧ MulDivRevert m mf o) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  pwp_steps
  by_cases hbad : (d.toNat = 0 ∨ (y.toNat ≠ 0 ∧ (2 ^ 256 - 1) / y.toNat < x.toNat))
  · have hz := mulDivGuard_eq_zero hbad
    simp only [hz]
    pwp_steps
    refine ⟨by simp only [mulDivDownN, MAXN, hbad, ↓reduceIte], ?_, rfl⟩
    rw [Memory.read_zero_len]
  · have hz : mulDivGuard x y d ≠ 0#256 := by rw [Ne, mulDivGuard_eq_zero_iff]; exact hbad
    pwp_steps
    refine WP.ret ⟨x.toNat * y.toNat / d.toNat, by simp only [mulDivDownN, MAXN, hbad, ↓reduceIte], ?_⟩
    simp only [Machine.resumeAt]
    rw [mulDivDownWord_eq (by omega)]

set_option maxHeartbeats 0 in
/-- **`mulDivUp` summary** (entry `0x0e7d`, stack `d :: y :: x :: r :: rest`). -/
theorem mulDivUp_wp {i : SolmateVault.Immutables} (m : Machine) {d y x r : Word} {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hpc : m.frame.pc = 0xe7d) (hs : m.frame.stack = d :: y :: x :: r :: rest)
    (hlen : rest.length ≤ 1010) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hg : 120 ≤ m.frame.gasLeft) :
    WP m (fun m' => ∃ v, mulDivUpN x.toNat y.toNat d.toNat = some v ∧
        m' = m.resumeAt r.toNat (BitVec.ofNat 256 v :: rest) (m.frame.gasLeft - 107))
      (fun mf o => mulDivUpN x.toNat y.toNat d.toNat = none ∧ MulDivRevert m mf o) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  pwp_steps
  by_cases hbad : (d.toNat = 0 ∨ (y.toNat ≠ 0 ∧ (2 ^ 256 - 1) / y.toNat < x.toNat))
  · have hz := mulDivGuard_eq_zero hbad
    simp only [hz]
    pwp_steps
    refine ⟨by simp only [mulDivUpN, MAXN, hbad, ↓reduceIte], ?_, rfl⟩
    rw [Memory.read_zero_len]
  · have hz : mulDivGuard x y d ≠ 0#256 := by rw [Ne, mulDivGuard_eq_zero_iff]; exact hbad
    pwp_steps
    refine WP.ret ⟨ceilDivN (x.toNat * y.toNat) d.toNat, by simp only [mulDivUpN, MAXN, hbad, ↓reduceIte], ?_⟩
    simp only [Machine.resumeAt]
    rw [mulDivUpWord_eq (by omega) (by omega)]

end Verified.Solmate.ERC4626
