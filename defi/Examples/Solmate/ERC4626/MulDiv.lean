import EvmLogic.Tactic.WpStep
import EvmLogic.Program.ExtraLogic
import EvmLogic.Solidity.ExtraWord
import Examples.Solmate.Contracts.SolmateVault
import EvmLogic.Tactic.Patched
import Examples.Solmate.ERC4626.SharesCode

/-!
# Solmate `FixedPointMathLib.mulDivDown` / `mulDivUp` in the compiled vault

The compiled `MockERC4626`, deployed with any immutables `i`
(`SolmateVault.runtimeCodeWith i`), contains each of Solmate's
two assembly `mulDiv` functions once, as an internal function called with
`JUMP` and stack `denominator :: y :: x :: return :: rest`:

| function | entry pc | gas on success |
|---|---|---|
| `mulDivDown(x, y, denominator)` | `0x0e62` | 81 |
| `mulDivUp(x, y, denominator)` | `0x0e7d` | 107 |

`mulDivDown_wp` / `mulDivUp_wp` summarise them once, for every machine executing the vault's
code at the entry pc: if the Solidity function does not revert (`mulDivDownN … = some v`,
the `Nat` mirror of the source and of the specification's `Vault.mulDivDown`), execution
returns to `return` with `v` on the stack and only pc, stack and gas changed
(`Machine.resumeAt`); otherwise the frame ends with `revert(0, 0)` and the world unchanged.
Callers compose them with `WP.bind_mono`.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

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

/-- A zero-length memory read is empty. -/
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

end EvmLeanSpecs.Refinement
