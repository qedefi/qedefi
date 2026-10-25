import Verified.Solady.Spec.Transfer

/-!
# Solady `ERC20` under the spec: `mint` and `burn` (`SoladyToken`'s open entry points)
-/

namespace Verified.Solady.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec
open EvmLean.Interpreter EvmLogic.Tactic Verified.Solady.Contracts Verified.Solady.Spec.AnyGas
open QEDefi.ERC4626

/-- The world after Solady's `_mint(dst, v)`: the supply raised, then the balance (unchecked). -/
def mintWorld (crypto : Crypto) (w : World) (t dst : Address) (v : Word) : World :=
  (w.sstore t supplySlot (w.sload t supplySlot + v)).sstore t (balSlot crypto dst)
    ((w.sstore t supplySlot (w.sload t supplySlot + v)).sload t (balSlot crypto dst) + v)

/-- The world after Solady's `_burn(src, v)`: the balance lowered, then the supply (unchecked). -/
def burnWorld (crypto : Crypto) (w : World) (t src : Address) (v : Word) : World :=
  (w.sstore t (balSlot crypto src) (w.sload t (balSlot crypto src) - v)).sstore t supplySlot
    ((w.sstore t (balSlot crypto src) (w.sload t (balSlot crypto src) - v)).sload t supplySlot - v)

/-- `mint(dst, v)`'s code-level end: `TotalSupplyOverflow` reverts, or success with
`mintWorld`. -/
def MintPost (m : Machine) (dst : Address) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  (2 ^ 256 ≤ (m.world.sload m.frame.msg.currentTarget supplySlot).toNat + v.toNat →
    ∃ out, o = .revert out) ∧
  ((m.world.sload m.frame.msg.currentTarget supplySlot).toNat + v.toNat < 2 ^ 256 →
    m.frame.msg.value = 0 ∧ (∃ out, o = .success out) ∧
    mf.world = mintWorld m.ctx.crypto m.world m.frame.msg.currentTarget dst v ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts)

/-- `burn(src, v)`'s code-level end: `InsufficientBalance` reverts, or success with
`burnWorld`. -/
def BurnPost (m : Machine) (src : Address) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  ((m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat < v.toNat →
    ∃ out, o = .revert out) ∧
  (v.toNat ≤ (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat →
    m.frame.msg.value = 0 ∧ (∃ out, o = .success out) ∧
    mf.world = burnWorld m.ctx.crypto m.world m.frame.msg.currentTarget src v ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts)

set_option maxHeartbeats 0 in
theorem mint_low (m : Machine) (dst : Address) (v : Word)
    (hf : Fresh SoladyToken.runtimeCode m)
    (hd : Args m.frame.msg.data 0x40c10f19 [Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (MintPost m dst v) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil] at hsize harg0 harg1
  have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  apply WP.halts_of_false
  solady_fresh_intro
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
    Nat.mul_one] at harg0 harg1
  hwp_steps [hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0, harg1,
    ofAddress_and_addressMask, Solidity.eq_self]
  all_goals
    have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
    try simp (disch := simp (disch := decide) only [Memory.read_expand,
      Memory.read_storeWord_of_disjoint, read_seed_tail]) only [read_balRow] at *
  have hno := lt_add_iszero_ne (by with_reducible assumption)
  exact pwp_stop (by pcode_fact) (hok _ _
    ⟨fun h => absurd h (Nat.not_le.mpr hno), fun _ => ⟨hv, ⟨_, rfl⟩, rfl, rfl, rfl⟩⟩)

set_option maxHeartbeats 0 in
theorem burn_low (m : Machine) (src : Address) (v : Word)
    (hf : Fresh SoladyToken.runtimeCode m)
    (hd : Args m.frame.msg.data 0x9dc29fac [Word.ofAddress src, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (BurnPost m src v) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil] at hsize harg0 harg1
  have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  apply WP.halts_of_false
  solady_fresh_intro
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
    Nat.mul_one] at harg0 harg1
  hwp_steps [hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0, harg1,
    ofAddress_and_addressMask, Solidity.eq_self]
  all_goals
    have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
    try simp (disch := simp (disch := decide) only [Memory.read_expand,
      Memory.read_storeWord_of_disjoint, read_seed_tail]) only [read_balRow] at *
  have hle := le_of_iszero_gt (by with_reducible assumption)
  exact pwp_stop (by pcode_fact) (hok _ _
    ⟨fun h => absurd (Nat.lt_of_lt_of_le h hle) (Nat.lt_irrefl _),
      fun _ => ⟨hv, ⟨_, rfl⟩, rfl, rfl, rfl⟩⟩)

end Verified.Solady.Spec
