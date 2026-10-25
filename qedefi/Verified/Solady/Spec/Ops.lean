import Verified.Solady.Spec.Transfer
import EvmLogic.Tactic.StepExt

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

set_option maxHeartbeats 0 in
theorem mint_high (m : Machine) (dst : Address) (v : Word)
    (hf : Fresh SoladyToken.runtimeCode m)
    (hd : Args m.frame.msg.data 0x40c10f19 [Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (MintPost m dst v) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil] at hsize harg0 harg1
  have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
    Nat.mul_one] at harg0 harg1
  by_cases hno : (m_world.sload m_msg.currentTarget 96006856662521017420#256).toNat + v.toNat <
      2 ^ 256
  · have hno' := lt_add_iszero_one hno
    pwp_xsteps [hval, hst, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0, harg1,
      hok, ofAddress_and_addressMask, Solidity.eq_self, hno']
    simp (disch := simp (disch := decide) only [Memory.read_expand,
      Memory.read_storeWord_of_disjoint, read_seed_tail]) only [read_balRow]
    exact pwp_stop (by pcode_fact)
      ⟨fun h => absurd h (Nat.not_le.mpr hno), fun _ => ⟨hval, ⟨_, rfl⟩, rfl, rfl, rfl⟩⟩
  · have hno' := lt_add_iszero_zero (Nat.le_of_not_lt hno)
    pwp_xsteps [hval, hst, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0, harg1,
      hok, ofAddress_and_addressMask, Solidity.eq_self, hno']
    exact ⟨fun _ => ⟨_, rfl⟩, fun h => absurd h hno⟩

set_option maxHeartbeats 0 in
theorem burn_high (m : Machine) (src : Address) (v : Word)
    (hf : Fresh SoladyToken.runtimeCode m)
    (hd : Args m.frame.msg.data 0x9dc29fac [Word.ofAddress src, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (BurnPost m src v) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil] at hsize harg0 harg1
  have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
    Nat.mul_one] at harg0 harg1
  pwp_steps [hval, hst, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0, harg1,
    hok, ofAddress_and_addressMask, Solidity.eq_self]
  simp (disch := simp (disch := decide) only [Memory.read_expand,
    Memory.read_storeWord_of_disjoint, read_seed_tail]) only [read_balRow]
  by_cases hle : v.toNat ≤ (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto src)).toNat
  · have hc := iszero_gt_of_le hle
    simp only [balSlot] at hc hle
    simp only [hc]
    pwp_xsteps [hval, hst, hc, Memory.read_64, ofAddress_and_addressMask, Solidity.eq_self]
    exact pwp_stop (by pcode_fact) ⟨fun h => absurd (Nat.lt_of_lt_of_le h hle) (Nat.lt_irrefl _),
      fun _ => ⟨hval, ⟨_, rfl⟩, rfl, rfl, rfl⟩⟩
  · have hc := iszero_gt_of_lt (Nat.lt_of_not_le hle)
    simp only [balSlot] at hc hle
    simp only [hc]
    pwp_steps [hval, hst, hc, Memory.read_64]
    exact ⟨fun _ => ⟨_, rfl⟩, fun h => absurd h hle⟩

/-! ## The obligation -/

theorem ofAddress_toAddress {x : Word} (h : x.toNat < 2 ^ 160) :
    Word.ofAddress x.toAddress = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [Word.ofAddress, Word.toAddress, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]

/-- The decoder's arguments are the ABI arguments it read. -/
theorem args_of_ops {data : ByteArray} {sel : Nat} {a : Address} (hsel : Abi.selectorOf data = sel)
    (hsz : ¬ data.size < 68) (ha : addrArg (argWord data 0) = some a) :
    Args data sel [Word.ofAddress a, argWord data 1] := by
  unfold addrArg at ha
  split at ha
  · rename_i hlt
    cases ha
    refine ⟨hsel, by simp; omega, ?_⟩
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · simp only [List.getElem_cons_zero]; rw [ofAddress_toAddress hlt]; rfl
    · rfl
  · cases ha

theorem solady_op_mint (s : VState Address) (c d : Address) (v : ℕ) :
    M.op s (.mint c d v) = if QEDefi.Math.MAX < s.supply + v then none
      else some { s with supply := s.supply + v, bal := s.bal + Finsupp.single d v } := by
  simp [M, Solady.soladyModel, Variant.stepOp, Variant.mint, Variant.solady, Variant.standard,
    Auth.allows, Variant.units]

theorem solady_op_burn (s : VState Address) (c a : Address) (v : ℕ) :
    M.op s (.burn c a v) = if s.bal a < v then none
      else some { s with supply := s.supply - v, bal := s.bal - Finsupp.single a v } := by
  simp [M, Solady.soladyModel, Variant.stepOp, Variant.burn, Variant.solady, Variant.standard,
    Auth.allows, Variant.units]

/-- Under the model's invariant an actor's balance is at most the supply, which fits a word. -/
theorem bal_le_supply {s : VState Address} (hw : M.wf s) (a : Address) :
    s.bal a ≤ s.supply ∧ s.supply ≤ QEDefi.Math.MAX := by
  simp only [M, Solady.soladyModel, Variant.model_wf, Variant.WF, Variant.solady,
    Variant.standard, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hw
  have := Token.le_total s.bal a
  constructor <;> omega

theorem op_mint (Act : Finset Address) (m : Machine) (hs : Start SoladyToken.runtimeCode soladyAbs M Act m)
    (a : Address) (haA : a ∈ Act) (hval : m.frame.msg.value = 0)
    (hd : Args m.frame.msg.data 0x40c10f19 [Word.ofAddress a, argWord m.frame.msg.data 1]) :
    Halts m fun mf o =>
      OpMatches soladyAbs M Act (.mint m.frame.msg.caller a (argWord m.frame.msg.data 1).toNat)
        m mf o ∨ (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)) := by
  set v := argWord m.frame.msg.data 1
  have hS := hs.sound
  have hpre := pre_eq hs hval
  have hwf := hs.wf
  refine halts_split' (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => mint_high m a v hs.fresh hd hs.size hval hG.2 hG.1)
    (mint_low m a v hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  left
  simp only [OpMatches]
  have hsup : (pre soladyAbs Act m).supply =
      (m.world.sload m.frame.msg.currentTarget supplySlot).toNat := by rw [hpre]; rfl
  rw [solady_op_mint, hsup]
  by_cases hov : 2 ^ 256 ≤ (m.world.sload m.frame.msg.currentTarget supplySlot).toNat + v.toNat
  · rw [ite_pos' (by simp only [QEDefi.Math.MAX]; omega)]
    obtain ⟨out, rfl⟩ := hrev hov
    trivial
  · rw [ite_neg' (by simp only [QEDefi.Math.MAX]; omega)]
    obtain ⟨-, ho, hw, ht, hcr⟩ := hok (Nat.lt_of_not_le hov)
    refine ⟨ho, ?_, ?_, ht, hcr⟩
    · show read _ _ _ _ = _
      have hbd : (pre soladyAbs Act m).bal a =
          (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto a)).toNat := by
        rw [hpre]; simp [read, balances, haA]
      have hb := (bal_le_supply hwf a).1
      rw [hbd, hsup] at hb
      rw [hw, mintWorld, read_sstore_bal hS haA, read_sstore_supply hS,
        World.sload_sstore_ne_key _ _ _ (hS.bal_supply a haA), hpre]
      simp only [read, balances_sstore_supply hS]
      congr 1
      · ext b
        simp only [Finsupp.update_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
        by_cases hba : b = a
        · rw [hba]
          have hlt : (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto a)).toNat +
              v.toNat < 2 ^ 256 := by omega
          simp only [balances, Finsupp.onFinset_apply, haA, ↓reduceIte, BitVec.toNat_add,
            Nat.mod_eq_of_lt hlt]
        · simp [hba, Ne.symm hba]
      · rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    · rw [hw, mintWorld]
      exact FrameKeeps.sstore (bal_mem _ haA) (FrameKeeps.sstore supply_mem frameKeeps_refl)

theorem op_burn (Act : Finset Address) (m : Machine) (hs : Start SoladyToken.runtimeCode soladyAbs M Act m)
    (a : Address) (haA : a ∈ Act) (hval : m.frame.msg.value = 0)
    (hd : Args m.frame.msg.data 0x9dc29fac [Word.ofAddress a, argWord m.frame.msg.data 1]) :
    Halts m fun mf o =>
      OpMatches soladyAbs M Act (.burn m.frame.msg.caller a (argWord m.frame.msg.data 1).toNat)
        m mf o ∨ (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)) := by
  set v := argWord m.frame.msg.data 1
  have hS := hs.sound
  have hpre := pre_eq hs hval
  have hwf := hs.wf
  refine halts_split' (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => burn_high m a v hs.fresh hd hs.size hval hG.2 hG.1)
    (burn_low m a v hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  left
  simp only [OpMatches]
  have hbd : (pre soladyAbs Act m).bal a =
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto a)).toNat := by
    rw [hpre]; simp [read, balances, haA]
  rw [solady_op_burn, hbd]
  by_cases hlt : (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto a)).toNat < v.toNat
  · rw [ite_pos' hlt]
    obtain ⟨out, rfl⟩ := hrev hlt
    trivial
  · rw [ite_neg' hlt]
    obtain ⟨-, ho, hw, ht, hcr⟩ := hok (Nat.le_of_not_lt hlt)
    refine ⟨ho, ?_, ?_, ht, hcr⟩
    · show read _ _ _ _ = _
      have hsup : (pre soladyAbs Act m).supply =
          (m.world.sload m.frame.msg.currentTarget supplySlot).toNat := by rw [hpre]; rfl
      have hb := (bal_le_supply hwf a).1
      rw [hbd, hsup] at hb
      rw [hw, burnWorld, read_sstore_supply hS, read_sstore_bal hS haA,
        World.sload_sstore_ne_key _ _ _ (hS.bal_supply a haA).symm, hpre]
      simp only [read]
      congr 1
      swap
      · rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]; rfl
      · ext b
        simp only [Finsupp.update_apply, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
        by_cases hba : b = a
        · rw [hba]
          have hle : v ≤ m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto a) := by
            rw [BitVec.le_def]; omega
          simp [balances, haA, BitVec.toNat_sub_of_le hle]
        · simp [hba, Ne.symm hba]
    · rw [hw, burnWorld]
      exact FrameKeeps.sstore supply_mem (FrameKeeps.sstore (bal_mem _ haA) frameKeeps_refl)

/-- **The other entry points**: `mint` and `burn`. -/
theorem ops_spec : OpSpec SoladyToken.runtimeCode soladyAbs M g₀ ops opAddrs := by
  intro Act m e hs hops haddr
  simp only [ops] at hops
  split at hops
  · cases hops
  rename_i hvs
  have hval : m.frame.msg.value = 0 := by
    have : m.frame.msg.value.toNat = 0 := by simp only [not_or] at hvs; omega
    exact BitVec.eq_of_toNat_eq this
  have hsz : ¬ m.frame.msg.data.size < 68 := fun h => hvs (.inr h)
  split at hops
  · rename_i hsel
    cases ha : addrArg (argWord m.frame.msg.data 0) with
    | none => simp [ha] at hops
    | some a =>
      simp only [ha, Option.map_some, Option.some.injEq] at hops
      subst hops
      have haA : a ∈ Act := haddr a (by simp [opAddrs])
      exact op_mint Act m hs a haA hval (args_of_ops hsel hsz ha)
  split at hops
  · rename_i _ hsel
    cases ha : addrArg (argWord m.frame.msg.data 0) with
    | none => simp [ha] at hops
    | some a =>
      simp only [ha, Option.map_some, Option.some.injEq] at hops
      subst hops
      have haA : a ∈ Act := haddr a (by simp [opAddrs])
      exact op_burn Act m hs a haA hval (args_of_ops hsel hsz ha)
  · cases hops

end Verified.Solady.Spec
