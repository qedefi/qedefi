import Verified.WeirdERC20.BNB.Spec.TransferFrom
import Verified.WeirdERC20.BNB.Spec.Fallback

/-!
# BNB under the spec: `burn`, `freeze`, `unfreeze`

Each checks the caller's row (`balanceOf` for `burn`/`freeze`, `freezeOf` for `unfreeze`) against
`v` and `v > 0` (`REVERT`), lowers that row, then lowers the supply (`burn`) or raises the other
row (`SafeMath`, `REVERT` on failure), logs its event and returns `true`.
-/

namespace Verified.WeirdERC20.BNB.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.BNB.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

/-- The `freezeOf` row of `a` (slot 6). -/
abbrev frzSlot (crypto : Crypto) (a : Address) : Word := mappingSlot crypto (Word.ofAddress a) 6#256

theorem fit_of_lt_s {S v : Word} (h : ((S + v).lt S).iszero.iszero = 0) :
    S.toNat + v.toNat < 2 ^ 256 := by
  by_contra hc
  rw [Verified.Solady.Spec.lt_add_iszero_zero (Nat.le_of_not_lt hc)] at h
  exact absurd h (by decide)

theorem iszero23 {x : Word} (h1 : x.iszero.iszero ≠ 0) (h2 : x.iszero.iszero.iszero ≠ 0) :
    False := by
  by_cases hx : x = 0
  · subst hx; exact h1 (by decide)
  · have h0 : x.iszero = 0 := by
      have h' : (x == 0#256) = false := by simpa using hx
      simp [Word.iszero, Word.ofBool, h']
    exact h2 (by rw [h0]; decide)

/-- The world after `v` is taken from the row `k`. -/
def subWorld (w : World) (t : Address) (k v : Word) : World := w.sstore t k (w.sload t k - v)

/-- `burn(v)`'s code-level end: a balance below `v` or a zero `v` revert; otherwise (when the
supply read after the debit covers `v`) the debit and the supply lowered, `true`. -/
def BurnPost (m : Machine) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  ((m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat <
      v.toNat ∨ v = 0 → ∃ out, o = .revert out) ∧
  (v.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller)).toNat → v ≠ 0 →
    v.toNat ≤ ((subWorld m.world m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller) v).sload m.frame.msg.currentTarget 3#256).toNat →
    m.frame.msg.isStatic = false ∧ o = .success (Bytes.ofWord 1) ∧
    mf.world = subWorld (subWorld m.world m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller) v) m.frame.msg.currentTarget 3#256 v ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts)

set_option maxHeartbeats 0 in
theorem burn_low (m : Machine) (v : Word) (hf : Fresh BNB.runtimeCode m)
    (hd : Args m.frame.msg.data 0x42966c68 [v])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (BurnPost m v) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero,
    Nat.mul_zero, Nat.add_zero] at hsize harg0
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, Memory.read_64, ofAddress_and_addressMask,
    addressMask_and_ofAddress]
  all_goals
    have hbs := le_of_lt_iszero (b := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord 5#256)))
      (by with_reducible assumption)
    have hv0 := ne_zero_of_gt (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨fun h => ?_, fun _ _ _ =>
      ⟨‹_›, ?_, rfl, rfl, rfl⟩⟩
    · rcases h with h | h
      · exact absurd (Nat.lt_of_lt_of_le h hbs) (Nat.lt_irrefl _)
      · exact absurd h hv0
    · simp only [outputData]
      apwp_norm []
      rfl

set_option maxHeartbeats 0 in
theorem burn_high (m : Machine) (v : Word) (hf : Fresh BNB.runtimeCode m)
    (hd : Args m.frame.msg.data 0x42966c68 [v])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (BurnPost m v) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero,
    Nat.mul_zero, Nat.add_zero] at hsize harg0
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  by_cases hbc : v.toNat ≤
      (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto m_msg.caller)).toNat
  swap
  · have h1 := lt_iszero_zero (Nat.lt_of_not_le hbc)
    simp only [balSlot, mappingSlot] at h1
    pwp_steps [hval, hst, hsel', hz, h1, harg0, Memory.read_64, ofAddress_and_addressMask,
      addressMask_and_ofAddress]
    exact ⟨fun _ => ⟨_, rfl⟩, fun h => absurd h hbc⟩
  have h1 := lt_iszero_one hbc
  simp only [balSlot, mappingSlot] at h1
  by_cases hv0 : v = 0
  · subst hv0
    pwp_steps [hval, hst, hsel', hz, h1, harg0, Memory.read_64, ofAddress_and_addressMask,
      addressMask_and_ofAddress]
    exact ⟨fun _ => ⟨_, rfl⟩, fun _ h => absurd rfl h⟩
  have h2 := gt_zero_iszero2 hv0
  have h3 := Verified.Solady.Spec.iszero_gt_of_le hbc
  simp only [balSlot, mappingSlot] at h3
  by_cases hs : v.toNat ≤ ((subWorld m_world m_msg.currentTarget
      (balSlot m_ctx.crypto m_msg.caller) v).sload m_msg.currentTarget 3#256).toNat
  swap
  · have h4 := Verified.Solady.Spec.iszero_gt_of_lt (Nat.lt_of_not_le hs)
    simp only [subWorld, balSlot, mappingSlot] at h4
    pwp_steps [hval, hst, hsel', hz, h1, h2, h3, h4, harg0, Memory.read_64,
      ofAddress_and_addressMask, addressMask_and_ofAddress]
    exact ⟨fun _ => ⟨_, rfl⟩, fun _ _ h => absurd h hs⟩
  have h4 := Verified.Solady.Spec.iszero_gt_of_le hs
  simp only [subWorld, balSlot, mappingSlot] at h4
  pwp_steps [hval, hst, hsel', hz, h1, h2, h3, h4, harg0, Memory.read_64,
    ofAddress_and_addressMask, addressMask_and_ofAddress]
  exact ⟨fun h => by
      rcases h with h | h
      · exact absurd (Nat.lt_of_lt_of_le h hbc) (Nat.lt_irrefl _)
      · exact absurd h hv0,
    fun _ _ _ => ⟨hst, rfl, rfl, rfl, rfl⟩⟩

/-- The world after `v` is added to the row `k`. -/
def addWorld (w : World) (t : Address) (k v : Word) : World := w.sstore t k (w.sload t k + v)

/-- `freeze(v)`'s code-level end: a source row below `v` or a zero `v` revert; otherwise (when
the target row read after the debit takes `v`) the source row lowered, the target raised, `true`. -/
def FreezePost (m : Machine) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  ((m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat <
      v.toNat ∨ v = 0 ∨
    2 ^ 256 ≤ ((subWorld m.world m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)
      v).sload m.frame.msg.currentTarget (frzSlot m.ctx.crypto m.frame.msg.caller)).toNat + v.toNat →
    ∃ out, o = .revert out) ∧
  (v.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller)).toNat → v ≠ 0 →
    ((subWorld m.world m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller) v).sload
      m.frame.msg.currentTarget (frzSlot m.ctx.crypto m.frame.msg.caller)).toNat + v.toNat <
        2 ^ 256 →
    m.frame.msg.isStatic = false ∧ o = .success (Bytes.ofWord 1) ∧
    mf.world = addWorld (subWorld m.world m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller) v) m.frame.msg.currentTarget
        (frzSlot m.ctx.crypto m.frame.msg.caller) v ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts)

set_option maxHeartbeats 0 in
theorem freeze_low (m : Machine) (v : Word) (hf : Fresh BNB.runtimeCode m)
    (hd : Args m.frame.msg.data 0xd7a78db8 [v])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (FreezePost m v) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero,
    Nat.mul_zero, Nat.add_zero] at hsize harg0
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, Memory.read_64, ofAddress_and_addressMask,
    addressMask_and_ofAddress]
  all_goals
    try exact (iszero23 (x := Word.lt ((m_world.sstore m_msg.currentTarget (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++
        Bytes.ofWord 5#256)) (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord 5#256)) - v)).sload m_msg.currentTarget
        (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord 6#256)) + v) ((m_world.sstore m_msg.currentTarget (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++
        Bytes.ofWord 5#256)) (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord 5#256)) - v)).sload m_msg.currentTarget
        (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord 6#256))))
        (by with_reducible assumption) (by with_reducible assumption)).elim
  all_goals
    have hbs := le_of_lt_iszero (b := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord 5#256)))
      (by with_reducible assumption)
    have hv0 := ne_zero_of_gt (by with_reducible assumption)
    have hfit := fit_of_lt_s (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨fun h => ?_, fun _ _ _ =>
      ⟨‹_›, ?_, rfl, rfl, rfl⟩⟩
    · rcases h with h | h | h
      · exact absurd (Nat.lt_of_lt_of_le h hbs) (Nat.lt_irrefl _)
      · exact absurd h hv0
      · exact absurd h (Nat.not_le.2 hfit)
    · simp only [outputData]
      apwp_norm []
      rfl

set_option maxHeartbeats 0 in
theorem freeze_high (m : Machine) (v : Word) (hf : Fresh BNB.runtimeCode m)
    (hd : Args m.frame.msg.data 0xd7a78db8 [v])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (FreezePost m v) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero,
    Nat.mul_zero, Nat.add_zero] at hsize harg0
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  by_cases hbc : v.toNat ≤
      (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto m_msg.caller)).toNat
  swap
  · have h1 := lt_iszero_zero (Nat.lt_of_not_le hbc)
    simp only [balSlot, balSlot, mappingSlot] at h1
    pwp_steps [hval, hst, hsel', hz, h1, harg0, Memory.read_64, ofAddress_and_addressMask,
      addressMask_and_ofAddress]
    exact ⟨fun _ => ⟨_, rfl⟩, fun h => absurd h hbc⟩
  have h1 := lt_iszero_one hbc
  simp only [balSlot, balSlot, mappingSlot] at h1
  by_cases hv0 : v = 0
  · subst hv0
    pwp_steps [hval, hst, hsel', hz, h1, harg0, Memory.read_64, ofAddress_and_addressMask,
      addressMask_and_ofAddress]
    exact ⟨fun _ => ⟨_, rfl⟩, fun _ h => absurd rfl h⟩
  have h2 := gt_zero_iszero2 hv0
  have h3 := Verified.Solady.Spec.iszero_gt_of_le hbc
  simp only [balSlot, balSlot, mappingSlot] at h3
  by_cases hs : ((subWorld m_world m_msg.currentTarget (balSlot m_ctx.crypto m_msg.caller) v).sload
      m_msg.currentTarget (frzSlot m_ctx.crypto m_msg.caller)).toNat + v.toNat < 2 ^ 256
  swap
  · have h4 := Verified.Solady.Spec.lt_add_iszero_zero (Nat.le_of_not_lt hs)
    simp only [subWorld, frzSlot, balSlot, mappingSlot] at h4
    pwp_steps [hval, hst, hsel', hz, h1, h2, h3, h4, harg0, Memory.read_64,
      ofAddress_and_addressMask, addressMask_and_ofAddress]
    exact ⟨fun _ => ⟨_, rfl⟩, fun _ _ h => absurd h hs⟩
  have h4 := Verified.Solady.Spec.lt_add_iszero_one hs
  have h5 := lt_add_iszero_one' hs
  simp only [subWorld, frzSlot, balSlot, mappingSlot] at h4 h5
  pwp_steps [hval, hst, hsel', hz, h1, h2, h3, h4, h5, harg0, Memory.read_64,
    ofAddress_and_addressMask, addressMask_and_ofAddress]
  exact ⟨fun h => by
      rcases h with h | h | h
      · exact absurd (Nat.lt_of_lt_of_le h hbc) (Nat.lt_irrefl _)
      · exact absurd h hv0
      · exact absurd h (Nat.not_le.2 hs),
    fun _ _ _ => ⟨hst, rfl, rfl, rfl, rfl⟩⟩

/-- `unfreeze(v)`'s code-level end: a source row below `v` or a zero `v` revert; otherwise (when
the target row read after the debit takes `v`) the source row lowered, the target raised, `true`. -/
def UnfreezePost (m : Machine) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  ((m.world.sload m.frame.msg.currentTarget (frzSlot m.ctx.crypto m.frame.msg.caller)).toNat <
      v.toNat ∨ v = 0 ∨
    2 ^ 256 ≤ ((subWorld m.world m.frame.msg.currentTarget (frzSlot m.ctx.crypto m.frame.msg.caller)
      v).sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat + v.toNat →
    ∃ out, o = .revert out) ∧
  (v.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (frzSlot m.ctx.crypto m.frame.msg.caller)).toNat → v ≠ 0 →
    ((subWorld m.world m.frame.msg.currentTarget (frzSlot m.ctx.crypto m.frame.msg.caller) v).sload
      m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat + v.toNat <
        2 ^ 256 →
    m.frame.msg.isStatic = false ∧ o = .success (Bytes.ofWord 1) ∧
    mf.world = addWorld (subWorld m.world m.frame.msg.currentTarget
      (frzSlot m.ctx.crypto m.frame.msg.caller) v) m.frame.msg.currentTarget
        (balSlot m.ctx.crypto m.frame.msg.caller) v ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts)

set_option maxHeartbeats 0 in
theorem unfreeze_low (m : Machine) (v : Word) (hf : Fresh BNB.runtimeCode m)
    (hd : Args m.frame.msg.data 0x6623fc46 [v])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (UnfreezePost m v) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero,
    Nat.mul_zero, Nat.add_zero] at hsize harg0
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, Memory.read_64, ofAddress_and_addressMask,
    addressMask_and_ofAddress]
  all_goals
    try exact (iszero23 (x := Word.lt ((m_world.sstore m_msg.currentTarget (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++
        Bytes.ofWord 6#256)) (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord 6#256)) - v)).sload m_msg.currentTarget
        (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord 5#256)) + v) ((m_world.sstore m_msg.currentTarget (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++
        Bytes.ofWord 6#256)) (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord 6#256)) - v)).sload m_msg.currentTarget
        (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord 5#256))))
        (by with_reducible assumption) (by with_reducible assumption)).elim
  all_goals
    have hbs := le_of_lt_iszero (b := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord 6#256)))
      (by with_reducible assumption)
    have hv0 := ne_zero_of_gt (by with_reducible assumption)
    have hfit := fit_of_lt_s (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨fun h => ?_, fun _ _ _ =>
      ⟨‹_›, ?_, rfl, rfl, rfl⟩⟩
    · rcases h with h | h | h
      · exact absurd (Nat.lt_of_lt_of_le h hbs) (Nat.lt_irrefl _)
      · exact absurd h hv0
      · exact absurd h (Nat.not_le.2 hfit)
    · simp only [outputData]
      apwp_norm []
      rfl

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 0 in
theorem unfreeze_high (m : Machine) (v : Word) (hf : Fresh BNB.runtimeCode m)
    (hd : Args m.frame.msg.data 0x6623fc46 [v])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (UnfreezePost m v) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero,
    Nat.mul_zero, Nat.add_zero] at hsize harg0
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  by_cases hbc : v.toNat ≤
      (m_world.sload m_msg.currentTarget (frzSlot m_ctx.crypto m_msg.caller)).toNat
  swap
  · have h1 := lt_iszero_zero (Nat.lt_of_not_le hbc)
    simp only [frzSlot, balSlot, mappingSlot] at h1
    pwp_steps [hval, hst, hsel', hz, h1, harg0, Memory.read_64, ofAddress_and_addressMask,
      addressMask_and_ofAddress]
    exact ⟨fun _ => ⟨_, rfl⟩, fun h => absurd h hbc⟩
  have h1 := lt_iszero_one hbc
  simp only [frzSlot, balSlot, mappingSlot] at h1
  by_cases hv0 : v = 0
  · subst hv0
    pwp_steps [hval, hst, hsel', hz, h1, harg0, Memory.read_64, ofAddress_and_addressMask,
      addressMask_and_ofAddress]
    exact ⟨fun _ => ⟨_, rfl⟩, fun _ h => absurd rfl h⟩
  have h2 := gt_zero_iszero2 hv0
  have h3 := Verified.Solady.Spec.iszero_gt_of_le hbc
  simp only [frzSlot, balSlot, mappingSlot] at h3
  by_cases hs : ((subWorld m_world m_msg.currentTarget (frzSlot m_ctx.crypto m_msg.caller) v).sload
      m_msg.currentTarget (balSlot m_ctx.crypto m_msg.caller)).toNat + v.toNat < 2 ^ 256
  swap
  · have h4 := Verified.Solady.Spec.lt_add_iszero_zero (Nat.le_of_not_lt hs)
    simp only [subWorld, frzSlot, balSlot, mappingSlot] at h4
    pwp_steps [hval, hst, hsel', hz, h1, h2, h3, h4, harg0, Memory.read_64,
      ofAddress_and_addressMask, addressMask_and_ofAddress]
    exact ⟨fun _ => ⟨_, rfl⟩, fun _ _ h => absurd h hs⟩
  have h4 := Verified.Solady.Spec.lt_add_iszero_one hs
  have h5 := lt_add_iszero_one' hs
  simp only [subWorld, frzSlot, balSlot, mappingSlot] at h4 h5
  pwp_steps [hval, hst, hsel', hz, h1, h2, h3, h4, h5, harg0, Memory.read_64,
    ofAddress_and_addressMask, addressMask_and_ofAddress]
  exact ⟨fun h => by
      rcases h with h | h | h
      · exact absurd (Nat.lt_of_lt_of_le h hbc) (Nat.lt_irrefl _)
      · exact absurd h hv0
      · exact absurd h (Nat.not_le.2 hs),
    fun _ _ _ => ⟨hst, rfl, rfl, rfl, rfl⟩⟩

/-! ## The obligation -/

set_option linter.unusedSimpArgs false in
theorem bnb_op_burn (s : VState Address) (c : Address) (v : ℕ) :
    M.op s (.burn c c v) = if v = 0 ∨ s.bal c < v then none
      else some { s with supply := s.supply - v, bal := s.bal - Finsupp.single c v } := by
  by_cases h1 : v = 0
  · simp [M, QEDefi.ERC20.Spec.BNB.bnbModel, Variant.stepOp, Variant.burn, Variant.bnb,
      Variant.standard, Auth.allows, h1]
  · by_cases h2 : s.bal c < v
    · simp [M, QEDefi.ERC20.Spec.BNB.bnbModel, Variant.stepOp, Variant.burn, Variant.bnb,
        Variant.standard, Auth.allows, Variant.units, h1, h2]
    · simp [M, QEDefi.ERC20.Spec.BNB.bnbModel, Variant.stepOp, Variant.burn, Variant.bnb,
        Variant.standard, Auth.allows, Variant.units, h1, h2]

set_option linter.unusedSimpArgs false in
theorem bnb_op_freeze (s : VState Address) (c : Address) (v : ℕ) :
    M.op s (.freeze c v) = if s.bal c < v ∨ v = 0 ∨ QEDefi.Math.MAX < s.frozen c + v then none
      else some { s with
        bal := s.bal - Finsupp.single c v
        frozen := s.frozen + Finsupp.single c v } := by
  by_cases h1 : s.bal c < v
  · simp [M, QEDefi.ERC20.Spec.BNB.bnbModel, Variant.stepOp, Variant.freeze, Variant.bnb,
      Variant.standard, h1]
  by_cases h2 : v = 0
  · simp [M, QEDefi.ERC20.Spec.BNB.bnbModel, Variant.stepOp, Variant.freeze, Variant.bnb,
      Variant.standard, h1, h2]
  by_cases h3 : QEDefi.Math.MAX < s.frozen c + v
  · simp [M, QEDefi.ERC20.Spec.BNB.bnbModel, Variant.stepOp, Variant.freeze, Variant.bnb,
      Variant.standard, h1, h2, h3]
  · simp [M, QEDefi.ERC20.Spec.BNB.bnbModel, Variant.stepOp, Variant.freeze, Variant.bnb,
      Variant.standard, h1, h2, h3]

set_option linter.unusedSimpArgs false in
theorem bnb_op_unfreeze (s : VState Address) (c : Address) (v : ℕ) :
    M.op s (.unfreeze c v) = if s.frozen c < v ∨ v = 0 ∨ QEDefi.Math.MAX < s.bal c + v then none
      else some { s with
        frozen := s.frozen - Finsupp.single c v
        bal := s.bal + Finsupp.single c v } := by
  by_cases h1 : s.frozen c < v
  · simp [M, QEDefi.ERC20.Spec.BNB.bnbModel, Variant.stepOp, Variant.unfreeze, Variant.bnb,
      Variant.standard, h1]
  by_cases h2 : v = 0
  · simp [M, QEDefi.ERC20.Spec.BNB.bnbModel, Variant.stepOp, Variant.unfreeze, Variant.bnb,
      Variant.standard, h1, h2]
  by_cases h3 : QEDefi.Math.MAX < s.bal c + v
  · simp [M, QEDefi.ERC20.Spec.BNB.bnbModel, Variant.stepOp, Variant.unfreeze, Variant.bnb,
      Variant.standard, h1, h2, h3]
  · simp [M, QEDefi.ERC20.Spec.BNB.bnbModel, Variant.stepOp, Variant.unfreeze, Variant.bnb,
      Variant.standard, h1, h2, h3]

theorem bnbRead_sstore_bal {crypto : Crypto} {Act : Finset Address} {w : World} {t a : Address}
    (hS : bnbSound crypto Act) (ha : a ∈ Act) (x : Word) :
    bnbRead crypto Act (w.sstore t (balSlot crypto a) x) t =
      { bnbRead crypto Act w t with bal := (bnbRead crypto Act w t).bal.update a x.toNat } := by
  simp only [bnbRead, balSlot]
  rw [readMap_sstore (base := 5#256) hS (by simp) ha,
    readMap_sstore_other (base' := 6#256) hS (by simp) (by simp) (by decide) ha,
    readMap2_sstore_map (base2 := 7#256) hS (by simp) (by simp) ha]
  simp only [readSlot, sload_sstore_map (k := 3#256) (base := 5#256) (x := x) (t := t) (w := w) hS
    (by simp) (by simp) ha, sload_sstore_map (k := 4#256) (base := 5#256) (x := x) (t := t)
    (w := w) hS (by simp) (by simp) ha, World.balance_sstore]

theorem bnbRead_sstore_frz {crypto : Crypto} {Act : Finset Address} {w : World} {t a : Address}
    (hS : bnbSound crypto Act) (ha : a ∈ Act) (x : Word) :
    bnbRead crypto Act (w.sstore t (frzSlot crypto a) x) t =
      { bnbRead crypto Act w t with frozen := (bnbRead crypto Act w t).frozen.update a x.toNat } := by
  simp only [bnbRead, frzSlot]
  rw [readMap_sstore (base := 6#256) hS (by simp) ha,
    readMap_sstore_other (base' := 5#256) hS (by simp) (by simp) (by decide) ha,
    readMap2_sstore_map (base2 := 7#256) hS (by simp) (by simp) ha]
  simp only [readSlot, sload_sstore_map (k := 3#256) (base := 6#256) (x := x) (t := t) (w := w) hS
    (by simp) (by simp) ha, sload_sstore_map (k := 4#256) (base := 6#256) (x := x) (t := t)
    (w := w) hS (by simp) (by simp) ha, World.balance_sstore]

theorem bnbRead_sstore_supply {crypto : Crypto} {Act : Finset Address} {w : World} {t : Address}
    (hS : bnbSound crypto Act) (x : Word) :
    bnbRead crypto Act (w.sstore t 3#256 x) t =
      { bnbRead crypto Act w t with supply := x.toNat } := by
  simp only [bnbRead]
  rw [readMap_sstore_fixed (base := 5#256) hS (by simp) (by simp),
    readMap_sstore_fixed (base := 6#256) hS (by simp) (by simp),
    readMap2_sstore_fixed (base := 7#256) hS (by simp) (by simp)]
  simp only [readSlot, World.sload_sstore_self,
    World.sload_sstore_ne_key _ _ _ (show (4#256 : Word) ≠ 3#256 by decide), World.balance_sstore]

/-- Under the model's invariant an actor's balance is at most the supply. -/
theorem bnb_bal_le_supply {s : VState Address} (hw : M.wf s) (a : Address) :
    s.bal a ≤ s.supply := by
  simp only [M, QEDefi.ERC20.Spec.BNB.bnbModel, Variant.model_wf, Variant.WF, Variant.bnb,
    Variant.standard, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hw
  have := Token.le_total s.bal a
  omega

theorem args_one {data : ByteArray} {k : Nat} (hsel : Abi.selectorOf data = k)
    (hsz : ¬ data.size < 36) : Args data k [argWord data 0] := by
  refine ⟨hsel, by simp; omega, ?_⟩
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0) with rfl
  rfl

/-- The common start of an operation's obligation: the value is zero. -/
theorem op_burn (Act : Finset Address) (m : Machine) (hs : Start BNB.runtimeCode bnbAbs M Act m)
    (hval : m.frame.msg.value = 0) (hd : Args m.frame.msg.data 0x42966c68 [argWord m.frame.msg.data 0]) :
    Halts m fun mf o =>
      OpMatches bnbAbs M Act (.burn m.frame.msg.caller m.frame.msg.caller
        (argWord m.frame.msg.data 0).toNat) m mf o ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)) := by
  set v := argWord m.frame.msg.data 0
  have hS := hs.sound
  have hcA := hs.caller
  have hpre := pre_eq hs hval
  refine halts_split' (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => burn_high m v hs.fresh hd hs.size hval hG.2 hG.1)
    (burn_low m v hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  left
  simp only [OpMatches]
  have hbc : (pre bnbAbs Act m).bal m.frame.msg.caller =
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat := by
    rw [hpre]; simp [bnbRead, hcA]
  have hsup : (pre bnbAbs Act m).supply = (m.world.sload m.frame.msg.currentTarget 3#256).toNat := by
    rw [hpre]; rfl
  have hle := bnb_bal_le_supply hs.wf m.frame.msg.caller
  rw [hbc, hsup] at hle
  have hv0 : v.toNat = 0 ↔ v = 0 := ⟨fun h => BitVec.eq_of_toNat_eq (by simp [h]), fun h => by simp [h]⟩
  rw [bnb_op_burn, hbc]
  by_cases hr : v.toNat = 0 ∨
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat <
        v.toNat
  · rw [ite_pos' hr]
    obtain ⟨out, rfl⟩ := hrev (by rcases hr with h | h; exact .inr (hv0.1 h); exact .inl h)
    trivial
  rw [ite_neg' hr]
  simp only [not_or, not_lt] at hr
  obtain ⟨hz, hb⟩ := hr
  have hS1 : (subWorld m.world m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)
      v).sload m.frame.msg.currentTarget 3#256 = m.world.sload m.frame.msg.currentTarget 3#256 := by
    simp only [subWorld, balSlot]
    exact sload_sstore_map (k := 3#256) hS (by simp) (by simp) hcA
  obtain ⟨-, ho, hw, ht, hcr⟩ := hok hb (fun h => hz (hv0.2 h)) (by rw [hS1]; omega)
  refine ⟨⟨_, ho⟩, ?_, ?_, ht, hcr⟩
  · show bnbRead _ _ _ _ = _
    rw [hw, subWorld, hS1, bnbRead_sstore_supply hS, subWorld, bnbRead_sstore_bal hS hcA, ← hpre]
    have h1 : (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller) -
        v).toNat = (m.world.sload m.frame.msg.currentTarget
          (balSlot m.ctx.crypto m.frame.msg.caller)).toNat - v.toNat :=
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hb)
    have h2 : (m.world.sload m.frame.msg.currentTarget 3#256 - v).toNat =
        (m.world.sload m.frame.msg.currentTarget 3#256).toNat - v.toNat :=
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
    rw [h1, h2, ← hsup, ← hbc]
    dsimp only
    congr 1
    ext b
    simp only [Finsupp.update_apply, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
    by_cases hba : b = m.frame.msg.caller
    · subst hba; simp
    · simp [hba, Ne.symm hba]
  · rw [hw, subWorld, subWorld]
    exact FrameKeeps.sstore' (.inl rfl)
      (FrameKeeps.sstore' (.inr (.inr (.inl ⟨_, hcA, rfl⟩))) frameKeeps_refl')

set_option linter.unusedSimpArgs false in
theorem op_freeze (Act : Finset Address) (m : Machine) (hs : Start BNB.runtimeCode bnbAbs M Act m)
    (hval : m.frame.msg.value = 0) (hd : Args m.frame.msg.data 0xd7a78db8 [argWord m.frame.msg.data 0]) :
    Halts m fun mf o =>
      OpMatches bnbAbs M Act (.freeze m.frame.msg.caller (argWord m.frame.msg.data 0).toNat) m mf o ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)) := by
  set v := argWord m.frame.msg.data 0
  have hS := hs.sound
  have hcA := hs.caller
  have hpre := pre_eq hs hval
  refine halts_split' (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => freeze_high m v hs.fresh hd hs.size hval hG.2 hG.1)
    (freeze_low m v hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  left
  simp only [OpMatches]
  have hsrc : (pre bnbAbs Act m).bal m.frame.msg.caller =
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat := by
    rw [hpre]; simp [bnbRead, hcA]
  have hdst : (pre bnbAbs Act m).frozen m.frame.msg.caller =
      (m.world.sload m.frame.msg.currentTarget (frzSlot m.ctx.crypto m.frame.msg.caller)).toNat := by
    rw [hpre]; simp [bnbRead, hcA]
  have hv0 : v.toNat = 0 ↔ v = 0 := ⟨fun h => BitVec.eq_of_toNat_eq (by simp [h]), fun h => by simp [h]⟩
  have hD1 : (subWorld m.world m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)
      v).sload m.frame.msg.currentTarget (frzSlot m.ctx.crypto m.frame.msg.caller) =
      m.world.sload m.frame.msg.currentTarget (frzSlot m.ctx.crypto m.frame.msg.caller) := by
    simp only [subWorld, balSlot, frzSlot]
    exact World.sload_sstore_ne_key _ _ _ (fun e => by
      have := (hS.inj1 6#256 (by simp) 5#256 (by simp) _ hcA _ hcA e).2
      exact absurd this (by decide))
  rw [bnb_op_freeze, hsrc, hdst]
  by_cases hr : (m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller)).toNat < v.toNat ∨ v.toNat = 0 ∨
      2 ^ 256 ≤ (m.world.sload m.frame.msg.currentTarget
        (frzSlot m.ctx.crypto m.frame.msg.caller)).toNat + v.toNat
  · rw [ite_pos' (by
      rcases hr with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (by unfold QEDefi.Math.MAX; omega)))]
    obtain ⟨out, rfl⟩ := hrev (by
      rcases hr with h | h | h
      · exact .inl h
      · exact .inr (.inl (hv0.1 h))
      · exact .inr (.inr (by rw [hD1]; exact h)))
    trivial
  rw [ite_neg' (by
    simp only [not_or, not_lt, not_le] at hr ⊢
    refine ⟨hr.1, hr.2.1, ?_⟩
    unfold QEDefi.Math.MAX; omega)]
  simp only [not_or, not_lt, not_le] at hr
  obtain ⟨hb, hz, hfit⟩ := hr
  obtain ⟨-, ho, hw, ht, hcr⟩ := hok hb (fun h => hz (hv0.2 h)) (by rw [hD1]; exact hfit)
  refine ⟨⟨_, ho⟩, ?_, ?_, ht, hcr⟩
  · show bnbRead _ _ _ _ = _
    rw [hw, addWorld, hD1, bnbRead_sstore_frz hS hcA, subWorld, bnbRead_sstore_bal hS hcA, ← hpre]
    have h1 : (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller) -
        v).toNat = (m.world.sload m.frame.msg.currentTarget
          (balSlot m.ctx.crypto m.frame.msg.caller)).toNat - v.toNat :=
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hb)
    have h2 : (m.world.sload m.frame.msg.currentTarget (frzSlot m.ctx.crypto m.frame.msg.caller) +
        v).toNat = (m.world.sload m.frame.msg.currentTarget
          (frzSlot m.ctx.crypto m.frame.msg.caller)).toNat + v.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hfit]
    rw [h1, h2, ← hsrc, ← hdst]
    dsimp only
    congr 1
    · ext b
      simp only [Finsupp.update_apply, Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply,
        Pi.add_apply, Finsupp.single_apply]
      by_cases hba : b = m.frame.msg.caller
      · subst hba; simp
      · simp [hba, Ne.symm hba]
    · ext b
      simp only [Finsupp.update_apply, Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply,
        Pi.add_apply, Finsupp.single_apply]
      by_cases hba : b = m.frame.msg.caller
      · subst hba; simp
      · simp [hba, Ne.symm hba]
  · rw [hw, addWorld, subWorld]
    exact FrameKeeps.sstore' (.inr (.inr (.inr (.inl ⟨_, hcA, rfl⟩))))
      (FrameKeeps.sstore' (.inr (.inr (.inl ⟨_, hcA, rfl⟩))) frameKeeps_refl')

set_option linter.unusedSimpArgs false in
theorem op_unfreeze (Act : Finset Address) (m : Machine) (hs : Start BNB.runtimeCode bnbAbs M Act m)
    (hval : m.frame.msg.value = 0) (hd : Args m.frame.msg.data 0x6623fc46 [argWord m.frame.msg.data 0]) :
    Halts m fun mf o =>
      OpMatches bnbAbs M Act (.unfreeze m.frame.msg.caller (argWord m.frame.msg.data 0).toNat) m mf o ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)) := by
  set v := argWord m.frame.msg.data 0
  have hS := hs.sound
  have hcA := hs.caller
  have hpre := pre_eq hs hval
  refine halts_split' (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => unfreeze_high m v hs.fresh hd hs.size hval hG.2 hG.1)
    (unfreeze_low m v hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  left
  simp only [OpMatches]
  have hsrc : (pre bnbAbs Act m).frozen m.frame.msg.caller =
      (m.world.sload m.frame.msg.currentTarget (frzSlot m.ctx.crypto m.frame.msg.caller)).toNat := by
    rw [hpre]; simp [bnbRead, hcA]
  have hdst : (pre bnbAbs Act m).bal m.frame.msg.caller =
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat := by
    rw [hpre]; simp [bnbRead, hcA]
  have hv0 : v.toNat = 0 ↔ v = 0 := ⟨fun h => BitVec.eq_of_toNat_eq (by simp [h]), fun h => by simp [h]⟩
  have hD1 : (subWorld m.world m.frame.msg.currentTarget (frzSlot m.ctx.crypto m.frame.msg.caller)
      v).sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller) =
      m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller) := by
    simp only [subWorld, balSlot, frzSlot]
    exact World.sload_sstore_ne_key _ _ _ (fun e => by
      have := (hS.inj1 5#256 (by simp) 6#256 (by simp) _ hcA _ hcA e).2
      exact absurd this (by decide))
  rw [bnb_op_unfreeze, hsrc, hdst]
  by_cases hr : (m.world.sload m.frame.msg.currentTarget
      (frzSlot m.ctx.crypto m.frame.msg.caller)).toNat < v.toNat ∨ v.toNat = 0 ∨
      2 ^ 256 ≤ (m.world.sload m.frame.msg.currentTarget
        (balSlot m.ctx.crypto m.frame.msg.caller)).toNat + v.toNat
  · rw [ite_pos' (by
      rcases hr with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (by unfold QEDefi.Math.MAX; omega)))]
    obtain ⟨out, rfl⟩ := hrev (by
      rcases hr with h | h | h
      · exact .inl h
      · exact .inr (.inl (hv0.1 h))
      · exact .inr (.inr (by rw [hD1]; exact h)))
    trivial
  rw [ite_neg' (by
    simp only [not_or, not_lt, not_le] at hr ⊢
    refine ⟨hr.1, hr.2.1, ?_⟩
    unfold QEDefi.Math.MAX; omega)]
  simp only [not_or, not_lt, not_le] at hr
  obtain ⟨hb, hz, hfit⟩ := hr
  obtain ⟨-, ho, hw, ht, hcr⟩ := hok hb (fun h => hz (hv0.2 h)) (by rw [hD1]; exact hfit)
  refine ⟨⟨_, ho⟩, ?_, ?_, ht, hcr⟩
  · show bnbRead _ _ _ _ = _
    rw [hw, addWorld, hD1, bnbRead_sstore_bal hS hcA, subWorld, bnbRead_sstore_frz hS hcA, ← hpre]
    have h1 : (m.world.sload m.frame.msg.currentTarget (frzSlot m.ctx.crypto m.frame.msg.caller) -
        v).toNat = (m.world.sload m.frame.msg.currentTarget
          (frzSlot m.ctx.crypto m.frame.msg.caller)).toNat - v.toNat :=
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hb)
    have h2 : (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller) +
        v).toNat = (m.world.sload m.frame.msg.currentTarget
          (balSlot m.ctx.crypto m.frame.msg.caller)).toNat + v.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hfit]
    rw [h1, h2, ← hsrc, ← hdst]
    dsimp only
    congr 1
    · ext b
      simp only [Finsupp.update_apply, Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply,
        Pi.add_apply, Finsupp.single_apply]
      by_cases hba : b = m.frame.msg.caller
      · subst hba; simp
      · simp [hba, Ne.symm hba]
    · ext b
      simp only [Finsupp.update_apply, Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply,
        Pi.add_apply, Finsupp.single_apply]
      by_cases hba : b = m.frame.msg.caller
      · subst hba; simp
      · simp [hba, Ne.symm hba]
  · rw [hw, addWorld, subWorld]
    exact FrameKeeps.sstore' (.inr (.inr (.inl ⟨_, hcA, rfl⟩)))
      (FrameKeeps.sstore' (.inr (.inr (.inr (.inl ⟨_, hcA, rfl⟩)))) frameKeeps_refl')

/-- **The other entry points**: `burn`, `freeze`, `unfreeze`. -/
theorem ops_spec : OpSpec BNB.runtimeCode bnbAbs M g₀ bnbOps bnbOpAddrs := by
  intro Act m e hs hops _
  simp only [bnbOps] at hops
  split at hops
  · cases hops
  rename_i hvs
  have hval : m.frame.msg.value = 0 := by
    have : m.frame.msg.value.toNat = 0 := by simp only [not_or] at hvs; omega
    exact BitVec.eq_of_toNat_eq this
  have hsz : ¬ m.frame.msg.data.size < 36 := fun h => hvs (.inr h)
  split at hops
  · rename_i hsel
    cases hops
    exact op_burn Act m hs hval (args_one hsel hsz)
  split at hops
  · rename_i _ hsel
    cases hops
    exact op_freeze Act m hs hval (args_one hsel hsz)
  split at hops
  · rename_i _ _ hsel
    cases hops
    exact op_unfreeze Act m hs hval (args_one hsel hsz)
  · cases hops

end Verified.WeirdERC20.BNB.Spec
