import Verified.WeirdERC20.STA.Spec.TransferFromCall
import Verified.WeirdERC20.STA.Spec.Fallback

/-!
# STA under the spec: `destroy`, `destroyFrom`, `upAllowance`, `downAllowance`

`destroy(v)` (`_destroy(caller, v)`): `v ≠ 0` and `v ≤ balance` (`REVERT`), the supply then the
balance lowered (`SafeMath.sub`, `INVALID` on failure), a `Transfer` to `0`. `destroyFrom(src, v)`
first spends `v` of `src`'s allowance for the caller (`REVERT` when it is below `v`), then runs
`_destroy(src, v)` in that world. `upAllowance`/`downAllowance(sp, x)`: `sp ≠ 0` (`REVERT`), the
allowance raised or lowered by `x` (`SafeMath`, `INVALID` on failure), an `Approval`, `true`.
-/

namespace Verified.WeirdERC20.STA.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.STA.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

theorem sta_ne_zero_of_iszero2 {v : Word} (h : v.iszero.iszero ≠ 0) : v ≠ 0 := by
  rintro rfl; exact h (by decide)

theorem sta_pos_of_ne {v : Word} (h : v ≠ 0) : 0 < v.toNat := by
  rcases Nat.eq_zero_or_pos v.toNat with h0 | h0
  · exact absurd (BitVec.eq_of_toNat_eq (by simp [h0])) h
  · exact h0

/-- The world after `v` is taken from slot `k`. -/
def subW (w : World) (t : Address) (k v : Word) : World := w.sstore t k (w.sload t k - v)

/-- `_destroy(a, v)` from the world `w`: the supply, then `a`'s balance, lowered by `v`. -/
def destroyWorld (crypto : Crypto) (w : World) (t a : Address) (v : Word) : World :=
  subW (subW w t 5#256 v) t (balSlot crypto a) v

/-- `destroy(v)`'s code-level end: a zero `v` or a balance below `v` fails; otherwise (when the
supply and the balance read after it cover `v`) the supply and the balance lowered. -/
def DestroyPost (m : Machine) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  (v = 0 ∨ (m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller)).toNat < v.toNat → Fails o) ∧
  (v ≠ 0 → v.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller)).toNat →
    v.toNat ≤ (m.world.sload m.frame.msg.currentTarget 5#256).toNat →
    v.toNat ≤ ((subW m.world m.frame.msg.currentTarget 5#256 v).sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller)).toNat →
    (∃ out, o = .success out) ∧
    mf.world = destroyWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller v ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts)

set_option maxHeartbeats 0 in
theorem destroy_low (m : Machine) (v : Word) (hf : Fresh STA.runtimeCode m)
    (hd : Args m.frame.msg.data 0x9d118770 [v])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (DestroyPost m v) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero,
    Nat.mul_zero, Nat.add_zero] at hsize harg0
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, Memory.read_64, ofAddress_and_addressMask,
    addressMask_and_ofAddress]
  have hv0 := sta_ne_zero_of_iszero2 (by with_reducible assumption)
  have hbs := Verified.Solady.Spec.le_of_iszero_gt (b := m_world.sload m_msg.currentTarget
    (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord 3#256)))
    (by with_reducible assumption)
  exact pwp_stop (by pcode_fact) (hok _ _ ⟨fun h => by
    rcases h with h | h
    · exact absurd h hv0
    · exact absurd (Nat.lt_of_lt_of_le h hbs) (Nat.lt_irrefl _),
    fun _ _ _ _ => ⟨⟨_, rfl⟩, rfl, rfl, rfl⟩⟩)

set_option maxHeartbeats 0 in
theorem destroy_high (m : Machine) (v : Word) (hf : Fresh STA.runtimeCode m)
    (hd : Args m.frame.msg.data 0x9d118770 [v])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (DestroyPost m v) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero,
    Nat.mul_zero, Nat.add_zero] at hsize harg0
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 32) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  by_cases hv0 : v = 0
  · subst hv0
    pwp_steps [hval, hst, hsel', hz, hl, harg0, Memory.read_64, ofAddress_and_addressMask, addressMask_and_ofAddress]
    exact ⟨fun _ => trivial, fun h => absurd rfl h⟩
  have h1 := sta_iszero2_of_pos (sta_pos_of_ne hv0)
  by_cases hbc : v.toNat ≤
      (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto m_msg.caller)).toNat
  swap
  · have h2 := Verified.Solady.Spec.iszero_gt_of_lt (Nat.lt_of_not_le hbc)
    simp only [balSlot, mappingSlot] at h2
    pwp_steps [hval, hst, hsel', hz, hl, harg0, h1, h2, Memory.read_64, ofAddress_and_addressMask, addressMask_and_ofAddress]
    exact ⟨fun _ => trivial, fun _ h => absurd h hbc⟩
  have h2 := Verified.Solady.Spec.iszero_gt_of_le hbc
  simp only [balSlot, mappingSlot] at h2
  by_cases hs : v.toNat ≤ (m_world.sload m_msg.currentTarget 5#256).toNat
  swap
  · have h3 := Verified.Solady.Spec.iszero_gt_of_lt (Nat.lt_of_not_le hs)
    pwp_steps [hval, hst, hsel', hz, hl, harg0, h1, h2, h3, Memory.read_64, ofAddress_and_addressMask, addressMask_and_ofAddress]
    refine WP.halt_of_step (step_invalid (by pcode_fact)) (.refl _) ⟨fun _ => trivial, ?_⟩
    exact fun _ _ h => absurd h hs
  have h3 := Verified.Solady.Spec.iszero_gt_of_le hs
  by_cases hb1 : v.toNat ≤ ((subW m_world m_msg.currentTarget 5#256 v).sload m_msg.currentTarget
      (balSlot m_ctx.crypto m_msg.caller)).toNat
  swap
  · have h4 := Verified.Solady.Spec.iszero_gt_of_lt (Nat.lt_of_not_le hb1)
    simp only [subW, balSlot, mappingSlot] at h4
    pwp_steps [hval, hst, hsel', hz, hl, harg0, h1, h2, h3, h4, Memory.read_64, ofAddress_and_addressMask, addressMask_and_ofAddress]
    refine WP.halt_of_step (step_invalid (by pcode_fact)) (.refl _) ⟨fun _ => trivial, ?_⟩
    exact fun _ _ _ h => absurd h hb1
  have h4 := Verified.Solady.Spec.iszero_gt_of_le hb1
  simp only [subW, balSlot, mappingSlot] at h4
  pwp_xsteps [hval, hst, hsel', hz, hl, harg0, h1, h2, h3, h4, Memory.read_64, ofAddress_and_addressMask, addressMask_and_ofAddress]
  exact pwp_stop (by pcode_fact) ⟨fun h => by
      rcases h with h | h
      · exact absurd h hv0
      · exact absurd (Nat.lt_of_lt_of_le h hbc) (Nat.lt_irrefl _),
    fun _ _ _ _ => ⟨⟨_, rfl⟩, rfl, rfl, rfl⟩⟩

theorem sta_add_ok {S v : Word} (h : ((S + v).lt v).iszero ≠ 0) : S.toNat + v.toNat < 2 ^ 256 := by
  by_contra hc
  exact h (sta_add_lt_zero (Nat.le_of_not_lt hc))

/-- `destroyFrom(a, v)`'s code-level end: an allowance below `v`, a zero `v` or a balance (read
after the allowance write) below `v` fails; otherwise (when the supply and the balance cover `v`)
the allowance spent and `_destroy(a, v)`. -/
def DFPost (m : Machine) (a : Address) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  ((m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto a m.frame.msg.caller)).toNat <
      v.toNat ∨ v = 0 ∨
    ((subW m.world m.frame.msg.currentTarget (allowSlot m.ctx.crypto a m.frame.msg.caller) v).sload
      m.frame.msg.currentTarget (balSlot m.ctx.crypto a)).toNat < v.toNat → Fails o) ∧
  (v.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto a m.frame.msg.caller)).toNat → v ≠ 0 →
    v.toNat ≤ ((subW m.world m.frame.msg.currentTarget (allowSlot m.ctx.crypto a m.frame.msg.caller)
      v).sload m.frame.msg.currentTarget (balSlot m.ctx.crypto a)).toNat →
    v.toNat ≤ ((subW m.world m.frame.msg.currentTarget (allowSlot m.ctx.crypto a m.frame.msg.caller)
      v).sload m.frame.msg.currentTarget 5#256).toNat →
    v.toNat ≤ ((subW (subW m.world m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto a m.frame.msg.caller) v) m.frame.msg.currentTarget 5#256 v).sload
        m.frame.msg.currentTarget (balSlot m.ctx.crypto a)).toNat →
    (∃ out, o = .success out) ∧
    mf.world = destroyWorld m.ctx.crypto (subW m.world m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto a m.frame.msg.caller) v) m.frame.msg.currentTarget a v ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts)

set_option maxHeartbeats 0 in
theorem destroyFrom_low (m : Machine) (a : Address) (v : Word) (hf : Fresh STA.runtimeCode m)
    (hd : Args m.frame.msg.data 0x33393efa [Word.ofAddress a, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (DFPost m a v) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, harg1, Memory.read_64, ofAddress_and_addressMask,
    addressMask_and_ofAddress]
  have hac := Verified.Solady.Spec.le_of_iszero_gt (b := m_world.sload m_msg.currentTarget
    (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress a) ++ Bytes.ofWord 4#256)))))
    (by with_reducible assumption)
  have hv0 := sta_ne_zero_of_iszero2 (by with_reducible assumption)
  have hbs := Verified.Solady.Spec.le_of_iszero_gt (b := (m_world.sstore m_msg.currentTarget
    (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress a) ++ Bytes.ofWord 4#256))))
    (m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
        (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress a) ++ Bytes.ofWord 4#256)))) -
      v)).sload m_msg.currentTarget
    (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress a) ++ Bytes.ofWord 3#256)))
    (by with_reducible assumption)
  exact pwp_stop (by pcode_fact) (hok _ _ ⟨fun h => by
    rcases h with h | h | h
    · exact absurd (Nat.lt_of_lt_of_le h hac) (Nat.lt_irrefl _)
    · exact absurd h hv0
    · exact absurd (Nat.lt_of_lt_of_le h hbs) (Nat.lt_irrefl _),
    fun _ _ _ _ _ => ⟨⟨_, rfl⟩, rfl, rfl, rfl⟩⟩)

set_option maxHeartbeats 0 in
theorem destroyFrom_high (m : Machine) (a : Address) (v : Word) (hf : Fresh STA.runtimeCode m)
    (hd : Args m.frame.msg.data 0x33393efa [Word.ofAddress a, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (DFPost m a v) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 64) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  by_cases hac : v.toNat ≤
      (m_world.sload m_msg.currentTarget (allowSlot m_ctx.crypto a m_msg.caller)).toNat
  swap
  · have h1 := Verified.Solady.Spec.iszero_gt_of_lt (Nat.lt_of_not_le hac)
    simp only [allowSlot, mappingSlot2, mappingSlot] at h1
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, h1, Memory.read_64,
      ofAddress_and_addressMask, addressMask_and_ofAddress]
    exact ⟨fun _ => trivial, fun h => absurd h hac⟩
  have h1 := Verified.Solady.Spec.iszero_gt_of_le hac
  simp only [allowSlot, mappingSlot2, mappingSlot] at h1
  by_cases hv0 : v = 0
  · subst hv0
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, h1, Memory.read_64,
      ofAddress_and_addressMask, addressMask_and_ofAddress]
    exact ⟨fun _ => trivial, fun _ h => absurd rfl h⟩
  have h2 := sta_iszero2_of_pos (sta_pos_of_ne hv0)
  by_cases hbc : v.toNat ≤ ((subW m_world m_msg.currentTarget
      (allowSlot m_ctx.crypto a m_msg.caller) v).sload m_msg.currentTarget
        (balSlot m_ctx.crypto a)).toNat
  swap
  · have h3 := Verified.Solady.Spec.iszero_gt_of_lt (Nat.lt_of_not_le hbc)
    simp only [subW, allowSlot, balSlot, mappingSlot2, mappingSlot] at h3
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, h1, h2, h3, Memory.read_64,
      ofAddress_and_addressMask, addressMask_and_ofAddress]
    exact ⟨fun _ => trivial, fun _ _ h => absurd h hbc⟩
  have h3 := Verified.Solady.Spec.iszero_gt_of_le hbc
  simp only [subW, allowSlot, balSlot, mappingSlot2, mappingSlot] at h3
  by_cases hs : v.toNat ≤ ((subW m_world m_msg.currentTarget
      (allowSlot m_ctx.crypto a m_msg.caller) v).sload m_msg.currentTarget 5#256).toNat
  swap
  · have h4 := Verified.Solady.Spec.iszero_gt_of_lt (Nat.lt_of_not_le hs)
    simp only [subW, allowSlot, mappingSlot2, mappingSlot] at h4
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, h1, h2, h3, h4, Memory.read_64,
      ofAddress_and_addressMask, addressMask_and_ofAddress]
    refine WP.halt_of_step (step_invalid (by pcode_fact)) (.refl _) ⟨fun _ => trivial, ?_⟩
    exact fun _ _ _ h => absurd h hs
  have h4 := Verified.Solady.Spec.iszero_gt_of_le hs
  simp only [subW, allowSlot, mappingSlot2, mappingSlot] at h4
  by_cases hb1 : v.toNat ≤ ((subW (subW m_world m_msg.currentTarget
      (allowSlot m_ctx.crypto a m_msg.caller) v) m_msg.currentTarget 5#256 v).sload
        m_msg.currentTarget (balSlot m_ctx.crypto a)).toNat
  swap
  · have h5 := Verified.Solady.Spec.iszero_gt_of_lt (Nat.lt_of_not_le hb1)
    simp only [subW, allowSlot, balSlot, mappingSlot2, mappingSlot] at h5
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, h1, h2, h3, h4, h5, Memory.read_64,
      ofAddress_and_addressMask, addressMask_and_ofAddress]
    refine WP.halt_of_step (step_invalid (by pcode_fact)) (.refl _) ⟨fun _ => trivial, ?_⟩
    exact fun _ _ _ _ h => absurd h hb1
  have h5 := Verified.Solady.Spec.iszero_gt_of_le hb1
  simp only [subW, allowSlot, balSlot, mappingSlot2, mappingSlot] at h5
  pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, h1, h2, h3, h4, h5, Memory.read_64,
    ofAddress_and_addressMask, addressMask_and_ofAddress]
  exact pwp_stop (by pcode_fact) ⟨fun h => by
      rcases h with h | h | h
      · exact absurd (Nat.lt_of_lt_of_le h hac) (Nat.lt_irrefl _)
      · exact absurd h hv0
      · exact absurd (Nat.lt_of_lt_of_le h hbc) (Nat.lt_irrefl _),
    fun _ _ _ _ _ => ⟨⟨_, rfl⟩, rfl, rfl, rfl⟩⟩

/-- `upAllowance(sp, x)`'s code-level end: a zero spender or an overflowing sum fails; otherwise
the allowance raised by `x`, `true`. -/
def UpPost (m : Machine) (sp : Address) (x : Word) (mf : Machine) (o : Outcome) : Prop :=
  (sp = 0 ∨ 2 ^ 256 ≤ x.toNat + (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat → Fails o) ∧
  (sp ≠ 0 → x.toNat + (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat < 2 ^ 256 →
    (∃ out, o = .success out) ∧
    mf.world = m.world.sstore m.frame.msg.currentTarget (allowSlot m.ctx.crypto m.frame.msg.caller sp)
      (x + m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto m.frame.msg.caller sp)) ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts)

/-- `downAllowance(sp, x)`'s code-level end: a zero spender or an allowance below `x` fails;
otherwise the allowance lowered by `x`, `true`. -/
def DownPost (m : Machine) (sp : Address) (x : Word) (mf : Machine) (o : Outcome) : Prop :=
  (sp = 0 ∨ (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat < x.toNat → Fails o) ∧
  (sp ≠ 0 → x.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat →
    (∃ out, o = .success out) ∧
    mf.world = subW m.world m.frame.msg.currentTarget (allowSlot m.ctx.crypto m.frame.msg.caller sp) x ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts)

set_option maxHeartbeats 0 in
theorem up_low (m : Machine) (sp : Address) (x : Word) (hf : Fresh STA.runtimeCode m)
    (hd : Args m.frame.msg.data 0xe5981a42 [Word.ofAddress sp, x])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (UpPost m sp x) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, harg1, Memory.read_64, ofAddress_and_addressMask,
    addressMask_and_ofAddress]
  have hs0 := ne_zero_of_iszero2 (by with_reducible assumption)
  have hfit := sta_add_ok (by with_reducible assumption)
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨fun h => ?_, fun _ _ =>
    ⟨⟨_, rfl⟩, rfl, rfl, rfl⟩⟩
  rcases h with h | h
  · exact absurd h hs0
  · exact absurd h (Nat.not_le.2 hfit)

set_option maxHeartbeats 0 in
theorem up_high (m : Machine) (sp : Address) (x : Word) (hf : Fresh STA.runtimeCode m)
    (hd : Args m.frame.msg.data 0xe5981a42 [Word.ofAddress sp, x])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (UpPost m sp x) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 64) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  by_cases hs0 : sp = 0
  · subst hs0
    have hc : (Word.ofAddress (0 : Address)).iszero.iszero = 0 := by decide
    pwp_steps [hval, hst, hsel', hz, hl, hc, harg0, harg1, Memory.read_64,
      ofAddress_and_addressMask, addressMask_and_ofAddress]
    exact ⟨fun _ => trivial, fun h => absurd rfl h⟩
  have hc := iszero2_of_ne hs0
  by_cases hfit : x.toNat + (m_world.sload m_msg.currentTarget
      (allowSlot m_ctx.crypto m_msg.caller sp)).toNat < 2 ^ 256
  swap
  · have h1 := sta_add_lt_zero (Nat.le_of_not_lt hfit)
    simp only [allowSlot, mappingSlot2, mappingSlot] at h1
    pwp_steps [hval, hst, hsel', hz, hl, hc, harg0, harg1, Memory.read_64,
      ofAddress_and_addressMask, addressMask_and_ofAddress]
    rw [h1]
    pwp_steps [hval, hst, hsel', hz, hl, hc, harg0, harg1, Memory.read_64,
      ofAddress_and_addressMask, addressMask_and_ofAddress]
    refine WP.halt_of_step (step_invalid (by pcode_fact)) (.refl _) ⟨fun _ => trivial, ?_⟩
    exact fun _ h => absurd h hfit
  have h1 := sta_add_lt_one hfit
  simp only [allowSlot, mappingSlot2, mappingSlot] at h1
  pwp_steps [hval, hst, hsel', hz, hl, hc, harg0, harg1, Memory.read_64,
    ofAddress_and_addressMask, addressMask_and_ofAddress]
  rw [h1]
  pwp_xsteps [hval, hst, hsel', hz, hl, hc, harg0, harg1, Memory.read_64,
    ofAddress_and_addressMask, addressMask_and_ofAddress]
  exact ⟨fun h => by
      rcases h with h | h
      · exact absurd h hs0
      · exact absurd h (Nat.not_le.2 hfit),
    fun _ _ => ⟨⟨_, rfl⟩, rfl, rfl, rfl⟩⟩

set_option maxHeartbeats 0 in
theorem down_low (m : Machine) (sp : Address) (x : Word) (hf : Fresh STA.runtimeCode m)
    (hd : Args m.frame.msg.data 0xdf401a96 [Word.ofAddress sp, x])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (DownPost m sp x) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, harg1, Memory.read_64, ofAddress_and_addressMask,
    addressMask_and_ofAddress]
  have hs0 := ne_zero_of_iszero2 (by with_reducible assumption)
  have hle := Verified.Solady.Spec.le_of_iszero_gt (by with_reducible assumption)
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨fun h => ?_, fun _ _ =>
    ⟨⟨_, rfl⟩, rfl, rfl, rfl⟩⟩
  rcases h with h | h
  · exact absurd h hs0
  · exact absurd (Nat.lt_of_lt_of_le h hle) (Nat.lt_irrefl _)

set_option maxHeartbeats 0 in
theorem down_high (m : Machine) (sp : Address) (x : Word) (hf : Fresh STA.runtimeCode m)
    (hd : Args m.frame.msg.data 0xdf401a96 [Word.ofAddress sp, x])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (DownPost m sp x) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 64) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  by_cases hs0 : sp = 0
  · subst hs0
    have hc : (Word.ofAddress (0 : Address)).iszero.iszero = 0 := by decide
    pwp_steps [hval, hst, hsel', hz, hl, hc, harg0, harg1, Memory.read_64,
      ofAddress_and_addressMask, addressMask_and_ofAddress]
    exact ⟨fun _ => trivial, fun h => absurd rfl h⟩
  have hc := iszero2_of_ne hs0
  by_cases hle : x.toNat ≤ (m_world.sload m_msg.currentTarget
      (allowSlot m_ctx.crypto m_msg.caller sp)).toNat
  swap
  · have h1 := Verified.Solady.Spec.iszero_gt_of_lt (Nat.lt_of_not_le hle)
    simp only [allowSlot, mappingSlot2, mappingSlot] at h1
    pwp_steps [hval, hst, hsel', hz, hl, hc, h1, harg0, harg1, Memory.read_64,
      ofAddress_and_addressMask, addressMask_and_ofAddress]
    refine WP.halt_of_step (step_invalid (by pcode_fact)) (.refl _) ⟨fun _ => trivial, ?_⟩
    exact fun _ h => absurd h hle
  have h1 := Verified.Solady.Spec.iszero_gt_of_le hle
  simp only [allowSlot, mappingSlot2, mappingSlot] at h1
  pwp_xsteps [hval, hst, hsel', hz, hl, hc, h1, harg0, harg1, Memory.read_64,
    ofAddress_and_addressMask, addressMask_and_ofAddress]
  exact ⟨fun h => by
      rcases h with h | h
      · exact absurd h hs0
      · exact absurd (Nat.lt_of_lt_of_le h hle) (Nat.lt_irrefl _),
    fun _ _ => ⟨⟨_, rfl⟩, rfl, rfl, rfl⟩⟩

end Verified.WeirdERC20.STA.Spec
