import Verified.WeirdERC20.USDT.Spec.TransferModel

/-!
# USDT's admin entry points on the lift

`issue`, `redeem`, `addBlackList`, `removeBlackList`, `destroyBlackFunds` and `setParams`, each
run through every branch of the code: `OpOut ok W` says the frame fails when the code's
condition `ok` (the owner check and the `require`s / SafeMath) does not hold, and otherwise
ends successfully with the world `W` (or fails in a static frame).
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Verified.WeirdERC20.USDT.Contracts EvmLogic.Program.Nested EvmLogic.GasMono
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.Math QEDefi.ERC4626

theorem expCost_6 : Gas.expCost 6 = 60 := by decide

/-- The owner as the code reads it from slot 0. -/
abbrev ownerA (w : World) (t : Address) : Address :=
  Word.toAddress (ownerField.get (w.sload t 0#256))

/-- What the lift of an admin entry point ends with: failure in a static frame or when the
code's condition `ok` fails; otherwise success with the world `W`. -/
def OpOut (ok : Prop) (W : World) (m mf : Machine) (o : Outcome) : Prop :=
  (m.frame.msg.isStatic = true ∧ Fails o) ∨ (¬ ok ∧ Fails o) ∨
  (ok ∧ (∃ out, o = .success out) ∧ mf.world = W ∧ mf.transient = m.transient ∧
    mf.createdAccounts = m.createdAccounts)

theorem opOut_halt {ok : Prop} {W : World} {m mf : Machine} {e e' : ExceptionalHalt}
    (h : OpOut ok W m mf (.halt e)) : OpOut ok W m mf (.halt e') := by
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, ⟨_, h2⟩, -⟩
  · exact .inl ⟨h1, trivial⟩
  · exact .inr (.inl ⟨h1, trivial⟩)
  · cases h2

/-! ## The conditions and the worlds, in the code's words -/

/-- `issue(v)`: the owner calls, and `supply + v`, `balances[owner] + v` grow. -/
def issueOk (crypto : Crypto) (w : World) (t c : Address) (v : Word) : Prop :=
  c = ownerA w t ∧ (w.sload t 1#256).toNat < (w.sload t 1#256 + v).toNat ∧
    (w.sload t (balKey crypto (ownerA w t))).toNat <
      (w.sload t (balKey crypto (ownerA w t)) + v).toNat

/-- `issue(v)`: credit the owner, then raise the supply. -/
def issueW (crypto : Crypto) (w : World) (t : Address) (v : Word) : World :=
  let W1 := w.sstore t (balKey crypto (ownerA w t)) (w.sload t (balKey crypto (ownerA w t)) + v)
  W1.sstore t 1#256 (W1.sload t 1#256 + v)

/-- `redeem(v)`: the owner calls, and `v ≤ supply`, `v ≤ balances[owner]`. -/
def redeemOk (crypto : Crypto) (w : World) (t c : Address) (v : Word) : Prop :=
  c = ownerA w t ∧ v.toNat ≤ (w.sload t 1#256).toNat ∧
    v.toNat ≤ (w.sload t (balKey crypto (ownerA w t))).toNat

/-- `redeem(v)`: lower the supply, then debit the owner. -/
def redeemW (crypto : Crypto) (w : World) (t : Address) (v : Word) : World :=
  let W1 := w.sstore t 1#256 (w.sload t 1#256 - v)
  W1.sstore t (balKey crypto (ownerA W1 t)) (W1.sload t (balKey crypto (ownerA W1 t)) - v)

/-- `addBlackList(u)` / `removeBlackList(u)`: the row's low byte set to `b`. -/
def blackSetW (crypto : Crypto) (w : World) (t u : Address) (b : Word) : World :=
  w.sstore t (blackKey crypto u)
    (b ||| 115792089237316195423570985008687907853269984665640564039457584007913129639680#256 &&&
      w.sload t (blackKey crypto u))

/-- `destroyBlackFunds(u)`: the owner calls and `u` is blacklisted. -/
def destroyOk (crypto : Crypto) (w : World) (t c u : Address) : Prop :=
  c = ownerA w t ∧ blackW crypto w t u ≠ 0#256

/-- `destroyBlackFunds(u)`: zero `u`'s balance, lower the supply by it. -/
def destroyW (crypto : Crypto) (w : World) (t u : Address) : World :=
  let W1 := w.sstore t (balKey crypto u) 0#256
  W1.sstore t 1#256 (W1.sload t 1#256 - w.sload t (balKey crypto u))

/-- `setParams(b, x)`: the owner calls, `b < 20`, `x < 50`. -/
def paramsOk (w : World) (t c : Address) (b x : Word) : Prop :=
  c = ownerA w t ∧ b.toNat < 20 ∧ x.toNat < 50

/-- `setParams(b, x)`: `basisPointsRate := b`, `maximumFee := x · 10^6`. -/
def paramsW (w : World) (t : Address) (b x : Word) : World :=
  (w.sstore t 3#256 b).sstore t 4#256 (x * 1000000#256)

/-! ## The runs -/

set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
/-- **`issue(v)`** on the lift. -/
theorem issue_high (m : Machine) (hf : Fresh USDT.runtimeCode m) (d : Nat) (v : Word)
    (hg : g₀ ≤ m.frame.gasLeft + d)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xcc872b66)
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (harg0 : Bytes.toWord (readBytes m.frame.msg.data 4 32) = v)
    (hval : m.frame.msg.value = 0) :
    WP (lift patchedCode d m) (fun mh' => mh'.frame.pc ∉ patchPcs ∧
      ExitsWith (OpOut (issueOk m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller v)
        (issueW m.ctx.crypto m.world m.frame.msg.currentTarget v) m) mh') (fun _ _ => False) := by
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  simp only [g₀] at hg
  lift_intro
  usdt_run [hval, hsel', hlt, Memory.read_64, div_selector, expCost_20, expCost_0, harg0,
    ofAddress_and_addressMask, addressMask_and_ofAddress, owner_mask2, owner_mask]
  by_cases hown : m_msg.caller = ownerA m_world m_msg.currentTarget
  swap
  · simp only [eq_of_ne (fun e => hown (Word.ofAddress_injective e)), Solidity.iszero_zero,
      Solidity.iszero_one]
    xrun [owner_mask]
    usdt_revert
    exact .inr (.inl ⟨fun h => hown h.1, trivial⟩)
  have heq : Word.eq (Word.ofAddress m_msg.caller)
      (Word.ofAddress (ownerA m_world m_msg.currentTarget)) = 1#256 := by
    rw [hown]; exact Solidity.eq_self _
  simp only [heq, Solidity.iszero_zero, Solidity.iszero_one]
  xrun [owner_mask]
  by_cases h1 : (m_world.sload m_msg.currentTarget 1#256).toNat <
      (m_world.sload m_msg.currentTarget 1#256 + v).toNat
  swap
  · simp only [gt_zero (Nat.le_of_not_lt h1), Solidity.iszero_zero, Solidity.iszero_one]
    xrun [owner_mask]
    usdt_revert
    exact .inr (.inl ⟨fun h => h1 h.2.1, trivial⟩)
  simp only [gt_one h1, Solidity.iszero_zero, Solidity.iszero_one]
  xrun [owner_mask]
  by_cases h2 : (m_world.sload m_msg.currentTarget
        (balKey m_ctx.crypto (ownerA m_world m_msg.currentTarget))).toNat <
      (m_world.sload m_msg.currentTarget
        (balKey m_ctx.crypto (ownerA m_world m_msg.currentTarget)) + v).toNat
  swap
  · simp only [gt_zero (Nat.le_of_not_lt h2), Solidity.iszero_zero, Solidity.iszero_one]
    xrun [owner_mask]
    usdt_revert
    exact .inr (.inl ⟨fun h => h2 h.2.2, trivial⟩)
  simp only [gt_one h2, Solidity.iszero_zero, Solidity.iszero_one]
  xrun [owner_mask]
  by_cases hst : m_msg.isStatic = true
  · usdt_static
    exact .inl ⟨hst, trivial⟩
  have hst' : m_msg.isStatic = false := by simpa using hst
  xrun [owner_mask]
  usdt_stop
  exact .inr (.inr ⟨⟨hown, h1, h2⟩, ⟨_, rfl⟩, rfl, rfl, rfl⟩)

set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
/-- **`redeem(v)`** on the lift. -/
theorem redeem_high (m : Machine) (hf : Fresh USDT.runtimeCode m) (d : Nat) (v : Word)
    (hg : g₀ ≤ m.frame.gasLeft + d)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xdb006a75)
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (harg0 : Bytes.toWord (readBytes m.frame.msg.data 4 32) = v)
    (hval : m.frame.msg.value = 0) :
    WP (lift patchedCode d m) (fun mh' => mh'.frame.pc ∉ patchPcs ∧
      ExitsWith (OpOut (redeemOk m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller v)
        (redeemW m.ctx.crypto m.world m.frame.msg.currentTarget v) m) mh') (fun _ _ => False) := by
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  simp only [g₀] at hg
  lift_intro
  usdt_run [hval, hsel', hlt, Memory.read_64, div_selector, expCost_20, expCost_0, harg0,
    ofAddress_and_addressMask, addressMask_and_ofAddress, owner_mask2, owner_mask]
  by_cases hown : m_msg.caller = ownerA m_world m_msg.currentTarget
  swap
  · simp only [eq_of_ne (fun e => hown (Word.ofAddress_injective e)), Solidity.iszero_zero,
      Solidity.iszero_one]
    xrun [owner_mask]
    usdt_revert
    exact .inr (.inl ⟨fun h => hown h.1, trivial⟩)
  have heq : Word.eq (Word.ofAddress m_msg.caller)
      (Word.ofAddress (ownerA m_world m_msg.currentTarget)) = 1#256 := by
    rw [hown]; exact Solidity.eq_self _
  simp only [heq, Solidity.iszero_zero, Solidity.iszero_one]
  xrun [owner_mask]
  by_cases h1 : v.toNat ≤ (m_world.sload m_msg.currentTarget 1#256).toNat
  swap
  · simp only [lt_one (Nat.lt_of_not_le h1), Solidity.iszero_zero, Solidity.iszero_one]
    xrun [owner_mask]
    usdt_revert
    exact .inr (.inl ⟨fun h => h1 h.2.1, trivial⟩)
  simp only [lt_zero h1, Solidity.iszero_zero, Solidity.iszero_one]
  xrun [owner_mask]
  by_cases h2 : v.toNat ≤ (m_world.sload m_msg.currentTarget
      (balKey m_ctx.crypto (ownerA m_world m_msg.currentTarget))).toNat
  swap
  · simp only [lt_one (Nat.lt_of_not_le h2), Solidity.iszero_zero, Solidity.iszero_one]
    xrun [owner_mask]
    usdt_revert
    exact .inr (.inl ⟨fun h => h2 h.2.2, trivial⟩)
  simp only [lt_zero h2, Solidity.iszero_zero, Solidity.iszero_one]
  xrun [owner_mask]
  by_cases hst : m_msg.isStatic = true
  · usdt_static
    exact .inl ⟨hst, trivial⟩
  have hst' : m_msg.isStatic = false := by simpa using hst
  xrun [owner_mask]
  usdt_stop
  exact .inr (.inr ⟨⟨hown, h1, h2⟩, ⟨_, rfl⟩, rfl, rfl, rfl⟩)

set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
/-- **`addBlackList(u)` (`flag = 1`, selector `0x0ecb93c0`) and `removeBlackList(u)`
(`flag = 0`, selector `0xe4997dc5`)** on the lift. -/
theorem blackSet_high (m : Machine) (hf : Fresh USDT.runtimeCode m) (d : Nat) (x : Word)
    (u : Address) (flag : Word) (hg : g₀ ≤ m.frame.gasLeft + d)
    (hsel : (Abi.selectorOf m.frame.msg.data = 0x0ecb93c0 ∧ flag = 1#256) ∨
      (Abi.selectorOf m.frame.msg.data = 0xe4997dc5 ∧ flag = 0#256))
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (harg0 : Bytes.toWord (readBytes m.frame.msg.data 4 32) = x)
    (hu : 1461501637330902918203684832716283019655932542975#256 &&& x = Word.ofAddress u)
    (hval : m.frame.msg.value = 0) :
    WP (lift patchedCode d m) (fun mh' => mh'.frame.pc ∉ patchPcs ∧
      ExitsWith (OpOut (m.frame.msg.caller = ownerA m.world m.frame.msg.currentTarget)
        (blackSetW m.ctx.crypto m.world m.frame.msg.currentTarget u flag) m) mh')
      (fun _ _ => False) := by
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  simp only [g₀] at hg
  rcases hsel with ⟨hsel, hfl⟩ | ⟨hsel, hfl⟩ <;> subst hfl <;>
  · have hsel' := Dispatch.selector_eq hsel
    lift_intro
    usdt_run [hval, hsel', hlt, Memory.read_64, div_selector, expCost_20, expCost_0, harg0, hu,
      ofAddress_and_addressMask, addressMask_and_ofAddress, owner_mask2, owner_mask]
    by_cases hown : m_msg.caller = ownerA m_world m_msg.currentTarget
    swap
    · simp only [eq_of_ne (fun e => hown (Word.ofAddress_injective e)), Solidity.iszero_zero,
        Solidity.iszero_one]
      xrun [owner_mask]
      usdt_revert
      exact .inr (.inl ⟨hown, trivial⟩)
    have heq : Word.eq (Word.ofAddress m_msg.caller)
        (Word.ofAddress (ownerA m_world m_msg.currentTarget)) = 1#256 := by
      rw [hown]; exact Solidity.eq_self _
    simp only [heq, Solidity.iszero_zero, Solidity.iszero_one]
    xrun [owner_mask]
    by_cases hst : m_msg.isStatic = true
    · usdt_static
      exact .inl ⟨hst, trivial⟩
    have hst' : m_msg.isStatic = false := by simpa using hst
    xrun [owner_mask]
    usdt_stop
    exact .inr (.inr ⟨hown, ⟨_, rfl⟩, rfl, rfl, rfl⟩)

set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
/-- **`destroyBlackFunds(u)`** on the lift (its `balanceOf` checks `deprecated`). -/
theorem destroy_high (m : Machine) (hf : Fresh USDT.runtimeCode m) (d : Nat) (x : Word)
    (u : Address) (hg : g₀ ≤ m.frame.gasLeft + d)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xf3bdc228)
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (harg0 : Bytes.toWord (readBytes m.frame.msg.data 4 32) = x)
    (hu : 1461501637330902918203684832716283019655932542975#256 &&& x = Word.ofAddress u)
    (hval : m.frame.msg.value = 0)
    (hdep : deprecatedField.get (m.world.sload m.frame.msg.currentTarget 10#256) = 0) :
    WP (lift patchedCode d m) (fun mh' => mh'.frame.pc ∉ patchPcs ∧
      ExitsWith (OpOut (destroyOk m.ctx.crypto m.world m.frame.msg.currentTarget
        m.frame.msg.caller u) (destroyW m.ctx.crypto m.world m.frame.msg.currentTarget u) m) mh')
      (fun _ _ => False) := by
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  simp only [g₀] at hg
  simp only [deprecatedField_get] at hdep
  lift_intro
  usdt_run [hval, hsel', hlt, Memory.read_64, div_selector, expCost_20, expCost_0, harg0, hu,
    ofAddress_and_addressMask, addressMask_and_ofAddress, owner_mask2, owner_mask]
  by_cases hown : m_msg.caller = ownerA m_world m_msg.currentTarget
  swap
  · simp only [eq_of_ne (fun e => hown (Word.ofAddress_injective e)), Solidity.iszero_zero,
      Solidity.iszero_one]
    xrun [owner_mask]
    usdt_revert
    exact .inr (.inl ⟨fun h => hown h.1, trivial⟩)
  have heq : Word.eq (Word.ofAddress m_msg.caller)
      (Word.ofAddress (ownerA m_world m_msg.currentTarget)) = 1#256 := by
    rw [hown]; exact Solidity.eq_self _
  simp only [heq, Solidity.iszero_zero, Solidity.iszero_one]
  xrun [owner_mask]
  by_cases hb : blackW m_ctx.crypto m_world m_msg.currentTarget u = 0#256
  · simp only [hb, Solidity.iszero_zero, Solidity.iszero_one]
    xrun [owner_mask]
    usdt_revert
    exact .inr (.inl ⟨fun h => h.2 hb, trivial⟩)
  simp only [iszero_of_ne hb, Solidity.iszero_zero, Solidity.iszero_one]
  xrun [owner_mask]
  simp only [hdep]
  xrun [owner_mask]
  by_cases hst : m_msg.isStatic = true
  · usdt_static
    exact .inl ⟨hst, trivial⟩
  have hst' : m_msg.isStatic = false := by simpa using hst
  xrun [owner_mask]
  usdt_stop
  exact .inr (.inr ⟨⟨hown, hb⟩, ⟨_, rfl⟩, rfl, rfl, rfl⟩)

set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
/-- **`setParams(b, x)`** on the lift (`10 ** decimals` with `decimals = 6`). -/
theorem params_high (m : Machine) (hf : Fresh USDT.runtimeCode m) (d : Nat) (b x : Word)
    (hg : g₀ ≤ m.frame.gasLeft + d)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xc0324c77)
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (harg0 : Bytes.toWord (readBytes m.frame.msg.data 4 32) = b)
    (harg1 : Bytes.toWord (readBytes m.frame.msg.data 36 32) = x)
    (hdec : m.world.sload m.frame.msg.currentTarget 9#256 = 6#256)
    (hval : m.frame.msg.value = 0) :
    WP (lift patchedCode d m) (fun mh' => mh'.frame.pc ∉ patchPcs ∧
      ExitsWith (OpOut (paramsOk m.world m.frame.msg.currentTarget m.frame.msg.caller b x)
        (paramsW m.world m.frame.msg.currentTarget b x) m) mh') (fun _ _ => False) := by
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  simp only [g₀] at hg
  lift_intro
  usdt_run [hval, hsel', hlt, Memory.read_64, div_selector, expCost_20, expCost_0, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, owner_mask2, owner_mask]
  by_cases hown : m_msg.caller = ownerA m_world m_msg.currentTarget
  swap
  · simp only [eq_of_ne (fun e => hown (Word.ofAddress_injective e)), Solidity.iszero_zero,
      Solidity.iszero_one]
    xrun [owner_mask]
    usdt_revert
    exact .inr (.inl ⟨fun h => hown h.1, trivial⟩)
  have heq : Word.eq (Word.ofAddress m_msg.caller)
      (Word.ofAddress (ownerA m_world m_msg.currentTarget)) = 1#256 := by
    rw [hown]; exact Solidity.eq_self _
  simp only [heq, Solidity.iszero_zero, Solidity.iszero_one]
  xrun [owner_mask]
  by_cases hb : b.toNat < 20
  swap
  · simp only [lt_zero (x := b) (y := 20#256) (Nat.le_of_not_lt hb), Solidity.iszero_zero,
      Solidity.iszero_one]
    xrun [owner_mask]
    usdt_revert
    exact .inr (.inl ⟨fun h => hb h.2.1, trivial⟩)
  simp only [lt_one (x := b) (y := 20#256) hb, Solidity.iszero_zero, Solidity.iszero_one]
  xrun [owner_mask]
  by_cases hx : x.toNat < 50
  swap
  · simp only [lt_zero (x := x) (y := 50#256) (Nat.le_of_not_lt hx), Solidity.iszero_zero,
      Solidity.iszero_one]
    xrun [owner_mask]
    usdt_revert
    exact .inr (.inl ⟨fun h => hx h.2.2, trivial⟩)
  simp only [lt_one (x := x) (y := 50#256) hx, Solidity.iszero_zero, Solidity.iszero_one]
  xrun [owner_mask]
  by_cases hst : m_msg.isStatic = true
  · usdt_static
    exact .inl ⟨hst, trivial⟩
  have hst' : m_msg.isStatic = false := by simpa using hst
  xrun [owner_mask]
  simp (disch := decide) only [World.sload_sstore_ne_key]
  simp only [hdec]
  xrun [owner_mask, expCost_6]
  by_cases hx0 : x = 0#256
  · have heq0 : Word.eq x 0#256 = 1#256 := by rw [hx0]; exact Solidity.eq_self _
    simp only [heq0, Solidity.iszero_zero, Solidity.iszero_one]
    xrun [owner_mask]
    usdt_stop
    subst hx0
    exact .inr (.inr ⟨⟨hown, hb, hx⟩, ⟨_, rfl⟩, rfl, rfl, rfl⟩)
  simp only [eq_of_ne hx0, Solidity.iszero_zero, Solidity.iszero_one]
  xrun [owner_mask]
  simp only [iszero_of_ne hx0, Solidity.iszero_zero, Solidity.iszero_one]
  xrun [owner_mask]
  have hm : x.toNat * (1000000#256 : Word).toNat < 2 ^ 256 := by
    rw [show (1000000#256 : Word).toNat = 1000000 from rfl]; omega
  simp only [mul_div_eq_one hx0 hm, Solidity.iszero_zero, Solidity.iszero_one]
  xrun [owner_mask]
  usdt_stop
  exact .inr (.inr ⟨⟨hown, hb, hx⟩, ⟨_, rfl⟩, rfl, rfl, rfl⟩)

end Verified.WeirdERC20.USDT.Spec
