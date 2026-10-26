import Verified.WeirdERC20.ZRX.Spec.Abs
import EvmLogic.Tactic.Patched
import EvmLogic.Program.Code
import EvmLogic.Solidity.Dispatch
import EvmLogic.Program.Call

/-!
# ZRX's views on the bytecode: the exact half of `ViewSpec`

`totalSupply()`, `balanceOf(a)` and `allowance(o, sp)` of the deployed ZRX code in any fresh
frame (top level or a callee at any depth), with at least 5000 gas and no value: the frame
returns the word of slot 3, of `a`'s `balances` row, of the `allowed[o][sp]` row, and changes
nothing (`totalSupply_halts`, `balanceOf_halts`, `allowance_halts`, by symbolic execution of the
dispatcher and the getter). `view_exact` states it as `ViewSpec`'s left disjunct for every view
whose accounts are actors, in every frame `Start` admits with `g₀ ≤ gas` and no value.

The rest of `ViewSpec` (frames with less gas or with value, which must fail or return the
same word) is `ViewSpec.lean`, by the any-gas calculus `hwp_steps`; `views` there is the full
obligation.
-/

namespace Verified.WeirdERC20.ZRX.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.ZRX.Contracts

code_table ZRX.runtimeCode

set_option hygiene false in
/-- Open a fresh frame (`hf : Fresh code m`) for symbolic execution (as
`Verified.Solmate.ERC20`'s `fresh_intro`). -/
macro "zrx_fresh_intro" : tactic => `(tactic| (
  obtain ⟨hc, hj, hpc, hs, hmem, -, -⟩ := hf.frame
  clear hf
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  wp_hide_jump_tables
  subst hs hpc hc hmem))

/-- solc 0.4's selector extraction (`CALLDATALOAD 0 / 2²²⁴ & 0xffffffff`). -/
theorem div_selector (data : ByteArray) :
    (4294967295#256 &&& Word.div (Bytes.toWord (readBytes data 0 32))
      26959946667150639794667015087019630673637144422540572481103610249216#256) =
      BitVec.ofNat 256 (Abi.selectorOf data) := by
  have hs := Abi.shr_calldataload_zero data
  have hsel : Abi.selectorOf data < 2 ^ 32 := by
    have := Bytes.toNat_lt (readBytes data 0 4)
    rw [size_readBytes] at this
    unfold Abi.selectorOf; simpa using this
  have hdiv : Word.div (Bytes.toWord (readBytes data 0 32))
      26959946667150639794667015087019630673637144422540572481103610249216#256 =
      Word.shr (BitVec.ofNat 256 224) (Bytes.toWord (readBytes data 0 32)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [Word.div, Word.shr, BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight,
      BitVec.toNat_udiv, BitVec.toNat_ofNat]
    rw [Nat.shiftRight_eq_div_pow]
  rw [hdiv, hs]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : Abi.selectorOf data < 2 ^ 256),
    show (4294967295 : Nat) % 2 ^ 256 = 2 ^ 32 - 1 by decide, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hsel]

/-- What a view returns: the word `x`, nothing changed. -/
def ViewPost (x : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord x) ∧ mf.world = m.world ∧ mf.transient = m.transient ∧
    mf.createdAccounts = m.createdAccounts ∧ mf.frame.sub.logs = m.frame.sub.logs

set_option maxHeartbeats 0 in
/-- **`totalSupply()`** returns slot 3, with enough gas and no value. -/
theorem totalSupply_halts (m : Machine) (hf : Fresh ZRX.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hsel : Abi.selectorOf m.frame.msg.data = 0x18160ddd)
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 5000 ≤ m.frame.gasLeft) :
    Halts m (ViewPost (m.world.sload m.frame.msg.currentTarget supplySlot) m) := by
  apply WP.halts_of_false
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz : Word.iszero (ofNat m.frame.msg.data.size) = 0 := by
    apply iszero_of_ne
    intro h
    have := congrArg BitVec.toNat h
    simp [ofNat] at this
    omega
  zrx_fresh_intro
  pwp_steps [hval, hsel', hz]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem calldatasize_ne {n : ℕ} (h4 : 4 ≤ n) (h : n < 2 ^ 64) : Word.iszero (ofNat n) = 0 := by
  apply iszero_of_ne
  intro h0
  have := congrArg BitVec.toNat h0
  simp [ofNat] at this
  omega

set_option maxHeartbeats 0 in
/-- **`balanceOf(a)`** returns `a`'s row of `balances`, with enough gas and no value. -/
theorem balanceOf_halts (m : Machine) (hf : Fresh ZRX.runtimeCode m) (a : Address)
    (hval : m.frame.msg.value = 0) (hsel : Abi.selectorOf m.frame.msg.data = 0x70a08231)
    (hsize : 36 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (harg : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress a)
    (hg : 5000 ≤ m.frame.gasLeft) :
    Halts m (ViewPost (m.world.sload m.frame.msg.currentTarget
      (mappingSlot m.ctx.crypto (Word.ofAddress a) balancesSlot)) m) := by
  apply WP.halts_of_false
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsize'
  zrx_fresh_intro
  pwp_steps [hval, hsel', hz, harg, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 0 in
/-- **`allowance(o, sp)`** returns the row `allowed[o][sp]`, with enough gas and no value. -/
theorem allowance_halts (m : Machine) (hf : Fresh ZRX.runtimeCode m) (o sp : Address)
    (hval : m.frame.msg.value = 0) (hsel : Abi.selectorOf m.frame.msg.data = 0xdd62ed3e)
    (hsize : 68 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (harg0 : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress o)
    (harg1 : Bytes.toWord (readBytes m.frame.msg.data 36 32) = Word.ofAddress sp)
    (hg : 5000 ≤ m.frame.gasLeft) :
    Halts m (ViewPost (m.world.sload m.frame.msg.currentTarget
      (mappingSlot2 m.ctx.crypto (Word.ofAddress o) (Word.ofAddress sp) allowedSlot)) m) := by
  apply WP.halts_of_false
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsize'
  zrx_fresh_intro
  pwp_steps [hval, hsel', hz, harg0, harg1, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **The exact half of `ViewSpec` for ZRX**: with at least `g₀` gas and no value, every view
whose accounts are actors returns the model's value of the state at the start of the frame, as
one word, and changes nothing. -/
theorem view_exact (v : View) (Act : Finset Address) (m : Machine)
    (hs : Start ZRX.runtimeCode abs
      (QEDefi.ERC20.Spec.ZRX.model : TokenModel (VState Address) Address Empty) Act m)
    (hv : v.Encodes m.frame.msg.data) (ha : ∀ a ∈ v.addrs, a ∈ Act)
    (hg : g₀ ≤ m.frame.gasLeft) (hval : m.frame.msg.value = 0) :
    Halts m fun mf o =>
      ∃ x : Word, o = .success (Bytes.ofWord x) ∧
        x.toNat = v.value (QEDefi.ERC20.Spec.ZRX.model : TokenModel (VState Address) Address Empty)
          (pre abs Act m) ∧
        mf.world = m.world ∧ mf.transient = m.transient ∧
        mf.createdAccounts = m.createdAccounts ∧ mf.frame.sub.logs = m.frame.sub.logs := by
  have hw : m.world = m.frame.snapshot.1 := by
    rw [hs.launched, transferValue_zero _ _ hval]
  have hg' : 5000 ≤ m.frame.gasLeft := le_trans (by decide) hg
  cases v with
  | totalSupply =>
    obtain ⟨hsel, hsize, -⟩ := hv
    refine (totalSupply_halts m hs.fresh hval hsel (by simpa using hsize) hs.size hg').mono
      fun mf o _ ⟨ho, h1, h2, h3, h4⟩ => ⟨_, ho, ?_, h1, h2, h3, h4⟩
    simp [View.value, pre, abs, read, hw, QEDefi.ERC20.Spec.ZRX.model, Variant.model,
      Variant.totalSupply, QEDefi.ERC20.Spec.ZRX.variant, Variant.standard, VState.ofToken,
      readSlot]
  | balanceOf a =>
    obtain ⟨hsel, hsize, harg⟩ := hv
    have ha' : a ∈ Act := ha a (by simp [View.addrs])
    refine (balanceOf_halts m hs.fresh a hval hsel (by simpa using hsize) hs.size
      (harg 0 (by simp)) hg').mono fun mf o _ ⟨ho, h1, h2, h3, h4⟩ => ⟨_, ho, ?_, h1, h2, h3, h4⟩
    simp [View.value, pre, abs, read, hw, QEDefi.ERC20.Spec.ZRX.model, Variant.model,
      Variant.balanceOf, QEDefi.ERC20.Spec.ZRX.variant, Variant.standard, VState.ofToken, ha']
  | allowance o sp =>
    obtain ⟨hsel, hsize, harg⟩ := hv
    have ho : o ∈ Act := ha o (by simp [View.addrs])
    have hsp : sp ∈ Act := ha sp (by simp [View.addrs])
    refine (allowance_halts m hs.fresh o sp hval hsel (by simpa using hsize) hs.size
      (harg 0 (by simp)) (harg 1 (by simp)) hg').mono
      fun mf o' _ ⟨ho', h1, h2, h3, h4⟩ => ⟨_, ho', ?_, h1, h2, h3, h4⟩
    simp [View.value, pre, abs, read, hw, QEDefi.ERC20.Spec.ZRX.model, Variant.model,
      Variant.allowanceOf, QEDefi.ERC20.Spec.ZRX.variant, Variant.standard, VState.ofToken,
      readMap2, ho, hsp]

end Verified.WeirdERC20.ZRX.Spec
