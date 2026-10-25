import Verified.OpenZeppelin.VestingWallet.Views
import EvmLogic.Program.CallCodeless

/-!
# `VestingWallet.release()` at the bytecode level

`release_halts`: in any fresh frame (top level or called by another contract) without value,
not static, with room for one more call level and the owner a code-less non-precompile
account, `release()` ends as the model's `release` at `uint64(block.timestamp)`: when
`releasable` is `some a`, `_released` becomes `released + a` and `a` wei go to the owner
(`ReleasePost`); otherwise it reverts with the world unchanged. The proof reuses `vested_wp`
(the schedule, once for a symbolic time) and `release_tail` (`Address.sendValue`, through
`WP.call_codeless`).

An owner with code would run during the payment (re-entrancy), which this file does not
cover: `hocode` restricts the owner to an account without code.
-/

namespace Verified.OpenZeppelin.VestingWallet
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Tactic
open Verified.OpenZeppelin.Contracts QEDefi.Vesting

/-- The world after paying `a` from `src` to `dst` (nothing moves when `a = 0`). -/
def payOut (w : World) (src dst : Address) (a : Word) : World :=
  if a = 0 then w else moveEther w src dst a

/-- The value transfer of a `CALL` child message is `payOut`. -/
theorem transferValue_childMsg (w : World) (M : Machine) (c t : Address) (v : Word) (g : Nat)
    (st : Bool) (i1 i2 o1 o2 : Word) :
    transferValue w (childMsg M c t t v g true st i1 i2 o1 o2) = payOut w c t v := by
  by_cases hv : v = 0
  · subst hv; simp [transferValue, childMsg, payOut]
  · simp [transferValue, childMsg, payOut]

/-- A call with empty input and output windows does not touch memory. -/
theorem callMemory_zero (M : Machine) (i o : Word) : callMemory M i 0#256 o 0#256 = M.frame.memory := by
  simp [callMemory, Memory.expand_zero]

/-- Empty return data leaves memory unchanged. -/
theorem returnMemory_empty' (mem : Memory) (o s : Nat) : returnMemory mem o s .empty = mem := by
  have : (ByteArray.empty.extract 0 (min s ByteArray.empty.size)).size = 0 := by simp
  simp only [returnMemory, this, ite_true]

set_option maxHeartbeats 0 in
/-- **`Address.sendValue(owner, a)` and the return of `release()`** (from `0x6c7`, the stack as
`release()` leaves it): the balance check passes, `a` moves to the code-less owner, and the
frame stops. -/
theorem release_tail {i : VestingWallet.Immutables} (m : Machine) {a o sel : Word}
    (hv : WalletFrame i m) (hpc : m.frame.pc = 0x6c7)
    (hs : m.frame.stack = [a, o, 0x474#256, a, 0x174#256, sel])
    (hfmp : m.frame.memory.loadWord 64 = 128#256) (hmsz : m.frame.memory.size = 160)
    (hbal : a.toNat ≤ (m.world.balance m.frame.msg.currentTarget).toNat)
    (hcode0 : (m.world.code (Word.toAddress o)).size = 0)
    (hpre : m.precompiles.isPrecompile (Word.toAddress o) = false)
    (hstatic : m.frame.msg.isStatic = false)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hg : 50000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun _ => False) (fun mf out => out = .success .empty ∧
      mf.world = payOut m.world m.frame.msg.currentTarget (Word.toAddress o) a) := by
  obtain ⟨hc, hj⟩ := hv
  have hagree := jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  pwp_steps
  rw [iszero_lt_eq_one hbal]
  pwp_steps [hfmp, hmsz]
  have hext : ∀ M : Machine, (callExt M 160#256 0#256 0#256 0#256).cost = 0 := by
    intro M; simp [callExt, Gas.extendMemory]
  have hacc := accessCost_le (m_sub.accessedAddresses.contains (Word.toAddress o))
  have hcc : createCost m_world a (Word.toAddress o) ≤ 25000 := by
    unfold createCost; split <;> decide
  have htc : transferCost a ≤ 9000 := by unfold transferCost; split <;> decide
  refine WP.call_codeless (by pcode_fact) rfl hcode0 ?_ (.inl hstatic) hbal hdepth hpre ?_
  · apply callCost_le
    rw [hext]
    dsimp only
    omega
  · rw [resumeAfter_success (o := 0) (s := 0) (by rfl)]
    wp_generalize_gas g2 hg2d
    have hlow := le_gas_after_call' (by rw [hext]; dsimp only; omega) rfl hg2d
    rw [hext] at hlow
    dsimp only at hlow
    clear hg2d
    dsimp only [callerFrame]
    simp only [transferValue_childMsg, callMemory_zero, returnMemory_empty', Nat.reduceAdd]
    pwp_steps
    apply WP.halt_of_step
    case h =>
      apply step_stop
      pcode_fact
    case hs => same_frame
    exact ⟨rfl, rfl⟩

/-- What `release()` ends with: when the model's `releasable` at the block's clock is `some a`,
success, `_released` set to `released + a` and `a` paid to the owner; otherwise a revert with
the world unchanged. -/
def ReleasePost (i : VestingWallet.Immutables) (m mf : Machine) (out : Outcome) : Prop :=
  match releasable (sched i) (clock m.ctx.block) (state m.world m.frame.msg.currentTarget) with
  | some a => out = .success .empty ∧
    mf.world = payOut (m.world.sstore m.frame.msg.currentTarget 1#256
      (BitVec.ofNat 256 ((state m.world m.frame.msg.currentTarget).released + a)))
      m.frame.msg.currentTarget (Word.toAddress (m.world.sload m.frame.msg.currentTarget 0#256))
      (BitVec.ofNat 256 a)
  | none => (∃ o, out = .revert o) ∧ mf.world = m.world

set_option maxHeartbeats 0 in
/-- **`release()`** ends with `ReleasePost`: the model's `release` at the block's clock. -/
theorem release_halts {i : VestingWallet.Immutables} (m : Machine) (h : WalletPre i m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x86d1a69f) (hsz4 : 4 ≤ m.frame.msg.data.size)
    (hstatic : m.frame.msg.isStatic = false) (hgas : 100000 ≤ m.frame.gasLeft)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hocode : (m.world.code (Word.toAddress (m.world.sload m.frame.msg.currentTarget 0#256))).size = 0)
    (hopre : m.precompiles.isPrecompile (Word.toAddress (m.world.sload m.frame.msg.currentTarget 0#256)) = false) :
    Halts m (ReleasePost i m) := by
  have hsel' := Dispatch.selector_eq hsel
  wallet_intro
  pwp_run_to 0x2a5 [hval, hsel', hlt, Abi.shr_calldataload_zero]
  refine WP.bind_mono (vested_wp _ ⟨rfl, hj⟩ rfl rfl (by simp) (by pjumpdest_disch)
    (by dsimp only; evm_gas) (by dsimp only; omega)
    (by simp [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words])) ?_ ?_
  · rintro mf o - ⟨hnone, hrev, hw⟩
    dsimp only at hnone hw
    rw [ofNat, toNat_timestamp_mask] at hnone
    simp only [ReleasePost, releasable, hnone]
    exact ⟨hrev, hw⟩
  rintro m' - ⟨v, g, hv, rfl, hgu, hg1⟩
  dsimp only at hv hgu
  rw [ofNat, toNat_timestamp_mask] at hv
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg1 ⊢
  pwp_steps
  have hvW := (vestedAmount_eq_some hv)
  have hvlt : v < 2 ^ 256 := Nat.lt_of_le_of_lt (hvW.1 ▸ Schedule.vested_le _ _) hvW.2
  have hvn : (BitVec.ofNat 256 v).toNat = v := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt]
  by_cases hle : (m_world.sload m_msg.currentTarget 1#256).toNat ≤ v
  · rw [checkedSub_ok (by rw [hvn]; exact hle), ofNat_sub_word hvlt hle]
    pwp_steps
    have hamt : (BitVec.ofNat 256 (v - (m_world.sload m_msg.currentTarget 1#256).toNat)).toNat =
        v - (m_world.sload m_msg.currentTarget 1#256).toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [checkedAdd_ok (by rw [hamt]; omega), ofNat_sub_add_word hvlt hle]
    have hown : (m_world.sstore m_msg.currentTarget 1#256 (BitVec.ofNat 256 v)).sload
        m_msg.currentTarget 0#256 = m_world.sload m_msg.currentTarget 0#256 :=
      World.sload_sstore_ne_key _ _ _ (by decide)
    pwp_run_to 0x6c7 [hown, World.balance_sstore]
    wp_generalize_gas g1 hg1d
    have hsl := sloadCost_le (storageKeyWarm m_sub.accessedStorageKeys m_msg.currentTarget 1#256)
    have hg1' : 50000 ≤ g1 := by subst hg1d; evm_gas
    have hg1'' : g1 < 2 ^ 64 := by subst hg1d; omega
    clear hg1d
    have hbal : v - (m_world.sload m_msg.currentTarget 1#256).toNat ≤
        (m_world.balance m_msg.currentTarget).toNat := by
      have h1 := Schedule.vested_le (p := sched i) (state m_world m_msg.currentTarget).total
        (clock m_ctx.block)
      have h2 : (state m_world m_msg.currentTarget).total = (m_world.balance m_msg.currentTarget).toNat +
        (m_world.sload m_msg.currentTarget 1#256).toNat := rfl
      rw [← hvW.1] at h1
      omega
    refine WP.bind_mono (release_tail _ ⟨rfl, hj⟩ rfl rfl ?_ ?_ ?_ ?_ ?_ hstatic hdepth ?_ ?_)
      (fun mf out _ h => ?_) (fun _ _ h => h.elim)
    · simp only [Memory.loadWord_expand]
      rw [Memory.loadWord_storeWord_of_disjoint _ _ _ _ (by omega), Memory.loadWord_expand,
        Memory.loadWord_storeWord]
    · simp [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words]
    · simp only [World.balance_sstore]; rw [hamt]; exact hbal
    · simp only [World.code_sstore, toAddress_mask_and]; exact hocode
    · rw [toAddress_mask_and]; exact hopre
    · omega
    · omega
    · obtain ⟨ho, hw⟩ := h
      have hrel : releasable (sched i) (clock m_ctx.block) (state m_world m_msg.currentTarget) =
          some (v - (m_world.sload m_msg.currentTarget 1#256).toNat) := by
        simp only [releasable, hv, show (state m_world m_msg.currentTarget).released =
          (m_world.sload m_msg.currentTarget 1#256).toNat from rfl, Nat.not_lt.mpr hle, ↓reduceIte]
      simp only [ReleasePost, hrel]
      refine ⟨ho, ?_⟩
      rw [hw]
      dsimp only
      rw [toAddress_mask_and, show (state m_world m_msg.currentTarget).released =
        (m_world.sload m_msg.currentTarget 1#256).toNat from rfl,
        show (m_world.sload m_msg.currentTarget 1#256).toNat +
        (v - (m_world.sload m_msg.currentTarget 1#256).toNat) = v by omega]
  · rw [checkedSub_underflow (by rw [hvn]; omega)]
    pwp_steps
    have hrel : releasable (sched i) (clock m_ctx.block) (state m_world m_msg.currentTarget) = none := by
      simp only [releasable, hv, show (state m_world m_msg.currentTarget).released =
        (m_world.sload m_msg.currentTarget 1#256).toNat from rfl,
        show v < (m_world.sload m_msg.currentTarget 1#256).toNat by omega, ↓reduceIte]
    simp only [ReleasePost, hrel]
    exact ⟨⟨_, rfl⟩, rfl⟩

end Verified.OpenZeppelin.VestingWallet
