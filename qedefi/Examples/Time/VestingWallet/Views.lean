import Examples.Time.VestingWallet.Vested

/-!
# `VestingWallet`: the views at the bytecode level

`*_halts`: `released()`, `releasable()` and `vestedAmount(uint64)` of the wallet (any
immutables), in any fresh frame without value (top level or called by another contract), end
with `ViewPost`: world unchanged, and the ABI word of the model's value or a revert when the
model reverts. `releasable()` reads the clock: its value is the model's `releasable` at
`clock m.ctx.block` (`uint64(block.timestamp)`), for a symbolic block environment.
-/

namespace Examples.Time.VestingWallet
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Tactic
open Examples.Time.Contracts QEDefi.Vesting

theorem lt_size_four {n : Nat} (h₁ : 4 ≤ n) (h₂ : n < 2 ^ 256) :
    Word.lt (ofNat n) (BitVec.ofNat 256 4) = 0 := by
  rw [Word.lt_eq_zero_iff]; simp only [ofNat, BitVec.toNat_ofNat]; omega

/-- A fresh frame of the wallet (immutables `i`) without value, with `30000 ≤ gas < 2⁶⁴` and
calldata shorter than `2⁶⁴` bytes. -/
structure WalletPre (i : VestingWallet.Immutables) (m : Machine) : Prop where
  /-- The frame has just started running the wallet's code. -/
  fresh : Fresh (code i) m
  /-- No value. -/
  value : m.frame.msg.value = 0
  /-- Enough gas. -/
  gas : 30000 ≤ m.frame.gasLeft
  /-- Gas below `2⁶⁴`. -/
  gasLt : m.frame.gasLeft < 2 ^ 64
  /-- Calldata below `2⁶⁴` bytes. -/
  sizeLt : m.frame.msg.data.size < 2 ^ 64

/-- What a view ends with: world unchanged; the ABI word of `v` when the specification gives
`some v`, a revert on `none`. -/
def ViewPost (m : Machine) (r : Option Nat) (mf : Machine) (o : Outcome) : Prop :=
  mf.world = m.world ∧
    match r with
    | some v => o = .success (Bytes.ofWord (BitVec.ofNat 256 v))
    | none => ∃ out, o = .revert out

set_option hygiene false in
/-- Common start of a proof from a fresh frame: `Halts` to `WP`, unpack `WalletPre` and the
fresh frame, destructure the machine. Expects `h : WalletPre i m` and `hsz4`. -/
macro "wallet_intro" : tactic => `(tactic| (
  apply WP.halts_of_false
  obtain ⟨hf, hval, hg, hg', hsz'⟩ := h
  obtain ⟨hc, hj, hpc, hs, hmem, -, -⟩ := hf.frame
  clear hf
  have hagree := jumpDestsAgree i
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsz4 (by omega)
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  wp_hide_jump_tables
  subst hs hpc hc hmem))

theorem toNat_timestamp_mask (ctx : Context) :
    (BitVec.ofNat 256 ctx.block.timestamp).toNat % 2 ^ 64 = clock ctx.block := by
  rw [BitVec.toNat_ofNat, clock, Nat.mod_mod_of_dvd _ (by decide)]

set_option maxHeartbeats 0 in
/-- **`releasable()`**: the model's `releasable` at the block's clock. -/
theorem releasable_halts {i : VestingWallet.Immutables} (m : Machine) (h : WalletPre i m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xfbccedae) (hsz4 : 4 ≤ m.frame.msg.data.size) :
    Halts m (ViewPost m (releasable (sched i) (clock m.ctx.block)
      (state m.world m.frame.msg.currentTarget))) := by
  have hsel' := Dispatch.selector_eq hsel
  wallet_intro
  pwp_run_to 0x2a5 [hval, hsel', hlt, Abi.shr_calldataload_zero]
  refine WP.bind_mono (vested_wp _ ⟨rfl, hj⟩ rfl rfl (by simp) (by pjumpdest_disch)
    (by dsimp only; evm_gas) (by dsimp only; omega) (by simp [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words])) ?_ ?_
  · rintro mf o - ⟨hnone, hrev, hw⟩
    dsimp only at hnone hw
    rw [ofNat, toNat_timestamp_mask] at hnone
    refine ⟨hw, ?_⟩
    simp only [releasable, hnone]
    exact hrev
  rintro m' - ⟨v, g, hv, rfl, -, hg1⟩
  dsimp only at hv
  rw [ofNat, toNat_timestamp_mask] at hv
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg1 ⊢
  pwp_steps
  have hvW := (vestedAmount_eq_some hv)
  have hvlt : v < 2 ^ 256 := Nat.lt_of_le_of_lt (hvW.1 ▸ Schedule.vested_le _ _) hvW.2
  have hvn : (BitVec.ofNat 256 v).toNat = v := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt]
  by_cases hle : (m_world.sload m_msg.currentTarget 1#256).toNat ≤ v
  · rw [checkedSub_ok (by rw [hvn]; exact hle)]
    pwp_steps
    refine ⟨rfl, ?_⟩
    have hr : (state m_world m_msg.currentTarget).released =
      (m_world.sload m_msg.currentTarget 1#256).toNat := rfl
    simp only [releasable, hv, hr, Nat.not_lt.mpr hle, ↓reduceIte]
    rw [ofNat_sub_word hvlt hle]
  · rw [checkedSub_underflow (by rw [hvn]; omega)]
    pwp_steps
    refine ⟨rfl, ?_⟩
    have hr : (state m_world m_msg.currentTarget).released =
      (m_world.sload m_msg.currentTarget 1#256).toNat := rfl
    simp only [releasable, hv, hr, show v < (m_world.sload m_msg.currentTarget 1#256).toNat by omega,
      ↓reduceIte]
    exact ⟨_, rfl⟩

/-- Calldata with selector `sel` and one word argument `x`, described through what the decoder
reads (so it covers calldata a calling contract assembled in memory). -/
structure WordCall (data : ByteArray) (sel : Nat) (x : Word) : Prop where
  /-- The selector. -/
  selector : Abi.selectorOf data = sel
  /-- At least one argument word. -/
  size : 36 ≤ data.size
  /-- The argument word. -/
  arg : Bytes.toWord (readBytes data 4 32) = x

set_option maxHeartbeats 0 in
/-- **`vestedAmount(uint64 x)`**: the model's `vestedAmount` at time `x`; a revert when `x` is
not a valid `uint64`. -/
theorem vestedAmount_halts {i : VestingWallet.Immutables} (m : Machine) (h : WalletPre i m) {x : Word}
    (hd : WordCall m.frame.msg.data 0x0a17b06b x) :
    Halts m (ViewPost m (if x.toNat < 2 ^ 64 then vestedAmount (sched i) x.toNat
      (state m.world m.frame.msg.currentTarget) else none)) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have hsz4 : 4 ≤ m.frame.msg.data.size := by omega
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by have := h.sizeLt; omega)
  wallet_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg]
  by_cases hx : x.toNat < 2 ^ 64
  · rw [eq_and_mask_of_lt hx]
    pwp_run_to 0x2a5
    refine WP.bind_mono (vested_wp _ ⟨rfl, hj⟩ rfl rfl (by simp) (by pjumpdest_disch)
      (by dsimp only; omega) (by dsimp only; omega)
      (by simp [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words])) ?_ ?_
    · rintro mf o - ⟨hnone, hrev, hw⟩
      dsimp only at hnone hw
      rw [Nat.mod_eq_of_lt hx] at hnone
      refine ⟨hw, ?_⟩
      simp only [hx, ↓reduceIte, hnone]
      exact hrev
    rintro m' - ⟨v, g, hv, rfl, -, hg1⟩
    dsimp only at hv
    rw [Nat.mod_eq_of_lt hx] at hv
    simp only [Machine.resumeWith, BitVec.reduceToNat] at hg1 ⊢
    pwp_steps
    refine ⟨rfl, ?_⟩
    simp only [hx, ↓reduceIte, hv]
  · rw [eq_and_mask_of_ge (by omega)]
    pwp_steps
    refine ⟨rfl, ?_⟩
    simp only [hx, ↓reduceIte]
    exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- **`released()`**: `_released` (slot 1). -/
theorem released_halts {i : VestingWallet.Immutables} (m : Machine) (h : WalletPre i m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x96132521) (hsz4 : 4 ≤ m.frame.msg.data.size) :
    Halts m (ViewPost m (some (state m.world m.frame.msg.currentTarget).released)) := by
  have hsel' := Dispatch.selector_eq hsel
  wallet_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero]
  refine ⟨rfl, ?_⟩
  show _ = Outcome.success (Bytes.ofWord (BitVec.ofNat 256 (m_world.sload m_msg.currentTarget 1#256).toNat))
  rw [ofNat_toNat_word]

end Examples.Time.VestingWallet
