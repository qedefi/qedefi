import Examples.Time.VestingWallet.Release
import EvmLogic.Program.Nested.Frame

/-!
# `VestingWallet` at top level, against the model

Top-level message calls (`callMsg`) of the deployed wallet (`code i` at `self`), for **every**
block environment: the clock is `clock ctx.block = uint64(block.timestamp)`, symbolic.

* `release_refines`: `release()` refines the model's `release` at the block's clock: when the
  model succeeds the call succeeds and the wallet's accounting (`state`) is the model's, and
  the owner receives what was releasable; when the model reverts the world is unchanged.
* `releasable_correct`, `vestedAmount_correct`: the views return the model's values (or
  revert exactly when it does) and change nothing.

`processMessageCall` is total in its fuel: any run that terminates gives the result of the
frame summaries (`result_of_halts`).
-/

namespace Examples.Time.VestingWallet
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Solidity
open Examples.Time.Contracts QEDefi.Vesting

/-- The wallet's owner: slot 0 (`Ownable._owner`). -/
def owner (w : World) (self : Address) : Address := Word.toAddress (w.sload self 0#256)

/-- Calldata of `release()`: the selector, then anything (fewer than `2⁶⁴` bytes). -/
structure ReleaseData (data : ByteArray) : Prop where
  /-- The selector `0x86d1a69f`. -/
  selector : Abi.selectorOf data = 0x86d1a69f
  /-- At least the selector. -/
  size : 4 ≤ data.size
  /-- Fewer than `2⁶⁴` bytes. -/
  sizeLt : data.size < 2 ^ 64

/-- The side conditions of a top-level call to the wallet at `self`: no EIP-7702
authorizations (or before Prague), the wallet is no precompile, `100000 ≤ gas < 2⁶⁴`. -/
structure CallOk (ctx : Context) (target : Address) (gas : Nat) : Prop where
  /-- No EIP-7702 authorizations, or before Prague. -/
  deleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []
  /-- The wallet is no precompile. -/
  notPre : Precompile.isPrecompile ctx.fork target = false
  /-- Enough gas. -/
  gasLe : 100000 ≤ gas
  /-- Gas below `2⁶⁴`. -/
  gasLt : gas < 2 ^ 64

/-- The owner of a `release()` is a plain account: no code (so no re-entrancy) and no
precompile. -/
structure OwnerOk (ctx : Context) (w : World) (wallet : Address) : Prop where
  /-- No code. -/
  code : (w.code (owner w wallet)).size = 0
  /-- No precompile. -/
  notPre : Precompile.isPrecompile ctx.fork (owner w wallet) = false

/-! ## From frame summaries to results -/

/-- **Any terminating top-level run gives the summary's result** (`processMessageCall` is
monotone in its fuel). -/
theorem result_of_halts {ctx : Context} {w : World} {tr : TransientStorage} {code : ByteArray}
    {self caller : Address} {data : ByteArray} {gas : Nat} {wa : AddressSet} {wk : StorageKeySet}
    {H : Machine → Outcome → Prop} (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hdel : delegatedAddress? code = none) (hpre : Precompile.isPrecompile ctx.fork self = false)
    (h : Halts (EvmLogic.Solidity.start ctx w tr (callMsg code self caller data gas wa wk)) H) {fuel : Nat}
    {r : MessageResult}
    (hr : processMessageCall fuel ctx w tr (callMsg code self caller data gas wa wk) = .ok r) :
    ∃ mf o, H mf o ∧ SameFrame (EvmLogic.Solidity.start ctx w tr (callMsg code self caller data gas wa wk)) mf ∧
      r = topLevelResult (some self) (frameResult mf o).2.1 (frameResult mf o).2.2
        (frameResult mf o).1 := by
  obtain ⟨n, mf, o, hH, hs, hrun⟩ := h.run rfl
  refine ⟨mf, o, hH, hs, ?_⟩
  rw [processMessageCall_callMsg hdeleg hdel hpre] at hr
  have h1 := run_mono hr (Nat.le_max_left fuel n)
  have h2 := hrun (max fuel n) (Nat.le_max_right fuel n)
  rw [h1] at h2
  exact Except.ok.inj h2

/-- The world after a top-level summary ending in success or revert. -/
theorem world_of_success {mf : Machine} {out : ByteArray} {o s : Nat}
    (hk : mf.frame.kind = .call o s) {t : Option Address} :
    (topLevelResult t (frameResult mf (.success out)).2.1 (frameResult mf (.success out)).2.2
      (frameResult mf (.success out)).1).world = mf.world := by
  rw [topLevelResult_world, frameResult_success_call hk]

theorem world_of_revert {mf : Machine} {out : ByteArray} {t : Option Address} :
    (topLevelResult t (frameResult mf (.revert out)).2.1 (frameResult mf (.revert out)).2.2
      (frameResult mf (.revert out)).1).world = mf.frame.snapshot.1 := by
  rw [topLevelResult_world, frameResult_revert]

theorem walletPre_start {i : VestingWallet.Immutables} {ctx : Context} {w : World}
    {tr : TransientStorage} {self caller : Address} {data : ByteArray} {gas : Nat}
    {wa : AddressSet} {wk : StorageKeySet} (hok : CallOk ctx self gas)
    (hsz : data.size < 2 ^ 64) :
    WalletPre i (EvmLogic.Solidity.start ctx w tr (callMsg (code i) self caller data gas wa wk)) :=
  ⟨⟨_, _, _, rfl, rfl⟩, rfl, by
    have := hok.gasLe; simp only [EvmLogic.Solidity.start, Frame.init, callMsg]; omega,
    hok.gasLt, hsz⟩

/-! ## The wallet's accounting after a payment -/

theorem state_payOut {w : World} {self dst : Address} {a : Word}
    (hself : (w.code self).size ≠ 0) (hdst : (w.code dst).size = 0)
    (ha : a.toNat ≤ (w.balance self).toNat) :
    state (payOut w self dst a) self = ⟨(w.balance self).toNat - a.toNat, (w.sload self 1#256).toNat⟩ := by
  unfold payOut
  split
  · rename_i h; subst h; simp [state]
  · have hne : self ≠ dst := by intro h; subst h; exact hself hdst
    have hk := EvmLogic.Program.Nested.keep_moveEther (src := self) (dst := dst) (v := a) hself
    simp only [state, State.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [Interpreter.balance_moveEther _ _ hne]
      simp only [↓reduceIte]
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact ha)]
    · unfold World.sload; rw [hk.1]

/-! ## Views -/

/-- What a top-level view call returns: the world unchanged; success with the ABI word of the
specification's value, or failure when it is `none`. -/
def ViewResult (w : World) (spec : Option Nat) (r : MessageResult) : Prop :=
  r.world = w ∧
    match spec with
    | some v => r.success = true ∧ r.output = Bytes.ofWord (BitVec.ofNat 256 v)
    | none => r.success = false

theorem viewResult_of_halts {i : VestingWallet.Immutables} {ctx : Context} {w : World}
    {tr : TransientStorage} {self caller : Address} {data : ByteArray} {gas : Nat}
    {wa : AddressSet} {wk : StorageKeySet} {fuel : Nat} {r : MessageResult} {spec : Option Nat}
    (hok : CallOk ctx self gas)
    (hh : Halts (EvmLogic.Solidity.start ctx w tr (callMsg (code i) self caller data gas wa wk))
      (ViewPost (EvmLogic.Solidity.start ctx w tr (callMsg (code i) self caller data gas wa wk)) spec))
    (hr : processMessageCall fuel ctx w tr (callMsg (code i) self caller data gas wa wk) = .ok r) :
    ViewResult w spec r := by
  obtain ⟨mf, o, ⟨hw, hpost⟩, hs, rfl⟩ :=
    result_of_halts hok.deleg (delegatedAddress?_code i) hok.notPre hh hr
  have hk : mf.frame.kind = .call 0 0 := hs.kind
  have hsnap : mf.frame.snapshot = (w, tr) := hs.snapshot
  cases spec with
  | none =>
    obtain ⟨out, rfl⟩ := hpost
    refine ⟨by rw [world_of_revert, hsnap], ?_⟩
    simp [topLevelResult_success, frameResult_revert, ChildResult.success]
  | some v =>
    subst hpost
    obtain ⟨h1, h2, h3, -⟩ := topLevelResult_success_call (t := some self)
      (out := Bytes.ofWord (BitVec.ofNat 256 v)) hk
    exact ⟨h3.trans hw, h1, h2⟩

/-- **`releasable()` is correct at top level**: it returns the model's `releasable` at the
block's clock (or fails exactly when the model reverts) and changes nothing. -/
theorem releasable_correct {i : VestingWallet.Immutables} {ctx : Context} {w : World}
    {tr : TransientStorage} {self caller : Address} {data : ByteArray} {gas : Nat}
    {wa : AddressSet} {wk : StorageKeySet} {fuel : Nat} {r : MessageResult}
    (hok : CallOk ctx self gas) (hsel : Abi.selectorOf data = 0xfbccedae) (hsz : 4 ≤ data.size)
    (hsz' : data.size < 2 ^ 64)
    (hr : processMessageCall fuel ctx w tr (callMsg (code i) self caller data gas wa wk) = .ok r) :
    ViewResult w (releasable (sched i) (clock ctx.block) (state w self)) r :=
  viewResult_of_halts hok (releasable_halts _ (walletPre_start hok hsz') hsel hsz) hr

/-- **`vestedAmount(uint64 t)` is correct at top level**: the model's `vestedAmount` at time
`t` (failure when `t` is not a `uint64`), nothing changed. -/
theorem vestedAmount_correct {i : VestingWallet.Immutables} {ctx : Context} {w : World}
    {tr : TransientStorage} {self caller : Address} {data : ByteArray} {gas : Nat}
    {wa : AddressSet} {wk : StorageKeySet} {fuel : Nat} {r : MessageResult} {t : Word}
    (hok : CallOk ctx self gas) (hd : WordCall data 0x0a17b06b t) (hsz' : data.size < 2 ^ 64)
    (hr : processMessageCall fuel ctx w tr (callMsg (code i) self caller data gas wa wk) = .ok r) :
    ViewResult w (if t.toNat < 2 ^ 64 then vestedAmount (sched i) t.toNat (state w self) else none)
      r :=
  viewResult_of_halts hok (vestedAmount_halts _ (walletPre_start hok hsz') hd) hr

/-- **`released()` at top level** returns `_released` and changes nothing. -/
theorem released_correct {i : VestingWallet.Immutables} {ctx : Context} {w : World}
    {tr : TransientStorage} {self caller : Address} {data : ByteArray} {gas : Nat}
    {wa : AddressSet} {wk : StorageKeySet} {fuel : Nat} {r : MessageResult}
    (hok : CallOk ctx self gas) (hsel : Abi.selectorOf data = 0x96132521) (hsz : 4 ≤ data.size)
    (hsz' : data.size < 2 ^ 64)
    (hr : processMessageCall fuel ctx w tr (callMsg (code i) self caller data gas wa wk) = .ok r) :
    ViewResult w (some (state w self).released) r :=
  viewResult_of_halts hok (released_halts _ (walletPre_start hok hsz') hsel hsz) hr

/-! ## `release()` -/

/-- **`release()` refines the model's `release` at the block's clock**, for every block
environment. When the model succeeds with `s'`, the call succeeds, the wallet's accounting
is `s'`, its code is unchanged, and the owner is paid `s'.released − released`; when the model
reverts, the world is unchanged. -/
theorem release_refines {i : VestingWallet.Immutables} {ctx : Context} {w : World}
    {tr : TransientStorage} {self caller : Address} {data : ByteArray} {gas : Nat}
    {wa : AddressSet} {wk : StorageKeySet} {fuel : Nat} {r : MessageResult}
    (hdep : w.code self = code i) (hok : CallOk ctx self gas) (hd : ReleaseData data)
    (ho : OwnerOk ctx w self)
    (hr : processMessageCall fuel ctx w tr (callMsg (code i) self caller data gas wa wk) = .ok r) :
    match step (sched i) (clock ctx.block) (state w self) .release with
    | some s' => r.success = true ∧ state r.world self = s' ∧ r.world.code self = w.code self ∧
      r.world = payOut (w.sstore self 1#256 (BitVec.ofNat 256 s'.released)) self (owner w self)
        (BitVec.ofNat 256 (s'.released - (state w self).released))
    | none => r.world = w := by
  have hh := release_halts (EvmLogic.Solidity.start ctx w tr (callMsg (code i) self caller data gas wa wk))
    (walletPre_start hok hd.sizeLt) hd.selector hd.size rfl
    (by simp only [EvmLogic.Solidity.start, Frame.init, callMsg]; exact hok.gasLe)
    (by simp only [EvmLogic.Solidity.start, Frame.init, callMsg, Gas.stackDepthLimit]; omega)
    ho.code ho.notPre
  obtain ⟨mf, o, hpost, hs, rfl⟩ := result_of_halts hok.deleg (delegatedAddress?_code i) hok.notPre hh hr
  have hk : mf.frame.kind = .call 0 0 := hs.kind
  have hsnap : mf.frame.snapshot = (w, tr) := hs.snapshot
  unfold ReleasePost at hpost
  dsimp only [EvmLogic.Solidity.start, Frame.init, callMsg] at hpost
  have hself : (w.code self).size ≠ 0 := by rw [hdep, size_code]; decide
  cases hrel : releasable (sched i) (clock ctx.block) (state w self) with
  | none =>
    rw [hrel] at hpost
    obtain ⟨⟨out, rfl⟩, -⟩ := hpost
    simp only [QEDefi.Vesting.step, hrel]
    rw [world_of_revert, hsnap]
  | some a =>
    rw [hrel] at hpost
    obtain ⟨rfl, hw⟩ := hpost
    have hab := releasable_le_balance hrel
    have hstep : step (sched i) (clock ctx.block) (state w self) .release =
        some ⟨(state w self).balance - a, (state w self).released + a⟩ := by
      simp only [QEDefi.Vesting.step, hrel, Nat.not_lt.mpr hab, ↓reduceIte]
    rw [hstep]
    dsimp only
    have hlt : a < 2 ^ 256 := Nat.lt_of_le_of_lt hab (w.balance self).isLt
    have han : (BitVec.ofNat 256 a).toNat = a := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hrw : (topLevelResult (some self) (frameResult mf (.success .empty)).2.1
        (frameResult mf (.success .empty)).2.2 (frameResult mf (.success .empty)).1).world =
        mf.world := world_of_success hk
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (topLevelResult_success_call (t := some self) (out := .empty) hk).1
    · rw [hrw, hw, state_payOut (by rw [World.code_sstore]; exact hself)
        (by rw [World.code_sstore]; exact ho.code) (by rw [World.balance_sstore, han]; exact hab)]
      simp only [World.balance_sstore, World.sload_sstore_self, han, state]
      congr 1
      have hrl : (w.sload self 1#256).toNat + a < 2 ^ 256 := by
        obtain ⟨h1, h2, h3⟩ := releasable_eq_some hrel
        have hv := Schedule.vested_le (p := sched i) (state w self).total (clock ctx.block)
        have ht : (w.balance self).toNat + (w.sload self 1#256).toNat < 2 ^ 256 := h3
        have hr' : (state w self).released = (w.sload self 1#256).toNat := rfl
        have htot : (state w self).total = (w.balance self).toNat + (w.sload self 1#256).toNat := rfl
        generalize (sched i).vested (state w self).total (clock ctx.block) = V at *
        omega
      exact Nat.mod_eq_of_lt hrl
    · rw [hrw, hw]
      unfold payOut
      split
      · exact World.code_sstore _ _ _ _ _
      · have hk' := EvmLogic.Program.Nested.keep_moveEther
          (w := w.sstore self 1#256 (BitVec.ofNat 256 ((state w self).released + a)))
          (src := self) (dst := (w.sload self 0#256).toAddress) (v := BitVec.ofNat 256 a)
          (by rw [World.code_sstore]; exact hself)
        rw [EvmLogic.Program.Nested.Keep.code hk', World.code_sstore]
    · rw [hrw, hw, owner, Nat.add_sub_cancel_left]

end Examples.Time.VestingWallet
