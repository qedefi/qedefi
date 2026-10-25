import Verified.OpenZeppelin.VestingWallet.Spec
import EvmLogic.Program.Time

/-!
# `VestingWallet` across blocks

The wallet as a time-indexed system (`QEDefi.Trace.Time.TSystem`): concrete worlds, the
model state `state w self`, and the model step at time `t`.

* Calls (`WalletCall`): a top-level `release()` executed in a block whose clock
  (`uint64(block.timestamp)`) is `t`, under the side conditions of `release_refines`; and
  **deposits**, any transition that keeps the wallet's code and `_released` and adds `a` wei to
  its balance (plain transfers, `receive()`, `SELFDESTRUCT`, priority fees, withdrawals).
* Environment steps (`WalletEnv`): anything that keeps the wallet's code, `_released` and
  balance (calls to other contracts, the views, `transferOwnership`, failed calls).

`wallet_refinement` discharges the per-call obligations once, for a symbolic time, from
`release_refines`. The multi-block theorems are then instances of the generic ones
(`TSystem.Refinement.lift_blocks`, `timeInvariant_blocks`) along any `BlockChain` of block
environments with timestamps below `2⁶⁴` (where `uint64(block.timestamp)` is monotone):

* `released_le_vested_blocks`: `released ≤ vested(now) ≤ allocation` for every `now` at or
  after the last block;
* `total_blocks`: funds are conserved: the allocation is the initial one plus the deposits;
* `vested_mono_blocks`: the vested amount never decreases along the chain.

No time is enumerated: the invariant is carried by one induction over the trace, using only
`vested_mono_time` / `vested_mono_total` and the monotonicity of the block clocks.
-/

namespace Verified.OpenZeppelin.VestingWallet
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Solidity
open Verified.OpenZeppelin.Contracts QEDefi.Vesting QEDefi.Trace.Lift QEDefi.Trace.Time

/-- **The concrete calls implementing the model's operations at time `t`.** -/
inductive WalletCall (i : VestingWallet.Immutables) (self : Address) :
    Nat → World → Op → World → Prop
  /-- A top-level `release()` in a block whose clock is `t`. -/
  | release {t : Nat} {w : World} {ctx : Context} {tr : TransientStorage} {caller : Address}
      {data : ByteArray} {gas : Nat} {wa : AddressSet} {wk : StorageKeySet} {fuel : Nat}
      {r : MessageResult} :
      clock ctx.block = t → CallOk ctx self gas → ReleaseData data → OwnerOk ctx w self →
      processMessageCall fuel ctx w tr (callMsg (code i) self caller data gas wa wk) = .ok r →
      WalletCall i self t w .release r.world
  /-- Any transition adding `a` wei to the wallet, keeping its code and `_released`. -/
  | deposit {t : Nat} {w w' : World} {a : Nat} :
      w'.code self = w.code self → w'.sload self 1#256 = w.sload self 1#256 →
      (w'.balance self).toNat = (w.balance self).toNat + a →
      WalletCall i self t w (.deposit a) w'

/-- **Environment steps**: the wallet's code, `_released` and balance are unchanged. -/
def WalletEnv (self : Address) (w w' : World) : Prop :=
  w'.code self = w.code self ∧ w'.sload self 1#256 = w.sload self 1#256 ∧
    w'.balance self = w.balance self

/-- **The wallet at `self` (immutables `i`) as a time-indexed system.** -/
def wallet (i : VestingWallet.Immutables) (self : Address) : TSystem World State Op where
  step := QEDefi.Vesting.step (sched i)
  abs w := state w self
  call := WalletCall i self
  env := WalletEnv self
  Pre w := w.code self = code i
  Inv _ := True
  Agree := Eq
  Ok _ := True

/-- **The refinement obligations, discharged once for a symbolic time.** -/
theorem wallet_refinement (i : VestingWallet.Immutables) (self : Address) :
    (wallet i self).Refinement where
  agree := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
  inv_agree _ _ _ _ := trivial
  inv_step _ _ _ _ _ _ := trivial
  step_agree _ _ _ _ _ _ h := by simp only [wallet] at h ⊢; rw [h]
  call t w op w' hp _ _ hc := by
    cases hc with
    | release hclock hok hd ho hr =>
      have h := release_refines hp hok hd ho hr
      rw [hclock] at h
      unfold TSystem.OpRefinesAt
      simp only [wallet] at hp ⊢
      revert h
      cases QEDefi.Vesting.step (sched i) t (state w self) .release with
      | none => intro h; exact ⟨h ▸ hp, h⟩
      | some s' => intro h; exact ⟨h.2.2.1.trans hp, h.2.1⟩
    | deposit hcode hrel hbal =>
      refine ⟨hcode.trans hp, ?_⟩
      unfold TSystem.OpRefinesAt
      simp only [wallet, QEDefi.Vesting.step, state, State.mk.injEq]
      exact ⟨hbal, by rw [hrel]⟩
  env w w' hp he := by
    obtain ⟨hcode, hrel, hbal⟩ := he
    refine ⟨hcode.trans hp, ?_⟩
    simp only [wallet, state, hrel, hbal]

/-- The wallet's clock along a block chain is monotone while timestamps fit in 64 bits. -/
theorem clock_mono {bs : List BlockEnv} (hc : BlockChain bs)
    (h64 : ∀ b ∈ bs, b.timestamp < 2 ^ 64) : bs.Pairwise fun b b' => clock b ≤ clock b' := by
  have := hc.timestamp_le
  refine List.Pairwise.imp_of_mem ?_ this
  intro b b' hb hb' hle
  rw [clock, clock, Nat.mod_eq_of_lt (h64 b hb), Nat.mod_eq_of_lt (h64 b' hb')]
  exact hle

/-- **The lifting theorem for the wallet across blocks**: after any multi-block trace from a
deployed wallet, it is still deployed and its accounting is the model's execution of the
trace's operations, each at its block's clock. -/
theorem lift_blocks {i : VestingWallet.Immutables} {self : Address} {bs : List BlockEnv}
    {w₀ w : World} (hdep : w₀.code self = code i)
    (htr : BlockTrace (TSystem.BlockStep (wallet i self) clock) bs w₀ w) :
    w.code self = code i ∧ ∃ opss : List (List Op),
      state w self = texec (QEDefi.Vesting.step (sched i)) (state w₀ self) (stamp clock bs opss) := by
  obtain ⟨opss, -, hp, -, ha⟩ := (wallet_refinement i self).lift_blocks htr hdep trivial
  exact ⟨hp, opss, ha⟩

/-- **`released ≤ vested(now) ≤ allocation` across blocks.** Along any trace through a
consensus-valid chain of blocks (timestamps below `2⁶⁴`) from a deployed wallet that has
released at most what had vested at time `t₀`, at every time `now` from the last block on,
the wallet has released at most `vested(now)`, which is at most its allocation. -/
theorem released_le_vested_blocks {i : VestingWallet.Immutables} {self : Address}
    {bs : List BlockEnv} {w₀ w : World} (hdep : w₀.code self = code i)
    (hchain : BlockChain bs) (h64 : ∀ b ∈ bs, b.timestamp < 2 ^ 64)
    (htr : BlockTrace (TSystem.BlockStep (wallet i self) clock) bs w₀ w) {t₀ now : Nat}
    (h₀ : ReleasedLe (sched i) t₀ (state w₀ self))
    (hwithin : ∀ b ∈ bs, t₀ ≤ clock b ∧ clock b ≤ now) (ht : t₀ ≤ now) :
    (state w self).released ≤ (sched i).vested (state w self).total now ∧
      (sched i).vested (state w self).total now ≤ (state w self).total :=
  ⟨(wallet_refinement i self).timeInvariant_blocks (I := ReleasedLe (sched i))
      timeInvariant_released (fun _ _ _ h hs => h ▸ hs) htr (clock_mono hchain h64) hwithin ht
      hdep trivial h₀,
    Schedule.vested_le _ _⟩

/-- In particular from a wallet that has released nothing (as deployed). -/
theorem released_le_vested_of_zero {i : VestingWallet.Immutables} {self : Address}
    {bs : List BlockEnv} {w₀ w : World} (hdep : w₀.code self = code i)
    (h0 : w₀.sload self 1#256 = 0) (hchain : BlockChain bs)
    (h64 : ∀ b ∈ bs, b.timestamp < 2 ^ 64)
    (htr : BlockTrace (TSystem.BlockStep (wallet i self) clock) bs w₀ w) {now : Nat}
    (hnow : ∀ b ∈ bs, clock b ≤ now) :
    (state w self).released ≤ (sched i).vested (state w self).total now ∧
      (sched i).vested (state w self).total now ≤ (state w self).total :=
  released_le_vested_blocks hdep hchain h64 htr (t₀ := 0)
    (by simp [ReleasedLe, state, h0]) (fun b hb => ⟨Nat.zero_le _, hnow b hb⟩) (Nat.zero_le _)

/-- **Funds are conserved across blocks**: the allocation (balance + released) after any
multi-block trace is the initial one plus the deposits of the trace (and so it never
decreases). -/
theorem total_blocks {i : VestingWallet.Immutables} {self : Address} {bs : List BlockEnv}
    {w₀ w : World} (hdep : w₀.code self = code i)
    (htr : BlockTrace (TSystem.BlockStep (wallet i self) clock) bs w₀ w) :
    ∃ opss : List (List Op),
      (state w self).total = (state w₀ self).total + deposits (stamp clock bs opss) := by
  obtain ⟨-, opss, h⟩ := lift_blocks hdep htr
  exact ⟨opss, by rw [h, total_texec]⟩

/-- The allocation never decreases across blocks. -/
theorem total_mono_blocks {i : VestingWallet.Immutables} {self : Address} {bs : List BlockEnv}
    {w₀ w : World} (hdep : w₀.code self = code i)
    (htr : BlockTrace (TSystem.BlockStep (wallet i self) clock) bs w₀ w) :
    (state w₀ self).total ≤ (state w self).total := by
  obtain ⟨opss, h⟩ := total_blocks hdep htr
  rw [h]; exact Nat.le_add_right _ _

/-- **The vested amount never decreases across blocks**: from `vested(t₀)` of the initial
allocation to `vested(now)` of the final one. -/
theorem vested_mono_blocks {i : VestingWallet.Immutables} {self : Address}
    {bs : List BlockEnv} {w₀ w : World} (hdep : w₀.code self = code i)
    (hchain : BlockChain bs) (h64 : ∀ b ∈ bs, b.timestamp < 2 ^ 64)
    (htr : BlockTrace (TSystem.BlockStep (wallet i self) clock) bs w₀ w) {t₀ now : Nat}
    (hwithin : ∀ b ∈ bs, t₀ ≤ clock b ∧ clock b ≤ now) (ht : t₀ ≤ now) :
    (sched i).vested (state w₀ self).total t₀ ≤ (sched i).vested (state w self).total now := by
  obtain ⟨-, opss, h⟩ := lift_blocks hdep htr
  rw [h]
  exact vested_texec_mono (monotone_stamp (clock_mono hchain h64) opss)
    (within_stamp hwithin opss) ht

/-- **What the wallet reports agrees across blocks**: after any trace as above, a top-level
`vestedAmount(now)` call that succeeds returns a value between `released` and the
allocation. -/
theorem vestedAmount_call_blocks {i : VestingWallet.Immutables} {self : Address}
    {bs : List BlockEnv} {w₀ w : World} (hdep : w₀.code self = code i)
    (h0 : w₀.sload self 1#256 = 0) (hchain : BlockChain bs)
    (h64 : ∀ b ∈ bs, b.timestamp < 2 ^ 64)
    (htr : BlockTrace (TSystem.BlockStep (wallet i self) clock) bs w₀ w) {now : Word}
    (hnow : ∀ b ∈ bs, clock b ≤ now.toNat) {ctx : Context} {tr : TransientStorage}
    {caller : Address} {data : ByteArray} {gas : Nat} {wa : AddressSet} {wk : StorageKeySet}
    {fuel : Nat} {r : MessageResult} (hok : CallOk ctx self gas)
    (hd : WordCall data 0x0a17b06b now) (hsz : data.size < 2 ^ 64)
    (hr : processMessageCall fuel ctx w tr (callMsg (code i) self caller data gas wa wk) = .ok r)
    (hsucc : r.success = true) :
    ∃ v, r.output = Bytes.ofWord (BitVec.ofNat 256 v) ∧ (state w self).released ≤ v ∧
      v ≤ (state w self).total := by
  have hv := vestedAmount_correct hok hd hsz hr
  obtain ⟨-, hres⟩ := hv
  split at hres
  · rename_i v hspec
    split at hspec
    · obtain ⟨-, hout⟩ := hres
      obtain ⟨rfl, -⟩ := vestedAmount_eq_some hspec
      exact ⟨_, hout, released_le_vested_of_zero hdep h0 hchain h64 htr hnow⟩
    · cases hspec
  · rw [hres] at hsucc; cases hsucc

end Verified.OpenZeppelin.VestingWallet
