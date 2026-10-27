import Verified.WeirdERC20.AMPL.Spec.PermitFull
import Verified.WeirdERC20.AMPL.Spec.PermitBridge
import Verified.WeirdERC20.AMPL.Spec.Malformed

/-!
# AMPL's `permit` against `PermitSpec`, and the complete spec

**`ampl_permitSpec`**: `PermitSpec AMPL.runtimeCode amplAbs M amplGp amplRec`.

* `amplRec m n` (`PermitModel`) is the address `ecrecover` returns for AMPL's EIP-712 digest at
  nonce `n`, `address(0)` when the recovery fails (AMPL zeroes the output word before the
  call and does not check the owner against zero, so a failed recovery is a signature of
  `address(0)`). Its one quirk is the call-depth limit: there the `STATICCALL` to `0x01` fails
  without running, AMPL reverts on the failed call, and `amplRec` is an address other than the
  owner (`1` for the zero owner, `0` otherwise), so the model reverts too.
* `amplGp m` is `150000` when the token's `name` (slot 51, as solc 0.7 encodes a string) has at
  most 31 bytes, as AMPL's deployed name does; `2⁶⁴` otherwise, so with a longer `name`
  (an arbitrary world; `DOMAIN_SEPARATOR()` is recomputed from `name` by a copy loop) the spec
  only asks that `permit` never succeed unlike the model.
* With at least `amplGp m` gas, not static, no value (`permit_high`, from 150000 gas and a
  short `name`): success exactly when the model's condition holds (`permitOk_iff`), with the
  model's state, `Approval` and nothing else changed; a revert otherwise.
* Otherwise (`permit_low`, at any gas): every success is such a success.

**`PermitResidue`** (`ampl_malformed`'s open part): `permit` frames with no value and all seven
argument words, any gas, dirty argument words included. When `ecrecover` runs the precompile
(`EcrecoverPlain`) they end as the model's `permit` of the masked arguments with `amplRec`, or
fail (`permit_low`): `permitResidue_plain`. **`PermitDelegResidue`** is what is left: the frames
where the account `0x01` holds an EIP-7702 designator, so that the `STATICCALL` runs the
delegate's code. `ampl_complete` takes it as a hypothesis.
-/

namespace Verified.WeirdERC20.AMPL.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.AMPL.Contracts
open Verified.WeirdERC20.AMPL.Spec Verified.WeirdERC20.Common
open Verified.Solady.Spec (LowHalts halts_split ite_neg' ite_pos')

/-- **AMPL's `permit` gas bound**: `150000` for a `name` of at most 31 bytes (AMPL's deployed
`name` is `"Ampleforth"`), else `2⁶⁴` (no frame of `PermitSpec` is then `Normal`). -/
def amplGp (m : Machine) : Nat :=
  if nameLen07 (m.world.sload m.frame.msg.currentTarget 51#256) ≤ 31 then 150000 else 2 ^ 64

section
variable {Act : Finset Address} {m : Machine}

/-- The frame's own `permit` call matches the model: the end condition of both runs. -/
abbrev PMatch (Act : Finset Address) (m mf : Machine) (o : Outcome) : Prop :=
  Matches amplAbs Act m mf o (M.events (pre amplAbs Act m) m.frame.msg.caller (pCall m))
    (M.call (pre amplAbs Act m) m.frame.msg.caller (pCall m))

/-- **`permit` at any gas**: every success matches the model. -/
theorem permit_lowM (hS : Start AMPL.runtimeCode amplAbs M Act m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xd505accf) (h228 : 228 ≤ m.frame.msg.data.size)
    (hE : EcrecoverPlain m) (ho : pOwner m.frame.msg.data ∈ Act)
    (hsp : pSpender m.frame.msg.data ∈ Act) :
    LowHalts m (PMatch Act m) := fun H hF hP =>
  permit_low m hS.fresh hsel h228 hS.size hS.precompiles hE H hF fun mf o ⟨ho', hok, hd⟩ =>
    hP mf o (by rw [ho']; exact matches_of_permitDone hS hok.1 ho hsp hok hd)

/-- **`permit` in a `Normal` frame** (at least `amplGp m` gas, not static, no value): it ends
as the model's `permit`. -/
theorem permit_highM (hS : Start AMPL.runtimeCode amplAbs M Act m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xd505accf) (h228 : 228 ≤ m.frame.msg.data.size)
    (hE : EcrecoverPlain m) (ho : pOwner m.frame.msg.data ∈ Act)
    (hsp : pSpender m.frame.msg.data ∈ Act) (hN : Normal (amplGp m) m)
    (hgl : m.frame.gasLeft < 2 ^ 64) :
    Halts m (PMatch Act m) := by
  obtain ⟨hg, hst, hval⟩ := hN
  have hshort : nameLen07 (m.world.sload m.frame.msg.currentTarget 51#256) ≤ 31 := by
    by_contra h
    unfold amplGp at hg
    rw [ite_neg' h] at hg
    omega
  have hg' : 150000 ≤ m.frame.gasLeft := by
    unfold amplGp at hg
    rwa [ite_pos' hshort] at hg
  refine (permit_high m hS.fresh hsel h228 hS.size hval hst hg' hgl hshort hS.precompiles
    hE).mono fun mf o _ ⟨h1, h2⟩ => ?_
  by_cases hok : PermitOk m
  · obtain ⟨rfl, hd⟩ := h1 hok
    exact matches_of_permitDone hS hval ho hsp hok hd
  · obtain ⟨out, rfl⟩ := h2 hok
    have hc := mt (permitOk_iff hS hval hst ho).1 hok
    simp only [PMatch, pCall]
    rw [ampl_call_permit, ite_neg' hc]
    exact ⟨out, rfl⟩

/-- **`permit` with all seven words, `ecrecover` the precompile, below `2⁶⁴` gas**: it ends as
the model's `permit` of the masked arguments, or fails outside `Normal (amplGp m)`. -/
theorem permit_frame (hS : Start AMPL.runtimeCode amplAbs M Act m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xd505accf) (h228 : 228 ≤ m.frame.msg.data.size)
    (hE : EcrecoverPlain m) (ho : pOwner m.frame.msg.data ∈ Act)
    (hsp : pSpender m.frame.msg.data ∈ Act) (hgl : m.frame.gasLeft < 2 ^ 64) :
    Halts m fun mf o => PMatch Act m mf o ∨ (Fails o ∧ ¬ Normal (amplGp m) m) :=
  halts_split (fun hN => permit_highM hS hsel h228 hE ho hsp hN hgl)
    (permit_lowM hS hsel h228 hE ho hsp) fun _ _ h => h

end

/-- **AMPL's `permit` meets `PermitSpec`**, with the recovery `amplRec` and the gas bound
`amplGp`. -/
theorem ampl_permitSpec : PermitSpec AMPL.runtimeCode amplAbs M amplGp amplRec := by
  intro Act m o sp v dl pv pr ps hS ho hsp hE hgl hA
  have h0 : argWord m.frame.msg.data 0 = Word.ofAddress o := hA.arg 0 (by simp)
  have h1 : argWord m.frame.msg.data 1 = Word.ofAddress sp := hA.arg 1 (by simp)
  have h2 : argWord m.frame.msg.data 2 = v := hA.arg 2 (by simp)
  have h3 : argWord m.frame.msg.data 3 = dl := hA.arg 3 (by simp)
  have hpo : pOwner m.frame.msg.data = o := by
    simp only [pOwner, h0, Word.toAddress_ofAddress]
  have hps : pSpender m.frame.msg.data = sp := by
    simp only [pSpender, h1, Word.toAddress_ofAddress]
  have hc : pCall m = .permit o sp v.toNat
      (decide (m.ctx.block.timestamp % 2 ^ 256 ≤ dl.toNat)) (amplRec m) := by
    simp only [pCall, pLive, hpo, hps, h2, h3]
  have h228 : 228 ≤ m.frame.msg.data.size := by
    have := hA.size
    simpa using this
  have h := permit_frame hS hA.selector h228 hE (hpo ▸ ho) (hps ▸ hsp) hgl
  simp only [PMatch, hc] at h
  exact h

/-- **`PermitResidue` where `ecrecover` runs the precompile**: any gas, dirty words included. -/
theorem permitResidue_plain {Act : Finset Address} {m : Machine}
    (hS : Start AMPL.runtimeCode amplAbs M Act m) (hAct : calldataAddrs m.frame.msg.data ⊆ Act)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xd505accf) (h228 : 228 ≤ m.frame.msg.data.size)
    (hE : EcrecoverPlain m) :
    Halts m (Post amplRec Act m) := by
  have ho : pOwner m.frame.msg.data ∈ Act := arg_mem hAct (i := 0) (by omega)
  have hsp : pSpender m.frame.msg.data ∈ Act := arg_mem hAct (i := 1) (by omega)
  refine permit_lowM hS hsel h228 hE ho hsp _
    ⟨fun _ _ => .inl trivial, fun _ _ => .inl trivial⟩ fun mf o h => ?_
  refine .inr (.inr (.inl ⟨pCall m, ⟨amplRec, rfl, fun _ => rfl⟩, fun a ha => ?_, h⟩))
  simp only [pCall, Call.addrs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl <;> assumption

/-- **The `permit` frames left open**: those of `PermitResidue amplRec` where the account `0x01`
holds an EIP-7702 designator (not `EcrecoverPlain`), so that AMPL's `STATICCALL` to `ecrecover`
runs the delegate's code (statically). `MalformedSpec` lets any recovery explain them. -/
def PermitDelegResidue : Prop :=
  ∀ Act m, Start AMPL.runtimeCode amplAbs M Act m →
    calldataAddrs m.frame.msg.data ⊆ Act → m.frame.msg.value = 0 →
    Abi.selectorOf m.frame.msg.data = 0xd505accf → 228 ≤ m.frame.msg.data.size →
    ¬ EcrecoverPlain m → Halts m (Post amplRec Act m)

theorem permitResidue_of (h : PermitDelegResidue) : PermitResidue amplRec := by
  intro Act m hS hAct hv hsel h228
  by_cases hE : EcrecoverPlain m
  · exact permitResidue_plain hS hAct hsel h228 hE
  · exact h Act m hS hAct hv hsel h228 hE

/-- **The complete spec of AMPL**, from the `permit` frames where `0x01` is delegated
(`PermitDelegResidue`): `ampl_spec`, `ampl_permitSpec`, and `MalformedSpec` with no entry point
excluded. -/
theorem ampl_complete (h : PermitDelegResidue) :
    ERC20Spec.Complete AMPL.runtimeCode amplAbs M g₀ sel amplOps amplOpAddrs
      (some (amplGp, amplRec)) [] where
  spec := ampl_spec
  permit gp rec hp := by
    simp only [Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ampl_permitSpec
  malformed := ampl_malformed amplRec (permitResidue_of h)

end Verified.WeirdERC20.AMPL.Spec.Malformed
