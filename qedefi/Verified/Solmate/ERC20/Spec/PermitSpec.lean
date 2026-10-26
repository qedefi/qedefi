import Verified.Solmate.ERC20.Spec.PermitDepth
import Verified.Solmate.ERC20.Spec.LowCall

/-!
# Solmate's `permit` against `PermitSpec`

`permit_spec_case`: the obligation `PermitSpec (code ia) solmateAbs solmateModel (solmateGp ia)
(solmateRec ia)` for every frame whose domain separator is in `Permit.DomainCase`: on the
deployment chain (`chainid() = INITIAL_CHAIN_ID`, the immutable separator), or off it with a
short `name` (under 32 bytes). Off the deployment chain with a long `name` (or an inconsistent
slot word) the domain separator is computed by the copy loop of `0x0a66`: `PermitLongSpec.lean`
(`solmate_permit`, every case).

* normal frames: `permit_normal` below the call-depth limit, `permit_halts_limit` at it
  (`solmateRec` is `0` there, so the model reverts too);
* other frames: lifted to gas `max gas gp` (`low_ecrecover`), where they end as a static frame
  (`permit_halts_static`), a frame with value (`value_reverts`) or a normal one.
-/

namespace Verified.Solmate.ERC20.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.Solmate QEDefi.Math
open Verified.Solmate.Contracts Verified.Solmate.ERC20

variable {ia : SolmateAsset.Immutables} {Act : Finset Address} {m : Machine}

/-- `permit` in a frame with gas from 100000, no value, not static, in `DomainCase`, at any depth. -/
theorem permit_exact (hS : Start (code ia) solmateAbs M Act m) {o sp : Address}
    {v dl pv pr ps : Word} (ho : o ∈ Act) (hsp : sp ∈ Act) (hep : EcrecoverPlain m)
    (hgl : m.frame.gasLeft < 2 ^ 64)
    (hA : Args m.frame.msg.data 0xd505accf [Word.ofAddress o, Word.ofAddress sp, v, dl, pv, pr, ps])
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : 100000 ≤ m.frame.gasLeft)
    (hcase : Permit.DomainCase ia.initialChainId (ofNat m.ctx.block.chainId)
      (m.world.sload m.frame.msg.currentTarget 0#256)) :
    Halts m fun mf out =>
      Matches solmateAbs Act m mf out
        (M.events (pre solmateAbs Act m) m.frame.msg.caller
          (.permit o sp v.toNat (decide (m.ctx.block.timestamp % 2 ^ 256 ≤ dl.toNat))
            (solmateRec ia m)))
        (M.call (pre solmateAbs Act m) m.frame.msg.caller
          (.permit o sp v.toNat (decide (m.ctx.block.timestamp % 2 ^ 256 ≤ dl.toNat))
            (solmateRec ia m))) := by
  by_cases hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit
  · exact permit_normal hS ho hsp hep hgl hA hval hst hg hcase hdepth
  · have hlim : Gas.stackDepthLimit < m.frame.msg.depth + 1 := by omega
    have hrec : ∀ n, solmateRec ia m n = 0 := fun n => by simp [solmateRec, hlim]
    have hno : ¬ (decide (m.ctx.block.timestamp % 2 ^ 256 ≤ dl.toNat) = true ∧
        solmateRec ia m ((pre solmateAbs Act m).nonces o) = o ∧ o ≠ 0) := by
      rintro ⟨-, h1, h2⟩; rw [hrec] at h1; exact h2 h1.symm
    simp only [M, solmateModel_call, call_permit, if_neg' hno]
    exact permit_halts_limit m hS.fresh hval hst (permitCall_of_args hA) hS.size hcase hg hgl
      hS.precompiles hep hlim

theorem getterGas_short {S : Word} (h : Permit.ShortString S) :
    Str.getterGas (Str.slotLen S) < 2 ^ 32 := by
  obtain ⟨h1, h2⟩ := h
  have hS : S.toNat % 2 = 0 := by
    have := congrArg BitVec.toNat h1
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat] at this
    rw [show (1 : Nat) % 2 ^ 256 = 2 ^ 1 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod] at this
    simpa using this
  have hL : Str.slotLen S < 32 := by
    unfold Str.slotLen; simp only [hS, ↓reduceIte]
    simp only [Permit.shortLength, BitVec.toNat_and, Word.shr,
      BitVec.toNat_ofNat] at h2
    rw [show (127 : Nat) % 2 ^ 256 = 2 ^ 7 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod] at h2
    simpa [Nat.shiftRight_eq_div_pow] using h2
  unfold Str.getterGas
  have hw : (Str.slotLen S + 31) / 32 ≤ 1 := by omega
  have := Gas.memoryCost_mono (show 256 + 64 * ((Str.slotLen S + 31) / 32) ≤ 320 by omega)
  have h320 : Gas.memoryCost 320 < 2 ^ 20 := by decide
  omega

theorem gp_lt (hcase : Permit.DomainCase ia.initialChainId (ofNat m.ctx.block.chainId)
      (m.world.sload m.frame.msg.currentTarget 0#256)) :
    100000 ≤ solmateGp ia m ∧ solmateGp ia m < 2 ^ 64 := by
  unfold solmateGp
  by_cases hc : ofNat m.ctx.block.chainId = ia.initialChainId
  · simp [hc]
  · simp only [hc, ↓reduceIte]
    rcases hcase with h | h
    · exact absurd h hc
    · have := getterGas_short h; omega

/-- **Solmate's `permit` meets `PermitSpec` in `DomainCase`**: on the deployment chain, or off
it with a short `name`. -/
theorem permit_spec_case (Act : Finset Address) (m : Machine) (o sp : Address)
    (v dl pv pr ps : Word) (hS : Start (code ia) solmateAbs M Act m) (ho : o ∈ Act)
    (hsp : sp ∈ Act) (hep : EcrecoverPlain m) (hgl : m.frame.gasLeft < 2 ^ 64)
    (hA : Args m.frame.msg.data 0xd505accf [Word.ofAddress o, Word.ofAddress sp, v, dl, pv, pr, ps])
    (hcase : Permit.DomainCase ia.initialChainId (ofNat m.ctx.block.chainId)
      (m.world.sload m.frame.msg.currentTarget 0#256)) :
    Halts m fun mf out =>
      Matches solmateAbs Act m mf out
        (M.events (pre solmateAbs Act m) m.frame.msg.caller
          (.permit o sp v.toNat (decide (m.ctx.block.timestamp % 2 ^ 256 ≤ dl.toNat))
            (solmateRec ia m)))
        (M.call (pre solmateAbs Act m) m.frame.msg.caller
          (.permit o sp v.toNat (decide (m.ctx.block.timestamp % 2 ^ 256 ≤ dl.toNat))
            (solmateRec ia m))) ∨
      (Fails out ∧ ¬ Normal (solmateGp ia m) m) := by
  obtain ⟨hgp, hgp'⟩ := gp_lt (ia := ia) hcase
  by_cases hN : Normal (solmateGp ia m) m
  · exact (permit_exact hS ho hsp hep hgl hA hN.2.2 hN.2.1 (by have := hN.1; omega) hcase).mono
      fun _ _ _ h => .inl h
  · let G := max m.frame.gasLeft (solmateGp ia m)
    have hG : m.frame.gasLeft ≤ G := Nat.le_max_left _ _
    have hG64 : G < 2 ^ 64 := by omega
    have hS' := hi_start hS hG
    have hgG := hi_gas (m := m) hG
    refine (low_ecrecover (P := fun out mf => Matches solmateAbs Act m mf (.success out)
        (M.events (pre solmateAbs Act m) m.frame.msg.caller
          (.permit o sp v.toNat (decide (m.ctx.block.timestamp % 2 ^ 256 ≤ dl.toNat))
            (solmateRec ia m)))
        (M.call (pre solmateAbs Act m) m.frame.msg.caller
          (.permit o sp v.toNat (decide (m.ctx.block.timestamp % 2 ^ 256 ≤ dl.toNat))
            (solmateRec ia m))))
      hS hep hG (by omega) (fun out mf mf' hw ht hc hl h => matches_congr hw ht hc hl h) ?_).mono
      fun mf o _ h => ?_
    · by_cases hval : m.frame.msg.value = 0
      · by_cases hst : m.frame.msg.isStatic = false
        · exact (permit_exact hS' ho hsp hep (by rw [hgG]; exact hG64) hA hval hst
            (by rw [hgG]; omega) hcase).mono fun mf o _ h out ho' => by subst ho'; exact h
        · exact (permit_halts_static (hi G m) hS'.fresh hval (by rw [hi_msg]; simpa using hst)
            (permitCall_of_args hA) hS.size hcase (by rw [hgG]; omega) (by rw [hgG]; exact hG64)
            hS'.precompiles).mono fun mf o _ h out ho' => absurd ho' (not_success_of_fails h out)
      · exact (value_reverts (hi G m) hS'.fresh hval (by rw [hgG]; omega)).mono
          fun mf o _ ⟨r, hr⟩ out ho' => by subst hr; cases ho'
    · rcases h with h | ⟨out, rfl, h⟩
      · exact .inr ⟨h, hN⟩
      · exact .inl h

end Verified.Solmate.ERC20.Spec
