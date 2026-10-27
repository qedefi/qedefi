import Verified.Solmate.ERC20.Spec.PermitModel

/-!
# Solmate's `permit` in normal frames, below the call-depth limit

`permit_normal`: with gas from 100000, no value, not static, `ecrecover` running the precompile,
the domain separator of `Permit.DomainCase` (the deployment chain, or a short `name`) and room
for the `STATICCALL`, the deployed `permit` ends as `solmateModel`'s `permit` call with
`solmateRec` (from `Permit.asset_permit_halts`).
-/

namespace Verified.Solmate.ERC20.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.Solmate QEDefi.Math Finsupp
open Verified.Solmate.Contracts Verified.Solmate.ERC20 Verified.Solmate.ERC4626 QEDefi.ERC4626

variable {ia : SolmateAsset.Immutables} {Act : Finset Address} {m : Machine}

theorem word_toNat' (x : Word) : word x.toNat = x := by simp [word]

/-- The `permit` arguments, as `Permit.PermitCall` reads them. -/
theorem permitCall_of_args {data : ByteArray} {o sp : Address} {v dl pv pr ps : Word}
    (h : Args data 0xd505accf [Word.ofAddress o, Word.ofAddress sp, v, dl, pv, pr, ps]) :
    Permit.PermitCall data o sp v dl pv pr ps :=
  ⟨h.selector, by have := h.size; simpa using this, by simpa using h.arg 0 (by simp),
    by simpa using h.arg 1 (by simp), by simpa using h.arg 2 (by simp),
    by simpa using h.arg 3 (by simp), by simpa using h.arg 4 (by simp),
    by simpa using h.arg 5 (by simp), by simpa using h.arg 6 (by simp)⟩

theorem argWord_of_args {data : ByteArray} {sel : Nat} {args : List Word} (h : Args data sel args)
    (j : Nat) (hj : j < args.length) : argWord data j = args[j] := h.arg j hj

/-- In `DomainCase`, the domain separator the code computes is `solmateDs`'s. -/
theorem solmateDs_of_case (hcase : Permit.DomainCase ia.initialChainId (ofNat m.ctx.block.chainId)
      (m.world.sload m.frame.msg.currentTarget 0#256)) :
    solmateDs ia m = some (Permit.dsOf ia.initialChainId ia.initialDomainSeparator m) := by
  unfold solmateDs Permit.dsOf Permit.domainSeparator
  by_cases hc : ofNat m.ctx.block.chainId = ia.initialChainId
  · simp [hc]
  · simp only [hc, ↓reduceIte]
    rcases hcase with h | ⟨h1, h2⟩
    · exact absurd h hc
    · simp only [nameBytes, h1, h2, ↓reduceIte, Option.map_some]
      rfl

/-- `solmateRec` below the depth limit, with a domain separator. -/
theorem solmateRec_eq {o sp : Address} {v dl pv pr ps : Word}
    (hA : Args m.frame.msg.data 0xd505accf [Word.ofAddress o, Word.ofAddress sp, v, dl, pv, pr, ps])
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit) {ds : Word}
    (hds : solmateDs ia m = some ds) (n : ℕ) :
    solmateRec ia m n = (ecrecoverAddress? m.ctx.crypto (Permit.digest m.ctx.crypto ds
      (Permit.structHash m.ctx.crypto o sp v (word n) dl)) pv pr ps).getD 0 := by
  have hnd : ¬ Gas.stackDepthLimit < m.frame.msg.depth + 1 := by omega
  simp only [solmateRec, hnd, ↓reduceIte, hds, argWord_of_args hA 0 (by simp),
    argWord_of_args hA 1 (by simp), argWord_of_args hA 2 (by simp), argWord_of_args hA 3 (by simp),
    argWord_of_args hA 4 (by simp), argWord_of_args hA 5 (by simp), argWord_of_args hA 6 (by simp)]
  simp

/-- The model's validity of a `permit` is the code's (`Permit.PermitValid`). -/
theorem permitValid_iff {crypto : Crypto} {ds : Word} {ts : Nat} {o sp : Address}
    {v dl pv pr ps nonce : Word} {rec : ℕ → Address}
    (hrec : rec nonce.toNat = (ecrecoverAddress? crypto (Permit.digest crypto ds
      (Permit.structHash crypto o sp v (word nonce.toNat) dl)) pv pr ps).getD 0) :
    Permit.PermitValid crypto ds ts o sp v dl pv pr ps nonce ↔
      (decide (ts % 2 ^ 256 ≤ dl.toNat) = true ∧ rec nonce.toNat = o ∧ o ≠ 0) := by
  rw [hrec, word_toNat']
  unfold Permit.PermitValid Permit.SigOk
  have hts : (ofNat ts).toNat = ts % 2 ^ 256 := by simp [ofNat]
  rw [hts]
  constructor
  · rintro ⟨-, hdl, ho, hr⟩
    exact ⟨by simpa using hdl, by rw [hr]; rfl, ho⟩
  · rintro ⟨hdl, hr, ho⟩
    have hsome : ecrecoverAddress? crypto (Permit.digest crypto ds
        (Permit.structHash crypto o sp v nonce dl)) pv pr ps = some o := by
      cases he : ecrecoverAddress? crypto (Permit.digest crypto ds
          (Permit.structHash crypto o sp v nonce dl)) pv pr ps with
      | none => rw [he] at hr; exact absurd hr.symm ho
      | some a => rw [he] at hr; simp only [Option.getD_some] at hr; rw [hr]
    have hv : pv.toNat < 256 := by
      unfold ecrecoverAddress? at hsome
      by_contra h
      simp only [show pv.toNat ≠ 27 by omega, show pv.toNat ≠ 28 by omega, ne_eq,
        not_false_eq_true, and_self, ↓reduceIte, reduceCtorEq] at hsome
    exact ⟨hv, by simpa using hdl, ho, hsome⟩

/-- `permitWorld` read back: the model's `permit` state. -/
theorem read_permitWorld {crypto : Crypto} {w : World} {token o sp : Address} {v : Word}
    (hS : SolmateSound crypto Act) (ho : o ∈ Act) (hsp : sp ∈ Act) :
    solmateRead crypto Act (Permit.permitWorld crypto w token o sp v) token =
      { (solmateRead crypto Act w token).setAllowance o sp v.toNat with
        nonces := (solmateRead crypto Act w token).nonces.update o
          (((solmateRead crypto Act w token).nonces o + 1) % U256) } ∧
    FrameKeeps solmateAbs crypto Act token w (Permit.permitWorld crypto w token o sp v) := by
  have hn : (w.sload token (mappingSlot crypto (Word.ofAddress o) 5#256)).toNat =
      (solmateRead crypto Act w token).nonces o := (readMap_of_mem ho w token 5#256).symm
  refine ⟨?_, ?_⟩
  · simp only [Permit.permitWorld, Permit.nonceSlot, ERC20.allowanceSlot, layout_allowances]
    rw [read_sstore_allowance hS ho hsp, read_sstore_nonce hS ho]
    have : (w.sload token (mappingSlot crypto (Word.ofAddress o) 5#256) + 1#256).toNat =
        ((solmateRead crypto Act w token).nonces o + 1) % U256 := by
      rw [BitVec.toNat_add, hn]; rfl
    rw [this]
    rfl
  · simp only [Permit.permitWorld, Permit.nonceSlot, ERC20.allowanceSlot, layout_allowances]
    exact frameKeeps_sstore (frameKeeps_sstore (frameKeeps_refl _ _ _ _) (footprint_nonce ho))
      (footprint_allowance ho hsp)

set_option maxHeartbeats 1000000 in
/-- **`permit` in a normal frame below the depth limit, in `DomainCase`.** -/
theorem permit_normal (hS : Start (code ia) solmateAbs M Act m) {o sp : Address}
    {v dl pv pr ps : Word} (ho : o ∈ Act) (hsp : sp ∈ Act) (hep : EcrecoverPlain m)
    (hgl : m.frame.gasLeft < 2 ^ 64)
    (hA : Args m.frame.msg.data 0xd505accf [Word.ofAddress o, Word.ofAddress sp, v, dl, pv, pr, ps])
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : 100000 ≤ m.frame.gasLeft)
    (hcase : Permit.DomainCase ia.initialChainId (ofNat m.ctx.block.chainId)
      (m.world.sload m.frame.msg.currentTarget 0#256))
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit) :
    Halts m fun mf out =>
      Matches solmateAbs Act m mf out
        (M.events (pre solmateAbs Act m) m.frame.msg.caller
          (.permit o sp v.toNat (decide (m.ctx.block.timestamp % 2 ^ 256 ≤ dl.toNat))
            (solmateRec ia m)))
        (M.call (pre solmateAbs Act m) m.frame.msg.caller
          (.permit o sp v.toNat (decide (m.ctx.block.timestamp % 2 ^ 256 ≤ dl.toNat))
            (solmateRec ia m))) := by
  have hpre := pre_eq hS hval
  have hds := solmateDs_of_case hcase
  have hn : (pre solmateAbs Act m).nonces o =
      (m.world.sload m.frame.msg.currentTarget (Permit.nonceSlot m.ctx.crypto o)).toNat := by
    rw [hpre]; exact readMap_of_mem ho _ _ 5#256
  have hrec := solmateRec_eq hA hdepth hds
  have hiff := permitValid_iff (crypto := m.ctx.crypto) (ts := m.ctx.block.timestamp)
    (nonce := m.world.sload m.frame.msg.currentTarget (Permit.nonceSlot m.ctx.crypto o))
    (rec := solmateRec ia m) (hrec _)
  rw [← hn] at hiff
  simp only [M, solmateModel_call, solmateModel_events, solmateEvents, call_permit]
  refine (Permit.asset_permit_halts m hS.fresh hval hst (permitCall_of_args hA) hS.size hcase hg
    hgl hS.precompiles hep hdepth).mono fun mf out _ ⟨h1, h2, _⟩ => ?_
  by_cases hv : decide (m.ctx.block.timestamp % 2 ^ 256 ≤ dl.toNat) = true ∧
      solmateRec ia m ((pre solmateAbs Act m).nonces o) = o ∧ o ≠ 0
  · rw [if_pos' hv]
    obtain ⟨ho', hw, ht, hc, hl⟩ := h1 (hiff.2 hv)
    have hrw := read_permitWorld (crypto := m.ctx.crypto) (w := m.world)
      (token := m.frame.msg.currentTarget) (v := v) hS.sound ho hsp
    refine ⟨ho', ?_, ?_, ht, hc, ?_⟩
    · show solmateRead _ _ _ _ = _
      rw [hw, hrw.1, hpre]
    · rw [hw]; exact hrw.2
    · rw [hl]; simp [eventLog_approval, word_toNat']
  · rw [if_neg' hv]
    exact h2 fun h => hv (hiff.1 h)

end Verified.Solmate.ERC20.Spec
