import Verified.Solmate.ERC20.Spec.PermitLongFrame
import Verified.Solmate.ERC20.Spec.PermitSpec

/-!
# Solmate's `permit` meets `PermitSpec`, every domain separator

`solmate_permit`: `PermitSpec (code ia) solmateAbs solmateModel (solmateGp ia) (solmateRec ia)`
without `Permit.DomainCase`. Inside it, `permit_spec_case`. Outside it (off the deployment
chain, the `name` slot word not a short string), three cases of the slot word:

* inconsistent (`nameBytes` is `none`): `permit` reverts in every frame with no value
  (`pl_permit_panic`); `solmateRec` is `0`, so the model reverts too;
* a long name of at most `2⁶⁴ + 1` words: exact from `solmateGp` (`pl_permit_long_halts`), and
  any other frame is lifted to gas `max gas gp`, below `2²⁵⁶` (`low_ecrecover`);
* a longer name: no frame is normal (`gp` exceeds `2⁶⁴`), and every frame fails, lifted to
  `max gas 100000` where the copy loop runs out of gas (`pl_permit_huge`).

`solmate_erc20Spec_permit`: with `solmate_erc20Spec`.
-/

namespace Verified.Solmate.ERC20.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.Solmate QEDefi.Math
open Verified.Solmate.Contracts Verified.Solmate.ERC20

variable {ia : SolmateAsset.Immutables} {Act : Finset Address} {m : Machine}

theorem nameBytes_long {crypto : Crypto} {sload : Word → Word}
    (hodd : sload 0#256 &&& 1#256 = 1#256) (hL : 32 ≤ (Word.shr 1#256 (sload 0#256)).toNat) :
    nameBytes crypto sload =
      some (Str.longData sload (arrayDataSlot crypto 0#256) (Word.shr 1#256 (sload 0#256)).toNat) := by
  have h10 : ¬ (1#256 : Word) = 0#256 := by decide
  simp only [nameBytes, hodd, h10, ↓reduceIte, hL]

/-- Off `DomainCase`: the slot word is inconsistent, or a long name. -/
theorem off_case {crypto : Crypto} {sload : Word → Word} {c c' : Word}
    (h : ¬ Permit.DomainCase c' c (sload 0#256)) :
    nameBytes crypto sload = none ∨
      (sload 0#256 &&& 1#256 = 1#256 ∧ 32 ≤ (Word.shr 1#256 (sload 0#256)).toNat) := by
  have hs : ¬ Permit.ShortString (sload 0#256) := fun hs => h (.inr hs)
  rcases and_one_cases (sload 0#256) with h0 | h1
  · left
    have : ¬ (Permit.shortLength (sload 0#256)).toNat < 32 := fun hl => hs ⟨h0, hl⟩
    simp [nameBytes, h0, this]
  · by_cases hL : 32 ≤ (Word.shr 1#256 (sload 0#256)).toNat
    · exact .inr ⟨h1, hL⟩
    · left
      have h10 : ¬ (1#256 : Word) = 0#256 := by decide
      simp only [nameBytes, h1, h10, ↓reduceIte, hL]

theorem slotLen_odd {S : Word} (h : S &&& 1#256 = 1#256) :
    Str.slotLen S = (Word.shr 1#256 S).toNat := by
  have h1 : S.toNat % 2 = 1 := by
    have := congrArg BitVec.toNat h
    rw [Str.toNat_and_one] at this; simpa using this
  have hlt : S.toNat / 2 < 2 ^ 256 := by have := S.isLt; omega
  simp only [Str.slotLen, Str.shr_one, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
    show ¬ S.toNat % 2 = 0 by omega, ↓reduceIte]

set_option maxHeartbeats 1000000 in
/-- **`permit` with a long name off the deployment chain**, no value, not static, gas from
`solmateGp` below `2²⁵⁶`, at any depth: exactly the model's `permit` with `solmateRec`. -/
theorem pl_permit_exact (hS : Start (code ia) solmateAbs M Act m) {o sp : Address}
    {v dl pv pr ps : Word} (ho : o ∈ Act) (hsp : sp ∈ Act) (hep : EcrecoverPlain m)
    (hgl : m.frame.gasLeft < 2 ^ 256)
    (hA : Args m.frame.msg.data 0xd505accf [Word.ofAddress o, Word.ofAddress sp, v, dl, pv, pr, ps])
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hne : ofNat m.ctx.block.chainId ≠ ia.initialChainId)
    (hodd : m.world.sload m.frame.msg.currentTarget 0#256 &&& 1#256 = 1#256)
    (hL : 32 ≤ (Word.shr 1#256 (m.world.sload m.frame.msg.currentTarget 0#256)).toNat)
    (hg : 100000 + Str.getterGas
      (Word.shr 1#256 (m.world.sload m.frame.msg.currentTarget 0#256)).toNat ≤ m.frame.gasLeft) :
    Halts m fun mf out =>
      Matches solmateAbs Act m mf out
        (M.events (pre solmateAbs Act m) m.frame.msg.caller
          (.permit o sp v.toNat (decide (m.ctx.block.timestamp % 2 ^ 256 ≤ dl.toNat))
            (solmateRec ia m)))
        (M.call (pre solmateAbs Act m) m.frame.msg.caller
          (.permit o sp v.toNat (decide (m.ctx.block.timestamp % 2 ^ 256 ≤ dl.toNat))
            (solmateRec ia m))) := by
  have hds : solmateDs ia m = some (plDs m) := by
    simp only [solmateDs, hne, ↓reduceIte, nameBytes_long hodd hL, Option.map_some, plDs]
  by_cases hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit
  · have hpre := pre_eq hS hval
    have hn : (pre solmateAbs Act m).nonces o =
        (m.world.sload m.frame.msg.currentTarget (Permit.nonceSlot m.ctx.crypto o)).toNat := by
      rw [hpre]; exact readMap_of_mem ho _ _ 5#256
    have hrec := solmateRec_eq hA hdepth hds
    have hiff := permitValid_iff (crypto := m.ctx.crypto) (ts := m.ctx.block.timestamp)
      (nonce := m.world.sload m.frame.msg.currentTarget (Permit.nonceSlot m.ctx.crypto o))
      (rec := solmateRec ia m) (hrec _)
    rw [← hn] at hiff
    simp only [M, solmateModel_call, solmateModel_events, solmateEvents, call_permit]
    refine (pl_permit_long_halts m hS.fresh hval hst (permitCall_of_args hA) hS.size hne hodd hL
      hg hgl hS.precompiles hep hdepth).mono fun mf out _ ⟨h1, h2⟩ => ?_
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
  · have hlim : Gas.stackDepthLimit < m.frame.msg.depth + 1 := by omega
    have hrec : ∀ n, solmateRec ia m n = 0 := fun n => by simp [solmateRec, hlim]
    have hno : ¬ (decide (m.ctx.block.timestamp % 2 ^ 256 ≤ dl.toNat) = true ∧
        solmateRec ia m ((pre solmateAbs Act m).nonces o) = o ∧ o ≠ 0) := by
      rintro ⟨-, h1, h2⟩; rw [hrec] at h1; exact h2 h1.symm
    simp only [M, solmateModel_call, call_permit, if_neg' hno]
    exact pl_permit_long_limit m hS.fresh hval hst (permitCall_of_args hA) hS.size hne hodd hL hg
      hgl hS.precompiles hep hlim


theorem getterGas_ge (L : Nat) : 2400 * ((L + 31) / 32) ≤ Str.getterGas L := by
  unfold Str.getterGas; omega

theorem getterGas_lt {L : Nat} (h : (L + 31) / 32 ≤ 2 ^ 65) : Str.getterGas L < 2 ^ 200 := by
  unfold Str.getterGas
  have hm := Gas.memoryCost_mono (show 256 + 64 * ((L + 31) / 32) ≤ 256 + 64 * 2 ^ 65 by omega)
  have : Gas.memoryCost (256 + 64 * 2 ^ 65) < 2 ^ 199 := by decide
  omega

/-- The common shape of the cases: a frame that may only revert or fail. -/
theorem fails_lift (hS : Start (code ia) solmateAbs M Act m) (hep : EcrecoverPlain m)
    {P : ByteArray → Machine → Prop}
    (hP : ∀ out mf mf', mf'.world = mf.world → mf'.transient = mf.transient →
      mf'.createdAccounts = mf.createdAccounts → mf'.frame.sub.logs = mf.frame.sub.logs →
      P out mf → P out mf')
    (hgl : m.frame.gasLeft < 2 ^ 64)
    (hfail : ∀ m', Start (code ia) solmateAbs M Act m' → m'.frame.msg = { m.frame.msg with gas := m'.frame.gasLeft } →
      m'.world = m.world → m'.ctx = m.ctx → m'.frame.msg.value = 0 → 100000 ≤ m'.frame.gasLeft →
      m'.frame.gasLeft < 2 ^ 64 → Halts m' fun _ o => Fails o) :
    Halts m fun mf o => Fails o ∨ ∃ out, o = .success out ∧ P out mf := by
  let G := max m.frame.gasLeft 100000
  have hG : m.frame.gasLeft ≤ G := Nat.le_max_left _ _
  have hS' := hi_start hS hG
  have hgG := hi_gas (m := m) hG
  refine low_ecrecover hS hep hG (by omega) hP ?_
  by_cases hval : m.frame.msg.value = 0
  · exact (hfail _ hS' (by rw [hi_msg, hgG]) rfl rfl (by rw [hi_msg]; exact hval)
      (by rw [hgG]; omega) (by rw [hgG]; omega)).mono
      fun mf o _ h out ho => absurd ho (not_success_of_fails h out)
  · exact (value_reverts (hi G m) hS'.fresh (by rw [hi_msg]; exact hval) (by rw [hgG]; omega)).mono
      fun mf o _ ⟨r, hr⟩ out ho => by subst hr; cases ho

set_option maxHeartbeats 1000000 in
/-- **Solmate's `permit` meets `PermitSpec`**, for every domain separator: the deployment chain,
or off it with a short, long or inconsistent `name`. -/
theorem solmate_permit (ia : SolmateAsset.Immutables) :
    PermitSpec (SolmateAsset.runtimeCodeWith ia) solmateAbs solmateModel (solmateGp ia)
      (solmateRec ia) := by
  intro Act m o sp v dl pv pr ps hS ho hsp hep hgl hA
  by_cases hcase : Permit.DomainCase ia.initialChainId (ofNat m.ctx.block.chainId)
      (m.world.sload m.frame.msg.currentTarget 0#256)
  · exact permit_spec_case Act m o sp v dl pv pr ps hS ho hsp hep hgl hA hcase
  have hne : ofNat m.ctx.block.chainId ≠ ia.initialChainId := fun h => hcase (.inl h)
  have hgp : solmateGp ia m = 100000 + Str.getterGas
      (Str.slotLen (m.world.sload m.frame.msg.currentTarget 0#256)) := by
    simp [solmateGp, hne]
  let c : Call Address :=
    .permit o sp v.toNat (decide (m.ctx.block.timestamp % 2 ^ 256 ≤ dl.toNat)) (solmateRec ia m)
  have hP : ∀ out mf mf', mf'.world = mf.world → mf'.transient = mf.transient →
      mf'.createdAccounts = mf.createdAccounts → mf'.frame.sub.logs = mf.frame.sub.logs →
      Matches solmateAbs Act m mf (.success out) (M.events (pre solmateAbs Act m)
        m.frame.msg.caller c) (M.call (pre solmateAbs Act m) m.frame.msg.caller c) →
      Matches solmateAbs Act m mf' (.success out) (M.events (pre solmateAbs Act m)
        m.frame.msg.caller c) (M.call (pre solmateAbs Act m) m.frame.msg.caller c) :=
    fun out mf mf' hw ht hc hl h => matches_congr hw ht hc hl h
  rcases off_case (crypto := m.ctx.crypto) hcase with hnone | ⟨hodd, hL⟩
  · -- an inconsistent slot word: `permit` reverts, and so does the model
    have hds : solmateDs ia m = none := by simp [solmateDs, hne, hnone]
    have hrec : ∀ n, solmateRec ia m n = 0 := fun n => by
      unfold solmateRec; split
      · rfl
      · simp [hds]
    have hno : ¬ (decide (m.ctx.block.timestamp % 2 ^ 256 ≤ dl.toNat) = true ∧
        solmateRec ia m ((pre solmateAbs Act m).nonces o) = o ∧ o ≠ 0) := by
      rintro ⟨-, h1, h2⟩; rw [hrec] at h1; exact h2 h1.symm
    have hcall : M.call (pre solmateAbs Act m) m.frame.msg.caller c = .halt .revert := by
      simp only [c, M, solmateModel_call, call_permit, if_neg' hno]
    by_cases hN : Normal (solmateGp ia m) m
    · refine (pl_permit_panic m hS.fresh hN.2.2 (permitCall_of_args hA) hS.size hne hnone
        (by have := hN.1; omega) hS.precompiles).mono fun mf out _ h => .inl ?_
      show Matches solmateAbs Act m mf out _ (M.call (pre solmateAbs Act m) m.frame.msg.caller c)
      rw [hcall]; exact h
    · refine (fails_lift hS hep hP hgl fun m' hS' hmsg hw hctx hval hg hg' => ?_).mono
        fun mf o _ h => ?_
      · refine (pl_permit_panic m' hS'.fresh hval (permitCall_of_args (by rw [hmsg]; exact hA)) ?_ ?_ ?_ hg
          hS'.precompiles).mono fun _ o _ ⟨r, hr⟩ => by subst hr; trivial
        · rw [hmsg]; exact hS.size
        · rw [hctx]; exact hne
        · rw [hw, hctx, hmsg]; exact hnone
      · rcases h with h | ⟨out, rfl, h⟩
        · exact .inr ⟨h, hN⟩
        · exact .inl h
  · have hsl := slotLen_odd hodd
    have hgpv : solmateGp ia m = 100000 + Str.getterGas
        (Word.shr 1#256 (m.world.sload m.frame.msg.currentTarget 0#256)).toNat := by
      rw [hgp, hsl]
    clear hgp
    by_cases hsmall : ((Word.shr 1#256 (m.world.sload m.frame.msg.currentTarget 0#256)).toNat
        + 31) / 32 ≤ 2 ^ 65
    · -- a long name: exact from `gp`, lifted below it
      have hgp' := getterGas_lt hsmall
      by_cases hN : Normal (solmateGp ia m) m
      · exact (pl_permit_exact hS ho hsp hep (by omega) hA hN.2.2 hN.2.1 hne hodd hL
          (by have := hN.1; omega)).mono fun _ _ _ h => .inl h
      · let G := max m.frame.gasLeft (solmateGp ia m)
        have hG : m.frame.gasLeft ≤ G := Nat.le_max_left _ _
        have hG256 : G < 2 ^ 256 := by omega
        have hS' := hi_start hS hG
        have hgG := hi_gas (m := m) hG
        refine (low_ecrecover hS hep hG hG256 hP ?_).mono fun mf o _ h => ?_
        · by_cases hval : m.frame.msg.value = 0
          · by_cases hst : m.frame.msg.isStatic = false
            · have hgg : 100000 + Str.getterGas
                  (Word.shr 1#256 (m.world.sload m.frame.msg.currentTarget 0#256)).toNat ≤
                  (hi G m).frame.gasLeft := by rw [hgG]; omega
              exact (pl_permit_exact hS' ho hsp hep (by rw [hgG]; exact hG256) hA hval hst hne
                hodd hL hgg).mono fun mf o _ h out ho' => by subst ho'; exact h
            · exact (pl_permit_long_static (hi G m) hS'.fresh hval (by rw [hi_msg]; simpa using hst)
                (permitCall_of_args hA) hS.size hne hodd hL
                (show 100000 + Str.getterGas
                  (Word.shr 1#256 (m.world.sload m.frame.msg.currentTarget 0#256)).toNat ≤
                  (hi G m).frame.gasLeft by rw [hgG]; omega) (by rw [hgG]; exact hG256)
                hS'.precompiles).mono fun mf o _ h out ho' => absurd ho' (not_success_of_fails h out)
          · exact (value_reverts (hi G m) hS'.fresh hval (by rw [hgG]; omega)).mono
              fun mf o _ ⟨r, hr⟩ out ho' => by subst hr; cases ho'
        · rcases h with h | ⟨out, rfl, h⟩
          · exact .inr ⟨h, hN⟩
          · exact .inl h
    · -- a name longer than any frame's gas: every frame fails, and none is normal
      have hge := getterGas_ge (Word.shr 1#256 (m.world.sload m.frame.msg.currentTarget 0#256)).toNat
      have hN : ¬ Normal (solmateGp ia m) m := fun hN => by have := hN.1; omega
      refine (fails_lift hS hep hP hgl fun m' hS' hmsg hw hctx hval hg hg' => ?_).mono
        fun mf o _ h => ?_
      · refine pl_permit_huge m' hS'.fresh hval (permitCall_of_args (by rw [hmsg]; exact hA)) ?_ ?_ ?_ hg ?_
          hS'.precompiles
        · rw [hmsg]; exact hS.size
        · rw [hctx]; exact hne
        · rw [hw, hmsg]; exact hodd
        · rw [hw, hmsg]; dsimp only; omega
      · rcases h with h | ⟨out, rfl, h⟩
        · exact .inr ⟨h, hN⟩
        · exact .inl h

/-- **Solmate's `ERC20` with its `permit`**: `solmate_erc20Spec` and `solmate_permit`. -/
theorem solmate_erc20Spec_permit (ia : SolmateAsset.Immutables) :
    ERC20Spec (SolmateAsset.runtimeCodeWith ia) solmateAbs solmateModel g₀
      Verified.Solmate.ERC4626.assetSelectors
      solmateOps solmateOpAddrs ∧
    PermitSpec (SolmateAsset.runtimeCodeWith ia) solmateAbs solmateModel (solmateGp ia)
      (solmateRec ia) :=
  ⟨solmate_erc20Spec ia, solmate_permit ia⟩

end Verified.Solmate.ERC20.Spec
