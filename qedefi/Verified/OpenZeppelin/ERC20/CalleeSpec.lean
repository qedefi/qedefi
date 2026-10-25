import Verified.OpenZeppelin.ERC20.CalleeTransfer
import Verified.OpenZeppelin.ERC20.CalleeApprove
import Verified.OpenZeppelin.ERC20.CalleeTransferFrom
import Verified.OpenZeppelin.ERC20.CalleeMintBurn
import QEDefi.ERC20.RepOz

/-!
# `OzAsset`'s functions refine `Token.oz*`, in any frame

The callee summaries stated against the `ℕ` ledger (`QEDefi.ERC20.Rep`/`RepOn`): when the
token's storage represents a well-formed ledger `t`, `transfer`, `approve`, `transferFrom`,
`mint` and `burn` succeed (with the event) exactly when `Token.ozTransfer` etc. return
`some t'`, the new storage then represents `t'` (allowances in unwritten slots), and otherwise
they revert; `balanceOf` returns the represented balance. Hypotheses: `BalanceSlotOk`,
`AllowanceSlotOk`, `SupplySlotOk` for the written entries, `Token.WF` (the unchecked additions
do not wrap).
-/

namespace Verified.OpenZeppelin.ERC20
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Solidity.ERC20
open EvmLean.Interpreter QEDefi.ERC20 QEDefi.Math Verified.OpenZeppelin.Contracts
open Verified.Solmate.ERC20 (TwoWordCall ThreeWordCall Reverts)

/-- **`balanceOf(a)`** returns the represented balance, in any frame. -/
theorem assetBalanceOf_refines (m : Machine) (hf : Fresh OzAsset.runtimeCode m) (a : Address)
    (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x70a08231)
    (hsize : 36 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (harg : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress a)
    (hg : 3000 ≤ m.frame.gasLeft) {P : Address → Address → Prop} {t : Token Address}
    (hr : RepOn P (assetView m) t) :
    Halts m (fun mf o => o = .success (Bytes.ofWord (BitVec.ofNat 256 (t.balanceOf a))) ∧
      mf.world = m.world) :=
  (balanceOf_halts m hf a hval hsel hsize hsize' harg hg).mono fun _ _ _ ⟨ho, hw, _⟩ =>
    ⟨by rw [ho, ← hr.balanceOf a, ofNat_toNat_word]; rfl, hw⟩

/-- **`transfer(dst, amount)` refines `Token.ozTransfer`**, in any non-static frame. -/
theorem assetTransfer_refines (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {dst : Address}
    {amount : Word} (hd : TwoWordCall m.frame.msg.data 0xa9059cbb (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    (hs : BalanceSlotOk m.ctx.crypto Layout.oz m.frame.msg.caller)
    (hdst : BalanceSlotOk m.ctx.crypto Layout.oz dst)
    {t : Token Address} (hr : Rep (assetView m) t) (hw : t.WF) :
    match t.ozTransfer m.frame.msg.caller dst amount.toNat with
    | some t' => Halts m (fun mf o => TransferOk dst amount m mf o ∧
        RepOn (fun o sp => allowanceSlot m.ctx.crypto Layout.oz o sp ≠
            balanceSlot m.ctx.crypto Layout.oz m.frame.msg.caller ∧
          allowanceSlot m.ctx.crypto Layout.oz o sp ≠ balanceSlot m.ctx.crypto Layout.oz dst)
          (view m.ctx.crypto Layout.oz mf.world m.frame.msg.currentTarget) t')
    | none => Halts m (Reverts 10000 m) := by
  have hiff := ozTransfer_isSome_iff hr m.frame.msg.caller dst amount
  split
  · rename_i t' hT
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1 (hiff.2 (by simp [hT]))
    have hrep := rep_ozTransfer hr hw hm hT
    unfold Model.ozTransfer at hm
    split at hm
    · cases hm
    rename_i hc0
    split at hm
    · cases hm
    rename_i hd0
    have hbal : amount.toNat ≤ ((assetView m).balanceOf m.frame.msg.caller).toNat := by
      unfold Model.transfer at hm
      split at hm
      · assumption
      · cases hm
    obtain ⟨h1, h2, h3, -⟩ := view_moveWorld (token := m.frame.msg.currentTarget) hs hdst hm
    refine (transfer_halts_ok m hf hval hstatic hd hsz hg hc0 hd0 hbal).mono
      fun mf o _ hok => ⟨hok, ?_⟩
    rw [hok.2.1]
    exact RepOn.of_eq h1 h2 (fun o sp hp => h3 o sp hp.1 hp.2) hrep
  · rename_i hT
    refine transfer_halts_revert m hf hval hd hsz (by omega) ?_
    simpa [hT] using hiff

/-- **`approve(spender, amount)` refines `Token.ozApprove`**, in any non-static frame. -/
theorem assetApprove_refines (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {spender : Address}
    {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x095ea7b3 (Word.ofAddress spender) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 40000 ≤ m.frame.gasLeft)
    (ha : AllowanceSlotOk m.ctx.crypto Layout.oz m.frame.msg.caller spender)
    {t : Token Address} (hr : Rep (assetView m) t) :
    match t.ozApprove m.frame.msg.caller spender amount.toNat with
    | some t' => Halts m (fun mf o => ApproveOk spender amount m mf o ∧
        RepOn (fun o sp => (o = m.frame.msg.caller ∧ sp = spender) ∨
            allowanceSlot m.ctx.crypto Layout.oz o sp ≠
              allowanceSlot m.ctx.crypto Layout.oz m.frame.msg.caller spender)
          (view m.ctx.crypto Layout.oz mf.world m.frame.msg.currentTarget) t')
    | none => Halts m (Reverts 10000 m) := by
  have hiff := ozApprove_isSome_iff (s := assetView m) (t := t) m.frame.msg.caller spender
    amount amount.toNat
  split
  · rename_i t' hT
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1 (hiff.2 (by simp [hT]))
    have hrep := rep_ozApprove hr rfl hm hT
    unfold Model.ozApprove at hm
    split at hm
    · cases hm
    rename_i hc0
    split at hm
    · cases hm
    rename_i hs0
    cases hm
    obtain ⟨h1, h2, h3, -⟩ := view_allowanceWorld (w := m.world)
      (token := m.frame.msg.currentTarget) (amount := amount) ha
    refine (approve_halts_ok m hf hval hstatic hd hsz hg hc0 hs0).mono
      fun mf o _ hok => ⟨hok, ?_⟩
    rw [hok.2.1]
    exact RepOn.of_eq h1 h2 h3 hrep
  · rename_i hT
    refine approve_halts_revert m hf hval hd hsz (by omega) ?_
    simpa [hT] using hiff

/-- With `AllowanceSlotOk`, the storage condition `TransferFromCond` is the success of
`Model.ozTransferFrom`. -/
theorem transferFromCond_iff (m : Machine) (src dst : Address) (amount : Word)
    (ha : AllowanceSlotOk m.ctx.crypto Layout.oz src m.frame.msg.caller) :
    TransferFromCond m src dst amount ↔
      (Model.ozTransferFrom (assetView m) m.frame.msg.caller src dst amount).isSome := by
  have hb : (ozSpendWorld m.ctx.crypto Layout.oz m.world m.frame.msg.currentTarget src
      m.frame.msg.caller amount).sload m.frame.msg.currentTarget
        (balanceSlot m.ctx.crypto Layout.oz src) =
      m.world.sload m.frame.msg.currentTarget (balanceSlot m.ctx.crypto Layout.oz src) := by
    simp only [ozSpendWorld]
    split
    · rfl
    · rw [allowanceWorld, World.sload_sstore_ne_key _ _ _ (balanceSlot_ne_allowanceSlot ha src)]
  unfold TransferFromCond
  rw [hb, show m.world.sload m.frame.msg.currentTarget
      (allowanceSlot m.ctx.crypto Layout.oz src m.frame.msg.caller) =
        (assetView m).allowance src m.frame.msg.caller from rfl,
    show m.world.sload m.frame.msg.currentTarget (balanceSlot m.ctx.crypto Layout.oz src) =
      (assetView m).balanceOf src from rfl]
  generalize assetView m = s
  unfold Model.ozTransferFrom Model.ozSpend
  by_cases hmax : s.allowance src m.frame.msg.caller = maxWord
  · simp only [hmax, true_or, true_and, ↓reduceIte, Option.bind_some]
    unfold Model.ozTransfer Model.transfer
    by_cases hs : src = 0 <;> by_cases hd : dst = 0 <;>
      simp only [hs, hd, ↓reduceIte, Option.isSome_none, ne_eq, not_true_eq_false,
        not_false_eq_true, false_and, and_false, true_and] <;> simp
  · simp only [hmax, false_or, ↓reduceIte]
    by_cases hle : amount.toNat ≤ (s.allowance src m.frame.msg.caller).toNat
    · unfold Model.ozApprove Model.ozTransfer Model.transfer
      by_cases hs : src = 0 <;> by_cases hc : m.frame.msg.caller = 0 <;>
        by_cases hd : dst = 0 <;>
        simp only [hs, hd, hc, hle, ↓reduceIte, Option.bind_some,
          Option.isSome_none, ne_eq, not_true_eq_false, not_false_eq_true, false_and, and_false,
          true_and, Model.approve, State.setAllowance] <;> simp
    · simp [hle]

/-- **`transferFrom(src, dst, amount)` refines `Token.ozTransferFrom`** (the caller is the
spender), in any non-static frame. -/
theorem assetTransferFrom_refines (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {src dst : Address}
    {amount : Word}
    (hd : ThreeWordCall m.frame.msg.data 0x23b872dd (Word.ofAddress src) (Word.ofAddress dst)
      amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 90000 ≤ m.frame.gasLeft)
    (hs : BalanceSlotOk m.ctx.crypto Layout.oz src)
    (hdst : BalanceSlotOk m.ctx.crypto Layout.oz dst)
    (ha : AllowanceSlotOk m.ctx.crypto Layout.oz src m.frame.msg.caller)
    {t : Token Address} (hr : Rep (assetView m) t) (hw : t.WF) :
    match t.ozTransferFrom m.frame.msg.caller src dst amount.toNat with
    | some t' => Halts m (fun mf o => TransferFromOk src dst amount m mf o ∧
        RepOn (fun o sp => allowanceSlot m.ctx.crypto Layout.oz o sp ≠
            balanceSlot m.ctx.crypto Layout.oz src ∧
          allowanceSlot m.ctx.crypto Layout.oz o sp ≠ balanceSlot m.ctx.crypto Layout.oz dst ∧
          ((o = src ∧ sp = m.frame.msg.caller) ∨
            allowanceSlot m.ctx.crypto Layout.oz o sp ≠
              allowanceSlot m.ctx.crypto Layout.oz src m.frame.msg.caller))
          (view m.ctx.crypto Layout.oz mf.world m.frame.msg.currentTarget) t')
    | none => Halts m (Reverts 80000 m) := by
  have hiff := ozTransferFrom_isSome_iff hr m.frame.msg.caller src dst amount
  have hc := transferFromCond_iff m src dst amount ha
  split
  · rename_i t' hT
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1 (hiff.2 (by simp [hT]))
    have hrep := rep_ozTransferFrom hr hw hm hT
    obtain ⟨h1, h2, h3, -⟩ := view_ozTransferFromWorld (token := m.frame.msg.currentTarget)
      hs hdst ha hm
    refine (transferFrom_halts_ok m hf hval hstatic hd hsz hg (hc.2 (by simp [hm]))).mono
      fun mf o _ hok => ⟨hok, ?_⟩
    rw [hok.2.1]
    exact RepOn.of_eq h1 h2 (fun o sp hp => h3 o sp hp.1 hp.2.1 hp.2.2) hrep
  · rename_i hT
    refine transferFrom_halts_revert m hf hval hstatic hd hsz hg fun h => ?_
    have := hiff.1 (hc.1 h)
    simp [hT] at this

/-- **`mint(dst, amount)` refines `Token.ozMint`** (any caller), in any non-static frame. -/
theorem assetMint_refines (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {dst : Address}
    {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x40c10f19 (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    (hdst : BalanceSlotOk m.ctx.crypto Layout.oz dst) (hk : SupplySlotOk m.ctx.crypto Layout.oz)
    {t : Token Address} (hr : Rep (assetView m) t) (hw : t.WF) :
    match t.ozMint dst amount.toNat with
    | some t' => Halts m (fun mf o => MintOk dst amount m mf o ∧
        RepOn (fun o sp => allowanceSlot m.ctx.crypto Layout.oz o sp ≠ Layout.oz.totalSupply ∧
          allowanceSlot m.ctx.crypto Layout.oz o sp ≠ balanceSlot m.ctx.crypto Layout.oz dst)
          (view m.ctx.crypto Layout.oz mf.world m.frame.msg.currentTarget) t')
    | none => Halts m (Reverts 10000 m) := by
  have hiff := ozMint_isSome_iff hr dst amount
  split
  · rename_i t' hT
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1 (hiff.2 (by simp [hT]))
    have hrep := rep_ozMint hr hw hm hT
    obtain ⟨h1, h2, h3, -⟩ := view_mintWorld (token := m.frame.msg.currentTarget) hdst hk hm
    unfold Model.ozMint at hm
    split at hm
    · cases hm
    rename_i hd0
    split at hm
    · rename_i hov
      refine (mint_halts_ok m hf hval hstatic hd hsz hg hd0 hov).mono
        fun mf o _ hok => ⟨hok, ?_⟩
      rw [hok.2.1]
      exact RepOn.of_eq h1 h2 (fun o sp hp => h3 o sp hp.1 hp.2) hrep
    · cases hm
  · rename_i hT
    refine mint_halts_revert m hf hval hd hsz (by omega) ?_
    simpa [hT] using hiff

/-- **`burn(src, amount)` refines `Token.ozBurn`** (any caller), in any non-static frame. -/
theorem assetBurn_refines (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {src : Address}
    {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x9dc29fac (Word.ofAddress src) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    (hs : BalanceSlotOk m.ctx.crypto Layout.oz src) (hk : SupplySlotOk m.ctx.crypto Layout.oz)
    {t : Token Address} (hr : Rep (assetView m) t) (hw : t.WF) :
    match t.ozBurn src amount.toNat with
    | some t' => Halts m (fun mf o => BurnOk src amount m mf o ∧
        RepOn (fun o sp => allowanceSlot m.ctx.crypto Layout.oz o sp ≠ Layout.oz.totalSupply ∧
          allowanceSlot m.ctx.crypto Layout.oz o sp ≠ balanceSlot m.ctx.crypto Layout.oz src)
          (view m.ctx.crypto Layout.oz mf.world m.frame.msg.currentTarget) t')
    | none => Halts m (Reverts 10000 m) := by
  have hiff := ozBurn_isSome_iff hr src amount
  split
  · rename_i t' hT
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1 (hiff.2 (by simp [hT]))
    have hrep := rep_ozBurn hr hw hm hT
    obtain ⟨h1, h2, h3, -⟩ := view_burnWorld (token := m.frame.msg.currentTarget) hs hk hm
    unfold Model.ozBurn at hm
    split at hm
    · cases hm
    rename_i hs0
    split at hm
    · rename_i hv
      refine (burn_halts_ok m hf hval hstatic hd hsz hg hs0 hv).mono
        fun mf o _ hok => ⟨hok, ?_⟩
      rw [hok.2.1]
      exact RepOn.of_eq h1 h2 (fun o sp hp => h3 o sp hp.1 hp.2) hrep
    · cases hm
  · rename_i hT
    refine burn_halts_revert m hf hval hd hsz (by omega) ?_
    simpa [hT] using hiff

end Verified.OpenZeppelin.ERC20
