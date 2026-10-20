module

public import Defi.ERC20.VariantProps

/-!
# USDT's deprecation forwarding

`TetherToken.deprecate(a)` (owner, irreversible) sets `deprecated` and `upgradedAddress = a`.
From then on `transfer(to, v)` runs USDT's own `whenNotPaused` and `!isBlackListed[msg.sender]`
checks and then calls `a.transferByLegacy(msg.sender, to, v)`; `transferFrom(from, to, v)`
checks `whenNotPaused`, `!isBlackListed[from]` and calls `a.transferFromByLegacy(msg.sender,
from, to, v)`; `approve(s, v)` calls `a.approveByLegacy(msg.sender, s, v)` with no checks;
`balanceOf`, `allowance`, `totalSupply` return `a`'s. Each forward is
`require(extcodesize(a) > 0)`, a `CALL` (value 0, gas `gas − 710`) and `require(success)`; the
legacy functions return nothing.

The model is a two-contract system `DState`: the legacy USDT storage, the switch, and the
upgraded token's storage (`none`: no code at `upgradedAddress`), the upgraded token being any
`Variant` `W` with the legacy entry points `Variant.byLegacy`. **`msg.sender` rewriting**: in
the forwarded call `msg.sender` is USDT, not the user; the user is an argument, so the
upgraded token can trust it only by checking `msg.sender = trusted` (its legacy contract).
`byLegacy` does; `byLegacyUnchecked` does not, and then anyone can spend anyone's tokens
(`byLegacyUnchecked_impersonation`).

Results (`DState.call W trusted`):
* not deprecated: exactly `usdt.call` (`call_of_not_deprecated`);
* deprecated, through `SafeTransferLib`: the legacy guards, then the upgraded token's ordinary
  entry point **called by the original user** (`safe_call_deprecated`); the legacy ledger is
  frozen (`call_legacy_eq`);
* no code at `upgradedAddress`, or an upgraded token that does not trust USDT: every
  transfer, `transferFrom` and `approve` reverts, and so do the forwarded views
  (`call_noCode`, `call_untrusted`, `balanceOf_noCode`);
* every failure of the upgraded token, `INVALID` included, surfaces as `REVERT`
  (`call_halt_revert`), and a `false` returned by it is **dropped**: USDT reports success with
  nothing moved and a `SafeTransferLib` caller proceeds (`call_masks_returnFalse`);
* `approve` is forwarded while paused or blacklisted (`approve_ignores_guards`);
* `destroyBlackFunds` after deprecation reads the forwarded balance but zeroes only the stale
  legacy balance: the live ledger is unchanged (`destroyBlackFunds_deprecated`);
* `deprecated` is never cleared (`deprecated_call`, `deprecated_setDeprecated`).

Not modelled: `upgradedAddress = USDT` (views recurse until out of gas), the forwarded gas
amount, the short-return quirk of the forwarded views (the calldata word is returned when the
callee returns less than 32 bytes).
-/

@[expose] public noncomputable section

namespace Defi.ERC20
open Defi.Math Finsupp

namespace Result

/-- Apply `f` to the state of a successful outcome. -/
def map {σ τ : Type} (f : σ → τ) : Result σ → Result τ
  | .ok s r => .ok (f s) r
  | .halt h => .halt h

theorem safe_map {σ τ : Type} (f : σ → τ) (r : Result σ) : (r.map f).safe = r.safe.map f := by
  rcases r with ⟨s, _ | ⟨_ | _⟩⟩ | h <;> rfl

end Result

namespace Variant

variable {A : Type} [DecidableEq A] [Zero A] (W : Variant A)

/-- `transferByLegacy(orig, to, v)`, `transferFromByLegacy(orig, from, to, v)`,
`approveByLegacy(orig, spender, v)` on the upgraded token, called with `msg.sender = sender`:
accepted only from the legacy contract `trusted`, and then the ordinary entry point as called
by `orig`. -/
def byLegacy (trusted : A) (s : VState A) (sender orig : A) (c : Call A) : Result (VState A) :=
  if sender = trusted then W.call s orig c else .halt .revert

/-- The legacy entry points without the `msg.sender` check. -/
def byLegacyUnchecked (s : VState A) (orig : A) (c : Call A) : Result (VState A) := W.call s orig c

/-- A token that never returns `false` never reports `false`. -/
theorem call_ok_ne_false {s s' : VState A} {c : A} {op : Call A} {r : RetData}
    (hg : W.guardFail ≠ .returnFalse) (ha : W.arithFail ≠ .returnFalse)
    (h : W.call s c op = .ok s' r) : r ≠ .word false := by
  unfold call at h
  cases hst : W.step s c op with
  | some s1 =>
    rw [hst] at h; cases h
    cases op <;> simp only [retData] <;> (try split_ifs) <;> simp
  | none =>
    rw [hst] at h
    exfalso
    have hk : W.failKind s c op = .returnFalse := by
      revert h; cases W.failKind s c op <;> intro h <;> first | rfl | cases h
    unfold failKind at hk
    split_ifs at hk
    · exact hg hk
    · exact ha hk

/-- Without its check the upgraded token cannot be trusted: anyone (`msg.sender` arbitrary)
calls `transferByLegacy(victim, attacker, v)` and moves the victim's tokens. -/
theorem byLegacyUnchecked_impersonation (s : VState A) (victim attacker : A) {v : ℕ}
    (hv : v ≤ s.bal victim) :
    ((standard : Variant A).byLegacyUnchecked s victim (.transfer attacker v)).safe =
      some { s with bal := s.bal - single victim v + single attacker v } := by
  rw [byLegacyUnchecked, safe_call]
  simp [step, standard_transfer, Token.transfer, VState.toToken, VState.withToken,
    Nat.not_lt.2 hv]

/-- With the check, a direct call by anyone but the legacy contract reverts. -/
theorem byLegacy_spoof (trusted : A) (s : VState A) {sender : A} (orig : A) (c : Call A)
    (h : sender ≠ trusted) : W.byLegacy trusted s sender orig c = .halt .revert := by
  simp [byLegacy, h]

end Variant

/-- USDT with its deprecation switch and the upgraded token. -/
structure DState (A : Type) where
  /-- The legacy `TetherToken` storage. -/
  legacy : VState A
  /-- `deprecated`. -/
  deprecated : Bool
  /-- `upgradedAddress`. -/
  upgradedAddress : A
  /-- The upgraded token's storage; `none` if there is no code at `upgradedAddress`. -/
  upgraded : Option (VState A)

namespace DState

variable {A : Type} [DecidableEq A] [Zero A] (W : Variant A) (trusted : A)

/-- USDT's own checks before forwarding: `whenNotPaused` and the blacklist (caller for
`transfer`, `from` for `transferFrom`); none for `approve`. Other selectors do not exist. -/
def legacyGuard (s : DState A) (caller : A) : Call A → Bool
  | .transfer _ _ => !s.legacy.paused && !s.legacy.blacklisted caller
  | .transferFrom src _ _ => !s.legacy.paused && !s.legacy.blacklisted src
  | .approve _ _ => true
  | _ => false

/-- A call of USDT by `caller`. Not deprecated: `usdt.call`. Deprecated: the legacy guards,
`extcodesize(upgradedAddress) > 0`, the legacy entry point of the upgraded token with
`msg.sender` = USDT, `require(success)`; no return data. -/
def call (s : DState A) (caller : A) (c : Call A) : Result (DState A) :=
  if !s.deprecated then ((Variant.usdt : Variant A).call s.legacy caller c).map fun l => { s with legacy := l }
  else if !legacyGuard s caller c then .halt .revert
  else
    match s.upgraded with
    | Option.none => .halt .revert
    | Option.some u =>
      match W.byLegacy trusted u s.legacy.self caller c with
      | .ok u' _ => .ok { s with upgraded := some u' } .empty
      | .halt _ => .halt .revert

/-- `balanceOf(a)`; after deprecation forwarded (`none`: the call reverts). -/
def balanceOf (s : DState A) (a : A) : Option ℕ :=
  if s.deprecated then s.upgraded.map fun u => W.balanceOf u a
  else some ((Variant.usdt : Variant A).balanceOf s.legacy a)

/-- `totalSupply()`; after deprecation forwarded. -/
def totalSupply (s : DState A) : Option ℕ :=
  if s.deprecated then s.upgraded.map W.totalSupply
  else some ((Variant.usdt : Variant A).totalSupply s.legacy)

/-- `deprecate(a)` by `caller` (owner only), with `up` the storage found at `a`. -/
def setDeprecated (s : DState A) (caller a : A) (up : Option (VState A)) : Option (DState A) :=
  if caller = s.legacy.admin then
    some { s with deprecated := true, upgradedAddress := a, upgraded := up }
  else none

/-- `x − y` on `uint256` without a check (0.4 `-=`). -/
def subWrap (x y : ℕ) : ℕ := (x + (U256 - y % U256)) % U256

/-- `destroyBlackFunds(u)` by `caller` (owner, `u` blacklisted): reads `balanceOf(u)` — the
forwarded one after deprecation — then zeroes the local `balances[u]` and lowers the local
`_totalSupply` by the value read, unchecked. -/
def destroyBlackFunds (s : DState A) (caller u : A) : Option (DState A) :=
  if caller = s.legacy.admin ∧ s.legacy.blacklisted u = true then
    (balanceOf W s u).map fun x =>
      { s with legacy := { s.legacy with bal := s.legacy.bal - single u (s.legacy.bal u),
                                          supply := subWrap s.legacy.supply x } }
  else none

/-! ## Before deprecation -/

theorem call_of_not_deprecated (s : DState A) (caller : A) (c : Call A)
    (h : s.deprecated = false) :
    call W trusted s caller c =
      ((Variant.usdt : Variant A).call s.legacy caller c).map fun l => { s with legacy := l } := by
  simp [call, h]

omit [Zero A] in
theorem subWrap_of_le {x y : ℕ} (h : y ≤ x) (hx : x < U256) : subWrap x y = x - y := by
  have hy : y < U256 := lt_of_le_of_lt h hx
  unfold subWrap
  rw [Nat.mod_eq_of_lt hy]
  have : x + (U256 - y) = (x - y) + U256 := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

omit [Zero A] in
/-- Before deprecation `destroyBlackFunds` is the `usdt` one (in a well-formed state). -/
theorem destroyBlackFunds_of_not_deprecated (s : DState A) (u : A) (h : s.deprecated = false)
    (hw : (Variant.usdt : Variant A).WF s.legacy) :
    destroyBlackFunds W s s.legacy.admin u =
      ((Variant.usdt : Variant A).destroyBlackFunds s.legacy s.legacy.admin u).map
        fun l => { s with legacy := l } := by
  unfold Variant.WF at hw
  simp only [Variant.usdt, Variant.standard, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hw
  have h1 := Token.le_total s.legacy.bal u
  have hS : s.legacy.supply < U256 := lt_of_le_of_lt hw.2 MAX_lt_U256
  by_cases hb : s.legacy.blacklisted u = true
  · simp [destroyBlackFunds, Variant.destroyBlackFunds, balanceOf, h, hb, Variant.usdt, Variant.standard,
      Variant.balanceOf, subWrap_of_le (show s.legacy.bal u ≤ s.legacy.supply by omega) hS]
  · simp [destroyBlackFunds, Variant.destroyBlackFunds, hb]

/-! ## After deprecation -/

/-- With no code at `upgradedAddress` every forwarded call reverts (the token is bricked). -/
theorem call_noCode (s : DState A) (caller : A) (c : Call A) (h : s.deprecated = true)
    (hu : s.upgraded = none) : call W trusted s caller c = .halt .revert := by
  simp only [call, h, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hu]
  split_ifs <;> rfl

omit [DecidableEq A] [Zero A] in
/-- … and so do the views. -/
theorem balanceOf_noCode (s : DState A) (a : A) (h : s.deprecated = true)
    (hu : s.upgraded = none) : balanceOf W s a = none := by
  simp [balanceOf, h, hu]

/-- An upgraded token that does not trust USDT as its legacy contract rejects every forward. -/
theorem call_untrusted (s : DState A) (caller : A) (c : Call A) (h : s.deprecated = true)
    (ht : s.legacy.self ≠ trusted) : call W trusted s caller c = .halt .revert := by
  simp only [call, h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  split_ifs
  · rfl
  · rcases s.upgraded with _ | u
    · rfl
    · simp [Variant.byLegacy, ht]

/-- **Every failure of the upgraded token surfaces as `REVERT`**, `INVALID` included (the
`gas − 710` forwarded to it are consumed in that case). -/
theorem call_halt_revert (s : DState A) (caller : A) (c : Call A) {u : VState A} {k : Halt}
    (h : s.deprecated = true) (hu : s.upgraded = some u)
    (hk : W.byLegacy trusted u s.legacy.self caller c = .halt k) :
    call W trusted s caller c = .halt .revert := by
  simp only [call, h, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hu, hk]
  split_ifs <;> rfl

/-- **A `false` from the upgraded token is dropped.** If it fails by returning `false`, USDT
reports success with empty return data and nothing changed, so a `SafeTransferLib` caller
proceeds as if the tokens had moved. -/
theorem call_masks_returnFalse (s : DState A) (caller : A) (c : Call A) {u : VState A}
    (h : s.deprecated = true) (hg : legacyGuard s caller c = true) (hu : s.upgraded = some u)
    (ht : s.legacy.self = trusted) (hf : W.call u caller c = .ok u (.word false)) :
    call W trusted s caller c = .ok s .empty ∧ (call W trusted s caller c).safe = some s := by
  have : call W trusted s caller c = .ok s .empty := by
    simp [call, h, hg, hu, Variant.byLegacy, ht, hf]
    cases s; simp_all
  exact ⟨this, by rw [this]; rfl⟩

/-- **Through `SafeTransferLib`, a deprecated USDT is its upgraded token called by the
original user**, behind USDT's own guards (when the upgraded token has code, trusts USDT and
never returns `false`). -/
theorem safe_call_deprecated (s : DState A) (caller : A) (c : Call A) {u : VState A}
    (h : s.deprecated = true) (hu : s.upgraded = some u) (ht : s.legacy.self = trusted)
    (hg : W.guardFail ≠ .returnFalse) (ha : W.arithFail ≠ .returnFalse) :
    (call W trusted s caller c).safe =
      if legacyGuard s caller c = true then
        (W.step u caller c).map fun u' => { s with upgraded := some u' }
      else none := by
  by_cases hl : legacyGuard s caller c = true
  · simp only [hl, ↓reduceIte]
    simp only [call, h, hl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hu, Variant.byLegacy, ht]
    rw [← W.safe_call u caller c]
    cases hc : W.call u caller c with
    | ok u' r =>
      have hr := Variant.call_ok_ne_false W hg ha hc
      rcases r with _ | ⟨_ | _⟩
      · rfl
      · exact absurd rfl hr
      · rfl
    | halt k => rfl
  · have hl' : legacyGuard s caller c = false := by simpa using hl
    simp [call, h, hl']
    rfl

/-- After deprecation the legacy ledger never changes through the ERC-20 entry points. -/
theorem call_legacy_eq {s s' : DState A} {caller : A} {c : Call A} {r : RetData}
    (h : s.deprecated = true) (hc : call W trusted s caller c = .ok s' r) : s'.legacy = s.legacy := by
  simp only [call, h, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
  split_ifs at hc
  rcases hu : s.upgraded with _ | u
  · rw [hu] at hc; cases hc
  · rw [hu] at hc
    simp only at hc
    split at hc
    · cases hc; rfl
    · cases hc

/-- `approve` is forwarded while USDT is paused and whatever the blacklist says. -/
theorem approve_ignores_guards (s : DState A) (caller sp : A) (v : ℕ) {u : VState A}
    (h : s.deprecated = true) (hu : s.upgraded = some u) :
    call W trusted s caller (.approve sp v) =
      match W.byLegacy trusted u s.legacy.self caller (.approve sp v) with
      | .ok u' _ => .ok { s with upgraded := some u' } .empty
      | .halt _ => .halt .revert := by
  simp [call, h, legacyGuard, hu]

/-- A transfer by a blacklisted caller (or while paused) still reverts after deprecation. -/
theorem transfer_guarded (s : DState A) (caller d : A) (v : ℕ) (h : s.deprecated = true)
    (hb : s.legacy.paused = true ∨ s.legacy.blacklisted caller = true) :
    call W trusted s caller (.transfer d v) = .halt .revert := by
  have : legacyGuard s caller (.transfer d v) = false := by
    rcases hb with hb | hb <;> simp [legacyGuard, hb]
  simp [call, h, this]

omit [DecidableEq A] [Zero A] in
theorem balanceOf_deprecated (s : DState A) (a : A) {u : VState A} (h : s.deprecated = true)
    (hu : s.upgraded = some u) : balanceOf W s a = some (W.balanceOf u a) := by
  simp [balanceOf, h, hu]

omit [Zero A] in
/-- **`destroyBlackFunds` after deprecation destroys nothing live.** It zeroes the stale legacy
balance and lowers the stale legacy `_totalSupply` by the upgraded balance (unchecked), while
the upgraded ledger — which every view now reads — is unchanged. -/
theorem destroyBlackFunds_deprecated {s s' : DState A} {c u : A} (h : s.deprecated = true)
    (hd : destroyBlackFunds W s c u = some s') :
    s'.upgraded = s.upgraded ∧ s'.deprecated = true ∧ s'.legacy.bal u = 0 ∧
      (∀ a, balanceOf W s' a = balanceOf W s a) ∧ totalSupply W s' = totalSupply W s := by
  unfold destroyBlackFunds at hd
  split_ifs at hd
  obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.1 hd
  refine ⟨rfl, h, by simp, fun a => ?_, ?_⟩
  · simp [balanceOf, h]
  · simp [totalSupply, h]

theorem deprecated_call {s s' : DState A} {caller : A} {c : Call A} {r : RetData}
    (h : s.deprecated = true) (hc : call W trusted s caller c = .ok s' r) : s'.deprecated = true := by
  simp only [call, h, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
  split_ifs at hc
  rcases hu : s.upgraded with _ | u
  · rw [hu] at hc; cases hc
  · rw [hu] at hc
    simp only at hc
    split at hc
    · cases hc; rfl
    · cases hc

omit [Zero A] in
theorem deprecated_setDeprecated {s s' : DState A} {c a : A} {up : Option (VState A)}
    (hd : setDeprecated s c a up = some s') : s'.deprecated = true := by
  unfold setDeprecated at hd
  split_ifs at hd
  cases hd; rfl

end DState

end Defi.ERC20
