module

public import Defi.ERC20.Token

/-!
# ERC-20 variants

One parameterised token model for the deviations recorded in `docs/tokens.md`. A `Variant A`
is a record of policies (data, not code): the return-data convention per entry point, how a
failing check ends the call (`REVERT`, `INVALID`, or returning `false`), zero-address and
zero-value checks, the USDT approve race guard, how infinite allowances are treated, a
transfer fee (USDT's capped basis points paid to the owner, STA's burned `⌈v/100⌉`), pause and
blacklist (USDT), rebasing balances stored as gons with a global scale (AMPL), owner-only or
holder-only mint/burn, the fallback (BNB accepts every unknown selector, WETH9 deposits), and
whether `totalSupply` is stored or the contract's ether balance (WETH9).

The storage `VState A` holds every field any variant uses; a variant ignores the fields its
policies do not mention. Each operation returns `Option (VState A)` (`none`: the call fails);
`call` adds the observable convention (return data, failure kind) and `Result.safe`,
`Result.decoded`, `Result.unchecked` are the three ways a calling contract consumes it.

`standard` is Solmate's `ERC20` as modelled by `Token` (`standard_transfer` … prove its
operations are the `Token` operations), `oz` OpenZeppelin v5's (`oz_transfer` …: the `Token.oz*`
operations). The other instances are WETH9, Solady (Permit2), USDT, BNB, STA and AMPL.

Not modelled: events, gas, ABI decoding and short-payload checks, USDT's deprecation
forwarding, BNB's `freeze`/`unfreeze` ledger and `withdrawEther`, STA's `upAllowance`/
`downAllowance`/`destroyFrom`, `permit`, and the arithmetic overflow of fee computations
(USDT `v·bps` for `v > MAX/20`, STA `v + 100` for `v > MAX − 100`).
-/

@[expose] public noncomputable section

namespace Defi.ERC20
open Defi.Math Finsupp

/-- The entry points whose return data differs between tokens. -/
inductive Fn
  /-- `transfer(to, v)`. -/
  | transfer
  /-- `transferFrom(from, to, v)`. -/
  | transferFrom
  /-- `approve(spender, v)`. -/
  | approve
  deriving DecidableEq

/-- What a successful call of a state-changing entry point returns. -/
inductive Returns
  /-- The ABI-encoded `true`. -/
  | bool
  /-- No return data (pre-0.4.22 interfaces without `returns (bool)`: USDT, BNB `transfer`). -/
  | empty
  deriving DecidableEq

/-- How a failing check ends the call. -/
inductive OnFail
  /-- `REVERT` (`require`, custom errors, checked arithmetic `Panic`, 0.4 `throw`). -/
  | revert
  /-- The `INVALID` opcode (0.4.x SafeMath `assert`): all gas consumed, then failure. -/
  | invalid
  /-- Success with return data `false` and no effect. -/
  | returnFalse
  deriving DecidableEq

/-- Zero-address checks. -/
structure ZeroChecks where
  /-- Transfers and burns from `0` fail. -/
  sender : Bool
  /-- Transfers and mints to `0` fail. -/
  receiver : Bool
  /-- `approve` by `0` fails. -/
  owner : Bool
  /-- `approve` of `0` fails. -/
  spender : Bool
  deriving DecidableEq

/-- How an allowance of `MAX` is treated when spent. -/
inductive Infinite
  /-- Always decremented (BNB, STA, AMPL). -/
  | none
  /-- Not decremented when equal to `MAX` (Solmate, Solady, WETH9). -/
  | eqMax
  /-- Not decremented when at least `MAX` (OpenZeppelin `< MAX` test, USDT `< MAX_UINT`). -/
  | geMax
  deriving DecidableEq

/-- Whether an allowance counts as infinite. -/
def Infinite.test : Infinite → ℕ → Bool
  | .none, _ => false
  | .eqMax, a => decide (a = MAX)
  | .geMax, a => decide (MAX ≤ a)

/-- The transfer fee as a function of the transferred value. -/
inductive FeeRule
  /-- No fee. -/
  | none
  /-- USDT: `min(v · basisPointsRate / 10000, maximumFee)` with the state's parameters. -/
  | bpsCapped
  /-- STA: `cut(v) = ceil(v, bp) · bp / 10000` with `ceil(v, m) = ⌊(v + m − 1)/m⌋·m`. -/
  | ceilPercent (basePercent : ℕ)
  deriving DecidableEq

/-- Where the fee goes. -/
inductive FeeSink
  /-- Credited to the privileged account (USDT `owner`). -/
  | owner
  /-- Burned: removed from the balances and from `totalSupply` (STA). -/
  | burn
  deriving DecidableEq

/-- Who may call a mint or burn entry point, for which account. -/
inductive Auth
  /-- Anyone, for any account (the test mocks `mint(to, v)`/`burn(from, v)`). -/
  | anyone
  /-- Only the privileged account, for itself (USDT `issue`/`redeem`). -/
  | owner
  /-- Only the holder, for itself (BNB `burn`, STA `destroy`). -/
  | holder
  /-- No such entry point. -/
  | nobody
  deriving DecidableEq

/-- Whether `caller` may mint to / burn from `acct` when the privileged account is `admin`. -/
def Auth.allows {A : Type} [DecidableEq A] : Auth → A → A → A → Bool
  | .anyone, _, _, _ => true
  | .owner, admin, caller, acct => decide (caller = admin) && decide (acct = admin)
  | .holder, _, caller, acct => decide (caller = acct)
  | .nobody, _, _, _ => false

/-- What a call with an unknown selector does. -/
inductive Fallback
  /-- It reverts (no fallback function). -/
  | revert
  /-- It succeeds with empty return data and keeps any ether (BNB's payable fallback). -/
  | accept
  /-- It deposits the ether sent (WETH9). -/
  | deposit
  deriving DecidableEq

/-- What `totalSupply()` returns. -/
inductive SupplyKind
  /-- A storage variable. -/
  | stored
  /-- The token contract's ether balance (WETH9). -/
  | ether
  deriving DecidableEq

/-- An ERC-20 implementation, as a record of policies. -/
structure Variant (A : Type) where
  /-- Return data of a successful `transfer`/`transferFrom`/`approve`. -/
  returns : Fn → Returns
  /-- How a failing guard (pause, blacklist, address/value checks, approve guard) ends. -/
  guardFail : OnFail
  /-- How an insufficient balance or allowance (or a fee above the value) ends. -/
  arithFail : OnFail
  /-- Zero-address checks. -/
  zero : ZeroChecks
  /-- The allowance decrease goes through `_approve` with its owner/spender checks (OZ). -/
  spendViaApprove : Bool
  /-- Transfers to the token's own address fail (AMPL `validRecipient`). -/
  rejectsSelf : Bool
  /-- Zero-value transfers and approvals fail (BNB). -/
  zeroValueReverts : Bool
  /-- `approve(s, v)` fails if `v ≠ 0` and the current allowance is not `0` (USDT). -/
  approveGuard : Bool
  /-- Treatment of `MAX` allowances. -/
  infinite : Infinite
  /-- `transferFrom(src, …)` by `src` itself skips the allowance (WETH9). -/
  selfSpendFree : Bool
  /-- A spender with a fixed infinite allowance that `approve` cannot change (Solady Permit2). -/
  permit2 : Option A
  /-- The transfer fee. -/
  fee : FeeRule
  /-- Where the fee goes. -/
  feeSink : FeeSink
  /-- `10^decimals`: the unit `setParams` scales the maximum fee by (USDT). -/
  feeUnit : ℕ
  /-- Transfers fail while the state's `paused` flag is set (USDT). -/
  pausable : Bool
  /-- Transfers from blacklisted accounts fail; `destroyBlackFunds` exists (USDT). -/
  blacklist : Bool
  /-- Balances are stored in internal units (gons) at `scale` per token (AMPL). -/
  rebasing : Bool
  /-- `TOTAL_GONS`, the constant sum of all gon balances (rebasing). -/
  totalGons : ℕ
  /-- The largest supply a rebase can set (rebasing). -/
  maxSupply : ℕ
  /-- Who may mint. -/
  mintAuth : Auth
  /-- Who may burn. -/
  burnAuth : Auth
  /-- Minting `0` fails (USDT `issue`). -/
  zeroMintReverts : Bool
  /-- Burning `0` fails (BNB `burn`, STA `destroy`). -/
  zeroBurnReverts : Bool
  /-- Unknown selectors. -/
  fallback : Fallback
  /-- What `totalSupply()` returns. -/
  supply : SupplyKind

/-- The storage of any of the variants. -/
structure VState (A : Type) where
  /-- The token's own address. -/
  self : A
  /-- Balances in internal units: gons for a rebasing token, `balanceOf` otherwise. -/
  bal : A →₀ ℕ
  /-- The `totalSupply` storage variable (unused when the supply is the ether balance). -/
  supply : ℕ
  /-- `allowance[owner][spender]`. -/
  allowance : A → A → ℕ
  /-- Internal units per token (`_gonsPerFragment`; rebasing only). -/
  scale : ℕ
  /-- The privileged account: USDT `owner` (fee sink), AMPL `monetaryPolicy`. -/
  admin : A
  /-- USDT `paused`. -/
  paused : Bool
  /-- USDT `isBlackListed`. -/
  blacklisted : A → Bool
  /-- USDT `basisPointsRate`. -/
  feeBps : ℕ
  /-- USDT `maximumFee`. -/
  feeMax : ℕ
  /-- The token contract's ether balance. -/
  ether : ℕ

namespace VState

variable {A : Type} [DecidableEq A]

/-- The `Token` part of the storage. -/
def toToken (s : VState A) : Token A := ⟨s.bal, s.supply, s.allowance⟩

/-- Replace the `Token` part of the storage. -/
def withToken (s : VState A) (t : Token A) : VState A :=
  { s with bal := t.balanceOf, supply := t.totalSupply, allowance := t.allowance }

/-- A `Token` as a variant state: unit scale, nothing paused or blacklisted, no fee, no ether. -/
def ofToken (t : Token A) (self admin : A) : VState A where
  self := self
  bal := t.balanceOf
  supply := t.totalSupply
  allowance := t.allowance
  scale := 1
  admin := admin
  paused := false
  blacklisted := fun _ => false
  feeBps := 0
  feeMax := 0
  ether := 0

/-- `allowance[owner][spender] = v`. -/
def setAllowance (s : VState A) (owner spender : A) (v : ℕ) : VState A :=
  { s with
    allowance := Function.update s.allowance owner (Function.update (s.allowance owner) spender v) }

@[simp] theorem toToken_withToken (s : VState A) (t : Token A) : (s.withToken t).toToken = t := rfl

@[simp] theorem withToken_withToken (s : VState A) (t u : Token A) :
    (s.withToken t).withToken u = s.withToken u := rfl

@[simp] theorem withToken_toToken (s : VState A) : s.withToken s.toToken = s := rfl

theorem toToken_ofToken (t : Token A) (self admin : A) : (ofToken t self admin).toToken = t := rfl

theorem withToken_setAllowance (s : VState A) (o sp : A) (v : ℕ) :
    s.withToken (s.toToken.setAllowance o sp v) = s.setAllowance o sp v := rfl

end VState

/-- A call of an ERC-20 entry point (without the caller). -/
inductive Call (A : Type) where
  /-- `transfer(dst, v)`. -/
  | transfer (dst : A) (v : ℕ)
  /-- `transferFrom(src, dst, v)`. -/
  | transferFrom (src dst : A) (v : ℕ)
  /-- `approve(spender, v)`. -/
  | approve (spender : A) (v : ℕ)
  /-- A selector the token does not implement (e.g. `permit` on BNB), with `value` wei. -/
  | other (value : ℕ)

/-- Why a call stopped without success. -/
inductive Halt
  /-- `REVERT`. -/
  | revert
  /-- `INVALID`: all gas forwarded to the call is consumed. -/
  | invalid
  deriving DecidableEq

/-- Return data of a successful call. -/
inductive RetData
  /-- Empty. -/
  | empty
  /-- One ABI-encoded `bool` word. -/
  | word (b : Bool)
  deriving DecidableEq

/-- The observable outcome of a call. -/
inductive Result (σ : Type) where
  /-- Success, with the new state and the return data. -/
  | ok (s : σ) (ret : RetData)
  /-- Failure; the state is unchanged. -/
  | halt (h : Halt)

namespace Result

variable {σ : Type}

/-- Solmate `SafeTransferLib` / OpenZeppelin `SafeERC20`: the call must succeed and return
nothing or `true`. -/
def safe : Result σ → Option σ
  | .ok s .empty => some s
  | .ok s (.word true) => some s
  | _ => none

/-- `require(IERC20(t).transfer(…))` through a `returns (bool)` interface: solc's ABI decoder
needs a return word (empty return data reverts), and it must be `true`. -/
def decoded : Result σ → Option σ
  | .ok s (.word true) => some s
  | _ => none

/-- A low-level call whose return data is ignored: only a halt is noticed. -/
def unchecked : Result σ → Option σ
  | .ok s _ => some s
  | .halt _ => none

end Result

namespace Variant

variable {A : Type} [DecidableEq A] [Zero A] (V : Variant A)

/-! ## Views -/

/-- `balanceOf(a)`: `gons / scale` for a rebasing token. -/
def balanceOf (s : VState A) (a : A) : ℕ := if V.rebasing then s.bal a / s.scale else s.bal a

/-- `totalSupply()`. -/
def totalSupply (s : VState A) : ℕ :=
  match V.supply with
  | .stored => s.supply
  | .ether => s.ether

/-- `allowance(owner, spender)`: Permit2's is fixed at `MAX` (Solady). -/
def allowanceOf (s : VState A) (o sp : A) : ℕ :=
  if V.permit2 = some sp then MAX else s.allowance o sp

/-- Internal units for `v` tokens. -/
def units (s : VState A) (v : ℕ) : ℕ := if V.rebasing then v * s.scale else v

/-- The fee on a transfer of `v`. -/
def feeOf (s : VState A) (v : ℕ) : ℕ :=
  match V.fee with
  | .none => 0
  | .bpsCapped => min (v * s.feeBps / 10000) s.feeMax
  | .ceilPercent bp => (v + bp - 1) / bp * bp * bp / 10000

/-! ## Transfers and allowances -/

/-- The guards of a transfer from `src` to `dst`: pause, blacklist, zero address, the token
itself as recipient, zero value. -/
def moveOk (s : VState A) (src dst : A) (v : ℕ) : Bool :=
  !(V.pausable && s.paused) && !(V.blacklist && s.blacklisted src) &&
  !(V.zero.sender && decide (src = 0)) && !(V.zero.receiver && decide (dst = 0)) &&
  !(V.rejectsSelf && decide (dst = s.self)) && !(V.zeroValueReverts && decide (v = 0))

/-- The state after a transfer of `v` from `src` to `dst`: debit `v`, credit `v`, then move
the fee from `dst` to its sink (USDT: `bal[from] −= v; bal[to] += v − fee; bal[owner] += fee`). -/
def credit (s : VState A) (src dst : A) (v : ℕ) : VState A :=
  if V.feeOf s v = 0 then
    { s with bal := s.bal - single src (V.units s v) + single dst (V.units s v) }
  else
    match V.feeSink with
    | .owner =>
      { s with bal := s.bal - single src (V.units s v) + single dst (V.units s v) -
                        single dst (V.units s (V.feeOf s v)) + single s.admin (V.units s (V.feeOf s v)) }
    | .burn =>
      { s with bal := s.bal - single src (V.units s v) + single dst (V.units s v) -
                        single dst (V.units s (V.feeOf s v)),
               supply := s.supply - V.feeOf s v }

/-- The balance update of a transfer: fails on an insufficient balance or a fee above `v`. -/
def move (s : VState A) (src dst : A) (v : ℕ) : Option (VState A) :=
  if s.bal src < V.units s v then none
  else if v < V.feeOf s v then none
  else some (V.credit s src dst v)

/-- The allowance step of `transferFrom(owner, …)` by `spender`. -/
def spend (s : VState A) (owner spender : A) (v : ℕ) : Option (VState A) :=
  if V.selfSpendFree && decide (owner = spender) then some s
  else if V.permit2 = some spender then some s
  else if V.infinite.test (s.allowance owner spender) then some s
  else if s.allowance owner spender < v then none
  else if V.spendViaApprove && (decide (owner = 0) || decide (spender = 0)) then none
  else some (s.setAllowance owner spender (s.allowance owner spender - v))

/-- `transfer(dst, v)` by `caller`. -/
def transfer (s : VState A) (caller dst : A) (v : ℕ) : Option (VState A) :=
  if V.moveOk s caller dst v then V.move s caller dst v else none

/-- `transferFrom(src, dst, v)` by `caller`. -/
def transferFrom (s : VState A) (caller src dst : A) (v : ℕ) : Option (VState A) :=
  if V.moveOk s src dst v then (V.spend s src caller v).bind fun s1 => V.move s1 src dst v
  else none

/-- The guards of `approve(sp, v)` by `caller`. -/
def approveOk (s : VState A) (caller sp : A) (v : ℕ) : Bool :=
  !(V.zero.owner && decide (caller = 0)) && !(V.zero.spender && decide (sp = 0)) &&
  !(V.zeroValueReverts && decide (v = 0)) &&
  !(V.approveGuard && decide (v ≠ 0) && decide (s.allowance caller sp ≠ 0)) &&
  !(decide (V.permit2 = some sp) && decide (v ≠ MAX))

/-- `approve(sp, v)` by `caller`. -/
def approve (s : VState A) (caller sp : A) (v : ℕ) : Option (VState A) :=
  if V.approveOk s caller sp v then some (s.setAllowance caller sp v) else none

/-! ## Supply changes -/

/-- The mint entry point (`mint(dst, v)`, USDT `issue(v)` with `dst = owner`). -/
def mint (s : VState A) (caller dst : A) (v : ℕ) : Option (VState A) :=
  if !V.mintAuth.allows s.admin caller dst then none
  else if V.zero.receiver && decide (dst = 0) then none
  else if V.zeroMintReverts && decide (v = 0) then none
  else if MAX < s.supply + v then none
  else some { s with supply := s.supply + v, bal := s.bal + single dst (V.units s v) }

/-- The burn entry point (`burn(src, v)`, USDT `redeem`, BNB `burn`, STA `destroy`). -/
def burn (s : VState A) (caller src : A) (v : ℕ) : Option (VState A) :=
  if !V.burnAuth.allows s.admin caller src then none
  else if V.zero.sender && decide (src = 0) then none
  else if V.zeroBurnReverts && decide (v = 0) then none
  else if s.bal src < V.units s v then none
  else some { s with supply := s.supply - v, bal := s.bal - single src (V.units s v) }

/-! ## Ether (WETH9) -/

/-- WETH9 `deposit()` with `value` wei: credits `value` tokens. -/
def deposit (s : VState A) (caller : A) (value : ℕ) : Option (VState A) :=
  if V.supply = .ether then
    some { s with bal := s.bal + single caller value, ether := s.ether + value }
  else none

/-- WETH9 `withdraw(wad)`: debits `wad`, then sends `wad` wei to `caller`; `sendOk` is
whether the recipient's code accepts it (the call reverts otherwise). -/
def withdraw (s : VState A) (caller : A) (wad : ℕ) (sendOk : Bool) : Option (VState A) :=
  if V.supply ≠ .ether then none
  else if s.bal caller < wad then none
  else if s.ether < wad then none
  else if !sendOk then none
  else some { s with bal := s.bal - single caller wad, ether := s.ether - wad }

/-- An unknown selector with `value` wei. -/
def fallbackCall (s : VState A) (caller : A) (value : ℕ) : Option (VState A) :=
  match V.fallback with
  | .revert => none
  | .accept => some { s with ether := s.ether + value }
  | .deposit => V.deposit s caller value

/-! ## Administration (USDT, AMPL) -/

/-- USDT `pause()`/`unpause()` by `caller`. -/
def setPaused (s : VState A) (caller : A) (b : Bool) : Option (VState A) :=
  if V.pausable && decide (caller = s.admin) then some { s with paused := b } else none

/-- USDT `addBlackList(u)`/`removeBlackList(u)` by `caller`. -/
def setBlacklisted (s : VState A) (caller u : A) (b : Bool) : Option (VState A) :=
  if V.blacklist && decide (caller = s.admin) then
    some { s with blacklisted := Function.update s.blacklisted u b }
  else none

/-- USDT `destroyBlackFunds(u)`: zeroes a blacklisted balance and lowers the supply. -/
def destroyBlackFunds (s : VState A) (caller u : A) : Option (VState A) :=
  if V.blacklist && decide (caller = s.admin) && s.blacklisted u then
    some { s with bal := s.bal - single u (s.bal u), supply := s.supply - s.bal u }
  else none

/-- USDT `setParams(bps, max)`: requires `bps < 20`, `max < 50`; stores `max · 10^decimals`. -/
def setParams (s : VState A) (caller : A) (bps mx : ℕ) : Option (VState A) :=
  if decide (V.fee = .bpsCapped) && decide (caller = s.admin) && decide (bps < 20) &&
      decide (mx < 50) then
    some { s with feeBps := bps, feeMax := mx * V.feeUnit }
  else none

/-- AMPL `rebase` by the monetary policy, to the new supply `S` (capped at `maxSupply`):
`_gonsPerFragment = TOTAL_GONS / _totalSupply`; every balance changes, no gons move. -/
def rebase (s : VState A) (caller : A) (S : ℕ) : Option (VState A) :=
  if V.rebasing && decide (caller = s.admin) && decide (0 < S) then
    some { s with supply := min S V.maxSupply, scale := V.totalGons / min S V.maxSupply }
  else none

/-! ## Calls and their observable outcome -/

/-- The state change of a call by `caller`. -/
def step (s : VState A) (caller : A) : Call A → Option (VState A)
  | .transfer dst v => V.transfer s caller dst v
  | .transferFrom src dst v => V.transferFrom s caller src dst v
  | .approve sp v => V.approve s caller sp v
  | .other value => V.fallbackCall s caller value

/-- Whether the call passes the guards (a failure after them is an arithmetic one). -/
def guardOk (s : VState A) (caller : A) : Call A → Bool
  | .transfer dst v => V.moveOk s caller dst v
  | .transferFrom src dst v => V.moveOk s src dst v
  | .approve sp v => V.approveOk s caller sp v
  | .other _ => V.fallback != .revert

/-- Return data of a successful call. -/
def retData : Call A → RetData
  | .transfer _ _ => if V.returns .transfer = .bool then .word true else .empty
  | .transferFrom _ _ _ => if V.returns .transferFrom = .bool then .word true else .empty
  | .approve _ _ => if V.returns .approve = .bool then .word true else .empty
  | .other _ => .empty

/-- A failure of kind `k` in state `s`. -/
def failWith {σ : Type} (s : σ) : OnFail → Result σ
  | .revert => .halt .revert
  | .invalid => .halt .invalid
  | .returnFalse => .ok s (.word false)

/-- The observable outcome of a call by `caller`. -/
def call (s : VState A) (caller : A) (c : Call A) : Result (VState A) :=
  match V.step s caller c with
  | Option.some s' => .ok s' (V.retData c)
  | Option.none => failWith s (if V.guardOk s caller c then V.arithFail else V.guardFail)

/-- Every state-changing operation of the variants. -/
inductive Op (A : Type) where
  /-- An ERC-20 call. -/
  | call (caller : A) (c : Call A)
  /-- The mint entry point. -/
  | mint (caller dst : A) (v : ℕ)
  /-- The burn entry point. -/
  | burn (caller src : A) (v : ℕ)
  /-- WETH9 `deposit()` with `value` wei. -/
  | deposit (caller : A) (value : ℕ)
  /-- WETH9 `withdraw(wad)`. -/
  | withdraw (caller : A) (wad : ℕ) (sendOk : Bool)
  /-- Ether arriving without a call (`SELFDESTRUCT` beneficiary, block reward). -/
  | receiveEther (value : ℕ)
  /-- USDT `pause`/`unpause`. -/
  | setPaused (caller : A) (b : Bool)
  /-- USDT `addBlackList`/`removeBlackList`. -/
  | setBlacklisted (caller u : A) (b : Bool)
  /-- USDT `destroyBlackFunds`. -/
  | destroyBlackFunds (caller u : A)
  /-- USDT `setParams`. -/
  | setParams (caller : A) (bps mx : ℕ)
  /-- AMPL `rebase`. -/
  | rebase (caller : A) (S : ℕ)

/-- One operation; `none` = it fails. -/
def stepOp (s : VState A) : Op A → Option (VState A)
  | .call c op => V.step s c op
  | .mint c d v => V.mint s c d v
  | .burn c src v => V.burn s c src v
  | .deposit c v => V.deposit s c v
  | .withdraw c w ok => V.withdraw s c w ok
  | .receiveEther v => some { s with ether := s.ether + v }
  | .setPaused c b => V.setPaused s c b
  | .setBlacklisted c u b => V.setBlacklisted s c u b
  | .destroyBlackFunds c u => V.destroyBlackFunds s c u
  | .setParams c b m => V.setParams s c b m
  | .rebase c S => V.rebase s c S

/-- A sequence of operations; a failed one leaves the state unchanged. -/
def exec (s : VState A) : List (Op A) → VState A
  | [] => s
  | op :: ops => exec ((V.stepOp s op).getD s) ops

end Variant

/-! ## Instances -/

namespace Variant

variable {A : Type}

/-- Solmate `ERC20` (with `MockERC20`'s open `mint`/`burn`): the reference behaviour, equal to
the `Token` operations. Returns `true`, reverts, no address checks, `MAX` allowances unspent. -/
def standard : Variant A where
  returns := fun _ => .bool
  guardFail := .revert
  arithFail := .revert
  zero := ⟨false, false, false, false⟩
  spendViaApprove := false
  rejectsSelf := false
  zeroValueReverts := false
  approveGuard := false
  infinite := .eqMax
  selfSpendFree := false
  permit2 := none
  fee := .none
  feeSink := .burn
  feeUnit := 1
  pausable := false
  blacklist := false
  rebasing := false
  totalGons := 0
  maxSupply := 0
  mintAuth := .anyone
  burnAuth := .anyone
  zeroMintReverts := false
  zeroBurnReverts := false
  fallback := .revert
  supply := .stored

/-- OpenZeppelin `ERC20` v5 (`ERC20Mock`): deviates by zero-address checks on sender, receiver,
approver and spender, also inside the allowance decrease (`_spendAllowance → _approve`), and
treats allowances `≥ MAX` as infinite. -/
def oz : Variant A :=
  { standard with zero := ⟨true, true, true, true⟩, spendViaApprove := true, infinite := .geMax }

/-- Solady `ERC20` (`SoladyToken`): deviates by the Permit2 spender `p`, whose allowance reads
`MAX`, is never spent, and cannot be approved to anything but `MAX`. -/
def solady (p : A) : Variant A := { (standard : Variant A) with permit2 := some p }

/-- WETH9: deviates by `totalSupply() = address(this).balance`, `deposit`/`withdraw` (and a
depositing fallback) instead of `mint`/`burn`, and `transferFrom` by the owner itself skipping
the allowance. -/
def weth9 : Variant A :=
  { standard with selfSpendFree := true, mintAuth := .nobody, burnAuth := .nobody,
                  fallback := .deposit, supply := .ether }

/-- USDT (`TetherToken`): deviates by returning nothing, failing with `INVALID` on insufficient
balance or allowance, the approve race guard, a capped basis-point fee paid to the owner,
pause and blacklist on transfers, `destroyBlackFunds`, owner-only `issue`/`redeem`. -/
def usdt : Variant A :=
  { standard with returns := fun _ => .empty, arithFail := .invalid, approveGuard := true,
                  infinite := .geMax, fee := .bpsCapped, feeSink := .owner, feeUnit := 10 ^ 6,
                  pausable := true, blacklist := true, mintAuth := .owner, burnAuth := .owner,
                  zeroMintReverts := true }

/-- BNB: deviates by `transfer` returning nothing, zero-value transfers/approvals/burns
failing, transfers to `0` failing, infinite allowances spent, holder-only `burn`, no `mint`,
and a payable fallback that accepts every unknown selector. -/
def bnb : Variant A :=
  { standard with returns := fun f => if f = .transfer then .empty else .bool,
                  zero := ⟨false, true, false, false⟩, zeroValueReverts := true,
                  infinite := .none, mintAuth := .nobody, burnAuth := .holder,
                  zeroBurnReverts := true, fallback := .accept }

/-- STA (Statera): deviates by burning `⌈v/100⌉` of every transfer (`basePercent = 100`),
transfers to `0` and approvals of `0` failing, infinite allowances spent, holder-only
`destroy`, no `mint`. -/
def sta : Variant A :=
  { standard with zero := ⟨false, true, false, true⟩, infinite := .none,
                  fee := .ceilPercent 100, feeSink := .burn, mintAuth := .nobody,
                  burnAuth := .holder, zeroBurnReverts := true }

/-- AMPL's `TOTAL_GONS = MAX − MAX mod INITIAL_FRAGMENTS_SUPPLY` (`5·10^16`). -/
def amplTotalGons : ℕ := MAX - MAX % (5 * 10 ^ 16)

/-- AMPL (`UFragments`): deviates by rebasing (balances are `gons / gonsPerFragment`, `rebase`
by the monetary policy changes every balance), transfers to `0` or to the token failing,
infinite allowances spent, no `mint`/`burn`. -/
def ampl : Variant A :=
  { standard with zero := ⟨false, true, false, false⟩, rejectsSelf := true, infinite := .none,
                  rebasing := true, totalGons := amplTotalGons, maxSupply := 2 ^ 128 - 1,
                  mintAuth := .nobody, burnAuth := .nobody }

end Variant

/-! ## `standard` is the `Token` model, `oz` its OpenZeppelin operations -/

namespace Variant

variable {A : Type} [DecidableEq A] [Zero A]

theorem standard_balanceOf (s : VState A) (a : A) : (standard : Variant A).balanceOf s a = s.bal a :=
  rfl

theorem standard_totalSupply (s : VState A) : (standard : Variant A).totalSupply s = s.supply := rfl

theorem standard_move (s : VState A) (src dst : A) (v : ℕ) :
    (standard : Variant A).move s src dst v = (s.toToken.transfer src dst v).map s.withToken := by
  unfold move credit Token.transfer
  simp only [units, feeOf, standard, Bool.false_eq_true, ↓reduceIte, Nat.not_lt_zero,
    VState.toToken]
  by_cases h : s.bal src < v <;> simp [h, VState.withToken]

theorem standard_spend (s : VState A) (o sp : A) (v : ℕ) :
    (standard : Variant A).spend s o sp v = (s.toToken.spend o sp v).map s.withToken := by
  unfold spend Token.spend
  simp only [standard, Bool.false_and, Bool.false_eq_true, ↓reduceIte, reduceCtorEq,
    Infinite.test, decide_eq_true_eq, VState.toToken]
  by_cases h1 : s.allowance o sp = MAX
  · simp [h1]; rfl
  by_cases h2 : s.allowance o sp < v
  · simp [h1, h2]
  · simp [h1, h2]; rfl

theorem standard_moveOk (s : VState A) (src dst : A) (v : ℕ) :
    (standard : Variant A).moveOk s src dst v = true := by
  simp [moveOk, standard]

theorem standard_transfer (s : VState A) (c d : A) (v : ℕ) :
    (standard : Variant A).transfer s c d v = (s.toToken.transfer c d v).map s.withToken := by
  simp only [transfer, standard_moveOk, ↓reduceIte, standard_move]

theorem standard_transferFrom (s : VState A) (c src d : A) (v : ℕ) :
    (standard : Variant A).transferFrom s c src d v =
      (s.toToken.transferFrom c src d v).map s.withToken := by
  simp only [transferFrom, standard_moveOk, ↓reduceIte, standard_spend, Option.bind_map,
    Token.transferFrom, Option.map_bind]
  congr 1
  funext t
  rw [Function.comp_apply, standard_move]
  rfl

theorem standard_approve (s : VState A) (c sp : A) (v : ℕ) :
    (standard : Variant A).approve s c sp v = some (s.withToken (s.toToken.approve c sp v)) := by
  simp [approve, approveOk, standard, Token.approve, VState.withToken_setAllowance]

theorem standard_mint (s : VState A) (c d : A) (v : ℕ) :
    (standard : Variant A).mint s c d v = (s.toToken.mint d v).map s.withToken := by
  unfold mint Token.mint
  simp only [standard, Auth.allows, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Bool.false_and, units, VState.toToken]
  by_cases h : MAX < s.supply + v <;> simp [h, VState.withToken]

theorem standard_burn (s : VState A) (c src : A) (v : ℕ) :
    (standard : Variant A).burn s c src v = (s.toToken.burn src v).map s.withToken := by
  unfold burn Token.burn
  simp only [standard, Auth.allows, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Bool.false_and, units, VState.toToken]
  by_cases h : s.bal src < v <;> simp [h, VState.withToken]

theorem oz_move (s : VState A) (src dst : A) (v : ℕ) :
    (oz : Variant A).move s src dst v = (s.toToken.transfer src dst v).map s.withToken :=
  standard_move s src dst v

theorem oz_moveOk (s : VState A) (src dst : A) (v : ℕ) :
    (oz : Variant A).moveOk s src dst v = (!decide (src = 0) && !decide (dst = 0)) := by
  simp [moveOk, oz, standard]

/-- OpenZeppelin `_transfer` after its address checks is the Solmate transfer. -/
theorem ozTransfer_eq_transfer (t : Token A) {src dst : A} (hs : src ≠ 0) (hd : dst ≠ 0)
    (v : ℕ) : t.ozTransfer src dst v = t.transfer src dst v := by
  simp only [Token.ozTransfer, Token.ozUpdate, Token.transfer, hs, hd, ↓reduceIte]
  by_cases h : t.balanceOf src < v <;> simp [h]

theorem oz_transfer (s : VState A) (c d : A) (v : ℕ) :
    (oz : Variant A).transfer s c d v = (s.toToken.ozTransfer c d v).map s.withToken := by
  rw [transfer, oz_moveOk, oz_move]
  by_cases hc : c = 0
  · simp [hc, Token.ozTransfer]
  by_cases hd : d = 0
  · simp [hd, Token.ozTransfer]
  simp [hc, hd, ozTransfer_eq_transfer _ hc hd]

theorem oz_spend (s : VState A) (o sp : A) (v : ℕ) :
    (oz : Variant A).spend s o sp v = (s.toToken.ozSpend o sp v).map s.withToken := by
  unfold spend Token.ozSpend Token.ozApprove
  simp only [oz, standard, Bool.false_and, Bool.false_eq_true, ↓reduceIte, reduceCtorEq,
    Infinite.test, decide_eq_true_eq, Bool.true_and, Bool.or_eq_true, VState.toToken]
  by_cases h1 : s.allowance o sp < MAX
  · have h1' : ¬ MAX ≤ s.allowance o sp := by omega
    by_cases h2 : s.allowance o sp < v
    · simp [h1, h1', h2]
    by_cases ho : o = 0
    · subst ho; simp [h1, h1', h2]
    by_cases hs : sp = 0
    · subst hs; simp [h1, h1', h2, ho]
    simp [h1, h1', h2, ho, hs]; rfl
  · have h1' : MAX ≤ s.allowance o sp := by omega
    simp [h1, h1']; rfl

theorem oz_transferFrom (s : VState A) (c src d : A) (v : ℕ) :
    (oz : Variant A).transferFrom s c src d v =
      (s.toToken.ozTransferFrom c src d v).map s.withToken := by
  rw [transferFrom, oz_moveOk, oz_spend, Option.bind_map, Token.ozTransferFrom, Option.map_bind]
  by_cases hs : src = 0
  · cases s.toToken.ozSpend src c v <;> simp [hs, Token.ozTransfer]
  by_cases hd : d = 0
  · cases s.toToken.ozSpend src c v <;> simp [hd, Token.ozTransfer]
  simp only [hs, hd, decide_false, Bool.not_false, Bool.and_self, ↓reduceIte]
  congr 1
  funext t
  rw [Function.comp_apply, oz_move, Function.comp_apply, ozTransfer_eq_transfer _ hs hd]
  rfl

theorem oz_approve (s : VState A) (c sp : A) (v : ℕ) :
    (oz : Variant A).approve s c sp v = (s.toToken.ozApprove c sp v).map s.withToken := by
  unfold approve approveOk Token.ozApprove
  by_cases hc : c = 0
  · simp [oz, standard, hc]
  by_cases hs : sp = 0
  · simp [oz, standard, hs]
  simp [oz, standard, hc, hs]; rfl

theorem oz_mint (s : VState A) (c d : A) (v : ℕ) :
    (oz : Variant A).mint s c d v = (s.toToken.ozMint d v).map s.withToken := by
  unfold mint Token.ozMint Token.ozUpdate
  by_cases hd : d = 0
  · simp [oz, standard, Auth.allows, hd]
  by_cases h : MAX < s.supply + v
  · simp [oz, standard, Auth.allows, hd, h, VState.toToken]
  · simp [oz, standard, Auth.allows, hd, h, VState.toToken, units, VState.withToken]

theorem oz_burn (s : VState A) (c src : A) (v : ℕ) :
    (oz : Variant A).burn s c src v = (s.toToken.ozBurn src v).map s.withToken := by
  unfold burn Token.ozBurn Token.ozUpdate
  by_cases hs : src = 0
  · simp [oz, standard, Auth.allows, hs]
  by_cases h : s.bal src < v
  · simp [oz, standard, Auth.allows, hs, h, VState.toToken, units]
  · simp [oz, standard, Auth.allows, hs, h, VState.toToken, units, VState.withToken]

end Variant

end Defi.ERC20
