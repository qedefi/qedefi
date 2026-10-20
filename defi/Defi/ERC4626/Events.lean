module

public import Defi.ERC4626.Solmate

/-!
# Events of the Solmate vault model

The events each model operation (`Solmate.Op`) emits, as a function of the pre-state and the
arguments, exactly as Solmate's `ERC20` / `ERC4626` and `MockERC20` / `MockERC4626` emit them:

* `ERC20.transfer(to, v)` from `c`: `Transfer(c, to, v)`;
* `ERC20.transferFrom(src, dst, v)`: `Transfer(src, dst, v)` only — Solmate does **not** emit
  `Approval` when it spends an allowance (neither in `transferFrom` nor in `withdraw` /
  `redeem`);
* `ERC20.approve(sp, v)` from `c`: `Approval(c, sp, v)`;
* `_mint(to, v)` (also `MockERC20.mint`): `Transfer(0, to, v)`; `_burn(from, v)` (also
  `MockERC20.burn`): `Transfer(from, 0, v)`;
* `deposit` / `mint` of the vault: the asset's `Transfer(caller, vault, assets)` (inside
  `safeTransferFrom`), the shares' `Transfer(0, receiver, shares)` (`_mint`), then
  `Deposit(caller, receiver, assets, shares)`;
* `withdraw` / `redeem`: the shares' `Transfer(owner, 0, shares)` (`_burn`, after the
  `beforeWithdraw` hook), `Withdraw(caller, receiver, owner, assets, shares)`, then the asset's
  `Transfer(vault, receiver, assets)` (inside `safeTransfer`).

An operation that reverts (`Solmate.step s op = none`) emits nothing (`events_eq_nil`). Every
`Transfer` / `Approval` carries its emitter (`Emitter.vault` for the share token,
`Emitter.asset` for the asset); `Deposit` / `Withdraw` are always the vault's. The zero address
is `0 : A` (`[Zero A]`). `stream s ops` is the event stream of a sequence of calls (reverted
ones contribute nothing, as `Solmate.exec`). The encoding as EVM logs is in
`Examples.Solmate.ERC4626.Events`.
-/

@[expose] public noncomputable section

namespace Defi.ERC4626.Solmate
open Defi.Math Defi.ERC20

/-- Which contract emits an ERC-20 event. -/
inductive Emitter where
  /-- The vault (its share token). -/
  | vault
  /-- The asset (`MockERC20`). -/
  | asset
  deriving DecidableEq

/-- An event of the system. -/
inductive Event (A : Type) where
  /-- ERC-20 `Transfer(from, to, amount)` of the emitter's token. -/
  | transfer (emitter : Emitter) (src dst : A) (amount : ℕ)
  /-- ERC-20 `Approval(owner, spender, amount)` of the emitter's token. -/
  | approval (emitter : Emitter) (owner spender : A) (amount : ℕ)
  /-- ERC-4626 `Deposit(caller, owner, assets, shares)` of the vault. -/
  | deposit (caller owner : A) (assets shares : ℕ)
  /-- ERC-4626 `Withdraw(caller, receiver, owner, assets, shares)` of the vault. -/
  | withdraw (caller receiver owner : A) (assets shares : ℕ)

variable {A : Type} [DecidableEq A] [Zero A]

namespace Events
open Defi.Math Defi.ERC20

/-- `Transfer(src, dst, v)` of emitter `e` if the Solmate `transfer` succeeds, else nothing. -/
def transfer (e : Emitter) (t : Token A) (src dst : A) (v : ℕ) : List (Event A) :=
  if (t.transfer src dst v).isSome then [.transfer e src dst v] else []

/-- `transferFrom` by `spender`: `Transfer(src, dst, v)` if it succeeds (no `Approval`). -/
def transferFrom (e : Emitter) (t : Token A) (spender src dst : A) (v : ℕ) : List (Event A) :=
  if (t.transferFrom spender src dst v).isSome then [.transfer e src dst v] else []

/-- `approve` never reverts: `Approval(owner, spender, v)`. -/
def approve (e : Emitter) (owner spender : A) (v : ℕ) : List (Event A) :=
  [.approval e owner spender v]

/-- `MockERC20.mint(dst, v)`: `Transfer(0, dst, v)` if the supply does not overflow. -/
def mint (e : Emitter) (t : Token A) (dst : A) (v : ℕ) : List (Event A) :=
  if (t.mint dst v).isSome then [.transfer e 0 dst v] else []

/-- `MockERC20.burn(src, v)`: `Transfer(src, 0, v)` if the balance covers `v`. -/
def burn (e : Emitter) (t : Token A) (src : A) (v : ℕ) : List (Event A) :=
  if (t.burn src v).isSome then [.transfer e src 0 v] else []

/-- `deposit(assets, receiver)` from `caller` on the vault `self`, given its result. -/
def deposit (self caller receiver : A) (assets : ℕ) :
    Option (State A × ℕ) → List (Event A)
  | some (_, shares) =>
    [.transfer .asset caller self assets, .transfer .vault 0 receiver shares,
      .deposit caller receiver assets shares]
  | none => []

/-- `mint(shares, receiver)` from `caller` on the vault `self`, given its result. -/
def mint4626 (self caller receiver : A) (shares : ℕ) :
    Option (State A × ℕ) → List (Event A)
  | some (_, assets) =>
    [.transfer .asset caller self assets, .transfer .vault 0 receiver shares,
      .deposit caller receiver assets shares]
  | none => []

/-- `withdraw(assets, receiver, owner)` from `caller` on the vault `self`, given its result. -/
def withdraw (self caller receiver owner : A) (assets : ℕ) :
    Option (State A × ℕ) → List (Event A)
  | some (_, shares) =>
    [.transfer .vault owner 0 shares, .withdraw caller receiver owner assets shares,
      .transfer .asset self receiver assets]
  | none => []

/-- `redeem(shares, receiver, owner)` from `caller` on the vault `self`, given its result. -/
def redeem (self caller receiver owner : A) (shares : ℕ) :
    Option (State A × ℕ) → List (Event A)
  | some (_, assets) =>
    [.transfer .vault owner 0 shares, .withdraw caller receiver owner assets shares,
      .transfer .asset self receiver assets]
  | none => []

end Events

/-- The events emitted by one external call from state `s`, in emission order. -/
def events (s : State A) : Op A → List (Event A)
  | .deposit c a r => Events.deposit s.self c r a (deposit s c a r)
  | .mint c n r => Events.mint4626 s.self c r n (mint s c n r)
  | .withdraw c a r o => Events.withdraw s.self c r o a (withdraw s c a r o)
  | .redeem c n r o => Events.redeem s.self c r o n (redeem s c n r o)
  | .transfer c d v => Events.transfer .vault s.shares c d v
  | .transferFrom c src d v => Events.transferFrom .vault s.shares c src d v
  | .approve c sp v => Events.approve .vault c sp v
  | .assetTransfer c d v => Events.transfer .asset s.asset c d v
  | .assetTransferFrom c src d v => Events.transferFrom .asset s.asset c src d v
  | .assetApprove c sp v => Events.approve .asset c sp v
  | .assetMint d v => Events.mint .asset s.asset d v
  | .assetBurn src v => Events.burn .asset s.asset src v

/-- The event stream of a sequence of calls (reverted ones emit nothing). -/
def stream (s : State A) : List (Op A) → List (Event A)
  | [] => []
  | op :: ops => events s op ++ stream ((step s op).getD s) ops

/-- A reverting call emits nothing. -/
theorem events_eq_nil {s : State A} {op : Op A} (h : step s op = none) : events s op = [] := by
  cases op <;> simp_all [step, events, Events.deposit, Events.mint4626, Events.withdraw,
    Events.redeem, Events.transfer, Events.transferFrom, Events.mint, Events.burn]

/-- The stream of a concatenation. -/
theorem stream_append (s : State A) (ops₁ ops₂ : List (Op A)) :
    stream s (ops₁ ++ ops₂) = stream s ops₁ ++ stream (exec s ops₁) ops₂ := by
  induction ops₁ generalizing s with
  | nil => rfl
  | cons op ops ih => simp [stream, exec, ih]

end Defi.ERC4626.Solmate
