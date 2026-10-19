module

public import EvmLeanSpecs.Vault.Token

/-!
# EIP-2612 `permit` on a Solmate ERC-20 ledger

Solmate's `ERC20` keeps, besides the ledger (`Token`), a nonce per owner
(`mapping(address => uint256) nonces`), and offers

```solidity
function permit(address owner, address spender, uint256 value, uint256 deadline,
                uint8 v, bytes32 r, bytes32 s)
```

which, if the signature `(v, r, s)` of the EIP-712 message
`Permit(owner, spender, value, nonces[owner], deadline)` recovers to `owner` (and the deadline
has not passed), sets `allowance[owner][spender] = value` and increments `nonces[owner]`;
otherwise it reverts.

`PermitToken A` is the ledger extended with the nonces, and `PermitToken.permit` the
operation. Whether a permit is valid is **not** decided here: it depends on the chain (block
timestamp, chain id), on the token's domain separator and on the signature scheme. The
operation takes it as a predicate `valid` of the owner's current nonce; the refinement layer
instantiates it with the exact check the bytecode performs, for an arbitrary `Crypto`
(`EvmLeanSpecs.Refinement.Permit.PermitValid`). The nonce increment is unchecked in the
source (`nonces[owner]++` inside `unchecked`), so it wraps modulo `2²⁵⁶` here as well; it is
`+ 1` for every nonce below `MAX` (`permit_nonce_of_lt`).

The other operations of the token leave the nonces unchanged (`liftOp`).
-/

@[expose] public noncomputable section

namespace EvmLeanSpecs.Vault

open Finsupp

/-- A Solmate ERC-20 with EIP-2612: the ledger and the per-owner nonces. -/
structure PermitToken (A : Type) where
  /-- Balances, total supply, allowances. -/
  token : Token A
  /-- `nonces[owner]`. -/
  nonces : A →₀ ℕ

namespace PermitToken

variable {A : Type} [DecidableEq A]

/-- Solmate `ERC20.permit(owner, spender, value, …)`: if the permit is valid at the owner's
current nonce (`valid (nonces owner)`: deadline, signature, …), approve `value` for `spender`
and increment the owner's nonce (modulo `2²⁵⁶`, as the unchecked `++` does); otherwise revert
(`none`). -/
def permit (s : PermitToken A) (owner spender : A) (value : ℕ) (valid : ℕ → Prop)
    [DecidablePred valid] : Option (PermitToken A) :=
  if valid (s.nonces owner) then
    some { token := s.token.approve owner spender value
           nonces := s.nonces.update owner ((s.nonces owner + 1) % U256) }
  else none

/-- An operation of the plain ledger, lifted: the nonces are unchanged. -/
def liftOp (f : Token A → Option (Token A)) (s : PermitToken A) : Option (PermitToken A) :=
  (f s.token).map fun t => { s with token := t }

/-- `permit` succeeds exactly when the permit is valid at the current nonce. -/
theorem permit_isSome {s : PermitToken A} {owner spender : A} {value : ℕ} {valid : ℕ → Prop}
    [DecidablePred valid] :
    (s.permit owner spender value valid).isSome ↔ valid (s.nonces owner) := by
  unfold permit; split <;> simp_all

/-- The result of a successful `permit`. -/
theorem permit_eq_some {s s' : PermitToken A} {owner spender : A} {value : ℕ}
    {valid : ℕ → Prop} [DecidablePred valid] (h : s.permit owner spender value valid = some s') :
    valid (s.nonces owner) ∧ s'.token = s.token.approve owner spender value ∧
      s'.nonces = s.nonces.update owner ((s.nonces owner + 1) % U256) := by
  unfold permit at h
  split at h
  · cases h; exact ⟨‹_›, rfl, rfl⟩
  · cases h

/-- Below `MAX` the nonce increment is `+ 1`. -/
theorem permit_nonce_of_lt {n : ℕ} (h : n < MAX) : (n + 1) % U256 = n + 1 :=
  Nat.mod_eq_of_lt (by unfold MAX at h; unfold U256; omega)

/-- `permit` keeps balances and the total supply, hence well-formedness of the ledger. -/
theorem WF_permit {s s' : PermitToken A} {owner spender : A} {value : ℕ} {valid : ℕ → Prop}
    [DecidablePred valid] (hw : s.token.WF) (h : s.permit owner spender value valid = some s') :
    s'.token.WF := by
  obtain ⟨-, ht, -⟩ := permit_eq_some h
  rw [ht]; exact hw

/-- Nonces of other owners are unchanged by `permit`. -/
theorem permit_nonces_ne {s s' : PermitToken A} {owner spender : A} {value : ℕ}
    {valid : ℕ → Prop} [DecidablePred valid] (h : s.permit owner spender value valid = some s')
    {a : A} (ha : a ≠ owner) : s'.nonces a = s.nonces a := by
  obtain ⟨-, -, hn⟩ := permit_eq_some h
  rw [hn, Finsupp.update_apply]; simp [ha]

end PermitToken

end EvmLeanSpecs.Vault
