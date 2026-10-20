module

public import Defi.ERC20.Token

/-!
# EIP-2612 `permit` on a Solmate ERC-20 ledger

`PermitToken A` is a `Token` plus per-owner nonces. Validity of a permit (deadline,
signature, domain) is a parameter `valid` of the owner's current nonce, instantiated by the
bytecode layer (`Examples.Solmate.ERC20.Permit.PermitValid`). The nonce increment is
unchecked in the source, so it wraps modulo `2²⁵⁶`.
-/

@[expose] public noncomputable section

namespace Defi.ERC20
open Defi.Math Finsupp

/-- A Solmate ERC-20 with EIP-2612: the ledger and the per-owner nonces. -/
structure PermitToken (A : Type) where
  /-- Balances, total supply, allowances. -/
  token : Token A
  /-- `nonces[owner]`. -/
  nonces : A →₀ ℕ

namespace PermitToken

variable {A : Type} [DecidableEq A]

/-- Solmate `ERC20.permit`: if valid at the owner's current nonce, approve `value` and
increment the nonce (wrapping); otherwise revert. -/
def permit (s : PermitToken A) (owner spender : A) (value : ℕ) (valid : ℕ → Prop)
    [DecidablePred valid] : Option (PermitToken A) :=
  if valid (s.nonces owner) then
    some { token := s.token.approve owner spender value
           nonces := s.nonces.update owner ((s.nonces owner + 1) % U256) }
  else none

/-- An operation of the plain ledger, lifted: the nonces are unchanged. -/
def liftOp (f : Token A → Option (Token A)) (s : PermitToken A) : Option (PermitToken A) :=
  (f s.token).map fun t => { s with token := t }

theorem permit_isSome {s : PermitToken A} {owner spender : A} {value : ℕ} {valid : ℕ → Prop}
    [DecidablePred valid] :
    (s.permit owner spender value valid).isSome ↔ valid (s.nonces owner) := by
  unfold permit; split <;> simp_all

theorem permit_eq_some {s s' : PermitToken A} {owner spender : A} {value : ℕ}
    {valid : ℕ → Prop} [DecidablePred valid] (h : s.permit owner spender value valid = some s') :
    valid (s.nonces owner) ∧ s'.token = s.token.approve owner spender value ∧
      s'.nonces = s.nonces.update owner ((s.nonces owner + 1) % U256) := by
  unfold permit at h
  split at h
  · cases h; exact ⟨‹_›, rfl, rfl⟩
  · cases h

theorem permit_nonce_of_lt {n : ℕ} (h : n < MAX) : (n + 1) % U256 = n + 1 :=
  Nat.mod_eq_of_lt (by unfold MAX at h; unfold U256; omega)

theorem WF_permit {s s' : PermitToken A} {owner spender : A} {value : ℕ} {valid : ℕ → Prop}
    [DecidablePred valid] (hw : s.token.WF) (h : s.permit owner spender value valid = some s') :
    s'.token.WF := by
  obtain ⟨-, ht, -⟩ := permit_eq_some h
  rw [ht]; exact hw

theorem permit_nonces_ne {s s' : PermitToken A} {owner spender : A} {value : ℕ}
    {valid : ℕ → Prop} [DecidablePred valid] (h : s.permit owner spender value valid = some s')
    {a : A} (ha : a ≠ owner) : s'.nonces a = s.nonces a := by
  obtain ⟨-, -, hn⟩ := permit_eq_some h
  rw [hn, Finsupp.update_apply]; simp [ha]

end PermitToken

end Defi.ERC20
