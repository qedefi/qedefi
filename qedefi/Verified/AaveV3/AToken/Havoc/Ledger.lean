import Verified.AaveV3.AToken.Havoc.Slots

/-!
# The scaled ledger under the AToken's writes

How `ledgerSum` (Σ of the low 120 bits over the `_userState` slots) changes when the token
writes its storage, and `Good.of_writes`: after writes at a protected account `t` that leave its
code, the other accounts and the fixed slots `0`, `1`, the EIP-1967 slot alone, `Good` holds again
as soon as the ledger at `t` balances.
-/

namespace Verified.AaveV3.AToken.Havoc
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
  EvmLogic.Solidity Verified.AaveV3.Contracts

variable {crypto : Crypto}

/-! ## The ledger -/

/-- **Writing one `_userState` entry** changes the ledger by the difference of the low bits. -/
theorem ledgerSum_sstore_user (w : World) (t a : Address) (v : Word) :
    ledgerSum crypto (w.sstore t (mappingSlot crypto (Word.ofAddress a) 52#256) v) t +
        low120 (w.sload t (mappingSlot crypto (Word.ofAddress a) 52#256)) =
      ledgerSum crypto w t + low120 v := by
  unfold ledgerSum
  have hs := mem_userSlots crypto a
  rw [← Finset.add_sum_erase _ _ hs,
    ← Finset.add_sum_erase _ (fun s => low120 (w.sload t s)) hs]
  have : ∑ x ∈ (userSlots crypto).erase (userSlot crypto a),
      low120 ((w.sstore t (mappingSlot crypto (Word.ofAddress a) 52#256) v).sload t x) =
      ∑ x ∈ (userSlots crypto).erase (userSlot crypto a), low120 (w.sload t x) :=
    Finset.sum_congr rfl fun x hx => by
      rw [World.sload_sstore_ne_key _ _ _ (Finset.ne_of_mem_erase hx)]
  simp only [userSlot] at this ⊢
  rw [this, World.sload_sstore_self]
  omega

/-- A write outside the `_userState` slots leaves the ledger. -/
theorem ledgerSum_sstore_other (w : World) (t : Address) {k : Word} (hk : k ∉ userSlots crypto)
    (v : Word) : ledgerSum crypto (w.sstore t k v) t = ledgerSum crypto w t := by
  unfold ledgerSum
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [World.sload_sstore_ne_key _ _ _ (fun (h : s = k) => hk (by rw [← h]; exact hs))]

/-- A write at another account leaves the ledger. -/
theorem ledgerSum_sstore_addr (w : World) {t t' : Address} (h : t' ≠ t) (k v : Word) :
    ledgerSum crypto (w.sstore t k v) t' = ledgerSum crypto w t' := by
  unfold ledgerSum
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [World.sload_sstore_ne_addr _ _ _ _ h]

/-- One balance is at most the ledger. -/
theorem low120_le_ledgerSum (w : World) (t a : Address) :
    low120 (w.sload t (mappingSlot crypto (Word.ofAddress a) 52#256)) ≤ ledgerSum crypto w t :=
  Finset.single_le_sum (f := fun s => low120 (w.sload t s)) (fun _ _ => Nat.zero_le _)
    (mem_userSlots crypto a)

theorem low120_lt (x : Word) : low120 x < 2 ^ 120 := Nat.mod_lt _ (by decide)

/-! ## `Good` after the token's writes -/

/-- **`Good` after writes at a protected account `t`**: if the other accounts keep storage and
code, `t` keeps its code and its fixed slots other than `_totalSupply`, and the ledger at `t`
balances, `Good` holds. -/
theorem Good.of_writes {w w' : World} {t : Address} (h : Good crypto w) (ht : Prot t)
    (hk : ∀ p, p ≠ t → Keep p w w') (hcode : w'.code t = w.code t)
    (h0 : w'.sload t 0#256 = w.sload t 0#256) (h1 : w'.sload t 1#256 = w.sload t 1#256)
    (himpl : w'.sload t ATokenProxy.implSlot = w.sload t ATokenProxy.implSlot)
    (hl : ledgerSum crypto w' t = (w'.sload t 54#256).toNat) : Good crypto w' := by
  have tok : ∀ p, Prot p → TokenOk crypto w p → TokenOk crypto w' p := by
    intro p _ hp
    by_cases hpt : p = t
    · subst hpt
      exact ⟨by rw [h0]; exact hp.rev, by rw [h1]; exact hp.init, hl⟩
    · exact hp.keep (hk p hpt)
  have code : ∀ p, w'.code p = w.code p := by
    intro p
    by_cases hpt : p = t
    · subst hpt; exact hcode
    · exact (hk p hpt).code
  refine ⟨by rw [code]; exact h.proxyCode, by rw [code]; exact h.implCode, ?_,
    tok _ (.inl rfl) h.proxyOk, tok _ (.inr rfl) h.implOk⟩
  by_cases hpt : proxy = t
  · rw [← hpt] at himpl; rw [himpl]; exact h.implSlot
  · rw [(hk proxy hpt).sload]; exact h.implSlot

/-- A write at `t` keeps every other account. -/
theorem keep_sstore_of_ne {w : World} {t : Address} (k v : Word) :
    ∀ p, p ≠ t → Keep p w (w.sstore t k v) :=
  fun _ hp => keep_sstore hp

/-- **A write outside the ledger and the fixed slots** (an allowance, a nonce) keeps `Good`. -/
theorem Good.sstore_free {w : World} {t : Address} {k v : Word}
    (h : Good crypto w) (ht : Prot t) (hu : k ∉ userSlots crypto) (hf : k ∉ fixedSlots) :
    Good crypto (w.sstore t k v) := by
  have hne : ∀ j ∈ fixedSlots, j ≠ k := fun j hj e => hf (e ▸ hj)
  refine h.of_writes ht (keep_sstore_of_ne k v) (World.code_sstore _ _ _ _ _)
    (World.sload_sstore_ne_key _ _ _ (hne _ mem_fixed_0))
    (World.sload_sstore_ne_key _ _ _ (hne _ mem_fixed_1))
    (World.sload_sstore_ne_key _ _ _ (hne _ mem_fixed_impl)) ?_
  rw [ledgerSum_sstore_other _ _ hu, World.sload_sstore_ne_key _ _ _ (hne _ mem_fixed_54)]
  rcases ht with rfl | rfl
  · exact h.proxyOk.ledger
  · exact h.implOk.ledger

/-- An allowance write keeps `Good`. -/
theorem Good.sstore_allow (hK : SlotsOk crypto) {w : World} {t : Address} (o s : Address)
    (v : Word) (h : Good crypto w) (ht : Prot t) :
    Good crypto (w.sstore t
      (mappingSlot crypto (Word.ofAddress s) (mappingSlot crypto (Word.ofAddress o) 53#256)) v) :=
  h.sstore_free ht (Finset.disjoint_left.1 hK.allow (mem_allowanceSlots crypto o s))
    (Finset.disjoint_left.1 hK.allowFixed (mem_allowanceSlots crypto o s))

/-- A nonce write keeps `Good`. -/
theorem Good.sstore_nonce (hK : SlotsOk crypto) {w : World} {t : Address} (a : Address)
    (v : Word) (h : Good crypto w) (ht : Prot t) :
    Good crypto (w.sstore t (mappingSlot crypto (Word.ofAddress a) 58#256) v) :=
  h.sstore_free ht (Finset.disjoint_left.1 hK.nonce (mem_nonceSlots crypto a))
    (Finset.disjoint_left.1 hK.nonceFixed (mem_nonceSlots crypto a))

/-- The ledger equation at a protected account of a `Good` world. -/
theorem Good.ledger {w : World} {t : Address} (h : Good crypto w) (ht : Prot t) :
    ledgerSum crypto w t = (w.sload t 54#256).toNat := by
  rcases ht with rfl | rfl
  · exact h.proxyOk.ledger
  · exact h.implOk.ledger

/-- **Mint- and burn-shaped writes**: `_userState[u]` (`V1`, keeping the balance), then
`_totalSupply` (`V2`), then `_userState[u]` again (`V3`): `Good` holds when the new balance and the
new supply moved together (`low V3 + S = low V1 + V2`). -/
theorem Good.writes3 (hK : SlotsOk crypto) {w : World} {t u : Address} {V1 V2 V3 : Word}
    (h : Good crypto w) (ht : Prot t)
    (h1 : low120 V1 = low120 (w.sload t (mappingSlot crypto (Word.ofAddress u) 52#256)))
    (h3 : low120 V3 + (w.sload t 54#256).toNat = low120 V1 + V2.toNat) :
    Good crypto (((w.sstore t (mappingSlot crypto (Word.ofAddress u) 52#256) V1).sstore t 54#256
      V2).sstore t (mappingSlot crypto (Word.ofAddress u) 52#256) V3) := by
  have hu54 := user_ne_fixed hK u mem_fixed_54
  have hne : ∀ k ∈ fixedSlots, k ≠ 54#256 → ∀ v1 v2 v3 : Word,
      (((w.sstore t (mappingSlot crypto (Word.ofAddress u) 52#256) v1).sstore t 54#256
        v2).sstore t (mappingSlot crypto (Word.ofAddress u) 52#256) v3).sload t k = w.sload t k := by
    intro k hk h54 v1 v2 v3
    rw [World.sload_sstore_ne_key _ _ _ (user_ne_fixed hK u hk),
      World.sload_sstore_ne_key _ _ _ h54, World.sload_sstore_ne_key _ _ _ (user_ne_fixed hK u hk)]
  refine h.of_writes ht (fun p hp => ((keep_sstore hp).trans (keep_sstore hp)).trans
    (keep_sstore hp)) (by simp only [World.code_sstore]) (hne _ mem_fixed_0 (by decide) _ _ _)
    (hne _ mem_fixed_1 (by decide) _ _ _) (hne _ mem_fixed_impl (by decide) _ _ _) ?_
  have e3 := ledgerSum_sstore_user (crypto := crypto)
    ((w.sstore t (mappingSlot crypto (Word.ofAddress u) 52#256) V1).sstore t 54#256 V2) t u V3
  have e2 := ledgerSum_sstore_other (crypto := crypto)
    (w.sstore t (mappingSlot crypto (Word.ofAddress u) 52#256) V1) t
    (k := 54#256) (fun hm => Finset.disjoint_left.1 hK.userFixed hm mem_fixed_54) V2
  have e1 := ledgerSum_sstore_user (crypto := crypto) w t u V1
  have hl := h.ledger ht
  rw [World.sload_sstore_ne_key _ _ _ hu54.symm, World.sload_sstore_self] at e3
  rw [World.sload_sstore_ne_key _ _ _ hu54, World.sload_sstore_self]
  omega

end Verified.AaveV3.AToken.Havoc
