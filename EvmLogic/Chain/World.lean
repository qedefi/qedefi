import EvmLean.Block
import EvmLogic.Program.Nested.Run

/-!
# World operations of the block layer

The two world operations a block performs outside the interpreter:

* **Balance credits** (`Tx.creditBalance`, used by withdrawals, the gas refund and the
  priority fee): `modifyState` of the balance, wrapping mod 2²⁵⁶. Every account keeps its nonce
  and code; every account other than the credited one is untouched; the credited account keeps
  its storage unless the credit leaves it empty, in which case it is erased (EIP-161: a credit of
  `0` to an existing empty account deletes it, with any storage it had). A credit to an absent
  account with a non-zero amount creates it. Accounts holding code are never erased
  (`keep_creditBalance`).
* **Withdrawals** (`Block.applyWithdrawals`, EIP-4895): credits in order, so the same holds, and
  the balance of `p` is the old balance plus every amount credited to `p`, in wei, mod 2²⁵⁶
  (`balance_applyWithdrawals`); balances only increase while that sum fits in 256 bits.
* **EIP-161 clean-up** (`Tx.destroyTouchedEmpty`): only empty accounts are erased
  (`EraseEmpty`), so nonces, balances and code of every account and the whole account of every
  account holding code are unchanged.
-/

namespace EvmLogic.Chain
open EvmLean EvmLean.Interpreter EvmLean.Block EvmLogic.Program.Nested

/-! ## Byte arrays -/

theorem byteArray_eq_empty {b : ByteArray} (h : b.size = 0) : b = .empty :=
  Classical.byContradiction fun hne => size_ne_zero_of_ne_empty hne h

/-! ## `modifyState` with a balance-only update -/

/-- An update that changes at most the balance of an account. -/
def BalanceOnly (f : Account → Account) : Prop :=
  ∀ acc, (f acc).nonce = acc.nonce ∧ (f acc).code = acc.code ∧ (f acc).storage = acc.storage

theorem getElem?_modifyState (w : World) (a : Address) (f : Account → Account) (p : Address) :
    (modifyState w a f)[p]? =
      if p = a then (if (f (w.account a)).isEmpty then none else some (f (w.account a)))
      else w[p]? := by
  unfold modifyState
  by_cases hp : p = a
  · subst hp
    by_cases he : (f (w.account p)).isEmpty = true
    · simp [he]
    · simp [he]
  · have hp' : ¬ a = p := fun e => hp e.symm
    simp only [hp, ↓reduceIte]
    split <;> simp [Std.ExtTreeMap.getElem?_erase, Std.ExtTreeMap.getElem?_insert, hp']

theorem getElem?_modifyState_ne (w : World) {a p : Address} (f : Account → Account)
    (h : p ≠ a) : (modifyState w a f)[p]? = w[p]? := by
  rw [getElem?_modifyState]; simp [h]

theorem account_modifyState_ne (w : World) {a p : Address} (f : Account → Account) (h : p ≠ a) :
    (modifyState w a f).account p = w.account p := by
  simp only [World.account, Std.ExtTreeMap.getD_eq_getD_getElem?, getElem?_modifyState_ne w f h]

/-- Nonce and code of every account are unchanged by a balance-only `modifyState`. -/
theorem nonce_code_modifyState {w : World} {a : Address} {f : Account → Account}
    (hf : BalanceOnly f) (p : Address) :
    ((modifyState w a f).account p).nonce = (w.account p).nonce ∧
      ((modifyState w a f).account p).code = (w.account p).code := by
  by_cases hp : p = a
  · subst hp
    have hacc : (modifyState w p f).account p =
        if (f (w.account p)).isEmpty then {} else f (w.account p) := by
      simp only [World.account, Std.ExtTreeMap.getD_eq_getD_getElem?, getElem?_modifyState,
        ite_true]
      split <;> rfl
    rw [hacc]
    obtain ⟨hn, hc, -⟩ := hf (w.account p)
    split
    · rename_i he
      simp only [Account.isEmpty, Bool.and_eq_true, decide_eq_true_eq, hn, hc] at he
      exact ⟨he.1.1.symm, (byteArray_eq_empty he.2).symm⟩
    · exact ⟨hn, hc⟩
  · rw [account_modifyState_ne w f hp]; exact ⟨rfl, rfl⟩

/-- An account with code is never erased by a balance-only `modifyState`; it keeps its storage. -/
theorem storage_modifyState {w : World} {a p : Address} {f : Account → Account}
    (hf : BalanceOnly f) (hp : (w.code p).size ≠ 0) :
    ((modifyState w a f).account p).storage = (w.account p).storage :=
  (keep_modifyState (fun acc => ⟨(hf acc).2.2, (hf acc).2.1⟩) hp).1

/-! ## Balance credits -/

theorem balanceOnly_credit (amount : Nat) :
    BalanceOnly fun acc : Account =>
      { acc with balance := BitVec.ofNat 256 (acc.balance.toNat + amount) } :=
  fun _ => ⟨rfl, rfl, rfl⟩

/-- **A credit touches only the credited account.** -/
theorem getElem?_creditBalance_ne (w : World) {a p : Address} (amount : Nat) (h : p ≠ a) :
    (Tx.creditBalance w a amount)[p]? = w[p]? :=
  getElem?_modifyState_ne w _ h

/-- What a credit does to the credited account: the new balance, erased if left empty. -/
theorem getElem?_creditBalance_self (w : World) (a : Address) (amount : Nat) :
    (Tx.creditBalance w a amount)[a]? =
      let acc := { w.account a with
        balance := BitVec.ofNat 256 ((w.account a).balance.toNat + amount) }
      if acc.isEmpty then none else some acc := by
  unfold Tx.creditBalance; rw [getElem?_modifyState]; simp

theorem balance_creditBalance (w : World) (a : Address) (amount : Nat) (p : Address) :
    (Tx.creditBalance w a amount).balance p =
      if p = a then BitVec.ofNat 256 ((w.balance a).toNat + amount) else w.balance p := by
  unfold Tx.creditBalance; rw [balance_modifyState]; rfl

theorem nonce_creditBalance (w : World) (a : Address) (amount : Nat) (p : Address) :
    ((Tx.creditBalance w a amount).account p).nonce = (w.account p).nonce :=
  (nonce_code_modifyState (balanceOnly_credit amount) p).1

theorem code_creditBalance (w : World) (a : Address) (amount : Nat) (p : Address) :
    (Tx.creditBalance w a amount).code p = w.code p :=
  (nonce_code_modifyState (balanceOnly_credit amount) p).2

/-- **A credit keeps the storage and code of every account holding code.** -/
theorem keep_creditBalance {w : World} {p : Address} (a : Address) (amount : Nat)
    (hp : (w.code p).size ≠ 0) : Keep p w (Tx.creditBalance w a amount) :=
  keep_modifyState (fun _ => ⟨rfl, rfl⟩) hp

/-- A credit keeps the storage and code of every protected account that holds code. -/
theorem keepP_creditBalance {P : Address → Prop} {w : World}
    (hP : ∀ p, P p → (w.code p).size ≠ 0) (a : Address) (amount : Nat) :
    KeepP P w (Tx.creditBalance w a amount) :=
  fun p hp => keep_creditBalance a amount (hP p hp)

/-- A predicate of the kind the nested simulation handles (`GoodOk`) survives any credit. -/
theorem good_creditBalance {P : Address → Prop} {Good : World → Prop} (S : GoodOk P Good)
    {w : World} (hw : Good w) (a : Address) (amount : Nat) : Good (Tx.creditBalance w a amount) :=
  S.keep _ _ hw (keepP_creditBalance (S.code w hw) a amount)

/-! ## Withdrawals -/

/-- The wei credited to `p` by the withdrawals `ws`. -/
def credited (p : Address) : List Withdrawal → Nat
  | [] => 0
  | wd :: ws => (if p = wd.address then wd.amount * weiPerGwei else 0) + credited p ws

theorem applyWithdrawals_cons (w : World) (wd : Withdrawal) (ws : List Withdrawal) :
    applyWithdrawals w (wd :: ws) =
      applyWithdrawals (Tx.creditBalance w wd.address (wd.amount * weiPerGwei)) ws := rfl

@[simp] theorem applyWithdrawals_nil (w : World) : applyWithdrawals w [] = w := rfl

/-- **Balances after withdrawals**: each account gains exactly what is credited to it (in wei,
mod 2²⁵⁶). -/
theorem balance_applyWithdrawals (ws : List Withdrawal) :
    ∀ (w : World) (p : Address),
      (applyWithdrawals w ws).balance p = BitVec.ofNat 256 ((w.balance p).toNat + credited p ws) := by
  induction ws with
  | nil => intro w p; simp [credited]
  | cons wd ws ih =>
    intro w p
    rw [applyWithdrawals_cons, ih, balance_creditBalance]
    apply BitVec.eq_of_toNat_eq
    simp only [credited]
    split
    · rename_i h
      subst h
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_add_mod, Nat.add_assoc]
    · simp

/-- **Balances only increase** under withdrawals, while the sum fits in 256 bits. -/
theorem balance_le_applyWithdrawals {ws : List Withdrawal} {w : World} {p : Address}
    (h : (w.balance p).toNat + credited p ws < 2 ^ 256) :
    (w.balance p).toNat ≤ ((applyWithdrawals w ws).balance p).toNat := by
  rw [balance_applyWithdrawals, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  exact Nat.le_add_right _ _

/-- Withdrawals touch only their recipients. -/
theorem getElem?_applyWithdrawals_of_not_mem (ws : List Withdrawal) :
    ∀ (w : World) {p : Address}, (∀ wd ∈ ws, wd.address ≠ p) →
      (applyWithdrawals w ws)[p]? = w[p]? := by
  induction ws with
  | nil => intro w p _; rfl
  | cons wd ws ih =>
    intro w p hp
    rw [applyWithdrawals_cons, ih _ (fun wd' h => hp wd' (List.mem_cons_of_mem _ h)),
      getElem?_creditBalance_ne _ _ (fun e => hp wd (List.mem_cons_self ..) e.symm)]

/-- **Withdrawals keep nonce and code of every account.** -/
theorem nonce_code_applyWithdrawals (ws : List Withdrawal) :
    ∀ (w : World) (p : Address),
      ((applyWithdrawals w ws).account p).nonce = (w.account p).nonce ∧
        (applyWithdrawals w ws).code p = w.code p := by
  induction ws with
  | nil => intro w p; exact ⟨rfl, rfl⟩
  | cons wd ws ih =>
    intro w p
    rw [applyWithdrawals_cons]
    obtain ⟨h1, h2⟩ := ih (Tx.creditBalance w wd.address (wd.amount * weiPerGwei)) p
    exact ⟨h1.trans (nonce_creditBalance ..), h2.trans (code_creditBalance ..)⟩

/-- **Withdrawals keep storage and code of every account holding code.** -/
theorem keep_applyWithdrawals (ws : List Withdrawal) :
    ∀ {w : World} {p : Address}, (w.code p).size ≠ 0 → Keep p w (applyWithdrawals w ws) := by
  induction ws with
  | nil => intro w p _; exact keep_refl p w
  | cons wd ws ih =>
    intro w p hp
    rw [applyWithdrawals_cons]
    have h1 := keep_creditBalance (p := p) wd.address (wd.amount * weiPerGwei) hp
    exact h1.trans (ih (by rw [h1.code]; exact hp))

/-- A `GoodOk` predicate survives withdrawals. -/
theorem good_applyWithdrawals {P : Address → Prop} {Good : World → Prop} (S : GoodOk P Good)
    {w : World} (hw : Good w) (ws : List Withdrawal) : Good (Block.applyWithdrawals w ws) :=
  S.keep _ _ hw fun p hp => keep_applyWithdrawals ws (S.code w hw p hp)

/-- An invariant kept by every credit is kept by withdrawals. -/
theorem applyWithdrawals_induction {I : World → Prop}
    (hI : ∀ w a amount, I w → I (Tx.creditBalance w a amount)) (ws : List Withdrawal) :
    ∀ {w : World}, I w → I (applyWithdrawals w ws) := by
  induction ws with
  | nil => intro w hw; exact hw
  | cons wd ws ih => intro w hw; rw [applyWithdrawals_cons]; exact ih (hI _ _ _ hw)

/-! ## EIP-161 clean-up -/

/-- `w'` is `w` with some empty accounts erased. -/
def EraseEmpty (w w' : World) : Prop :=
  ∀ p, w'[p]? = w[p]? ∨ (w'[p]? = none ∧ (w.account p).isEmpty = true)

theorem EraseEmpty.refl (w : World) : EraseEmpty w w := fun _ => .inl rfl

theorem EraseEmpty.trans {w₁ w₂ w₃ : World} (h₁ : EraseEmpty w₁ w₂) (h₂ : EraseEmpty w₂ w₃) :
    EraseEmpty w₁ w₃ := by
  intro p
  rcases h₂ p with h | ⟨h, he⟩
  · rw [h]; exact h₁ p
  · refine .inr ⟨h, ?_⟩
    rcases h₁ p with h' | ⟨h', he'⟩
    · simpa only [World.account, Std.ExtTreeMap.getD_eq_getD_getElem?, h'] using he
    · exact he'

/-- One step of `destroyTouchedEmpty`. -/
def eraseIfEmpty (w : World) (a : Address) : World :=
  match w.account? a with
  | some acc => if acc.isEmpty then w.erase a else w
  | none => w

theorem eraseEmpty_eraseIfEmpty (w : World) (a : Address) : EraseEmpty w (eraseIfEmpty w a) := by
  intro p
  unfold eraseIfEmpty
  split
  · rename_i acc hacc
    split
    · rename_i he
      by_cases hp : p = a
      · subst hp
        refine .inr ⟨by simp, ?_⟩
        simp only [World.account?] at hacc
        simpa only [World.account, Std.ExtTreeMap.getD_eq_getD_getElem?, hacc,
          Option.getD_some] using he
      · have hp' : ¬ a = p := fun e => hp e.symm
        exact .inl (by simp [Std.ExtTreeMap.getElem?_erase, hp'])
    · exact .inl rfl
  · exact .inl rfl

theorem destroyTouchedEmpty_eq (w : World) (t : AddressSet) :
    Tx.destroyTouchedEmpty w t = t.toList.foldl eraseIfEmpty w := by
  unfold Tx.destroyTouchedEmpty
  rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
  rfl

theorem eraseEmpty_foldl (l : List Address) :
    ∀ w : World, EraseEmpty w (l.foldl eraseIfEmpty w) := by
  induction l with
  | nil => exact EraseEmpty.refl
  | cons a l ih => intro w; exact (eraseEmpty_eraseIfEmpty w a).trans (ih _)

/-- **`destroyTouchedEmpty` only erases empty accounts.** -/
theorem eraseEmpty_destroyTouchedEmpty (w : World) (t : AddressSet) :
    EraseEmpty w (Tx.destroyTouchedEmpty w t) := by
  rw [destroyTouchedEmpty_eq]; exact eraseEmpty_foldl _ w

theorem getElem?_foldl_eraseIfEmpty_of_not_mem (l : List Address) :
    ∀ (w : World) {p : Address}, p ∉ l → (l.foldl eraseIfEmpty w)[p]? = w[p]? := by
  induction l with
  | nil => intro w p _; rfl
  | cons a l ih =>
    intro w p hp
    simp only [List.mem_cons, not_or] at hp
    rw [List.foldl_cons, ih _ hp.2]
    unfold eraseIfEmpty
    have hp' : ¬ a = p := fun e => hp.1 e.symm
    split
    · split
      · simp [Std.ExtTreeMap.getElem?_erase, hp']
      · rfl
    · rfl

/-- `destroyTouchedEmpty` touches only the touched accounts. -/
theorem getElem?_destroyTouchedEmpty_of_not_mem (w : World) {t : AddressSet} {p : Address}
    (hp : p ∉ t) : (Tx.destroyTouchedEmpty w t)[p]? = w[p]? := by
  rw [destroyTouchedEmpty_eq]
  exact getElem?_foldl_eraseIfEmpty_of_not_mem _ w (fun h => hp (Std.ExtTreeSet.mem_toList.1 h))

theorem destroyTouchedEmpty_empty (w : World) : Tx.destroyTouchedEmpty w ∅ = w := by
  rw [destroyTouchedEmpty_eq, Std.ExtTreeSet.toList_eq_nil_iff.2 rfl]; rfl

theorem eraseIfEmpty_idem (w : World) (a : Address) :
    eraseIfEmpty (eraseIfEmpty w a) a = eraseIfEmpty w a := by
  unfold eraseIfEmpty
  cases hacc : w.account? a with
  | none => simp only [hacc]
  | some acc =>
    by_cases he : acc.isEmpty = true
    · have : World.account? (Std.ExtTreeMap.erase w a) a = none := by simp [World.account?]
      simp only [he, ↓reduceIte, this]
    · simp only [he, Bool.false_eq_true, ↓reduceIte, hacc]

theorem foldl_eraseIfEmpty_const {a : Address} :
    ∀ (l : List Address) (w : World), (∀ x ∈ l, x = a) →
      l.foldl eraseIfEmpty (eraseIfEmpty w a) = eraseIfEmpty w a := by
  intro l
  induction l with
  | nil => intro w _; rfl
  | cons x l ih =>
    intro w hl
    rw [List.foldl_cons, hl x (List.mem_cons_self ..), eraseIfEmpty_idem]
    exact ih w fun y hy => hl y (List.mem_cons_of_mem _ hy)

/-- Cleaning up a single touched account. -/
theorem destroyTouchedEmpty_singleton (w : World) (a : Address) :
    Tx.destroyTouchedEmpty w ((∅ : AddressSet).insert a) = eraseIfEmpty w a := by
  rw [destroyTouchedEmpty_eq]
  have hall : ∀ x ∈ ((∅ : AddressSet).insert a).toList, x = a := by
    intro x hx
    rcases Std.ExtTreeSet.mem_insert.1 (Std.ExtTreeSet.mem_toList.1 hx) with h | h
    · exact (Std.LawfulEqCmp.eq_of_compare h).symm
    · exact absurd h Std.ExtTreeSet.not_mem_empty
  have hmem : a ∈ ((∅ : AddressSet).insert a).toList :=
    Std.ExtTreeSet.mem_toList.2 Std.ExtTreeSet.mem_insert_self
  generalize ((∅ : AddressSet).insert a).toList = l at hall hmem
  cases l with
  | nil => cases hmem
  | cons x l =>
    rw [List.foldl_cons, hall x (List.mem_cons_self ..)]
    exact foldl_eraseIfEmpty_const l w fun y hy => hall y (List.mem_cons_of_mem _ hy)

theorem eraseIfEmpty_eq (w : World) (a : Address) :
    eraseIfEmpty w a = if accountExistsAndIsEmpty w a then w.erase a else w := by
  unfold eraseIfEmpty accountExistsAndIsEmpty
  split <;> simp_all

namespace EraseEmpty

variable {w w' : World}

theorem account (h : EraseEmpty w w') (p : Address) :
    w'.account p = w.account p ∨ (w'.account p = {} ∧ (w.account p).isEmpty = true) := by
  rcases h p with h | ⟨h, he⟩
  · exact .inl (by simp only [World.account, Std.ExtTreeMap.getD_eq_getD_getElem?, h])
  · exact .inr ⟨by simp only [World.account, Std.ExtTreeMap.getD_eq_getD_getElem?, h,
      Option.getD_none], he⟩

/-- Nonce, balance and code of every account are unchanged. -/
theorem nonce_balance_code (h : EraseEmpty w w') (p : Address) :
    (w'.account p).nonce = (w.account p).nonce ∧ w'.balance p = w.balance p ∧
      w'.code p = w.code p := by
  rcases h.account p with h | ⟨h, he⟩
  · simp only [World.balance, World.code, h, and_self]
  · simp only [Account.isEmpty, Bool.and_eq_true, decide_eq_true_eq] at he
    simp only [World.balance, World.code, h]
    exact ⟨he.1.1.symm, he.1.2.symm, (byteArray_eq_empty he.2).symm⟩

/-- An account holding code is not erased. -/
theorem account_of_code (h : EraseEmpty w w') {p : Address} (hp : (w.code p).size ≠ 0) :
    w'.account p = w.account p := by
  rcases h.account p with h | ⟨-, he⟩
  · exact h
  · simp only [Account.isEmpty, Bool.and_eq_true, decide_eq_true_eq] at he
    exact absurd he.2 hp

theorem keep (h : EraseEmpty w w') {p : Address} (hp : (w.code p).size ≠ 0) : Keep p w w' := by
  have := h.account_of_code hp
  exact ⟨by rw [this], by rw [this]⟩

end EraseEmpty

/-- A `GoodOk` predicate survives the EIP-161 clean-up. -/
theorem good_destroyTouchedEmpty {P : Address → Prop} {Good : World → Prop}
    (S : GoodOk P Good) {w : World} (hw : Good w) (t : AddressSet) :
    Good (Tx.destroyTouchedEmpty w t) :=
  S.keep _ _ hw fun p hp => (eraseEmpty_destroyTouchedEmpty w t).keep (S.code w hw p hp)

end EvmLogic.Chain
