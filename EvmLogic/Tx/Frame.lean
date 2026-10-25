import EvmLogic.Tx.Process

/-!
# What the prefix and suffix of a transaction change

`Tx.process` wraps the top-level message in a **prefix** (`prefixWorld`: the sender's nonce is
incremented and the upfront fees debited) and a **suffix** (`suffixWorld`: the unused gas
refunded to the sender, the priority fee credited to the coinbase, the self-destructed accounts
erased, the touched empty accounts destroyed). Their frame conditions:

* `keep_prefixWorld`: the prefix keeps storage and code of **every** account, and
  `balance_prefixWorld` changes only the sender's balance.
* `keep_suffixWorld`: the suffix keeps storage and code of every account that holds code and is
  not in `accountsToDelete`; `balance_suffixWorld` changes balances only by the two credits
  (to the sender and to the coinbase) and by erasure.
* `destroyTouchedEmpty` never changes a balance, a nonce or a code (`destroyTouchedEmpty_account`:
  it erases only empty accounts), so it never erases an account holding code.
-/

namespace EvmLogic.Tx
open EvmLean EvmLean.Interpreter EvmLean.Tx EvmLogic.Program.Nested

/-! ## `modifyState` -/

theorem account_modifyState_ne (w : World) {a b : Address} (f : Account → Account) (h : b ≠ a) :
    (modifyState w a f).account b = w.account b := by
  have hne : ¬ compare a b = .eq := fun e => h (Std.LawfulEqCmp.eq_of_compare e).symm
  unfold modifyState
  dsimp only
  split <;> simp [World.account, Std.ExtTreeMap.getD_erase, Std.ExtTreeMap.getD_insert, hne]

theorem account_modifyState_self (w : World) (a : Address) {f : Account → Account}
    (h : (f (w.account a)).isEmpty = false) : (modifyState w a f).account a = f (w.account a) := by
  unfold modifyState
  dsimp only
  simp only [h, Bool.false_eq_true, ite_false]
  simp [World.account]

/-! ## The prefix -/

theorem account_prefixWorld (w : World) (s : Address) (bal : Word) (a : Address) :
    (prefixWorld w s bal).account a = if a = s then
      { w.account s with nonce := (w.account s).nonce + 1, balance := bal } else w.account a := by
  unfold prefixWorld setAccountBalance incrementNonce
  by_cases h : a = s
  · subst h
    have h1 : ({ w.account a with nonce := (w.account a).nonce + 1 } : Account).isEmpty = false := by
      simp [Account.isEmpty]
    rw [account_modifyState_self _ _ (by rw [account_modifyState_self _ _ h1]; simp [Account.isEmpty]),
      account_modifyState_self _ _ h1]
    simp
  · simp only [h, ite_false]
    rw [account_modifyState_ne _ _ h, account_modifyState_ne _ _ h]

/-- **The prefix keeps storage and code of every account.** -/
theorem keep_prefixWorld (w : World) (s : Address) (bal : Word) (p : Address) :
    Keep p w (prefixWorld w s bal) := by
  unfold Keep
  rw [account_prefixWorld]
  split
  · subst_vars; exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- **The prefix changes only the sender's balance.** -/
theorem balance_prefixWorld (w : World) (s : Address) (bal : Word) (a : Address) :
    (prefixWorld w s bal).balance a = if a = s then bal else w.balance a := by
  unfold World.balance
  rw [account_prefixWorld]
  split <;> rfl

theorem code_prefixWorld (w : World) (s : Address) (bal : Word) (a : Address) :
    (prefixWorld w s bal).code a = w.code a := (keep_prefixWorld w s bal a).code

/-! ## Credits -/

theorem balance_creditBalance (w : World) (a : Address) (k : Nat) (b : Address) :
    (creditBalance w a k).balance b =
      if b = a then BitVec.ofNat 256 ((w.balance a).toNat + k) else w.balance b := by
  unfold creditBalance
  rw [balance_modifyState]
  rfl

theorem keep_creditBalance {w : World} {p : Address} (hp : (w.code p).size ≠ 0) (a : Address)
    (k : Nat) : Keep p w (creditBalance w a k) :=
  keep_modifyState (fun _ => ⟨rfl, rfl⟩) hp

theorem code_creditBalance (w : World) (a : Address) (k : Nat) (b : Address) :
    (creditBalance w a k).code b = w.code b := by
  unfold creditBalance; exact code_modifyState (by intro; rfl) b

/-- A credit that does not wrap around increases the balance by the amount. -/
theorem toNat_balance_creditBalance_self {w : World} {a : Address} {k : Nat}
    (h : (w.balance a).toNat + k < 2 ^ 256) :
    ((creditBalance w a k).balance a).toNat = (w.balance a).toNat + k := by
  rw [balance_creditBalance]
  simp only [ite_true, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

/-! ## Erasing the self-destructed accounts -/

theorem account_foldl_erase_list (l : List Address) (w : World) (b : Address) :
    (l.foldl (fun w a => w.erase a) w).account b = if b ∈ l then {} else w.account b := by
  induction l generalizing w with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, List.mem_cons]
    by_cases hb : b ∈ xs
    · simp [hb]
    · by_cases hx : b = x
      · subst hx; simp [World.account]
      · have hne : ¬ compare x b = .eq := fun e => hx (Std.LawfulEqCmp.eq_of_compare e).symm
        simp [hb, hx, World.account, Std.ExtTreeMap.getD_erase, hne]

/-- Erasing a set of accounts: the erased ones become the empty account, the others are kept. -/
theorem account_foldl_erase (s : AddressSet) (w : World) (b : Address) :
    (s.foldl (fun w a => w.erase a) w).account b = if b ∈ s then {} else w.account b := by
  rw [Std.ExtTreeSet.foldl_eq_foldl_toList, account_foldl_erase_list]
  simp [Std.ExtTreeSet.mem_toList]

/-! ## Destroying the touched empty accounts -/

theorem destroyTouchedEmpty_list (l : List Address) (w₀ w : World)
    (hw : ∀ b, w.account b = w₀.account b ∨ ((w₀.account b).isEmpty = true ∧ w.account b = {}))
    (b : Address) :
    (l.foldl (fun w a => match w.account? a with
      | some acc => if acc.isEmpty then w.erase a else w
      | none => w) w).account b = w₀.account b ∨
      ((w₀.account b).isEmpty = true ∧
        (l.foldl (fun w a => match w.account? a with
          | some acc => if acc.isEmpty then w.erase a else w
          | none => w) w).account b = {}) := by
  induction l generalizing w with
  | nil => exact hw b
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih
    intro c
    split
    · rename_i acc hacc
      split
      · rename_i he
        have hxa : w.account x = acc := by
          simp only [World.account?] at hacc
          simp [World.account, Std.ExtTreeMap.getD_eq_getD_getElem?, hacc]
        by_cases hc : c = x
        · subst hc
          right
          refine ⟨?_, by simp [World.account]⟩
          rcases hw c with h | h
          · rw [← h, hxa]; exact he
          · exact h.1
        · have hne : ¬ compare x c = .eq := fun e => hc (Std.LawfulEqCmp.eq_of_compare e).symm
          have : World.account (w.erase x) c = w.account c := by
            simp [World.account, Std.ExtTreeMap.getD_erase, hne]
          rw [this]; exact hw c
      · exact hw c
    · exact hw c

/-- **`destroyTouchedEmpty` erases only empty accounts**: every account is kept, or was empty
and is now the empty account. -/
theorem destroyTouchedEmpty_account (w : World) (t : AddressSet) (b : Address) :
    (destroyTouchedEmpty w t).account b = w.account b ∨
      ((w.account b).isEmpty = true ∧ (destroyTouchedEmpty w t).account b = {}) := by
  unfold destroyTouchedEmpty
  rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
  exact destroyTouchedEmpty_list _ w w (fun _ => .inl rfl) b

theorem destroyTouchedEmpty_balance (w : World) (t : AddressSet) (b : Address) :
    (destroyTouchedEmpty w t).balance b = w.balance b := by
  unfold World.balance
  rcases destroyTouchedEmpty_account w t b with h | ⟨he, h⟩
  · rw [h]
  · rw [h]
    simp only [Account.isEmpty, Bool.and_eq_true, decide_eq_true_eq] at he
    exact he.1.2.symm

theorem destroyTouchedEmpty_code (w : World) (t : AddressSet) (b : Address) :
    (destroyTouchedEmpty w t).code b = w.code b := by
  unfold World.code
  rcases destroyTouchedEmpty_account w t b with h | ⟨he, h⟩
  · rw [h]
  · rw [h]
    simp only [Account.isEmpty, Bool.and_eq_true, decide_eq_true_eq] at he
    exact (eq_empty_of_size he.2).symm

theorem destroyTouchedEmpty_nonce (w : World) (t : AddressSet) (b : Address) :
    ((destroyTouchedEmpty w t).account b).nonce = (w.account b).nonce := by
  rcases destroyTouchedEmpty_account w t b with h | ⟨he, h⟩
  · rw [h]
  · rw [h]
    simp only [Account.isEmpty, Bool.and_eq_true, decide_eq_true_eq] at he
    exact he.1.1.symm

/-- `destroyTouchedEmpty` keeps every account that holds code. -/
theorem keep_destroyTouchedEmpty {w : World} {p : Address} (hp : (w.code p).size ≠ 0)
    (t : AddressSet) : Keep p w (destroyTouchedEmpty w t) := by
  rcases destroyTouchedEmpty_account w t p with h | ⟨he, -⟩
  · unfold Keep; rw [h]; exact ⟨rfl, rfl⟩
  · simp only [Account.isEmpty, Bool.and_eq_true, decide_eq_true_eq] at he
    exact absurd he.2 hp

/-! ## The suffix -/

/-- The world after the two credits of the suffix. -/
abbrev creditedWorld (r : MessageResult) (sender coinbase : Address) (refund reward : Nat) :
    World :=
  creditBalance (creditBalance r.world sender refund) coinbase reward

theorem account_suffixWorld (r : MessageResult) (sender coinbase : Address) (refund reward : Nat)
    {p : Address} (hd : p ∉ r.accountsToDelete) :
    (suffixWorld r sender coinbase refund reward).account p =
      (creditedWorld r sender coinbase refund reward).account p ∨
    (((creditedWorld r sender coinbase refund reward).account p).isEmpty = true ∧
      (suffixWorld r sender coinbase refund reward).account p = {}) := by
  unfold suffixWorld
  have he := account_foldl_erase r.accountsToDelete (creditedWorld r sender coinbase refund reward) p
  simp only [hd, ite_false] at he
  rcases destroyTouchedEmpty_account (r.accountsToDelete.foldl (fun w a => w.erase a)
    (creditedWorld r sender coinbase refund reward)) r.touchedAccounts p with h | h
  · exact .inl (h.trans he)
  · rw [he] at h; exact .inr h

/-- **The suffix keeps storage and code of every account that holds code and is not
self-destructed.** -/
theorem keep_suffixWorld {r : MessageResult} {p : Address} (hp : (r.world.code p).size ≠ 0)
    (hd : p ∉ r.accountsToDelete) (sender coinbase : Address) (refund reward : Nat) :
    Keep p r.world (suffixWorld r sender coinbase refund reward) := by
  have k1 := keep_creditBalance hp sender refund
  have k2 := keep_creditBalance (by rw [k1.code]; exact hp) coinbase reward
  have k12 := k1.trans k2
  rcases account_suffixWorld r sender coinbase refund reward hd with h | ⟨he, -⟩
  · unfold Keep at k12 ⊢; rw [h]; exact k12
  · simp only [Account.isEmpty, Bool.and_eq_true, decide_eq_true_eq] at he
    exact absurd (by rw [← k12.code]; exact he.2) hp

/-- **The suffix changes balances only by its two credits**, except at self-destructed accounts. -/
theorem balance_suffixWorld (r : MessageResult) (sender coinbase : Address) (refund reward : Nat)
    {p : Address} (hd : p ∉ r.accountsToDelete) :
    (suffixWorld r sender coinbase refund reward).balance p =
      (creditedWorld r sender coinbase refund reward).balance p := by
  unfold suffixWorld
  rw [destroyTouchedEmpty_balance]
  unfold World.balance
  rw [account_foldl_erase]
  simp [hd]

theorem code_suffixWorld (r : MessageResult) (sender coinbase : Address) (refund reward : Nat)
    {p : Address} (hd : p ∉ r.accountsToDelete) :
    (suffixWorld r sender coinbase refund reward).code p = r.world.code p := by
  unfold suffixWorld
  rw [destroyTouchedEmpty_code]
  unfold World.code
  rw [account_foldl_erase]
  simp only [hd, ite_false]
  show (creditedWorld r sender coinbase refund reward).code p = r.world.code p
  rw [code_creditBalance, code_creditBalance]

/-- A self-destructed account is the empty account after the suffix. -/
theorem account_suffixWorld_of_mem (r : MessageResult) (sender coinbase : Address)
    (refund reward : Nat) {p : Address} (hd : p ∈ r.accountsToDelete) :
    (suffixWorld r sender coinbase refund reward).account p = {} := by
  unfold suffixWorld
  have he := account_foldl_erase r.accountsToDelete (creditedWorld r sender coinbase refund reward) p
  simp only [hd, ite_true] at he
  rcases destroyTouchedEmpty_account (r.accountsToDelete.foldl (fun w a => w.erase a)
    (creditedWorld r sender coinbase refund reward)) r.touchedAccounts p with h | h
  · exact h.trans he
  · exact h.2

end EvmLogic.Tx
