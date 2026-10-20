import EvmLean

/-!
# Storage, world-state and access-set lemmas

Read-after-write lemmas for `Storage`, `World` (`sload`/`sstore`, balances under `transfer` and
`moveEther`) and the EIP-2929 warm-key set, from the `Std.ExtTreeMap` `getD` lemmas.
-/

namespace EvmLean

namespace Storage

@[simp] theorem get_empty (k : Word) : Storage.get ∅ k = 0 := by
  simp [Storage.get]

@[simp] theorem get_set_self (s : Storage) (k v : Word) : (s.set k v).get k = v := by
  unfold Storage.set Storage.get
  split
  · simp_all
  · simp

theorem get_set_ne (s : Storage) {k k' : Word} (v : Word) (h : k' ≠ k) :
    (s.set k v).get k' = s.get k' := by
  have h' : ¬ k = k' := fun e => h e.symm
  unfold Storage.set Storage.get
  split <;> simp [Std.ExtTreeMap.getD_insert, Std.ExtTreeMap.getD_erase, h']

theorem get_set (s : Storage) (k v k' : Word) :
    (s.set k v).get k' = if k' = k then v else s.get k' := by
  split
  · subst_vars; exact get_set_self s _ v
  · exact get_set_ne s v ‹_›

end Storage

namespace World

@[simp] theorem account_modify_self (w : World) (a : Address) (f : Account → Account) :
    (w.modify a f).account a = f (w.account a) := by
  simp [World.modify, World.account]

theorem account_modify_ne (w : World) {a b : Address} (f : Account → Account) (h : b ≠ a) :
    (w.modify a f).account b = w.account b := by
  have h' : ¬ a = b := fun e => h e.symm
  simp [World.modify, World.account, Std.ExtTreeMap.getD_insert, h']

@[simp] theorem sload_sstore_self (w : World) (a : Address) (k v : Word) :
    (w.sstore a k v).sload a k = v := by
  simp [World.sstore, World.sload]

theorem sload_sstore_ne_key (w : World) (a : Address) {k k' : Word} (v : Word) (h : k' ≠ k) :
    (w.sstore a k v).sload a k' = w.sload a k' := by
  simp only [World.sstore, World.sload, account_modify_self]
  exact Storage.get_set_ne _ v h

theorem sload_sstore_ne_addr (w : World) {a b : Address} (k v k' : Word) (h : b ≠ a) :
    (w.sstore a k v).sload b k' = w.sload b k' := by
  simp only [World.sstore, World.sload, account_modify_ne _ _ h]

theorem sload_sstore (w : World) (a : Address) (k v : Word) (b : Address) (k' : Word) :
    (w.sstore a k v).sload b k' = if b = a ∧ k' = k then v else w.sload b k' := by
  by_cases hb : b = a
  · subst hb
    by_cases hk : k' = k
    · subst hk; simp
    · simp only [hk, and_false, ite_false]; exact sload_sstore_ne_key w b v hk
  · simp only [hb, false_and, ite_false]; exact sload_sstore_ne_addr w k v k' hb

@[simp] theorem balance_sstore (w : World) (a : Address) (k v : Word) (b : Address) :
    (w.sstore a k v).balance b = w.balance b := by
  by_cases h : b = a
  · subst h; simp [World.sstore, World.balance]
  · simp only [World.sstore, World.balance, account_modify_ne _ _ h]

@[simp] theorem code_sstore (w : World) (a : Address) (k v : Word) (b : Address) :
    (w.sstore a k v).code b = w.code b := by
  by_cases h : b = a
  · subst h; simp [World.sstore, World.code]
  · simp only [World.sstore, World.code, account_modify_ne _ _ h]

theorem balance_setBalance (w : World) (a : Address) (v : Word) (b : Address) :
    (w.setBalance a v).balance b = if b = a then v else w.balance b := by
  split
  · subst_vars; simp [World.setBalance, World.balance]
  · simp only [World.setBalance, World.balance, account_modify_ne _ _ ‹_›]

theorem isSome_transfer (w : World) (src dst : Address) (v : Word) :
    (w.transfer src dst v).isSome = decide (v.toNat ≤ (w.balance src).toNat) := by
  unfold World.transfer
  dsimp only
  split <;> simp_all

theorem balance_transfer {w w' : World} {src dst : Address} {v : Word}
    (h : w.transfer src dst v = some w') (hne : src ≠ dst) (b : Address) :
    w'.balance b = if b = src then w.balance src - v
      else if b = dst then w.balance dst + v else w.balance b := by
  unfold World.transfer at h
  dsimp only at h
  split at h
  · cases h
    have hne' : dst ≠ src := fun e => hne e.symm
    simp only [balance_setBalance, hne', ite_false]
    by_cases hb : b = src
    · subst hb; simp [hne]
    · by_cases hd : b = dst
      · subst hd; simp [hb]
      · simp [hb, hd]
  · cases h

theorem balance_add_balance_transfer {w w' : World} {src dst : Address} {v : Word}
    (h : w.transfer src dst v = some w') (hne : src ≠ dst) :
    w'.balance src + w'.balance dst = w.balance src + w.balance dst := by
  have hne' : dst ≠ src := fun e => hne e.symm
  rw [balance_transfer h hne, balance_transfer h hne]
  simp only [ite_true, hne', ite_false]
  bv_omega

end World

namespace Interpreter

/-- Balance after `modifyState` (which deletes the account if it becomes empty; an empty
account has zero balance, so the balance is the same either way). -/
theorem balance_modifyState (w : World) (a : Address) (f : Account → Account) (b : Address) :
    (modifyState w a f).balance b = if b = a then (f (w.account a)).balance else w.balance b := by
  unfold modifyState
  dsimp only
  have hne : ∀ {x y : Address}, x ≠ y → ¬ y = x := fun h e => h e.symm
  by_cases he : (f (w.account a)).isEmpty = true
  · simp only [he, ite_true]
    by_cases hb : b = a
    · subst hb
      have hbal : (f (w.account b)).balance = 0 := by
        simp only [Account.isEmpty, Bool.and_eq_true, decide_eq_true_eq] at he
        exact he.1.2
      simp only [World.balance, World.account, Std.ExtTreeMap.getD_erase_self, ite_true]
      exact hbal.symm
    · simp [World.balance, World.account, Std.ExtTreeMap.getD_erase, hne hb, hb]
  · simp only [he, Bool.false_eq_true, ite_false]
    by_cases hb : b = a
    · subst hb; simp [World.balance, World.account]
    · simp [World.balance, World.account, Std.ExtTreeMap.getD_insert, hne hb, hb]

theorem balance_moveEther (w : World) {src dst : Address} (amount : Word) (hne : src ≠ dst)
    (b : Address) :
    (moveEther w src dst amount).balance b = if b = src then w.balance src - amount
      else if b = dst then w.balance dst + amount else w.balance b := by
  have hne' : dst ≠ src := fun e => hne e.symm
  simp only [moveEther, balance_modifyState]
  by_cases hb : b = src
  · subst hb; simp [hne, World.balance]
  · have := balance_modifyState w src
      (fun acc => { acc with balance := acc.balance - amount }) b
    simp only [hb, ite_false, World.balance] at this
    by_cases hd : b = dst
    · subst hd
      simp only [hb, ite_true, ite_false, World.balance, this]
    · simp only [hb, hd, ite_false, World.balance]

theorem storageKeyWarm_addStorageKey (s : StorageKeySet) (a : Address) (k : Word)
    (a' : Address) (k' : Word) :
    storageKeyWarm (addStorageKey s a k) a' k' = ((a' = a ∧ k' = k) || storageKeyWarm s a' k') := by
  unfold storageKeyWarm addStorageKey
  by_cases ha : a' = a
  · subst ha
    simp only [Std.ExtTreeMap.getD_insert_self, Std.ExtTreeSet.contains_insert, true_and]
    by_cases hk : k' = k
    · subst hk; simp
    · have : ¬ k = k' := fun e => hk e.symm
      simp [hk, this]
  · have : ¬ a = a' := fun e => ha e.symm
    simp [ha, Std.ExtTreeMap.getD_insert, this]

theorem addStorageKey_of_warm {s : StorageKeySet} {a : Address} {k : Word}
    (h : storageKeyWarm s a k = true) : addStorageKey s a k = s := by
  unfold storageKeyWarm at h
  unfold addStorageKey
  have h1 : (s.getD a ∅).insert k = s.getD a ∅ := by
    apply Std.ExtTreeSet.ext_contains
    intro x
    rw [Std.ExtTreeSet.contains_insert]
    by_cases hx : k = x
    · subst hx; simp [h]
    · simp [hx]
  rw [h1]
  apply Std.ExtTreeMap.ext_getElem?
  intro x
  rw [Std.ExtTreeMap.getElem?_insert]
  by_cases hx : a = x
  · subst hx
    rw [Std.ExtTreeMap.getD_eq_getD_getElem?] at h
    cases hs : s[a]? with
    | none => simp [hs] at h
    | some t => simp [Std.ExtTreeMap.getD_eq_getD_getElem?, hs]
  · simp [hx]

@[simp] theorem storageKeyWarm_empty (a : Address) (k : Word) :
    storageKeyWarm ∅ a k = false := by
  simp [storageKeyWarm]

@[simp] theorem storageKeyWarm_addStorageKey_self (s : StorageKeySet) (a : Address) (k : Word) :
    storageKeyWarm (addStorageKey s a k) a k = true := by
  simp [storageKeyWarm_addStorageKey]

end Interpreter

end EvmLean
