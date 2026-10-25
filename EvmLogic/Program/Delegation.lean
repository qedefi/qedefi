import EvmLogic.State
import EvmLogic.Program.Nested.Frame

/-!
# EIP-7702 authorizations at the top level

A type-4 transaction carries authorizations; `setDelegation` applies them before the top-level
message runs, and `applyTopLevelDelegation` then resolves the target's delegation designator.
This module bounds what they can do to the world and the message:

* `DelegFrame w w'`: every balance is kept; every account either is unchanged, or held empty
  code or a designator in `w` (`Delegable`) and holds empty code or a designator in `w'`
  (`DelegCode`), with its storage kept or (when the account became empty and was deleted)
  cleared. An account with real code (nonempty, not a designator) is unchanged.
* `setDelegation_induct`: a world predicate closed under one authorization (set the code of an
  account holding empty code or a designator to empty code or a designator, then bump its
  nonce) holds after `setDelegation`. `setDelegation_frame`: the frame relation, and the warm set
  only grows.
* `applyTopLevelDelegation_frame`: the delegated world is in the frame relation with the
  original one, and the message keeps its target, caller, depth, staticness, gas and value
  transfer; a message that runs its target's own code still does, unless the target (after the
  authorizations) holds a designator, in which case it runs the delegate's code.
-/

namespace EvmLogic.Program
open EvmLean EvmLean.Interpreter EvmLogic.Program.Nested

/-- Code an authorization may replace: empty code or a delegation designator. -/
def Delegable (c : ByteArray) : Prop := c.size = 0 ∨ isValidDelegation c = true

/-- Code an authorization installs: empty code (delegation to address zero) or a designator. -/
def DelegCode (c : ByteArray) : Prop := c = .empty ∨ ∃ d, c = delegationCode d

/-- **The frame of EIP-7702 authorizations.** Every balance is kept, and every account is either
unchanged or held empty code or a designator before and holds empty code or a designator after,
with its storage kept or cleared. -/
structure DelegFrame (w w' : World) : Prop where
  balance : ∀ a, w'.balance a = w.balance a
  account : ∀ a, w'.account a = w.account a ∨
    (Delegable (w.code a) ∧ DelegCode (w'.code a) ∧
      ((w'.account a).storage = (w.account a).storage ∨ (w'.account a).storage = ∅))

theorem DelegFrame.refl (w : World) : DelegFrame w w := ⟨fun _ => rfl, fun _ => .inl rfl⟩

theorem DelegFrame.trans {w₁ w₂ w₃ : World} (h₁ : DelegFrame w₁ w₂) (h₂ : DelegFrame w₂ w₃) :
    DelegFrame w₁ w₃ := by
  refine ⟨fun a => (h₂.balance a).trans (h₁.balance a), fun a => ?_⟩
  rcases h₁.account a with e₁ | ⟨d₁, c₁, s₁⟩ <;> rcases h₂.account a with e₂ | ⟨d₂, c₂, s₂⟩
  · exact .inl (e₂.trans e₁)
  · refine .inr ⟨?_, c₂, ?_⟩
    · have : w₂.code a = w₁.code a := by simp only [World.code, e₁]
      rw [← this]; exact d₂
    · rw [← e₁]; exact s₂
  · refine .inr ⟨d₁, ?_, ?_⟩
    · have : w₃.code a = w₂.code a := by simp only [World.code, e₂]
      rw [this]; exact c₁
    · rw [e₂]; exact s₁
  · refine .inr ⟨d₁, c₂, ?_⟩
    rcases s₂ with s₂ | s₂
    · rw [s₂]; exact s₁
    · exact .inr s₂

/-- A designator is not empty code. -/
theorem size_delegationCode (d : Address) : (delegationCode d).size = 23 := by
  simp only [delegationCode, ByteArray.size_append, Bytes.size_ofAddress, eoaDelegationMarker]
  rfl

/-- `delegatedAddress?` is `none` exactly on code that is not a designator. -/
theorem delegatedAddress?_eq_none {c : ByteArray} :
    delegatedAddress? c = none ↔ isValidDelegation c = false := by
  unfold delegatedAddress?
  split <;> simp_all

/-- An account with real code (nonempty, not a designator) is unchanged. -/
theorem DelegFrame.account_eq {w w' : World} (h : DelegFrame w w') {a : Address}
    (hsize : (w.code a).size ≠ 0) (hdel : delegatedAddress? (w.code a) = none) :
    w'.account a = w.account a := by
  rcases h.account a with e | ⟨d, -, -⟩
  · exact e
  · rcases d with d | d
    · exact absurd d hsize
    · rw [delegatedAddress?_eq_none.1 hdel] at d; cases d

theorem DelegFrame.keep {w w' : World} (h : DelegFrame w w') {a : Address}
    (hsize : (w.code a).size ≠ 0) (hdel : delegatedAddress? (w.code a) = none) : Keep a w w' := by
  have e := h.account_eq hsize hdel
  exact ⟨by rw [e], by rw [e]⟩

/-- The code of every account is kept, or replaced as an authorization allows. -/
theorem DelegFrame.code {w w' : World} (h : DelegFrame w w') (a : Address) :
    w'.code a = w.code a ∨ (Delegable (w.code a) ∧ DelegCode (w'.code a)) := by
  rcases h.account a with e | ⟨d, c, -⟩
  · exact .inl (by simp only [World.code, e])
  · exact .inr ⟨d, c⟩

theorem DelegFrame.sload {w w' : World} (h : DelegFrame w w') (a : Address) (k : Word) :
    w'.sload a k = w.sload a k ∨ (Delegable (w.code a) ∧ w'.sload a k = 0) := by
  rcases h.account a with e | ⟨d, -, s | s⟩
  · exact .inl (by simp only [World.sload, e])
  · exact .inl (by simp only [World.sload, s])
  · exact .inr ⟨d, by simp [World.sload, s]⟩

/-! ## One authorization -/

theorem mem_insert_of_mem' {s : AddressSet} {a x : Address} (h : x ∈ s) : x ∈ s.insert a :=
  Std.ExtTreeSet.mem_insert.2 (.inr h)

theorem account_modifyState (w : World) (a : Address) (f : Account → Account) (b : Address) :
    (modifyState w a f).account b =
      if b = a then (if (f (w.account a)).isEmpty then {} else f (w.account a))
      else w.account b := by
  unfold modifyState
  have hne : ∀ {x y : Address}, x ≠ y → ¬ y = x := fun h e => h e.symm
  by_cases he : (f (w.account a)).isEmpty = true
  · simp only [he, ite_true]
    by_cases hb : b = a
    · subst hb; simp [World.account]
    · simp [World.account, Std.ExtTreeMap.getD_erase, hb, hne hb]
  · simp only [he, Bool.false_eq_true, ite_false]
    by_cases hb : b = a
    · subst hb; simp [World.account]
    · simp [World.account, Std.ExtTreeMap.getD_insert, hb, hne hb]

theorem account_incrementNonce_self (w : World) (a : Address) :
    (incrementNonce w a).account a =
      { w.account a with nonce := (w.account a).nonce + 1 } := by
  unfold incrementNonce
  rw [account_modifyState, ite_eq_left rfl, ite_eq_right (by simp [Account.isEmpty])]

theorem account_setCode_self (w : World) (a : Address) (c : ByteArray) :
    (setCode w a c).account a =
      if ({ w.account a with code := c } : Account).isEmpty then {}
      else { w.account a with code := c } := by
  unfold setCode
  rw [account_modifyState, ite_eq_left rfl]

theorem account_delegate_ne (w : World) {a b : Address} (c : ByteArray) (hb : b ≠ a) :
    (incrementNonce (setCode w a c) a).account b = w.account b := by
  unfold incrementNonce setCode
  rw [account_modifyState, ite_eq_right hb, account_modifyState, ite_eq_right hb]

/-- **One authorization is in the frame relation**: setting the code of an account holding empty
code or a designator to empty code or a designator, then bumping its nonce. -/
theorem delegFrame_delegate {w : World} {a : Address} {c : ByteArray}
    (ha : Delegable (w.code a)) (hc : DelegCode c) :
    DelegFrame w (incrementNonce (setCode w a c) a) := by
  refine ⟨fun b => ?_, fun b => ?_⟩
  · by_cases hb : b = a
    · subst hb
      unfold World.balance
      rw [account_incrementNonce_self, account_setCode_self]
      split
      · rename_i h
        simp only [Account.isEmpty, Bool.and_eq_true, decide_eq_true_eq] at h
        exact h.1.2.symm
      · rfl
    · unfold World.balance
      rw [account_delegate_ne w c hb]
  · by_cases hb : b = a
    · subst hb
      right
      refine ⟨ha, ?_, ?_⟩
      · have : (incrementNonce (setCode w b c) b).code b = c := by
          unfold World.code
          rw [account_incrementNonce_self, account_setCode_self]
          split
          · rename_i h
            by_cases hce : c = .empty
            · subst hce; rfl
            · exfalso
              simp only [Account.isEmpty, Bool.and_eq_true, decide_eq_true_eq] at h
              exact size_ne_zero_of_ne_empty hce h.2
          · rfl
        rw [this]; exact hc
      · rw [account_incrementNonce_self, account_setCode_self]
        split
        · exact .inr rfl
        · exact .inl rfl
    · exact .inl (account_delegate_ne w c hb)

/-! ## All authorizations -/

/-- `validateAuthorization` accepts only the signer of the authorization, holding empty code or
a designator, and only adds to the warm set. -/
theorem validateAuthorization_spec (crypto : Crypto) (chainId : Nat) (w : World)
    (warm : AddressSet) (auth : Authorization) :
    (∀ a, (validateAuthorization crypto chainId w warm auth).1 = some a →
      Delegable (w.code a) ∧ recoverAuthority crypto auth = some a) ∧
      ∀ x, x ∈ warm → x ∈ (validateAuthorization crypto chainId w warm auth).2 := by
  unfold validateAuthorization
  split
  · exact ⟨fun _ h => (by cases h), fun _ h => h⟩
  split
  · exact ⟨fun _ h => (by cases h), fun _ h => h⟩
  split
  · exact ⟨fun _ h => (by cases h), fun _ h => h⟩
  · rename_i authority hrec
    dsimp only
    split
    · exact ⟨fun _ h => (by cases h), fun _ h => mem_insert_of_mem' h⟩
    split
    · exact ⟨fun _ h => (by cases h), fun _ h => mem_insert_of_mem' h⟩
    · rename_i hcode _
      refine ⟨fun a h => ?_, fun _ h => mem_insert_of_mem' h⟩
      cases h
      refine ⟨?_, hrec⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        not_and, Bool.not_eq_false] at hcode
      by_cases hs : (w.account authority).code.size = 0
      · exact .inl hs
      · exact .inr (hcode hs)

/-- The step `setDelegation` folds over the authorizations. -/
theorem setDelegation_eq_foldl (crypto : Crypto) (chainId : Nat) (auths : List Authorization)
    (w : World) (warm : AddressSet) :
    setDelegation crypto chainId auths w warm =
      auths.foldl (fun (s : World × AddressSet × Int) auth =>
        match validateAuthorization crypto chainId s.1 s.2.1 auth with
        | (none, warm) => (s.1, warm, s.2.2)
        | (some authority, warm) =>
          (incrementNonce (setCode s.1 authority
            (if auth.address = 0 then .empty else delegationCode auth.address)) authority, warm,
            if s.1.exists authority then
              s.2.2 + ((authPerEmptyAccount - refundAuthPerExistingAccount : Nat) : Int)
            else s.2.2)) (w, warm, 0) := rfl

theorem setDelegation_foldl_spec (crypto : Crypto) (chainId : Nat) (Q : World → Prop)
    (A : Address → Prop)
    (hstep : ∀ w a c, Q w → A a → Delegable (w.code a) → DelegCode c →
      Q (incrementNonce (setCode w a c) a)) :
    ∀ (auths : List Authorization) (s : World × AddressSet × Int),
      (∀ auth ∈ auths, ∀ a, recoverAuthority crypto auth = some a → A a) → Q s.1 →
      Q (auths.foldl (fun (s : World × AddressSet × Int) auth =>
        match validateAuthorization crypto chainId s.1 s.2.1 auth with
        | (none, warm) => (s.1, warm, s.2.2)
        | (some authority, warm) =>
          (incrementNonce (setCode s.1 authority
            (if auth.address = 0 then .empty else delegationCode auth.address)) authority, warm,
            if s.1.exists authority then
              s.2.2 + ((authPerEmptyAccount - refundAuthPerExistingAccount : Nat) : Int)
            else s.2.2)) s).1 ∧
      ∀ x, x ∈ s.2.1 → x ∈ (auths.foldl (fun (s : World × AddressSet × Int) auth =>
        match validateAuthorization crypto chainId s.1 s.2.1 auth with
        | (none, warm) => (s.1, warm, s.2.2)
        | (some authority, warm) =>
          (incrementNonce (setCode s.1 authority
            (if auth.address = 0 then .empty else delegationCode auth.address)) authority, warm,
            if s.1.exists authority then
              s.2.2 + ((authPerEmptyAccount - refundAuthPerExistingAccount : Nat) : Int)
            else s.2.2)) s).2.1
  | [], _, _, hq => ⟨hq, fun _ h => h⟩
  | auth :: auths, s, hA, hq => by
    rw [List.foldl_cons]
    have hv := validateAuthorization_spec crypto chainId s.1 s.2.1 auth
    have key : Q (match validateAuthorization crypto chainId s.1 s.2.1 auth with
        | (none, warm) => (s.1, warm, s.2.2)
        | (some authority, warm) =>
          (incrementNonce (setCode s.1 authority
            (if auth.address = 0 then .empty else delegationCode auth.address)) authority, warm,
            if s.1.exists authority then
              s.2.2 + ((authPerEmptyAccount - refundAuthPerExistingAccount : Nat) : Int)
            else s.2.2)).1 ∧
        ∀ x, x ∈ s.2.1 → x ∈ (match validateAuthorization crypto chainId s.1 s.2.1 auth with
        | (none, warm) => (s.1, warm, s.2.2)
        | (some authority, warm) =>
          (incrementNonce (setCode s.1 authority
            (if auth.address = 0 then .empty else delegationCode auth.address)) authority, warm,
            if s.1.exists authority then
              s.2.2 + ((authPerEmptyAccount - refundAuthPerExistingAccount : Nat) : Int)
            else s.2.2)).2.1 := by
      revert hv
      cases validateAuthorization crypto chainId s.1 s.2.1 auth with
      | mk o warm' =>
        cases o with
        | none => exact fun hv => ⟨hq, hv.2⟩
        | some a =>
          intro hv
          refine ⟨hstep _ _ _ hq (hA auth (List.mem_cons_self ..) a (hv.1 a rfl).2)
            (hv.1 a rfl).1 ?_, hv.2⟩
          split
          · exact .inl rfl
          · exact .inr ⟨_, rfl⟩
    obtain ⟨h1, h2⟩ := setDelegation_foldl_spec crypto chainId Q A hstep auths _
      (fun auth' h' => hA auth' (List.mem_cons_of_mem _ h')) key.1
    exact ⟨h1, fun x hx => h2 x (key.2 x hx)⟩

/-- **Induction over the authorizations, by signer.** A world predicate closed under one
authorization by a signer satisfying `A` holds after all of them, when every signer of the list
satisfies `A`; the warm set only grows. -/
theorem setDelegation_induct_by (crypto : Crypto) (chainId : Nat) (auths : List Authorization)
    (Q : World → Prop) (A : Address → Prop)
    (hA : ∀ auth ∈ auths, ∀ a, recoverAuthority crypto auth = some a → A a)
    (hstep : ∀ w a c, Q w → A a → Delegable (w.code a) → DelegCode c →
      Q (incrementNonce (setCode w a c) a))
    {w : World} (hw : Q w) (warm : AddressSet) :
    Q (setDelegation crypto chainId auths w warm).1 ∧
      ∀ x, x ∈ warm → x ∈ (setDelegation crypto chainId auths w warm).2.1 := by
  rw [setDelegation_eq_foldl]
  exact setDelegation_foldl_spec crypto chainId Q A hstep auths (w, warm, 0) hA hw

/-- **Induction over the authorizations.** A world predicate closed under one authorization
holds after all of them; the warm set only grows. -/
theorem setDelegation_induct (crypto : Crypto) (chainId : Nat) (auths : List Authorization)
    (Q : World → Prop)
    (hstep : ∀ w a c, Q w → Delegable (w.code a) → DelegCode c →
      Q (incrementNonce (setCode w a c) a))
    {w : World} (hw : Q w) (warm : AddressSet) :
    Q (setDelegation crypto chainId auths w warm).1 ∧
      ∀ x, x ∈ warm → x ∈ (setDelegation crypto chainId auths w warm).2.1 :=
  setDelegation_induct_by crypto chainId auths Q (fun _ => True) (fun _ _ _ _ => trivial)
    (fun w a c hq _ => hstep w a c hq) hw warm

/-- **The frame of `setDelegation`**: every balance is kept; an account is unchanged unless it
held empty code or a designator, and then holds empty code or a designator; the warm set only
grows. -/
theorem setDelegation_frame (crypto : Crypto) (chainId : Nat) (auths : List Authorization)
    (w : World) (warm : AddressSet) :
    DelegFrame w (setDelegation crypto chainId auths w warm).1 ∧
      ∀ x, x ∈ warm → x ∈ (setDelegation crypto chainId auths w warm).2.1 :=
  setDelegation_induct crypto chainId auths (DelegFrame w)
    (fun _ _ _ h ha hc => h.trans (delegFrame_delegate ha hc)) (DelegFrame.refl w) warm

/-! ## The top-level message -/

/-- **`applyTopLevelDelegation`, for any transaction.** The delegated world is in the frame
relation with `w`; the message keeps `currentTarget`, `caller`, `target`, `depth`, `isStatic`,
`gas`, `value` and whether it transfers its value; its warm set only grows. A call that runs
its target `a`'s own code (`msg.code = w.code a`, `msg.codeAddress = some a`) runs the delegated
world's code of `a` when that is not a designator, and the delegate's code (with `codeAddress`
the delegate) when it is one, from Prague on. -/
theorem applyTopLevelDelegation_frame (ctx : Context) (isPre : Address → Bool) (w : World)
    (msg : Message) :
    DelegFrame w (applyTopLevelDelegation ctx isPre w msg).1 ∧
    (applyTopLevelDelegation ctx isPre w msg).2.1.currentTarget = msg.currentTarget ∧
    (applyTopLevelDelegation ctx isPre w msg).2.1.caller = msg.caller ∧
    (applyTopLevelDelegation ctx isPre w msg).2.1.target = msg.target ∧
    (applyTopLevelDelegation ctx isPre w msg).2.1.depth = msg.depth ∧
    (applyTopLevelDelegation ctx isPre w msg).2.1.isStatic = msg.isStatic ∧
    (applyTopLevelDelegation ctx isPre w msg).2.1.gas = msg.gas ∧
    (applyTopLevelDelegation ctx isPre w msg).2.1.value = msg.value ∧
    (applyTopLevelDelegation ctx isPre w msg).2.1.shouldTransferValue =
      msg.shouldTransferValue ∧
    (∀ x, x ∈ msg.accessedAddresses →
      x ∈ (applyTopLevelDelegation ctx isPre w msg).2.1.accessedAddresses) ∧
    (∀ a, msg.code = w.code a → msg.codeAddress = some a →
      (delegatedAddress? ((applyTopLevelDelegation ctx isPre w msg).1.code a) = none →
        (applyTopLevelDelegation ctx isPre w msg).2.1.code =
          (applyTopLevelDelegation ctx isPre w msg).1.code a ∧
        (applyTopLevelDelegation ctx isPre w msg).2.1.codeAddress = some a) ∧
      (∀ d, ¬ ctx.fork < .prague → msg.target ≠ none →
        delegatedAddress? ((applyTopLevelDelegation ctx isPre w msg).1.code a) = some d →
        (applyTopLevelDelegation ctx isPre w msg).2.1.code =
          delegateCode isPre (applyTopLevelDelegation ctx isPre w msg).1 d ∧
        (applyTopLevelDelegation ctx isPre w msg).2.1.codeAddress = some d)) := by
  unfold applyTopLevelDelegation
  split
  · rename_i hf
    refine ⟨.refl w, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ h => h,
      fun a hc hca => ⟨fun _ => ⟨hc, hca⟩, fun _ hf' => absurd hf hf'⟩⟩
  · rename_i hf
    split
    · rename_i ht _
      exact ⟨.refl w, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ h => h,
        fun a hc hca => ⟨fun _ => ⟨hc, hca⟩, fun _ _ hn => absurd ‹msg.target = none› hn⟩⟩
    · rename_i hca'
      exact ⟨.refl w, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ h => h,
        fun a _ hca => by rw [hca'] at hca; cases hca⟩
    · rename_i tgt ca ht hca'
      -- the world, warm set and code before resolving the designator
      have hpre : ∃ w' warm' refund' code', (if ctx.tx.authorizations.isEmpty then
            (w, msg.accessedAddresses, (0 : Int), msg.code)
          else ((setDelegation ctx.crypto ctx.block.chainId ctx.tx.authorizations w
              msg.accessedAddresses).1,
            (setDelegation ctx.crypto ctx.block.chainId ctx.tx.authorizations w
              msg.accessedAddresses).2.1,
            (setDelegation ctx.crypto ctx.block.chainId ctx.tx.authorizations w
              msg.accessedAddresses).2.2,
            (setDelegation ctx.crypto ctx.block.chainId ctx.tx.authorizations w
              msg.accessedAddresses).1.code ca)) = (w', warm', refund', code') ∧
          DelegFrame w w' ∧ (∀ x, x ∈ msg.accessedAddresses → x ∈ warm') ∧
          (msg.code = w.code ca → code' = w'.code ca) := by
        split
        · exact ⟨_, _, _, _, rfl, .refl w, fun _ h => h, id⟩
        · obtain ⟨h1, h2⟩ := setDelegation_frame ctx.crypto ctx.block.chainId
            ctx.tx.authorizations w msg.accessedAddresses
          exact ⟨_, _, _, _, rfl, h1, h2, fun _ => rfl⟩
      obtain ⟨w', warm', refund', code', he, hfr, hwarm, hcode⟩ := hpre
      simp only [he]
      split
      · rename_i hnone
        refine ⟨hfr, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hwarm, fun a hc hca => ?_⟩
        rw [hca'] at hca; cases hca
        have hc' := hcode hc
        refine ⟨fun _ => ⟨hc', ‹msg.codeAddress = some _›⟩, fun d _ _ hd => ?_⟩
        rw [← hc', hnone] at hd; cases hd
      · rename_i d hd
        refine ⟨hfr, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          fun x hx => mem_insert_of_mem' (hwarm x hx), fun a hc hca => ?_⟩
        rw [hca'] at hca; cases hca
        have hc' := hcode hc
        refine ⟨fun hn => ?_, fun d' _ _ hd' => ?_⟩
        · rw [← hc', hd] at hn; cases hn
        · rw [← hc', hd] at hd'; cases hd'; exact ⟨rfl, rfl⟩

/-- The delegated world is `w`, or `w` after `setDelegation` of the transaction's
authorizations. -/
theorem applyTopLevelDelegation_world (ctx : Context) (isPre : Address → Bool) (w : World)
    (msg : Message) :
    (applyTopLevelDelegation ctx isPre w msg).1 = w ∨
      ∃ warm, (applyTopLevelDelegation ctx isPre w msg).1 =
        (setDelegation ctx.crypto ctx.block.chainId ctx.tx.authorizations w warm).1 := by
  unfold applyTopLevelDelegation
  split
  · exact .inl rfl
  · split
    · exact .inl rfl
    · exact .inl rfl
    · rename_i ca _ _
      have hpre : ∃ w' warm' refund' code', (if ctx.tx.authorizations.isEmpty then
            (w, msg.accessedAddresses, (0 : Int), msg.code)
          else ((setDelegation ctx.crypto ctx.block.chainId ctx.tx.authorizations w
              msg.accessedAddresses).1,
            (setDelegation ctx.crypto ctx.block.chainId ctx.tx.authorizations w
              msg.accessedAddresses).2.1,
            (setDelegation ctx.crypto ctx.block.chainId ctx.tx.authorizations w
              msg.accessedAddresses).2.2,
            (setDelegation ctx.crypto ctx.block.chainId ctx.tx.authorizations w
              msg.accessedAddresses).1.code ca)) = (w', warm', refund', code') ∧
          (w' = w ∨ ∃ warm, w' =
            (setDelegation ctx.crypto ctx.block.chainId ctx.tx.authorizations w warm).1) := by
        split
        · exact ⟨_, _, _, _, rfl, .inl rfl⟩
        · exact ⟨_, _, _, _, rfl, .inr ⟨_, rfl⟩⟩
      obtain ⟨w', warm', refund', code', he, hw'⟩ := hpre
      simp only [he]
      split <;> exact hw'

/-- **Induction over the top-level delegation, by signer.** A world predicate closed under one
authorization by a signer satisfying `A` holds of the delegated world, when every signer of the
transaction's authorizations satisfies `A`. -/
theorem applyTopLevelDelegation_induct_by (ctx : Context) (isPre : Address → Bool)
    (msg : Message) (Q : World → Prop) (A : Address → Prop)
    (hA : ∀ auth ∈ ctx.tx.authorizations, ∀ a, recoverAuthority ctx.crypto auth = some a → A a)
    (hstep : ∀ w a c, Q w → A a → Delegable (w.code a) → DelegCode c →
      Q (incrementNonce (setCode w a c) a))
    {w : World} (hw : Q w) : Q (applyTopLevelDelegation ctx isPre w msg).1 := by
  rcases applyTopLevelDelegation_world ctx isPre w msg with h | ⟨warm, h⟩ <;> rw [h]
  · exact hw
  · exact (setDelegation_induct_by _ _ _ Q A hA hstep hw warm).1

/-- **Induction over the top-level delegation.** A world predicate closed under one
authorization holds of the delegated world. -/
theorem applyTopLevelDelegation_induct (ctx : Context) (isPre : Address → Bool) (msg : Message)
    (Q : World → Prop)
    (hstep : ∀ w a c, Q w → Delegable (w.code a) → DelegCode c →
      Q (incrementNonce (setCode w a c) a))
    {w : World} (hw : Q w) : Q (applyTopLevelDelegation ctx isPre w msg).1 := by
  rcases applyTopLevelDelegation_world ctx isPre w msg with h | ⟨warm, h⟩ <;> rw [h]
  · exact hw
  · exact (setDelegation_induct _ _ _ Q hstep hw warm).1

end EvmLogic.Program
