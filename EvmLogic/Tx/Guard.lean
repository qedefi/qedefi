import EvmLogic.Tx.Lift
import EvmLogic.Tx.IdleDel
import EvmLogic.Program.Nested.GuardDelegWorld

/-!
# Guards over whole transactions, and over sequences of them

The guard theorems of `EvmLogic.Program.Nested` (`processMessageCall_guard_world_7702`, …) are
about one top-level message call, with hypotheses on its sender, on the authorizations of its
context and on its code address. Here they become theorems about `EvmLean.Tx.process`, where the
hypotheses are facts about the transaction itself:

* **`TxIdle X crypto tx out`**: no idle principal acted in the transaction. It is not the
  transaction's recovered sender (`out.sender`), and it signed none of the transaction's
  EIP-7702 authorizations (signing one is acting: it installs a designator whose code then runs
  as the signer). This becomes the message-level `GuardTop.caller` and `IdleNoAuth`.
* `hca` (a call to an idle account runs the code at that account) is not assumed: the message
  of every transaction runs the code of its recipient (`prepareMessage_codeAddress`).
* The prefix (nonce increment, fee debit) and the suffix (refund, coinbase reward, deletions,
  EIP-161 clean-up) keep `GuardWorld`: relays hold real code, so they are not deleted and keep
  their storage; idle accounts are never created in the transaction, so they are not deleted
  (`processMessageCall_not_deleted`) and keep their nonce (`idleW_suffixWorld`).

`process_guardWorld` lifts any message-level guard to transactions; `process_guard_world_7702`
is the instance for `GuardInv` relays. `TxSteps Ok` is a sequence of successful transactions,
each admitted by `Ok` (`TxSteps.steps`: it is a sequence of `Step`s), and
`TxSteps.guard_world_7702` carries `GuardWorld` along every sequence of transactions in which no
idle principal acts. No environment step is assumed between transactions.
-/

namespace EvmLogic.Tx
open EvmLean EvmLean.Interpreter EvmLean.Tx EvmLogic.Program EvmLogic.Program.Nested

variable {Rl : Address → Prop} {C : Address → ByteArray} {X : Address → Prop} {G : World → Prop}
  {Iss : Address → Machine → Message → Prop} {J : Address → Machine → Prop}

/-! ## The hypotheses on a transaction -/

/-- **No account of `X` acts in the transaction**: none is its sender, none signed one of its
EIP-7702 authorizations (hashing with `crypto`). -/
def TxIdle (X : Address → Prop) (crypto : Crypto) (tx : Transaction) (out : TxOutput) : Prop :=
  ¬ X out.sender ∧ ∀ auth ∈ tx.authorizations, ∀ a, recoverAuthority crypto auth = some a → ¬ X a

/-- The world in which the message of a transaction runs: after the nonce increment and the fee
debit of the sender `c.sender`. -/
def msgWorld (fork : Fork) (env : BlockEnv) (w : World) (tx : Transaction) (c : Checked) :
    World :=
  prefixWorld w c.sender
    (BitVec.ofNat 256 ((w.account c.sender).balance.toNat - upfrontFee fork env tx c))

/-- **The machines a transaction's message reaches**: the machines of the top-level message call
that `process` runs (from `msgWorld`, in `txContext`, on `prepareMessage`). A run-level hypothesis
of a message-level theorem (`processMessageCall_guardD`'s `R`) becomes one on these machines. -/
def TxReaches (crypto : Crypto) (fork : Fork) (env : BlockEnv) (gasAvail blobAvail : Nat)
    (w : World) (tx : Transaction) (hint : Option Address) (m : Machine) : Prop :=
  ∃ c, check crypto fork env gasAvail blobAvail w tx hint = .ok c ∧
    Reaches (txContext crypto fork env tx c) (msgWorld fork env w tx c) ∅
      (prepareMessage crypto fork env (msgWorld fork env w tx c) tx c.sender
        (w.account c.sender).nonce (tx.gas - (intrinsicGas tx).regular)) m

/-- **A transaction's message runs the code of the account it calls.** -/
theorem prepareMessage_codeAddress (crypto : Crypto) (fork : Fork) (env : BlockEnv) (w : World)
    (tx : Transaction) (s : Address) (n g : Nat)
    (ht : (prepareMessage crypto fork env w tx s n g).target =
      some (prepareMessage crypto fork env w tx s n g).currentTarget) :
    (prepareMessage crypto fork env w tx s n g).codeAddress =
      some (prepareMessage crypto fork env w tx s n g).currentTarget := by
  cases hto : tx.to with
  | none => rw [prepareMessage_target, hto] at ht; cases ht
  | some to =>
    obtain ⟨h1, -, h3⟩ := prepareMessage_call crypto fork env tx w s n g hto
    rw [h1, h3]

/-- **A transaction's message call runs the code of the account it calls**, in the world it is
prepared in. -/
theorem prepareMessage_code (crypto : Crypto) (fork : Fork) (env : BlockEnv) (w : World)
    (tx : Transaction) (s : Address) (n g : Nat)
    (ht : (prepareMessage crypto fork env w tx s n g).target =
      some (prepareMessage crypto fork env w tx s n g).currentTarget) :
    (prepareMessage crypto fork env w tx s n g).code =
      w.code (prepareMessage crypto fork env w tx s n g).currentTarget := by
  cases hto : tx.to with
  | none => rw [prepareMessage_target, hto] at ht; cases ht
  | some to =>
    obtain ⟨h1, h2, -⟩ := prepareMessage_call crypto fork env tx w s n g hto
    rw [h1, h2]

/-! ## The decomposition -/

/-- **A successful transaction, for the guards**: `process_split` with, in addition, that the
message's sender is the transaction's recovered sender, that it runs the code of the account it
calls, and that its machines are the transaction's (`TxReaches`). -/
theorem process_split_guard {P : Address → Prop} {fuel : Nat} {crypto : Crypto} {fork : Fork}
    {env : BlockEnv} {gasAvail blobAvail : Nat} {w : World} {tx : Transaction}
    {hint : Option Address} {out : TxOutput} (hP : ∀ p, P p → RealCode (w.code p))
    (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    ∃ (c : Checked) (ctx : Context) (msg : Message) (r : MessageResult) (gasUsed : Nat),
      c.sender = out.sender ∧ msg.caller = c.sender ∧
      TopMsg P crypto fork env tx (msgWorld fork env w tx c) ctx msg ∧
      (msg.target = some msg.currentTarget → msg.codeAddress = some msg.currentTarget) ∧
      (msg.target = some msg.currentTarget →
        msg.code = (msgWorld fork env w tx c).code msg.currentTarget) ∧
      (∀ m, Reaches ctx (msgWorld fork env w tx c) ∅ msg m →
        TxReaches crypto fork env gasAvail blobAvail w tx hint m) ∧
      processMessageCall fuel ctx (msgWorld fork env w tx c) ∅ msg = .ok r ∧
      out.world = suffixWorld r c.sender env.coinbase ((tx.gas - gasUsed) * c.effectiveGasPrice)
        (gasUsed * (c.effectiveGasPrice - env.baseFee)) := by
  obtain ⟨i, c, r, gu, hv, hc, hr, hgu, hout, hs, -⟩ := process_ok h
  have hval := validate_ok hv
  refine ⟨c, _, _, r, gu, hs.symm, prepareMessage_caller .., ⟨topOk_prepareMessage hP hc _ _ _,
    prepareMessage_shouldTransferValue .., prepareMessage_isStatic .., by simp, rfl, rfl, rfl, rfl,
    ?_, fun ho => ?_, fun p hp => ?_⟩, fun ht => prepareMessage_codeAddress _ _ _ _ _ _ _ _ ht,
    fun ht => prepareMessage_code _ _ _ _ _ _ _ _ ht, fun m hm => ⟨c, hc, ?_⟩, hr,
    hout⟩
  · simp only [prepareMessage_gas]; omega
  · simp only [prepareMessage_gas]; have := hval.2.2.2 ho; omega
  · unfold msgWorld; rw [code_prefixWorld]; exact hP p hp
  · rw [← hval.1]; exact hm

/-! ## The prefix and the suffix -/

/-- The prefix keeps idle accounts idle. -/
theorem idleW_prefixWorld {w : World} (hi : IdleW X w) (s : Address) (bal : Word) :
    IdleW X (prefixWorld w s bal) := fun x hx => by
  refine ⟨by rw [code_prefixWorld]; exact (hi x hx).1, ?_⟩
  rw [account_prefixWorld]
  split
  · simp
  · exact (hi x hx).2

/-- The prefix keeps `GuardWorld`. -/
theorem guardWorld_prefixWorld (hG : ∀ w w', G w → KeepP Rl w w' → G w') {w : World}
    (hw : GuardWorld Rl C X G w) (s : Address) (bal : Word) :
    GuardWorld Rl C X G (prefixWorld w s bal) :=
  ⟨hG _ _ hw.1 fun p _ => keep_prefixWorld w s bal p,
    fun r hr => (code_prefixWorld w s bal r).trans (hw.2.1 r hr), idleW_prefixWorld hw.2.2 s bal⟩

/-- A credit decreases no nonce. -/
theorem nonceLe_creditBalance (w : World) (a : Address) (k : Nat) :
    NonceLe w (creditBalance w a k) := by
  unfold creditBalance
  exact nonce_modifyState fun acc => Nat.le_refl acc.nonce

/-- The two credits of the suffix decrease no nonce. -/
theorem nonceLe_creditedWorld (r : MessageResult) (sender coinbase : Address)
    (refund reward : Nat) : NonceLe r.world (creditedWorld r sender coinbase refund reward) :=
  (nonceLe_creditBalance _ _ _).trans (nonceLe_creditBalance _ _ _)

/-- **The suffix keeps idle accounts idle** when none of them is scheduled for deletion. -/
theorem idleW_suffixWorld {r : MessageResult} (hi : IdleW X r.world)
    (hd : ∀ x, X x → x ∉ r.accountsToDelete) (sender coinbase : Address) (refund reward : Nat) :
    IdleW X (suffixWorld r sender coinbase refund reward) := fun x hx => by
  refine ⟨by rw [code_suffixWorld _ _ _ _ _ (hd x hx)]; exact (hi x hx).1, ?_⟩
  have hn := nonceLe_creditedWorld r sender coinbase refund reward x
  have h0 := (hi x hx).2
  rcases account_suffixWorld r sender coinbase refund reward (hd x hx) with he | ⟨he, -⟩
  · rw [he]; omega
  · simp only [Account.isEmpty, Bool.and_eq_true, decide_eq_true_eq] at he
    omega

/-- **The suffix keeps `GuardWorld`** when the relays hold real code before the message and no
idle account is scheduled for deletion. -/
theorem guardWorld_suffixWorld (hC : RelayCodeOk Rl C)
    (hG : ∀ w w', G w → KeepP Rl w w' → G w') {fuel : Nat} {ctx : Context} {w₁ : World}
    {msg : Message} {r : MessageResult} (hw₁ : RelayCode Rl C w₁)
    (hr : processMessageCall fuel ctx w₁ ∅ msg = .ok r) (hw : GuardWorld Rl C X G r.world)
    (hd : ∀ x, X x → x ∉ r.accountsToDelete) (sender coinbase : Address) (refund reward : Nat) :
    GuardWorld Rl C X G (suffixWorld r sender coinbase refund reward) := by
  have hk : ∀ p, Rl p → Keep p r.world (suffixWorld r sender coinbase refund reward) :=
    fun p hp => by
      obtain ⟨hdel, hs⟩ := processMessageCall_realCode hr
        (by rw [hw₁ p hp]; exact realCode_of_deleg (hC.size p hp) (hC.deleg p hp))
      exact keep_suffixWorld hs hdel _ _ _ _
  exact ⟨hG _ _ hw.1 hk, fun p hp => (hk p hp).code.trans (hw.2.1 p hp),
    idleW_suffixWorld hw.2.2 hd _ _ _ _⟩

/-! ## The lifting theorem -/

/-- **A message-level guard is a transaction-level guard.** If every top-level message call
of the transaction (with the `TopMsg` facts, a `GuardTop` message, no authorization signed by
an idle account, the code of the account it calls, its machines the transaction's) from a world
satisfying `GuardWorld` ends in one, and schedules no idle account for deletion (`hmsg`), then
the transaction keeps `GuardWorld` — provided no idle account acts in it (`hidle`). -/
theorem process_guardWorld (hC : RelayCodeOk Rl C) (hG : ∀ w w', G w → KeepP Rl w w' → G w')
    {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv} {gasAvail blobAvail : Nat}
    {w : World} {tx : Transaction} {hint : Option Address} {out : TxOutput}
    (hmsg : ∀ (ctx : Context) (w₁ : World) (msg : Message) (r : MessageResult),
      GuardWorld Rl C X G w₁ → TopMsg Rl crypto fork env tx w₁ ctx msg →
      GuardTop Rl X w₁ msg → IdleNoAuth X ctx →
      (X msg.currentTarget → msg.target = some msg.currentTarget →
        msg.codeAddress = some msg.currentTarget) →
      (∀ m, Reaches ctx w₁ ∅ msg m → TxReaches crypto fork env gasAvail blobAvail w tx hint m) →
      processMessageCall fuel ctx w₁ ∅ msg = .ok r →
      GuardWorld Rl C X G r.world ∧ ∀ x, X x → x ∉ r.accountsToDelete)
    (hw : GuardWorld Rl C X G w) (hidle : TxIdle X crypto tx out)
    (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    GuardWorld Rl C X G out.world := by
  have hP : ∀ p, Rl p → RealCode (w.code p) := fun p hp => by
    rw [hw.2.1 p hp]; exact realCode_of_deleg (hC.size p hp) (hC.deleg p hp)
  obtain ⟨c, ctx, msg, r, gu, hs, hcl, htm, hca, hcode, hreach, hr, hout⟩ :=
    process_split_guard hP h
  have hw₁ : GuardWorld Rl C X G (msgWorld fork env w tx c) :=
    guardWorld_prefixWorld hG hw _ _
  have hauth : IdleNoAuth X ctx := fun auth ha a hra => by
    rw [htm.ctxAuths] at ha
    rw [htm.ctxCrypto] at hra
    exact hidle.2 auth ha a hra
  have htop : GuardTop Rl X (msgWorld fork env w tx c) msg :=
    ⟨htm.top, by rw [hcl, hs]; exact hidle.1, fun hx ht => by
      rw [hcode ht]; exact (hw₁.2.2 _ hx).1⟩
  obtain ⟨hwr, hd⟩ := hmsg ctx _ msg r hw₁ htm htop hauth (fun _ => hca) hreach hr
  rw [hout]
  exact guardWorld_suffixWorld hC hG hw₁.2.1 hr hwr hd _ _ _ _

/-- **A guarded transaction keeps its world hypotheses**, EIP-7702 authorizations included: from
a world satisfying `GuardWorld` (the world invariant, the relays' code, idle accounts idle), if
each relay's frames keep an invariant (`GuardInv`), every successful transaction in which no idle
account acts (`TxIdle`: not its sender, no signer of its authorizations) ends in a world
satisfying `GuardWorld`. -/
theorem process_guard_world_7702 (hC : RelayCodeOk Rl C)
    (hG : ∀ w w', G w → KeepP Rl w w' → G w') (hJ : ∀ r, Rl r → GuardInv Rl C X G Iss r (J r))
    {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv} {gasAvail blobAvail : Nat}
    {w : World} {tx : Transaction} {hint : Option Address} {out : TxOutput}
    (hw : GuardWorld Rl C X G w) (hidle : TxIdle X crypto tx out)
    (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    GuardWorld Rl C X G out.world :=
  process_guardWorld hC hG (fun _ _ _ _ hw₁ _ htop hauth hca _ hr =>
    ⟨processMessageCall_guard_world_7702 hC hG hJ hw₁ hauth hca htop hr,
      processMessageCall_not_deleted (fun _ hm => reaches_createIdle_7702 hC hG hJ hw₁.2.1 hw₁.1
        hw₁.2.2 hauth hca htop trivial hm) hr⟩) hw hidle h

/-! ## Sequences of transactions -/

/-- **The inputs of a transaction** other than the world: fuel, hashing, fork, block, the gas
and blob gas still available in the block, the transaction and the sender hint. -/
structure Input where
  fuel : Nat
  crypto : Crypto
  fork : Fork
  env : BlockEnv
  gasAvail : Nat
  blobAvail : Nat
  tx : Transaction
  hint : Option Address

/-- The transaction of `i`, run from `w`. -/
def Input.run (i : Input) (w : World) : Except TxError TxOutput :=
  process i.fuel i.crypto i.fork i.env i.gasAvail i.blobAvail w i.tx i.hint

/-- **Successful transactions admitted by `Ok`, in sequence**: `TxSteps Ok w w'` when `w'` is
reached from `w` by successful transactions (`Input.run`), each admitted by `Ok` (which may read
the transaction, the world it starts from and its output, e.g. its sender). Nothing happens
between two transactions. -/
inductive TxSteps (Ok : Input → World → TxOutput → Prop) : World → World → Prop where
  | refl (w : World) : TxSteps Ok w w
  | tail {w w₁ : World} {i : Input} {out : TxOutput} : TxSteps Ok w w₁ → i.run w₁ = .ok out →
      Ok i w₁ out → TxSteps Ok w out.world

namespace TxSteps

variable {Ok Ok' : Input → World → TxOutput → Prop}

/-- An invariant kept by every admitted transaction is kept by every sequence of them. -/
theorem keeps {Inv : World → Prop}
    (hstep : ∀ i w out, Inv w → i.run w = .ok out → Ok i w out → Inv out.world)
    {w w' : World} (hw : Inv w) (h : TxSteps Ok w w') : Inv w' := by
  induction h with
  | refl => exact hw
  | tail _ hr hok ih => exact hstep _ _ _ ih hr hok

/-- A sequence of admitted transactions is a sequence of transactions (`Steps`). -/
theorem steps {w w' : World} (h : TxSteps Ok w w') : Steps w w' := by
  induction h with
  | refl => exact .refl _
  | tail _ hr _ ih => exact .tail ih ⟨_, _, _, _, _, _, _, _, _, hr, rfl⟩

/-- Every sequence of transactions is a sequence of transactions admitted by `True`. -/
theorem of_steps {w w' : World} (h : Steps w w') : TxSteps (fun _ _ _ => True) w w' := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih =>
    obtain ⟨fuel, crypto, fork, env, gasAvail, blobAvail, tx, hint, out, hr, rfl⟩ := hs
    exact .tail (i := ⟨fuel, crypto, fork, env, gasAvail, blobAvail, tx, hint⟩) ih hr trivial

theorem mono (hOk : ∀ i w out, Ok i w out → Ok' i w out) {w w' : World} (h : TxSteps Ok w w') :
    TxSteps Ok' w w' := by
  induction h with
  | refl => exact .refl _
  | tail _ hr hok ih => exact .tail ih hr (hOk _ _ _ hok)

theorem trans {w₁ w₂ w₃ : World} (h₁ : TxSteps Ok w₁ w₂) (h₂ : TxSteps Ok w₂ w₃) :
    TxSteps Ok w₁ w₃ := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hr hok ih => exact .tail ih hr hok

end TxSteps

/-- **The transactions in which no account of `X` acts** (`TxIdle`). -/
def IdleOk (X : Address → Prop) (i : Input) (_ : World) (out : TxOutput) : Prop :=
  TxIdle X i.crypto i.tx out

/-- **Guarded relays keep `GuardWorld` along every sequence of transactions in which no idle
account acts**: from a world satisfying `GuardWorld`, any number of successful transactions
(any fuel, hashing, fork, block, type, sender, recipient, calldata, value and EIP-7702
authorizations), none sent by an idle account and none carrying an authorization signed by one,
end in a world satisfying `GuardWorld`. -/
theorem TxSteps.guard_world_7702 (hC : RelayCodeOk Rl C)
    (hG : ∀ w w', G w → KeepP Rl w w' → G w') (hJ : ∀ r, Rl r → GuardInv Rl C X G Iss r (J r))
    {w w' : World} (hw : GuardWorld Rl C X G w) (h : TxSteps (IdleOk X) w w') :
    GuardWorld Rl C X G w' :=
  h.keeps (fun _ _ _ hw hr hok => process_guard_world_7702 hC hG hJ hw hok hr) hw

end EvmLogic.Tx
