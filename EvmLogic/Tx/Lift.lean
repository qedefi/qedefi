import EvmLogic.Tx.Frame
import EvmLogic.Program.Nested.Run

/-!
# From top-level message calls to transactions

The headline theorems of the verified contracts are stated over one top-level
`processMessageCall`. This file lifts them to `EvmLean.Tx.process`, so that nothing about the
rest of the transaction (nonce, fee purchase, refund, coinbase reward, `SELFDESTRUCT` deletions,
EIP-161 clean-up) has to be assumed.

* `topOk_prepareMessage`: the message of a transaction is `TopOk` for any protection predicate
  that holds only at accounts with real code (non-empty, not an EIP-7702 designator): `check`
  enforces EIP-3607, so the sender is not protected, and a call to a protected account runs its
  code from the prefix world.
* `TopMsg`: everything known about the top-level message of a transaction.
* `process_keeps`: an invariant kept by every top-level message call with these facts, and by
  every change keeping storage and code of the protected accounts, is kept by every successful
  transaction. The prefix and suffix are such changes (`EvmLogic.Tx.Frame`); the protected
  accounts are never self-destructed (`EvmLogic.Tx.Delete`).
* `Step`: one successful transaction, `Steps`: any number of them; `Step.keeps`, `Steps.keeps`.
-/

namespace EvmLogic.Tx
open EvmLean EvmLean.Interpreter EvmLean.Tx EvmLogic.Program.Nested

/-! ## The top-level message is `TopOk` -/

/-- The sender of an includable transaction holds no real code (EIP-3607). -/
theorem not_realCode_sender {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {gasAvail blobAvail : Nat} {w : World} {tx : Transaction} {hint : Option Address}
    {c : Checked} (hc : check crypto fork env gasAvail blobAvail w tx hint = .ok c) :
    ¬ RealCode (w.code c.sender) := by
  intro ⟨hs, hd⟩
  rcases (check_ok hc).2.2.2.2.2.1 with h | ⟨-, h⟩
  · exact hs h
  · simp only [World.code] at hs hd; rw [hd] at h; cases h

/-- **The message of a transaction is `TopOk`** for a protection predicate holding only at
accounts with real code at the start of the transaction. -/
theorem topOk_prepareMessage {P : Address → Prop} {crypto : Crypto} {fork : Fork}
    {env : BlockEnv} {gasAvail blobAvail : Nat} {w : World} {tx : Transaction}
    {hint : Option Address} {c : Checked}
    (hP : ∀ p, P p → RealCode (w.code p))
    (hc : check crypto fork env gasAvail blobAvail w tx hint = .ok c) (bal : Word) (n g : Nat) :
    TopOk P (prefixWorld w c.sender bal)
      (prepareMessage crypto fork env (prefixWorld w c.sender bal) tx c.sender n g) := by
  refine ⟨prepareMessage_depth .., ?_, prepareMessage_target_cases .., fun _ ht => ?_⟩
  · rw [prepareMessage_caller]
    exact fun hp => not_realCode_sender hc (hP _ hp)
  · cases hto : tx.to with
    | none => rw [prepareMessage_target, hto] at ht; cases ht
    | some to =>
      obtain ⟨h1, h2, h3⟩ := prepareMessage_call crypto fork env tx (prefixWorld w c.sender bal)
        c.sender n g hto
      rw [h1, h2, h3]
      exact ⟨rfl, rfl⟩

/-! ## What is known about the top-level message -/

/-- **The top-level message of a transaction** from the prefix world `w₁`, in context `ctx`:
`TopOk`, it moves its value, it is not static, the transaction's origin is its caller, the
context carries the transaction's crypto, fork, block and authorizations, its gas is at most the
transaction's gas limit (and at most `2²⁴` from Osaka, EIP-7825), and the protected accounts
hold real code in `w₁`. -/
structure TopMsg (P : Address → Prop) (crypto : Crypto) (fork : Fork) (env : BlockEnv)
    (tx : Transaction) (w₁ : World) (ctx : Context) (msg : Message) : Prop where
  top : TopOk P w₁ msg
  transfers : msg.shouldTransferValue = true
  static : msg.isStatic = false
  origin : ctx.tx.origin = msg.caller
  ctxCrypto : ctx.crypto = crypto
  ctxFork : ctx.fork = fork
  ctxBlock : ctx.block = env
  ctxAuths : ctx.tx.authorizations = tx.authorizations
  gas : msg.gas ≤ tx.gas
  cap : fork ≥ .osaka → msg.gas ≤ txMaxGasLimit
  real : ∀ p, P p → RealCode (w₁.code p)

/-- From Osaka the top-level message has less than `2⁶⁴` gas (EIP-7825). -/
theorem TopMsg.gas_lt {P : Address → Prop} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {tx : Transaction} {w₁ : World} {ctx : Context} {msg : Message}
    (h : TopMsg P crypto fork env tx w₁ ctx msg) (ho : fork ≥ .osaka) : msg.gas < 2 ^ 64 := by
  have := h.cap ho
  simp only [txMaxGasLimit] at this
  omega

/-- The delegation hypothesis of the message-level theorems, from one on the transaction. -/
theorem TopMsg.deleg {P : Address → Prop} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {tx : Transaction} {w₁ : World} {ctx : Context} {msg : Message}
    (h : TopMsg P crypto fork env tx w₁ ctx msg)
    (hd : fork < .prague ∨ tx.authorizations = []) :
    ctx.fork < .prague ∨ ctx.tx.authorizations = [] := by
  rw [h.ctxFork, h.ctxAuths]; exact hd

/-- **The decomposition of a transaction**, in terms of `TopMsg`: a successful transaction ran one
top-level message call from its prefix world, with the `TopMsg` facts, and its world is the
suffix of the result. -/
theorem process_split {P : Address → Prop} {fuel : Nat} {crypto : Crypto} {fork : Fork}
    {env : BlockEnv} {gasAvail blobAvail : Nat} {w : World} {tx : Transaction}
    {hint : Option Address} {out : TxOutput} (hP : ∀ p, P p → RealCode (w.code p))
    (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    ∃ (c : Checked) (ctx : Context) (msg : Message) (r : MessageResult) (gasUsed : Nat),
      check crypto fork env gasAvail blobAvail w tx hint = .ok c ∧
      TopMsg P crypto fork env tx
        (prefixWorld w c.sender
          (BitVec.ofNat 256 ((w.account c.sender).balance.toNat - upfrontFee fork env tx c)))
        ctx msg ∧
      processMessageCall fuel ctx
        (prefixWorld w c.sender
          (BitVec.ofNat 256 ((w.account c.sender).balance.toNat - upfrontFee fork env tx c)))
        ∅ msg = .ok r ∧
      gasUsed ≤ tx.gas ∧
      out.world = suffixWorld r c.sender env.coinbase ((tx.gas - gasUsed) * c.effectiveGasPrice)
        (gasUsed * (c.effectiveGasPrice - env.baseFee)) := by
  obtain ⟨i, c, r, gu, hv, hc, hr, hgu, hout, -, -⟩ := process_ok h
  have hval := validate_ok hv
  refine ⟨c, _, _, r, gu, hc, ⟨topOk_prepareMessage hP hc _ _ _, prepareMessage_shouldTransferValue ..,
    prepareMessage_isStatic .., by simp, rfl, rfl, rfl, rfl, ?_, fun ho => ?_, fun p hp => ?_⟩,
    hr, hgu, hout⟩
  · simp only [prepareMessage_gas]; omega
  · simp only [prepareMessage_gas]; have := hval.2.2.2 ho; omega
  · rw [code_prefixWorld]; exact hP p hp

/-! ## The lifting theorem -/

/-- **An invariant of top-level message calls is an invariant of transactions.** If `Inv` holds
only in worlds where the protected accounts (`P`) hold real code (`hP`), is kept by every
top-level message call with the `TopMsg` facts (`hmsg`), and is kept by every change keeping
storage and code of the protected accounts (`hframe`), then every successful transaction keeps
it: the prefix keeps storage and code of every account, and the suffix keeps them at every
account holding code that is not self-destructed — and a protected account is never
self-destructed (its code was not created in the transaction). -/
theorem process_keeps {P : Address → Prop} {Inv : World → Prop} {fuel : Nat} {crypto : Crypto}
    {fork : Fork} {env : BlockEnv} {gasAvail blobAvail : Nat} {w : World} {tx : Transaction}
    {hint : Option Address} {out : TxOutput}
    (hP : ∀ w, Inv w → ∀ p, P p → RealCode (w.code p))
    (hmsg : ∀ (ctx : Context) (w₁ : World) (msg : Message) (r : MessageResult), Inv w₁ →
      TopMsg P crypto fork env tx w₁ ctx msg → processMessageCall fuel ctx w₁ ∅ msg = .ok r →
      Inv r.world)
    (hframe : ∀ w w', Inv w → (∀ p, P p → Keep p w w') → Inv w')
    (hw : Inv w) (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    Inv out.world := by
  obtain ⟨c, ctx, msg, r, gu, -, hmsg', hr, -, hout⟩ := process_split (hP w hw) h
  have h1 := hframe w (prefixWorld w c.sender
    (BitVec.ofNat 256 ((w.account c.sender).balance.toNat - upfrontFee fork env tx c))) hw
    fun p _ => keep_prefixWorld w c.sender _ p
  have h2 := hmsg ctx _ msg r h1 hmsg' hr
  rw [hout]
  refine hframe _ _ h2 fun p hp => ?_
  obtain ⟨hd, hs⟩ := processMessageCall_realCode hr (hmsg'.real p hp)
  exact keep_suffixWorld hs hd _ _ _ _

/-! ## Transactions as a relation on worlds -/

/-- **One successful transaction** takes `w` to `w'` (any fuel, crypto, fork, block, limits,
transaction and sender hint). -/
def Step (w w' : World) : Prop :=
  ∃ (fuel : Nat) (crypto : Crypto) (fork : Fork) (env : BlockEnv) (gasAvail blobAvail : Nat)
    (tx : Transaction) (hint : Option Address) (out : TxOutput),
    process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out ∧ out.world = w'

/-- Any number of successful transactions. -/
inductive Steps : World → World → Prop where
  | refl (w : World) : Steps w w
  | tail {w w₁ w₂ : World} : Steps w w₁ → Step w₁ w₂ → Steps w w₂

/-- **`process_keeps` for the `Step` relation**: the message-level hypothesis must then hold for
every crypto, fork, block and transaction. -/
theorem Step.keeps {P : Address → Prop} {Inv : World → Prop}
    (hP : ∀ w, Inv w → ∀ p, P p → RealCode (w.code p))
    (hmsg : ∀ (crypto : Crypto) (fork : Fork) (env : BlockEnv) (tx : Transaction) (fuel : Nat)
      (ctx : Context) (w₁ : World) (msg : Message) (r : MessageResult), Inv w₁ →
      TopMsg P crypto fork env tx w₁ ctx msg → processMessageCall fuel ctx w₁ ∅ msg = .ok r →
      Inv r.world)
    (hframe : ∀ w w', Inv w → (∀ p, P p → Keep p w w') → Inv w')
    {w w' : World} (hw : Inv w) (h : Step w w') : Inv w' := by
  obtain ⟨fuel, crypto, fork, env, gasAvail, blobAvail, tx, hint, out, hp, rfl⟩ := h
  exact process_keeps hP (hmsg crypto fork env tx fuel) hframe hw hp

theorem Steps.keeps {P : Address → Prop} {Inv : World → Prop}
    (hP : ∀ w, Inv w → ∀ p, P p → RealCode (w.code p))
    (hmsg : ∀ (crypto : Crypto) (fork : Fork) (env : BlockEnv) (tx : Transaction) (fuel : Nat)
      (ctx : Context) (w₁ : World) (msg : Message) (r : MessageResult), Inv w₁ →
      TopMsg P crypto fork env tx w₁ ctx msg → processMessageCall fuel ctx w₁ ∅ msg = .ok r →
      Inv r.world)
    (hframe : ∀ w w', Inv w → (∀ p, P p → Keep p w w') → Inv w')
    {w w' : World} (hw : Inv w) (h : Steps w w') : Inv w' := by
  induction h with
  | refl => exact hw
  | tail _ hs ih => exact Step.keeps hP hmsg hframe ih hs

end EvmLogic.Tx
