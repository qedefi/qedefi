import EvmLean.Tx
import EvmLogic.Tx.Delete

/-!
# A transaction is a prefix, one top-level message, and a suffix

`process_ok`: a successful `EvmLean.Tx.process` passed `validate` and `check`, ran one
`processMessageCall` from the **prefix world** (`prefixWorld`: the sender's nonce incremented,
its balance debited by the `upfrontFee`) with empty transient storage, in the context
`txContext`, on the message `prepareMessage` builds, and ended in the **suffix world**
(`suffixWorld`) of its result: the unused gas refunded to the sender, the priority fee credited
to the coinbase, `accountsToDelete` erased, the touched empty accounts destroyed.

`validate_ok`, `check_ok`: what the two checks guarantee (intrinsic gas within the limit, the
EIP-7825 cap from Osaka, the sender's nonce, that it can pay the fees and the value, EIP-3607).
The `prepareMessage_*` and `txContext_*` lemmas give the message's fields.
-/

namespace EvmLogic.Tx
open EvmLean EvmLean.Interpreter EvmLean.Tx

/-- The world after the prefix of a transaction: the sender's nonce incremented and its balance
set to `bal` (its balance minus the fees). -/
def prefixWorld (w : World) (sender : Address) (bal : Word) : World :=
  setAccountBalance (incrementNonce w sender) sender bal

/-- The world after the suffix of a transaction, from the result `r` of its message: `refund`
credited to the sender, `reward` to the coinbase, the self-destructed accounts erased and the
touched empty accounts destroyed. -/
def suffixWorld (r : MessageResult) (sender coinbase : Address) (refund reward : Nat) : World :=
  destroyTouchedEmpty (r.accountsToDelete.foldl (fun w a => w.erase a)
    (creditBalance (creditBalance r.world sender refund) coinbase reward)) r.touchedAccounts

/-- The context of a transaction's message. -/
def txContext (crypto : Crypto) (fork : Fork) (env : BlockEnv) (tx : Transaction) (c : Checked) :
    Context :=
  { crypto, fork, block := env,
    tx := { origin := c.sender, gasPrice := c.effectiveGasPrice,
            blobVersionedHashes := c.blobVersionedHashes.toArray,
            authorizations := tx.authorizations } }

/-- The fees debited from the sender before execution. -/
def upfrontFee (fork : Fork) (env : BlockEnv) (tx : Transaction) (c : Checked) : Nat :=
  tx.gas * c.effectiveGasPrice + c.blobGasUsed * Gas.blobGasPrice fork env.excessBlobGas

/-! ## The context and the message -/

section
variable (crypto : Crypto) (fork : Fork) (env : BlockEnv) (tx : Transaction) (c : Checked)

@[simp] theorem txContext_crypto : (txContext crypto fork env tx c).crypto = crypto := rfl
@[simp] theorem txContext_fork : (txContext crypto fork env tx c).fork = fork := rfl
@[simp] theorem txContext_block : (txContext crypto fork env tx c).block = env := rfl
@[simp] theorem txContext_origin : (txContext crypto fork env tx c).tx.origin = c.sender := rfl
@[simp] theorem txContext_authorizations :
    (txContext crypto fork env tx c).tx.authorizations = tx.authorizations := rfl

variable (w : World) (s : Address) (n g : Nat)

@[simp] theorem prepareMessage_caller : (prepareMessage crypto fork env w tx s n g).caller = s := by
  unfold prepareMessage; cases tx.to <;> rfl
@[simp] theorem prepareMessage_target :
    (prepareMessage crypto fork env w tx s n g).target = tx.to := by
  unfold prepareMessage; cases tx.to <;> rfl
@[simp] theorem prepareMessage_gas : (prepareMessage crypto fork env w tx s n g).gas = g := by
  unfold prepareMessage; cases tx.to <;> rfl
@[simp] theorem prepareMessage_depth : (prepareMessage crypto fork env w tx s n g).depth = 0 := by
  unfold prepareMessage; cases tx.to <;> rfl
@[simp] theorem prepareMessage_shouldTransferValue :
    (prepareMessage crypto fork env w tx s n g).shouldTransferValue = true := by
  unfold prepareMessage; cases tx.to <;> rfl
@[simp] theorem prepareMessage_isStatic :
    (prepareMessage crypto fork env w tx s n g).isStatic = false := by
  unfold prepareMessage; cases tx.to <;> rfl
@[simp] theorem prepareMessage_value :
    (prepareMessage crypto fork env w tx s n g).value = BitVec.ofNat 256 tx.value := by
  unfold prepareMessage; cases tx.to <;> rfl
@[simp] theorem prepareMessage_disablePrecompiles :
    (prepareMessage crypto fork env w tx s n g).disablePrecompiles = false := by
  unfold prepareMessage; cases tx.to <;> rfl

/-- A call runs the recipient's code in the prefix world. -/
theorem prepareMessage_call {to : Address} (h : tx.to = some to) :
    (prepareMessage crypto fork env w tx s n g).currentTarget = to ∧
      (prepareMessage crypto fork env w tx s n g).code = w.code to ∧
      (prepareMessage crypto fork env w tx s n g).codeAddress = some to := by
  unfold prepareMessage; rw [h]; exact ⟨rfl, rfl, rfl⟩

/-- A creation creates at the address of the sender and its pre-increment nonce. -/
theorem prepareMessage_create (h : tx.to = none) :
    (prepareMessage crypto fork env w tx s n g).currentTarget =
      createAddress crypto.keccak256 s n ∧
      (prepareMessage crypto fork env w tx s n g).codeAddress = none := by
  unfold prepareMessage; rw [h]; exact ⟨rfl, rfl⟩

/-- The message calls its `currentTarget`, or creates it. -/
theorem prepareMessage_target_cases :
    (prepareMessage crypto fork env w tx s n g).target =
        some (prepareMessage crypto fork env w tx s n g).currentTarget ∨
      (prepareMessage crypto fork env w tx s n g).target = none := by
  cases h : tx.to with
  | none => right; rw [prepareMessage_target, h]
  | some to => left; rw [prepareMessage_target, h, (prepareMessage_call crypto fork env tx w s n g h).1]

end

theorem validate_ok {fork : Fork} {tx : Transaction} {i : IntrinsicGas}
    (h : validate fork tx = .ok i) :
    i = intrinsicGas tx ∧ i.regular ≤ tx.gas ∧ (fork ≥ .prague → i.calldataFloor ≤ tx.gas) ∧
      (fork ≥ .osaka → tx.gas ≤ txMaxGasLimit) := by
  simp [validate, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
    Except.pure] at h
  repeat' split at h
  all_goals (first | (simp at h; done) | skip)
  all_goals
    simp only [Except.ok.injEq] at h
    subst h
    refine ⟨rfl, ?_, fun hp => ?_, fun ho => ?_⟩ <;> simp_all <;> omega

theorem gasPricing_ok {b : Nat} {tx : Transaction} {eff mg : Nat}
    (h : gasPricing b tx = .ok (eff, mg)) : tx.gas * eff ≤ mg ∧ b ≤ eff := by
  cases tx <;> simp only [gasPricing, gasPricing.fixed, gasPricing.market] at h <;>
    split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> simp only [Transaction.gas] <;>
    first
    | omega
    | (refine ⟨Nat.mul_le_mul_left _ (by omega), by omega⟩)

theorem blobChecks_ok {fork : Fork} {env : BlockEnv} {tx : Transaction} {mb : Nat}
    (h : blobChecks fork env tx = .ok mb) :
    totalBlobGas tx * Gas.blobGasPrice fork env.excessBlobGas ≤ mb := by
  cases tx with
  | eip4844 t =>
    simp [blobChecks, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
      Except.pure] at h
    repeat' split at h
    all_goals (first | (simp at h; done) | skip)
    all_goals
      simp only [Except.ok.injEq] at h
      subst h
      exact Nat.mul_le_mul_left _ (by omega)
  | _ => simp [totalBlobGas, Transaction.blobVersionedHashes]

theorem sender_code_of {code : ByteArray} {fork : Fork}
    (h : ¬(¬code = ByteArray.empty ∧ (¬Fork.prague ≤ fork ∨ isValidDelegation code = false))) :
    code.size = 0 ∨ (fork ≥ .prague ∧ isValidDelegation code = true) := by
  by_cases he : code = ByteArray.empty
  · left; rw [he]; rfl
  · right
    simp only [he, not_false_eq_true, true_and, not_or, Decidable.not_not, Bool.not_eq_false] at h
    exact h

/-- What `check` guarantees about an includable transaction: the blob data it reports, the
sender's nonce, that the sender can pay the upfront fees and the value, that the gas price covers
the base fee, that the sender holds no code or (from Prague) an EIP-7702 designator (EIP-3607),
and that the gas limit fits the block. -/
theorem check_ok {crypto : Crypto} {fork : Fork} {env : BlockEnv} {gasAvail blobAvail : Nat}
    {w : World} {tx : Transaction} {hint : Option Address} {c : Checked}
    (h : check crypto fork env gasAvail blobAvail w tx hint = .ok c) :
    c.blobGasUsed = totalBlobGas tx ∧ c.blobVersionedHashes = tx.blobVersionedHashes ∧
      (w.account c.sender).nonce = tx.nonce ∧
      upfrontFee fork env tx c + tx.value ≤ (w.account c.sender).balance.toNat ∧
      env.baseFee ≤ c.effectiveGasPrice ∧
      ((w.account c.sender).code.size = 0 ∨
        (fork ≥ .prague ∧ isValidDelegation (w.account c.sender).code = true)) ∧
      tx.gas ≤ gasAvail := by
  cases hci : chainIdOf tx with
  | error e =>
    simp [check, hci, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    repeat' split at h
    all_goals simp at h
  | ok ci =>
  cases hs : resolveSender crypto tx hint with
  | error e =>
    simp [check, hci, hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    repeat' split at h
    all_goals simp at h
  | ok sender =>
  cases hg : gasPricing env.baseFee tx with
  | error e =>
    simp [check, hci, hs, hg, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    repeat' split at h
    all_goals simp at h
  | ok pr =>
  obtain ⟨eff, mg⟩ := pr
  cases hb : blobChecks fork env tx with
  | error e =>
    simp [check, hci, hs, hg, hb, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    repeat' split at h
    all_goals simp at h
  | ok mb =>
  have hg' := gasPricing_ok hg
  have hb' := blobChecks_ok hb
  simp [check, hci, hs, hg, hb, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
    Except.pure] at h
  repeat' split at h
  all_goals (first | (simp at h; done) | skip)
  all_goals
    simp only [Except.ok.injEq] at h
    subst h
    dsimp only
    refine ⟨rfl, rfl, by omega, by simp only [upfrontFee]; omega, hg'.2,
      sender_code_of (by assumption), by omega⟩

theorem process_ok {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {gasAvail blobAvail : Nat} {w : World} {tx : Transaction} {hint : Option Address}
    {out : TxOutput}
    (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    ∃ (intrinsic : IntrinsicGas) (c : Checked) (r : MessageResult) (gasUsed : Nat),
      validate fork tx = .ok intrinsic ∧
      check crypto fork env gasAvail blobAvail w tx hint = .ok c ∧
      processMessageCall fuel (txContext crypto fork env tx c)
        (prefixWorld w c.sender
          (BitVec.ofNat 256 ((w.account c.sender).balance.toNat - upfrontFee fork env tx c))) ∅
        (prepareMessage crypto fork env (prefixWorld w c.sender
            (BitVec.ofNat 256 ((w.account c.sender).balance.toNat - upfrontFee fork env tx c)))
          tx c.sender (w.account c.sender).nonce (tx.gas - intrinsic.regular)) = .ok r ∧
      gasUsed ≤ tx.gas ∧
      out.world = suffixWorld r c.sender env.coinbase ((tx.gas - gasUsed) * c.effectiveGasPrice)
        (gasUsed * (c.effectiveGasPrice - env.baseFee)) ∧
      out.sender = c.sender ∧ out.gasUsed = gasUsed := by
  unfold process at h
  cases hv : validate fork tx with
  | error e => simp [hv, Except.mapError, bind, Except.bind] at h
  | ok intrinsic =>
  cases hc : check crypto fork env gasAvail blobAvail w tx hint with
  | error e => simp [hv, hc, Except.mapError, bind, Except.bind] at h
  | ok c =>
  simp only [hv, hc, Except.mapError, bind, Except.bind, Nat.sub_sub] at h
  split at h
  · rename_i r hr
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨intrinsic, c, r, _, rfl, rfl, hr, ?_, rfl, rfl, rfl⟩
    have hval := validate_ok hv
    split
    · have := hval.2.2.1 ‹_›; omega
    · omega
  · simp [throw, throwThe, MonadExceptOf.throw] at h

end EvmLogic.Tx
