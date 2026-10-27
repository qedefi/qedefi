import EvmLogic.Chain.Isolated
import EvmLogic.Chain.CodeKeep
import EvmLogic.Chain.Lift

/-!
# System calls are harmless to protected contracts

`blockPreserves_good` carries a `GoodOk` predicate (the nested simulation's storage-and-code
properties of protected contracts) through the system calls of a block given frame summaries
(`hsum`) for the protected frames a system call reaches. Here `hsum` is gone:

* `SystemCodeIn w`: the four system contracts hold their canonical code (`systemCode`, the
  mainnet code of EIP-4788, EIP-2935, EIP-7002 and EIP-7251). It is a block invariant
  (`blockPreserves_systemCodeIn`, `Applies.systemCodeIn`): no transaction, system call or
  balance credit changes real code (`process_code`, `systemCall_code`), so it need only hold
  at the start of a chain, as on mainnet from Prague on.
* In a world where it holds, a system call reaches no protected frame (the canonical codes are
  `Isolated`), so it keeps every `GoodOk` predicate whose protected accounts are neither
  `SYSTEM_ADDRESS` nor a system contract (`systemCall_good_systemCode`).
* `blockPreserves_good_systemCode`: the block obligations of `Good ∧ SystemCodeIn` reduce to the
  transaction obligation for `Good`; `Applies.good_systemCode` carries `Good` along any chain of
  valid blocks starting in a world where the system contracts hold their code.

A system contract *without* code is also harmless (`systemCall_good_systemCode` allows it), but
"canonical code or no code" is not a block invariant: nothing in the semantics stops a
transaction from deploying code at an address without code (a `CREATE` address collision, an
EIP-7702 authorization signed for that address); ruling that out needs cryptographic
assumptions.
-/

namespace EvmLogic.Chain
open EvmLean EvmLean.Interpreter EvmLean.Block EvmLogic.Program EvmLogic.Program.Nested

/-- **The system contracts hold their canonical code.** -/
def SystemCodeIn (w : World) : Prop := ∀ a ∈ systemContracts, w.code a = systemCode a

theorem realCode_of_systemCodeIn {w : World} (hw : SystemCodeIn w) {a : Address}
    (ha : a ∈ systemContracts) : Tx.RealCode (w.code a) := by
  rw [hw a ha]; exact realCode_systemCode ha

/-! ## A block invariant -/

theorem systemCodeIn_systemCall {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {world : World} {target : Address} {data : ByteArray} {w' : World} {res : MessageResult}
    (hw : SystemCodeIn world)
    (h : systemCall fuel crypto fork env world target data = .ok (w', res)) : SystemCodeIn w' :=
  fun a ha => (systemCall_code h (realCode_of_systemCodeIn hw ha)).trans (hw a ha)

theorem systemCodeIn_process {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {gasAvail blobAvail : Nat} {w : World} {tx : Transaction} {hint : Option Address}
    {out : Tx.TxOutput} (hw : SystemCodeIn w)
    (h : Tx.process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    SystemCodeIn out.world :=
  fun a ha => (process_code (realCode_of_systemCodeIn hw ha) h).trans (hw a ha)

theorem systemCodeIn_creditBalance {w : World} (hw : SystemCodeIn w) (b : Address)
    (amount : Nat) : SystemCodeIn (Tx.creditBalance w b amount) :=
  fun a ha => (creditBalance_code w b amount a).trans (hw a ha)

/-- **The canonical code of the system contracts is kept by every block step**: system calls,
transactions (any, EIP-7702 authorizations included) and balance credits. -/
theorem blockPreserves_systemCodeIn (fuel : Nat) (crypto : Crypto) (fork : Fork)
    (env : BlockEnv) : BlockPreserves fuel crypto fork env SystemCodeIn :=
  ⟨fun _ _ _ _ _ _ hw hs => systemCodeIn_systemCall hw hs,
   fun _ _ _ _ _ _ hw hp => systemCodeIn_process hw hp,
   fun _ _ _ hw => systemCodeIn_creditBalance hw _ _⟩

/-- **Along a chain of valid blocks the system contracts keep their canonical code.** -/
theorem Applies.systemCodeIn {crypto : Crypto} {chainId : Nat} {head head' : ChainHead}
    {bs : List (Nat × Fork × BlockEnv)} (h : Applies crypto chainId head bs head')
    (hw : SystemCodeIn head.world) : SystemCodeIn head'.world :=
  h.preserves (fun b _ => blockPreserves_systemCodeIn b.1 crypto b.2.1 b.2.2) hw

/-! ## Protected contracts -/

/-- **The block obligations of a `GoodOk` property, without frame summaries**: `Good` together
with `SystemCodeIn` is kept by system calls and credits, and by transactions as soon as
transactions keep `Good` (`htx`, the transaction layer's obligation, which may assume
`SystemCodeIn`). Hypotheses: `hsys`, `SYSTEM_ADDRESS` is not protected (as in
`blockPreserves_good`; it holds whenever `SYSTEM_ADDRESS` holds no code,
`not_protected_of_code_empty`); `hP`, no system contract is protected (their own storage
changes at every block, so a property of it could not be kept without a summary of their code).
Both hold of any set of protected DeFi contracts. -/
theorem blockPreserves_good_systemCode {P : Address → Prop} {Good : World → Prop}
    (S : GoodOk P Good) (hsys : ¬ P systemAddress) (hP : ∀ a ∈ systemContracts, ¬ P a)
    {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    (htx : ∀ gasAvailable blobGasAvailable w tx hint (r : Tx.TxOutput), Good w →
      SystemCodeIn w →
      Tx.process fuel crypto fork env gasAvailable blobGasAvailable w tx hint = .ok r →
      Good r.world) :
    BlockPreserves fuel crypto fork env (fun w => Good w ∧ SystemCodeIn w) :=
  ⟨fun _ _ _ _ _ ht hw hs =>
    ⟨systemCall_good_systemCode S hsys ht (hP _ ht) hw.1 (.inl (hw.2 _ ht)) hs,
      systemCodeIn_systemCall hw.2 hs⟩,
   fun _ _ _ _ _ _ hw hp => ⟨htx _ _ _ _ _ _ hw.1 hw.2 hp, systemCodeIn_process hw.2 hp⟩,
   fun _ _ _ hw => ⟨good_creditBalance S hw.1 _ _, systemCodeIn_creditBalance hw.2 _ _⟩⟩

/-- **A `GoodOk` property along a chain of valid blocks**, from a world in which it holds and
the system contracts hold their canonical code, given only that transactions keep it (`htx`,
in each block's fork and environment). `hsys`, `hP` as in `blockPreserves_good_systemCode`. -/
theorem Applies.good_systemCode {P : Address → Prop} {Good : World → Prop} (S : GoodOk P Good)
    (hsys : ¬ P systemAddress) (hP : ∀ a ∈ systemContracts, ¬ P a) {crypto : Crypto}
    {chainId : Nat} {head head' : ChainHead} {bs : List (Nat × Fork × BlockEnv)}
    (h : Applies crypto chainId head bs head')
    (htx : ∀ b ∈ bs, ∀ gasAvailable blobGasAvailable w tx hint (r : Tx.TxOutput), Good w →
      SystemCodeIn w →
      Tx.process b.1 crypto b.2.1 b.2.2 gasAvailable blobGasAvailable w tx hint = .ok r →
      Good r.world)
    (hw : Good head.world) (hc : SystemCodeIn head.world) : Good head'.world :=
  (h.preserves (I := fun w => Good w ∧ SystemCodeIn w)
    (fun b hb => blockPreserves_good_systemCode S hsys hP (htx b hb)) ⟨hw, hc⟩).1

end EvmLogic.Chain
