import EvmLean.Machine.Types
import EvmLean.Prelude.Rlp

/-!
# State operations used by the interpreter

World-state and transient-storage operations with the exact semantics of
`cancun/state_tracker.py`, plus access-set helpers (EIP-2929) and contract address
derivation (`cancun/utils/address.py`).

## Eager deletion of empty accounts

The reference's `modify_state` deletes an account (including its storage) as soon as a
modification leaves it existing-but-empty (zero nonce, zero balance, no code). Every
balance/nonce/code update here goes through `modifyState`, so the interpreter never creates
an empty account. In addition the interpreter reports EIP-161 touched accounts
(`MessageResult.touchedAccounts`, following the pre-`state_tracker` specification); with
eager deletion the only accounts that end-of-transaction clearing can still affect are ones
that were already empty in the pre-state.
-/

namespace EvmLean.Interpreter

/-- Apply `f` to the account at `a` (the empty account if absent); if the result is empty
(EIP-161), delete the account instead. Mirrors `modify_state`. -/
def modifyState (w : World) (a : Address) (f : Account → Account) : World :=
  let acc := f (w.account a)
  if acc.isEmpty then w.erase a else w.insert a acc

/-- Move `amount` wei from `src` to `dst`. Mirrors `move_ether`; the caller guarantees
`amount ≤ balance src` (the reference asserts it). A self-transfer leaves the balance
unchanged. -/
def moveEther (w : World) (src dst : Address) (amount : Word) : World :=
  let w := modifyState w src fun acc => { acc with balance := acc.balance - amount }
  modifyState w dst fun acc => { acc with balance := acc.balance + amount }

/-- Set the balance of `a`. Mirrors `set_account_balance`. -/
def setAccountBalance (w : World) (a : Address) (amount : Word) : World :=
  modifyState w a fun acc => { acc with balance := amount }

/-- Increment the nonce of `a`. Mirrors `increment_nonce`. -/
def incrementNonce (w : World) (a : Address) : World :=
  modifyState w a fun acc => { acc with nonce := acc.nonce + 1 }

/-- Set the code of `a`. Mirrors `set_code`. -/
def setCode (w : World) (a : Address) (code : ByteArray) : World :=
  modifyState w a fun acc => { acc with code := code }

/-- Write storage slot `k` of `a`. Mirrors `set_storage` (the account exists whenever code
runs on its behalf; writing never changes emptiness, so no `modifyState`). -/
def setStorage (w : World) (a : Address) (k v : Word) : World := w.sstore a k v

/-- Delete the account at `a` together with its storage. Mirrors `destroy_account`. -/
def destroyAccount (w : World) (a : Address) : World := w.erase a

/-- Is `a` alive, i.e. existing and non-empty? Mirrors `is_account_alive`. -/
def isAccountAlive (w : World) (a : Address) : Bool := !w.isDead a

/-- Does `a` exist and is it empty (EIP-161)? Mirrors `account_exists_and_is_empty`. -/
def accountExistsAndIsEmpty (w : World) (a : Address) : Bool :=
  match w.account? a with
  | some acc => acc.isEmpty
  | none => false

/-- Can a contract be deployed at `a`? Requires zero nonce, no code and (EIP-7610) empty
storage. Mirrors `account_deployable`, strengthened by EIP-7610's storage condition (the
reference instead wipes the storage of such an account in `process_create_message`). -/
def accountDeployable (w : World) (a : Address) : Bool :=
  let acc := w.account a
  acc.nonce = 0 && acc.code.size = 0 && acc.storage.isEmpty

/-- The original value of storage slot `k` of `a`, i.e. its value at the start of the
transaction (`original`), or zero for accounts created during the transaction. Mirrors
`get_storage_original`. -/
def getStorageOriginal (original : World) (created : AddressSet) (a : Address) (k : Word) :
    Word :=
  if created.contains a then 0 else original.sload a k

/-! ## Transient storage (EIP-1153) -/

/-- Read transient slot `k` of `a`. Mirrors `get_transient_storage`. -/
def getTransient (t : TransientStorage) (a : Address) (k : Word) : Word :=
  Storage.get (t.getD a ∅) k

/-- Write transient slot `k` of `a`, keeping the map canonical (no empty inner maps).
Mirrors `set_transient_storage`. -/
def setTransient (t : TransientStorage) (a : Address) (k v : Word) : TransientStorage :=
  let s := Storage.set (t.getD a ∅) k v
  if s.isEmpty then t.erase a else t.insert a s

/-! ## Access sets (EIP-2929) -/

/-- Is storage key `k` of `a` warm? -/
def storageKeyWarm (s : StorageKeySet) (a : Address) (k : Word) : Bool :=
  (s.getD a ∅).contains k

/-- Mark storage key `k` of `a` warm. -/
def addStorageKey (s : StorageKeySet) (a : Address) (k : Word) : StorageKeySet :=
  s.insert a ((s.getD a ∅).insert k)

/-! ## Contract addresses (`cancun/utils/address.py`) -/

/-- The address of the contract created by `sender` with nonce `nonce` (`CREATE` and
creation transactions): the low 20 bytes of `keccak256(rlp([sender, nonce]))`.
Mirrors `compute_contract_address`. -/
def createAddress (keccak256 : ByteArray → Word) (sender : Address) (nonce : Nat) : Address :=
  Word.toAddress (keccak256 (Rlp.encode (.list [.bytes (Bytes.ofAddress sender), Rlp.nat nonce])))

/-- The address of the contract created by `CREATE2`: the low 20 bytes of
`keccak256(0xff ‖ sender ‖ salt ‖ keccak256(initCode))`.
Mirrors `compute_create2_contract_address`. -/
def create2Address (keccak256 : ByteArray → Word) (sender : Address) (salt : Word)
    (initCode : ByteArray) : Address :=
  let preimage := ByteArray.mk #[0xff] ++ Bytes.ofAddress sender ++ Bytes.ofWord salt
    ++ Bytes.ofWord (keccak256 initCode)
  Word.toAddress (keccak256 preimage)

end EvmLean.Interpreter
