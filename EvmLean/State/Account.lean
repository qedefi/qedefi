import Std.Data.ExtTreeMap
import EvmLean.Prelude.Word

/-!
# Accounts and world state

World state and storage are extensional `Std.ExtTreeMap`s, so equal maps are `=`.
Storage never holds zero values (writing zero erases the slot), so absent and zero coincide.
-/

namespace EvmLean

/-- Contract storage: slot ↦ value, with no zero values stored. -/
abbrev Storage := Std.ExtTreeMap Word Word compare

namespace Storage

/-- Read a slot (absent slots read as zero). -/
def get (s : Storage) (k : Word) : Word := s.getD k 0

/-- Write a slot; writing zero erases it. -/
def set (s : Storage) (k v : Word) : Storage := if v = 0 then s.erase k else s.insert k v

end Storage

/-- An account. -/
structure Account where
  /-- Number of transactions sent (EOA) or contracts created (contract). -/
  nonce : Nat := 0
  /-- Balance in wei. -/
  balance : Word := 0
  /-- EVM bytecode (empty for EOAs). -/
  code : ByteArray := .empty
  /-- Persistent storage. -/
  storage : Storage := ∅
  deriving Inhabited, DecidableEq

namespace Account

/-- EIP-161 emptiness: no code, zero nonce, zero balance. -/
def isEmpty (a : Account) : Bool := a.nonce = 0 && a.balance = 0 && a.code.size = 0

end Account

/-- The world state: address ↦ account. Absent addresses are non-existent accounts. -/
abbrev World := Std.ExtTreeMap Address Account compare

namespace World

/-- The account at `a`, if it exists. -/
def account? (w : World) (a : Address) : Option Account := w[a]?

/-- The account at `a`, or the default (empty) account. -/
def account (w : World) (a : Address) : Account := w.getD a {}

/-- Does an account exist at `a`? -/
def «exists» (w : World) (a : Address) : Bool := w.contains a

/-- EIP-161 "dead": non-existent or empty. -/
def isDead (w : World) (a : Address) : Bool :=
  match w[a]? with
  | none => true
  | some acc => acc.isEmpty

/-- Balance of `a` (zero if absent). -/
def balance (w : World) (a : Address) : Word := (w.account a).balance

/-- Code of `a` (empty if absent). -/
def code (w : World) (a : Address) : ByteArray := (w.account a).code

/-- Storage slot `k` of `a`. -/
def sload (w : World) (a : Address) (k : Word) : Word := (w.account a).storage.get k

/-- Apply `f` to the account at `a`, creating it if absent. -/
def modify (w : World) (a : Address) (f : Account → Account) : World :=
  w.insert a (f (w.account a))

/-- Set the balance of `a` (creating the account if absent). -/
def setBalance (w : World) (a : Address) (v : Word) : World :=
  w.modify a fun acc => { acc with balance := v }

/-- Write storage slot `k` of `a`. -/
def sstore (w : World) (a : Address) (k v : Word) : World :=
  w.modify a fun acc => { acc with storage := acc.storage.set k v }

/-- Increment the nonce of `a`. -/
def incrementNonce (w : World) (a : Address) : World :=
  w.modify a fun acc => { acc with nonce := acc.nonce + 1 }

/-- Move `v` wei from `src` to `dst`; `none` on insufficient balance. Self-transfer is a no-op. -/
def transfer (w : World) (src dst : Address) (v : Word) : Option World :=
  let b := w.balance src
  if v.toNat ≤ b.toNat then
    let w := w.setBalance src (b - v)
    some (w.setBalance dst (w.balance dst + v))
  else none

/-- Delete the account at `a`. -/
def destroy (w : World) (a : Address) : World := w.erase a

end World

end EvmLean
