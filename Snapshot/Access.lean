import EvmLean

/-!
# Recording the state a run reads

`runObserved` iterates `Interpreter.step` exactly as `Interpreter.processMessageCallWith`
does, and before each step records the accounts, storage slots and block numbers the
instruction about to execute can read. It observes the machine and changes nothing, so the
result is the interpreter's. Reverted frames are included (EIP-2929 warm sets are not: they
roll back with the frame, so they would miss reads made inside reverted calls).

This is the tracer of the snapshot fetcher (which loads whatever a run read and was not
fetched yet, until nothing new is read) and the completeness check of offline runs (a read
outside the snapshot means the snapshot does not determine the result).
-/

namespace Snapshot

open EvmLean EvmLean.Interpreter

/-- Accounts, storage slots and `BLOCKHASH` arguments read by a run. -/
structure Accesses where
  accounts : AddressSet := ∅
  slots : StorageKeySet := ∅
  blockNumbers : Std.ExtTreeSet Nat compare := ∅

namespace Accesses

def addAccount (acc : Accesses) (a : Address) : Accesses :=
  { acc with accounts := acc.accounts.insert a }

def addSlot (acc : Accesses) (a : Address) (k : Word) : Accesses :=
  { acc with accounts := acc.accounts.insert a, slots := Tx.warmKey acc.slots a k }

def union (x y : Accesses) : Accesses :=
  { accounts := y.accounts.foldl (·.insert ·) x.accounts
    slots := y.slots.foldl (fun s a ks => ks.foldl (fun s k => Tx.warmKey s a k) s) x.slots
    blockNumbers := y.blockNumbers.foldl (·.insert ·) x.blockNumbers }

def isEmpty (acc : Accesses) : Bool :=
  acc.accounts.isEmpty && acc.slots.isEmpty && acc.blockNumbers.isEmpty

/-- All `(address, slot)` pairs. -/
def slotList (acc : Accesses) : List (Address × Word) :=
  acc.slots.toList.flatMap fun (a, ks) => ks.toList.map (a, ·)

end Accesses

/-- What the instruction at the machine's `pc` may read from the world, by opcode byte. -/
def observe (m : Machine) (acc : Accesses) : Accesses :=
  let f := m.frame
  -- A frame's own account (a fresh frame: a call target, or the address a creation deploys to).
  let acc := if f.pc = 0 then (acc.addAccount f.msg.currentTarget) else acc
  let arg (i : Nat) : Word := f.stack.getD i 0
  match f.code[f.pc]? with
  | some 0x54 | some 0x55 => acc.addSlot f.msg.currentTarget (arg 0)          -- SLOAD, SSTORE
  | some 0x31 | some 0x3b | some 0x3c | some 0x3f | some 0xff =>             -- BALANCE, EXTCODE*,
    acc.addAccount (Word.toAddress (arg 0))                                  -- SELFDESTRUCT
  | some 0xf1 | some 0xf2 | some 0xf4 | some 0xfa =>                         -- CALL, CALLCODE,
    acc.addAccount (Word.toAddress (arg 1))                                  -- DELEGATECALL, STATICCALL
  | some 0x40 =>                                                             -- BLOCKHASH
    if (arg 0).toNat < 2 ^ 64 then { acc with blockNumbers := acc.blockNumbers.insert (arg 0).toNat }
    else acc
  | _ => acc

/-- `run` with `observe` before every step. -/
def runObservedLoop : Nat → Machine → Accesses → Except OutOfFuel MessageResult × Accesses
  | 0, _, acc => (.error {}, acc)
  | fuel + 1, m, acc =>
    let acc := observe m acc
    match step m with
    | .done r => (.ok r, acc)
    | .running m' => runObservedLoop fuel m' acc

/-- `processMessageCall` that also returns what the run read. -/
def runObserved (fuel : Nat) (ctx : Context) (world : World) (msg : Message) :
    Except OutOfFuel MessageResult × Accesses :=
  let pre := PrecompileImpl.standard ctx
  let acc : Accesses := ({} : Accesses).addAccount msg.caller |>.addAccount msg.currentTarget
  let (world, msg, _) := applyTopLevelDelegation ctx pre.isPrecompile world msg
  let acc := match msg.codeAddress with
    | some a => acc.addAccount a
    | none => acc
  match initMachine pre ctx world ∅ msg with
  | .inl r => (.ok r, acc)
  | .inr m => runObservedLoop fuel m acc

end Snapshot
