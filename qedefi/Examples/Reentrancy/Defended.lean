import Examples.Reentrancy.Contracts.VulnerableBank
import Examples.Reentrancy.Contracts.VulnerableBankData
import Examples.Reentrancy.Contracts.CEIBank
import Examples.Reentrancy.Contracts.CEIBankData
import Examples.Reentrancy.Contracts.GuardedBank
import Examples.Reentrancy.Contracts.GuardedBankData
import Examples.Reentrancy.Contracts.OnceAttacker
import Examples.Reentrancy.Contracts.OnceAttackerData
import EvmLogic.Solidity.Abi
import EvmLogic.Tactic.KernelRfl

/-!
# Reentrancy attack and defences, side by side on bytecode

One attacker (`OnceAttacker`, which re-enters `withdraw()` exactly once) is run against the three
banks of `contracts/src/reentrancy/Banks.sol` from the same starting world: the bank holds a
victim's 2 ether (recorded in `balances[victim]`), and the attacker's account holds 1 ether to
deposit. Each run is evaluated by the kernel with the real Keccak-256 on the compiled runtime
code, and reported as `(success, bank ether, balances[victim], attacker ether)`:

| Bank | result | solvent? |
|---|---|---|
| `VulnerableBank` (send before debit) | `(true, 1e18, 2e18, 2e18)` | **no**: holds 1 ether, owes 2 |
| `CEIBank` (debit before send) | `(true, 2e18, 2e18, 1e18)` | yes: the re-entry withdrew 0 |
| `GuardedBank` (OpenZeppelin `ReentrancyGuard`) | `(false, 2e18, 2e18, 0)` | yes: the whole call reverts |

`vulnerable_drained` witnesses the exploit (the bank ends insolvent); `cei_solvent` and
`guarded_solvent` witness the two defences (the bank keeps the victim's ether).
-/

namespace Examples.Reentrancy.Defended
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Solidity Examples.Reentrancy.Contracts

/-- One ether in wei. -/
def ether : Nat := 10 ^ 18
/-- The victim, credited with 2 ether in the bank. -/
def victim : Address := 0xB0B
/-- The attacker's externally owned account, which sends the transaction. -/
def eoa : Address := 0xA11CE

/-- The storage slot of `balances[a]` (`keccak256(a ‖ 0)`). -/
def balanceSlot (crypto : Crypto) (a : Address) : Word := mappingSlot crypto (Word.ofAddress a) 0

/-- The world before the attack, for a bank with the given code and address: the bank holds the
victim's 2 ether (in `balances[victim]`), the attacker contract is deployed, and the attacker's
account holds 1 ether. -/
def world (bankCode : ByteArray) (bank : Address) : World :=
  ((∅ : World).insert bank
      { nonce := 1, balance := BitVec.ofNat 256 (2 * ether), code := bankCode,
        storage := (∅ : Storage).insert (balanceSlot Crypto.real victim)
          (BitVec.ofNat 256 (2 * ether)) }
    |>.insert OnceAttacker.address { nonce := 1, code := OnceAttacker.runtimeCode })
    |>.insert eoa { balance := BitVec.ofNat 256 ether }

/-- The attack transaction: `eoa` calls `attacker.attack(bank)` with 1 ether. -/
def msg (bank : Address) : Message where
  caller := eoa
  target := some OnceAttacker.address
  currentTarget := OnceAttacker.address
  gas := 3000000
  value := BitVec.ofNat 256 ether
  data := Abi.encodeCall 0xd018db3e [Word.ofAddress bank]
  codeAddress := some OnceAttacker.address
  code := OnceAttacker.runtimeCode
  depth := 0
  shouldTransferValue := true
  isStatic := false
  accessedAddresses := (∅ : AddressSet).insert eoa |>.insert OnceAttacker.address
  accessedStorageKeys := ∅

/-- The result of the attack against a bank: success flag, the bank's ether, `balances[victim]`,
and the attacker contract's ether. -/
def run (bankCode : ByteArray) (bank : Address) : Option (Bool × Nat × Nat × Nat) :=
  (Interpreter.processMessageCall 100000 { crypto := Crypto.real }
    (world bankCode bank) ∅ (msg bank)).toOption.map
      (fun r => (r.success, (r.world.balance bank).toNat,
        (r.world.sload bank (balanceSlot Crypto.real victim)).toNat,
        (r.world.balance OnceAttacker.address).toNat))

/-- **`VulnerableBank` is drained.** The attack succeeds; the bank is left holding 1 ether while
`balances[victim]` still claims 2, and the attacker holds 2 ether (1 deposited, 2 withdrawn). -/
theorem vulnerable_run :
    run VulnerableBank.runtimeCode VulnerableBank.address = some (true, ether, 2 * ether, 2 * ether) := by
  kernel_decide

/-- **`CEIBank` resists.** The attack succeeds but the re-entrant `withdraw()` reads a zero
balance, so the bank keeps the victim's 2 ether and the attacker recovers only its deposit. -/
theorem cei_run :
    run CEIBank.runtimeCode CEIBank.address = some (true, 2 * ether, 2 * ether, ether) := by
  kernel_decide

/-- **`GuardedBank` resists.** The re-entrant `withdraw()` reverts at the reentrancy guard and the
whole transaction reverts; the bank keeps the victim's 2 ether. -/
theorem guarded_run :
    run GuardedBank.runtimeCode GuardedBank.address = some (false, 2 * ether, 2 * ether, 0) := by
  kernel_decide

/-- Solvency: the bank's ether covers what it still owes the victim. -/
def Solvent (r : Bool × Nat × Nat × Nat) : Prop := r.2.2.1 ≤ r.2.1

/-- **The exploit breaks solvency** of `VulnerableBank`. -/
theorem vulnerable_drained : ∃ r, run VulnerableBank.runtimeCode VulnerableBank.address = some r ∧
    ¬ Solvent r := by
  exact ⟨_, vulnerable_run, by unfold Solvent ether; decide⟩

/-- **Checks-effects-interactions keeps `CEIBank` solvent.** -/
theorem cei_solvent : ∃ r, run CEIBank.runtimeCode CEIBank.address = some r ∧ Solvent r :=
  ⟨_, cei_run, by unfold Solvent ether; decide⟩

/-- **The reentrancy guard keeps `GuardedBank` solvent.** -/
theorem guarded_solvent : ∃ r, run GuardedBank.runtimeCode GuardedBank.address = some r ∧ Solvent r :=
  ⟨_, guarded_run, by unfold Solvent ether; decide⟩

end Examples.Reentrancy.Defended
