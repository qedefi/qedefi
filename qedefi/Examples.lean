import Examples.Actor.RoleOracle
import Examples.Actor.SafeProxyAdmin
import Examples.Actor.SafeProxyAdminLib
import Examples.Actor.Timelock
import Examples.Basic.AddStore
import Examples.Basic.Mcopy
import Examples.Basic.Sum
import Examples.Basic.Token
import Examples.Basic.TwoContracts
import Examples.Basic.VaultTotalSupply
import Examples.Deployment
import Examples.Reentrancy.Contracts.Attacker
import Examples.Reentrancy.Contracts.AttackerData
import Examples.Reentrancy.Contracts.CEIBank
import Examples.Reentrancy.Contracts.CEIBankData
import Examples.Reentrancy.Contracts.GuardedBank
import Examples.Reentrancy.Contracts.GuardedBankData
import Examples.Reentrancy.Contracts.OnceAttacker
import Examples.Reentrancy.Contracts.OnceAttackerData
import Examples.Reentrancy.Contracts.VulnerableBank
import Examples.Reentrancy.Contracts.VulnerableBankData
import Examples.Reentrancy.Defended
import Examples.Reentrancy.Exploit
import Examples.Reentrancy.Solvency.CEI
import Examples.Reentrancy.Solvency.Guarded

/-!
# Examples

Small demonstrations of the program logic (`Examples.Basic`), actor models of access control
(`Examples.Actor`), and the reentrancy demonstrators: two defended banks proved solvent and a
vulnerable one drained by a proved attack (`Examples.Reentrancy`). The verified contracts are in
`Verified`.
-/
