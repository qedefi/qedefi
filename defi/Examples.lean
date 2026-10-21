import Examples.Basic.AddStore
import Examples.Basic.Mcopy
import Examples.Basic.Sum
import Examples.Basic.Token
import Examples.Basic.TwoContracts
import Examples.Basic.VaultTotalSupply
import Examples.Deployment
import Examples.Differential.Family
import Examples.Differential.Gen
import Examples.Differential.Local
import Examples.Differential.Main
import Examples.Differential.Rpc
import Examples.OpenZeppelin.Contracts.Deploy
import Examples.OpenZeppelin.Contracts.OzAsset
import Examples.OpenZeppelin.Contracts.OzVault
import Examples.Solmate.Contracts.Deploy
import Examples.Solmate.Contracts.SolmateAsset
import Examples.Solmate.Contracts.SolmateVault
import Examples.Solmate.ERC20.Approve
import Examples.Solmate.ERC20.BalanceOf
import Examples.Solmate.ERC20.Events
import Examples.Solmate.ERC20.EventsTransfer
import Examples.Solmate.ERC20.Malformed
import Examples.Solmate.ERC20.MintBurn
import Examples.Solmate.ERC20.Permit
import Examples.Solmate.ERC20.Spec
import Examples.Solmate.ERC20.Strings
import Examples.Solmate.ERC20.StringsCode
import Examples.Solmate.ERC20.StringsVault
import Examples.Solmate.ERC20.Transfer
import Examples.Solmate.ERC20.TransferFrom
import Examples.Solmate.ERC4626.Abstraction
import Examples.Solmate.ERC4626.Convert
import Examples.Solmate.ERC4626.ConvertGas
import Examples.Solmate.ERC4626.Deposit
import Examples.Solmate.ERC4626.DepositInternal
import Examples.Solmate.ERC4626.Events
import Examples.Solmate.ERC4626.EventsConvert
import Examples.Solmate.ERC4626.EventsEntry
import Examples.Solmate.ERC4626.EventsInternal
import Examples.Solmate.ERC4626.EventsShares
import Examples.Solmate.ERC4626.EventsSharesCode
import Examples.Solmate.ERC4626.Invariants.Calldata
import Examples.Solmate.ERC4626.Invariants.Deployed
import Examples.Solmate.ERC4626.Invariants.Events
import Examples.Solmate.ERC4626.Invariants.System
import Examples.Solmate.ERC4626.LowGas.AnyGas
import Examples.Solmate.ERC4626.LowGas.Certify
import Examples.Solmate.ERC4626.LowGas.Code
import Examples.Solmate.ERC4626.LowGas.Frames
import Examples.Solmate.ERC4626.LowGas.Targets
import Examples.Solmate.ERC4626.Malformed
import Examples.Solmate.ERC4626.MulDiv
import Examples.Solmate.ERC4626.Nested.Calls
import Examples.Solmate.ERC4626.Nested.Coverage
import Examples.Solmate.ERC4626.Nested.Invariants
import Examples.Solmate.ERC4626.Nested.Permit
import Examples.Solmate.ERC4626.Nested.System
import Examples.Solmate.ERC4626.Nested.Views
import Examples.Solmate.ERC4626.Permit
import Examples.Solmate.ERC4626.PermitSpec
import Examples.Solmate.ERC4626.SafeTransfer
import Examples.Solmate.ERC4626.SafeTransferFrom
import Examples.Solmate.ERC4626.Shares
import Examples.Solmate.ERC4626.SharesBase
import Examples.Solmate.ERC4626.SharesRep
import Examples.Solmate.ERC4626.SharesCode
import Examples.Solmate.ERC4626.SharesFrame
import Examples.Solmate.ERC4626.Strings
import Examples.Solmate.ERC4626.StringsCode
import Examples.Solmate.ERC4626.StringsCommon
import Examples.Solmate.ERC4626.UnknownSelectors
import Examples.Solmate.ERC4626.Views
import Examples.Solmate.ERC4626.ViewsSpec
import Examples.Solmate.ERC4626.Withdraw
import Examples.Solmate.ERC4626.WithdrawInternal
import Examples.Tests.Contracts
import Examples.Tests.Solidity
import Examples.Tests.Strings

/-!
# Examples

Worked examples: small demos (`Examples.Basic`), the Solmate vault and asset verified
end to end (`Examples.Solmate`), the OpenZeppelin contracts (`Examples.OpenZeppelin`),
differential testing against anvil (`Examples.Differential`) and contract tests
(`Examples.Tests`).
-/
