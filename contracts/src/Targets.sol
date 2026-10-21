// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

// Compilation root for the verification targets. The deployed contracts are:
//   Solmate: MockERC20 (asset), MockERC4626 (vault)        -- vendored, unmodified
//   OpenZeppelin: ERC20Mock (asset), OzVault (vault, below) -- ERC20Mock vendored, unmodified
//   OpenZeppelin, decimals offset 3: ERC20Mock (asset), OzVaultOffset (vault, below)
//   Solady: SoladyToken (below; Solady's ERC20 vendored, unmodified)
//   Reentrancy demonstrators: VulnerableBank, CEIBank, GuardedBank, Attacker (reentrancy/Banks.sol)
// WETH9 and the mainnet tokens are not compiled here: their targets are the deployed mainnet
// bytecode (contracts/mainnet/).
import {MockERC20} from "solmate/test/utils/mocks/MockERC20.sol";
import {MockERC4626} from "solmate/test/utils/mocks/MockERC4626.sol";
import {ERC20Mock} from "@openzeppelin/contracts/mocks/token/ERC20Mock.sol";
import {OzVault} from "./OzVault.sol";
import {OzVaultOffset} from "./OzVaultOffset.sol";
import {SoladyToken} from "./SoladyToken.sol";
import {VulnerableBank, CEIBank, GuardedBank, Attacker} from "./reentrancy/Banks.sol";
