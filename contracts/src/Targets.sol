// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

// Compilation root for the verification targets. The deployed contracts are:
//   Solmate: MockERC20 (asset), MockERC4626 (vault)        -- vendored, unmodified
//   OpenZeppelin: ERC20Mock (asset), OzVault (vault, below) -- ERC20Mock vendored, unmodified
import {MockERC20} from "solmate/test/utils/mocks/MockERC20.sol";
import {MockERC4626} from "solmate/test/utils/mocks/MockERC4626.sol";
import {ERC20Mock} from "@openzeppelin/contracts/mocks/token/ERC20Mock.sol";
import {OzVault} from "./OzVault.sol";
