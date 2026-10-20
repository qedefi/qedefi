// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

import {IERC20, ERC20} from "@openzeppelin/contracts/token/ERC20/ERC20.sol";
import {ERC4626} from "@openzeppelin/contracts/token/ERC20/extensions/ERC4626.sol";

/// @notice The OpenZeppelin vault with a decimals offset: the stock ERC-4626 implementation
/// with only `_decimalsOffset()` overridden to 3 (10³ virtual shares per virtual asset), the
/// setting in which OpenZeppelin's bound on the inflation (donation) attack is meaningful.
/// `decimals() = asset decimals + 3`.
contract OzVaultOffset is ERC4626 {
    constructor(IERC20 asset_) ERC20("OZ Vault d3", "ozVLT3") ERC4626(asset_) {}

    function _decimalsOffset() internal pure override returns (uint8) {
        return 3;
    }
}
