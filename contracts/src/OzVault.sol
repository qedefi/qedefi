// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

import {IERC20, ERC20} from "@openzeppelin/contracts/token/ERC20/ERC20.sol";
import {ERC4626} from "@openzeppelin/contracts/token/ERC20/extensions/ERC4626.sol";

/// @notice The OpenZeppelin verification target: the stock ERC-4626 implementation with
/// nothing overridden. `totalAssets() = asset.balanceOf(address(this))` and
/// `_decimalsOffset() = 0` (one virtual share and one virtual asset).
contract OzVault is ERC4626 {
    constructor(IERC20 asset_) ERC20("OZ Vault", "ozVLT") ERC4626(asset_) {}
}
