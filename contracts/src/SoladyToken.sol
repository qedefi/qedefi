// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

import {ERC20} from "solady/tokens/ERC20.sol";

/// @notice The Solady verification target: Solady's `ERC20` (vendored, unmodified) made
/// concrete. Constant metadata, unrestricted `mint`/`burn` (like OpenZeppelin's
/// `ERC20Mock`), nothing else overridden: Permit2 infinite allowance stays enabled
/// (`_givePermit2InfiniteAllowance() = true`), the EIP-712 name hash is computed from `name()`.
/// No immutables and no Solidity state variables: all storage is Solady's hashed layout.
contract SoladyToken is ERC20 {
    function name() public pure override returns (string memory) {
        return "Solady Token";
    }

    function symbol() public pure override returns (string memory) {
        return "SLDY";
    }

    function mint(address to, uint256 amount) public {
        _mint(to, amount);
    }

    function burn(address from, uint256 amount) public {
        _burn(from, amount);
    }
}
