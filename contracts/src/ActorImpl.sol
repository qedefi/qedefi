// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

/// @notice A minimal implementation contract behind the OpenZeppelin `TransparentUpgradeableProxy`
/// target: one storage word (`value`, slot 0) and an unrestricted setter. No immutables.
contract ActorImpl {
    uint256 public value;

    function set(uint256 v) external {
        value = v;
    }
}
