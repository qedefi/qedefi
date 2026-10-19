// SPDX-License-Identifier: AGPL-3.0
pragma solidity 0.8.28;

// a16z ERC-4626 property suite (github.com/a16z/erc4626-tests) against both verification
// targets, deployed with the canonical parameters. Run with `contracts/run-a16z.sh`.
// This is a sanity check of the targets, not of evm-lean.

import "erc4626-tests/ERC4626.test.sol";

import {MockERC20} from "solmate/test/utils/mocks/MockERC20.sol";
import {MockERC4626} from "solmate/test/utils/mocks/MockERC4626.sol";
import {ERC20Mock} from "@openzeppelin/contracts/mocks/token/ERC20Mock.sol";
import {IERC20 as OzIERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import {OzVault} from "../src/OzVault.sol";

/// Solmate MockERC4626 over MockERC20, with the setup recommended by the suite.
contract SolmateERC4626StdTest is ERC4626Test {
    function setUp() public override {
        _underlying_ = address(new MockERC20("Solmate Asset", "SAST", 18));
        _vault_ = address(new MockERC4626(MockERC20(_underlying_), "Solmate Vault", "svSAST"));
        _delta_ = 0;
        _vaultMayBeEmpty = false;
        _unlimitedAmount = false;
        _skipRoundTripShares = false;
    }
}

/// OpenZeppelin ERC4626 (OzVault) over ERC20Mock, with the setup OpenZeppelin uses for its
/// own run of the suite (empty vaults and unlimited amounts allowed).
contract OzERC4626StdTest is ERC4626Test {
    function setUp() public override {
        _underlying_ = address(new ERC20Mock());
        _vault_ = address(new OzVault(OzIERC20(_underlying_)));
        _delta_ = 0;
        _vaultMayBeEmpty = true;
        _unlimitedAmount = true;
        _skipRoundTripShares = false;
    }
}
