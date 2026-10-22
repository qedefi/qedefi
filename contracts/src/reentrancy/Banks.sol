// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

import {ReentrancyGuard} from "@openzeppelin/contracts/utils/ReentrancyGuard.sol";

/// @notice The reentrancy demonstrators (docs/proving.md, "Untrusted callees and reentrancy").
/// Three ether banks with the same interface: `deposit()` credits `msg.value` to the caller,
/// `withdraw()` sends the caller's whole balance to it with a plain `call` (all remaining gas,
/// so the recipient's code may call back), `balances(a)` reads a balance.

/// @notice Sends before it debits: a recipient that calls `withdraw()` again from its
/// `receive()` is paid its balance once per nested call (the DAO bug).
contract VulnerableBank {
    mapping(address => uint256) public balances;

    function deposit() external payable {
        balances[msg.sender] += msg.value;
    }

    function withdraw() external {
        uint256 amount = balances[msg.sender];
        (bool ok,) = msg.sender.call{value: amount}("");
        require(ok);
        balances[msg.sender] = 0;
    }
}

/// @notice Checks-effects-interactions: the balance is debited before the call, so at the call
/// the storage already describes the state after the withdrawal.
contract CEIBank {
    mapping(address => uint256) public balances;

    function deposit() external payable {
        balances[msg.sender] += msg.value;
    }

    function withdraw() external {
        uint256 amount = balances[msg.sender];
        balances[msg.sender] = 0;
        (bool ok,) = msg.sender.call{value: amount}("");
        require(ok);
    }
}

/// @notice `VulnerableBank` with OpenZeppelin's `ReentrancyGuard` on both state-changing
/// functions: during the call the lock is held, so every callback that could write reverts.
contract GuardedBank is ReentrancyGuard {
    mapping(address => uint256) public balances;

    function deposit() external payable nonReentrant {
        balances[msg.sender] += msg.value;
    }

    function withdraw() external nonReentrant {
        uint256 amount = balances[msg.sender];
        (bool ok,) = msg.sender.call{value: amount}("");
        require(ok);
        balances[msg.sender] = 0;
    }
}

interface IBank {
    function deposit() external payable;
    function withdraw() external;
}

/// @notice The attacker of the exploit: deposits, withdraws, and withdraws again from
/// `receive()` while the bank still holds at least the amount being paid.
contract Attacker {
    function attack(IBank bank) external payable {
        bank.deposit{value: msg.value}();
        bank.withdraw();
    }

    receive() external payable {
        if (msg.sender.balance >= msg.value) IBank(msg.sender).withdraw();
    }
}

/// @notice An attacker that re-enters `withdraw()` exactly once (a storage flag stops the
/// recursion), so the exploit stays shallow. Against `VulnerableBank` one re-entry already
/// withdraws twice; against `CEIBank`/`GuardedBank` the re-entry withdraws zero or reverts.
contract OnceAttacker {
    bool private entered;

    function attack(IBank bank) external payable {
        bank.deposit{value: msg.value}();
        bank.withdraw();
    }

    receive() external payable {
        if (!entered) {
            entered = true;
            IBank(msg.sender).withdraw();
        }
    }
}
