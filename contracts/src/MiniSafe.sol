// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

/// @notice A minimal threshold multisig in the style of Safe 1.5.0, the owner of the
/// `ProxyAdmin` in the bytecode upgrade guard (`qedefi/Examples/Actor/Bytecode/SafeGuard.lean`).
/// Owners (`isOwner`), a threshold and a nonce in storage, fixed at deployment.
/// `execTransaction` calls `to` once `threshold` owners signed the transaction's digest, as
/// Safe's `checkNSignatures` with ECDSA signatures only: 65-byte `r ‖ s ‖ v` signatures
/// recovered by `ecrecover`, signers strictly increasing (hence distinct), each an owner.
/// Unlike Safe: no owner management, modules, guards, fallback handler, `approveHash`,
/// contract (EIP-1271) or `eth_sign` signatures, refunds, or `simulateAndRevert`.
contract MiniSafe {
    uint256 public threshold;
    uint256 public nonce;
    mapping(address => bool) public isOwner;

    constructor(address[] memory owners, uint256 _threshold) {
        require(_threshold >= 1 && _threshold <= owners.length, "threshold");
        for (uint256 i = 0; i < owners.length; i++) {
            address o = owners[i];
            require(o != address(0) && !isOwner[o], "owner");
            isOwner[o] = true;
        }
        threshold = _threshold;
    }

    /// The digest the owners sign: the chain, this Safe, the call and the nonce.
    function getTransactionHash(address to, uint256 value, bytes calldata data, uint256 _nonce)
        public
        view
        returns (bytes32)
    {
        return keccak256(abi.encode(block.chainid, address(this), to, value, keccak256(data), _nonce));
    }

    function execTransaction(address to, uint256 value, bytes calldata data, bytes calldata signatures)
        external
        payable
        returns (bool success)
    {
        bytes32 txHash = getTransactionHash(to, value, data, nonce);
        nonce++;
        checkSignatures(txHash, signatures);
        (success,) = to.call{value: value}(data);
    }

    function checkSignatures(bytes32 dataHash, bytes calldata signatures) internal view {
        uint256 t = threshold;
        require(signatures.length >= t * 65, "sigs");
        address lastOwner = address(0);
        for (uint256 i = 0; i < t;) {
            uint8 v;
            bytes32 r;
            bytes32 s;
            assembly ("memory-safe") {
                let p := add(signatures.offset, mul(i, 0x41))
                r := calldataload(p)
                s := calldataload(add(p, 0x20))
                v := byte(0, calldataload(add(p, 0x40)))
            }
            address currentOwner = ecrecover(dataHash, v, r, s);
            require(currentOwner > lastOwner && isOwner[currentOwner], "signer");
            lastOwner = currentOwner;
            unchecked {
                ++i;
            }
        }
    }
}
