# System contracts

The runtime code of the four system contracts a block calls from `SYSTEM_ADDRESS`, one hex file
each (no `0x` prefix). The Lean constants `EvmLogic.Chain.beaconRootsCode`,
`historyStorageCode`, `withdrawalRequestCode` and `consolidationRequestCode`
(`EvmLogic/Chain/SystemCode.lean`) hold the same bytes.

| File | EIP | Address | Bytes | Code hash (keccak-256) |
|---|---|---|---|---|
| `beacon-roots.hex` | EIP-4788 | `0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02` | 97 | `0xf57acd40259872606d76197ef052f3d35588dadf919ee1f0e3cb9b62d3f4b02c` |
| `history-storage.hex` | EIP-2935 | `0x0000F90827F1C53a10cb7A02335B175320002935` | 83 | `0x6e49e66782037c0555897870e29fa5e552daf4719552131a0abce779daec0a5d` |
| `withdrawal-request.hex` | EIP-7002 | `0x00000961Ef480Eb55e80D19ad83579A64c007002` | 504 | `0x0345a365d2f4c5975b9f1599abe0a2ee76b7a3a731bc68781bd04c84e4858f50` |
| `consolidation-request.hex` | EIP-7251 | `0x0000BBdDc7CE488642fb579F8B00f3a590007251` | 414 | `0x78c6cb5202685228bbcbfb992b1c4e116c7ec5ef11e25b8e92716cfc628ddd60` |

Where they come from:

- **Ethereum mainnet**: `eth_getCode` of each address at block 26,270,327 (October 2026); the
  code hashes are the `codeHash` that `eth_getProof` returns for the same accounts. Each account
  has nonce 1: it was deployed by the keyless transaction its EIP specifies.
- **Conformance fixtures**: the same bytes are the code of these accounts in the pre-state of
  the execution-spec-tests v5.4.0 Prague blockchain tests (`scripts/fetch-eest-fixtures.sh`),
  e.g. `prague/eip7251_consolidations/test_consolidation_requests.json`.
- **Kernel check**: `EvmLogic/Chain/SystemCodeHash.lean` recomputes the four code hashes from the
  Lean constants with the semantics' Keccak-256.

Reproduce (any Ethereum JSON-RPC endpoint):

```bash
for a in 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02 0x0000F90827F1C53a10cb7A02335B175320002935 \
         0x00000961Ef480Eb55e80D19ad83579A64c007002 0x0000BBdDc7CE488642fb579F8B00f3a590007251; do
  curl -s "$RPC_URL" -H 'content-type: application/json' \
    -d "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"eth_getCode\",\"params\":[\"$a\",\"latest\"]}"
  echo
done
```
