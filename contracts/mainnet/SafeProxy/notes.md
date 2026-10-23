# SafeProxy (Safe v1.5.0)

`runtime.hex` is the code of a Safe v1.5.0 proxy created by the v1.5.0 `SafeProxyFactory`
(`0x14F2982D601c9458F93bd70B218933A6f8165e7b`) with singleton `SafeSingleton`
(`0xFf51A5898e281Db6DfC7855790607438dF2ca44b`). Every such proxy has this code.

`source/contracts/proxies/SafeProxy.sol` is the file of the `safe-global/safe-smart-account`
tag `v1.5.0`, not Sourcify's copy: Sourcify verified this address with an older text of the
file (different comments) by replacing the CBOR metadata (`sourcify.json`,
`runtimeTransformations`). With the tag's file, solc 0.7.6 (optimizer off) reproduces
`runtime.hex` byte for byte, metadata included; `scripts/build-contracts.sh` checks this.
Rerunning `scripts/fetch-mainnet.sh` overwrites the file with Sourcify's copy.
