import EvmLogic.Chain.SystemCode
import EvmLean.Crypto.Keccak

/-!
# The code hashes of the system contracts

The Keccak-256 hash of each canonical code (`EvmLogic.Chain.systemCode`) is the code hash of the
system contract on Ethereum mainnet (`eth_getProof`), recomputed by the kernel with the
semantics' own Keccak-256 (`Keccak.hash256`, the `keccak256` of `Crypto.real`). A separate
module: the four hashes take about 13 s of kernel time, which nothing downstream waits for.
-/

namespace EvmLogic.Chain
open EvmLean

theorem keccak_beaconRootsCode : Keccak.hash256 beaconRootsCode =
    0xf57acd40259872606d76197ef052f3d35588dadf919ee1f0e3cb9b62d3f4b02c := by decide +kernel
theorem keccak_historyStorageCode : Keccak.hash256 historyStorageCode =
    0x6e49e66782037c0555897870e29fa5e552daf4719552131a0abce779daec0a5d := by decide +kernel
theorem keccak_withdrawalRequestCode : Keccak.hash256 withdrawalRequestCode =
    0x0345a365d2f4c5975b9f1599abe0a2ee76b7a3a731bc68781bd04c84e4858f50 := by decide +kernel
theorem keccak_consolidationRequestCode : Keccak.hash256 consolidationRequestCode =
    0x78c6cb5202685228bbcbfb992b1c4e116c7ec5ef11e25b8e92716cfc628ddd60 := by decide +kernel

end EvmLogic.Chain
