import EvmLean.Fork

/-!
# Per-chain configuration

Alchemy network names (the RPC URL is built from `ALCHEMY_KEY` when no `--rpc` is given),
Blockscout instances (verified sources when Sourcify has none) and the fork schedule.
-/

namespace Snapshot

open EvmLean

/-- Alchemy's network name for a chain id. -/
def alchemyNetwork? : Nat → Option String
  | 1 => some "eth-mainnet"
  | 10 => some "opt-mainnet"
  | 56 => some "bnb-mainnet"
  | 100 => some "gnosis-mainnet"
  | 130 => some "unichain-mainnet"
  | 137 => some "polygon-mainnet"
  | 146 => some "sonic-mainnet"
  | 8453 => some "base-mainnet"
  | 42161 => some "arb-mainnet"
  | 43114 => some "avax-mainnet"
  | 59144 => some "linea-mainnet"
  | 80094 => some "berachain-mainnet"
  | 534352 => some "scroll-mainnet"
  | _ => none

/-- The public Blockscout API base for a chain id. -/
def blockscoutBase? : Nat → Option String
  | 1 => some "https://eth.blockscout.com"
  | 10 => some "https://optimism.blockscout.com"
  | 100 => some "https://gnosis.blockscout.com"
  | 130 => some "https://unichain.blockscout.com"
  | 137 => some "https://polygon.blockscout.com"
  | 8453 => some "https://base.blockscout.com"
  | 42161 => some "https://arbitrum.blockscout.com"
  | 534352 => some "https://scroll.blockscout.com"
  | _ => none

/-- The fork in force at `timestamp`, where the schedule is known (Ethereum mainnet only:
other chains have their own upgrade names and EVM differences, so their fork is set by hand). -/
def forkAt? (chainId timestamp : Nat) : Option Fork :=
  if chainId = 1 then
    if timestamp ≥ 1764798551 then some .osaka        -- Fusaka, 2025-12-03
    else if timestamp ≥ 1746612311 then some .prague  -- Pectra, 2025-05-07
    else if timestamp ≥ 1710338135 then some .cancun  -- Dencun, 2024-03-13
    else none
  else none

end Snapshot
