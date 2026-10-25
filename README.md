# qedefi - Open formal verification for DeFi

A growing corpus of Lean theorems about deployed EVM bytecode.

## Why

Formal verification is the only defense against a superintelligent cyberattacker.

Frontier LLMs write and reason about Lean exceptionally well - to the point where they can advance unsolved open problems in mathematics.

An audit checks some inputs, and an attacker needs only one. A proof covers every input, and the Lean kernel checks it, so it doesn't matter who or what wrote it.

## Progress

We build up from the EVM to the standard building blocks of DeFi, and then to the protocols made of them.

`evm-lean` is our Lean semantics for the EVM. It passes all 82,618 official Ethereum fixtures, and every proof here reasons over it.

Proved on bytecode, for any transaction:

- WETH9 (mainnet): the ether it holds covers every token balance.
- Safe v1.5.0 (mainnet) owning an OpenZeppelin proxy: fewer than `threshold` signers can't upgrade it.
- Solmate's ERC-4626 vault stays solvent, and users can't lower its share price.
- Aave V3's aWETH (mainnet) ignores Pool-only calls from anyone but the Pool.

Next are the remaining ERC-20s and vaults, then Aave V3 end to end and Uniswap. The full list is in [docs/status.md](docs/status.md).

## Standard

A theorem here holds for the bytecode as deployed, for any transaction from anyone, at any gas and call depth, with every other contract hostile, including those that call back in. Hash functions stay abstract; where a proof needs two storage slots not to collide, that is a hypothesis of the theorem.

We trust the Lean kernel, our EVM definition and Lean's standard axioms. No `sorry`, no new axioms (`scripts/check-trust.sh`).

The kernel can't tell whether a theorem states what you meant. Statements are kept short enough to read, and never weakened to get a proof through.

Keys, bridges, front ends and oracles are out of scope.

## Contributing

Lend us your AI compute. The kernel rejects wrong proofs, so nobody has to vet you or your agent, and every proof becomes a lemma for the next one. Attackers already spend compute on these contracts.

Agents start at [AGENTS.md](AGENTS.md). People help most by reviewing theorem statements; see [CONTRIBUTING.md](CONTRIBUTING.md). Report live exploits privately ([SECURITY.md](SECURITY.md)).

## Build

```bash
lake build && lake test
cd qedefi && lake exe cache get && lake build
```

Layout, conformance results and how to depend on the packages: [docs/status.md](docs/status.md). Writing proofs: [docs/proving.md](docs/proving.md).

## License

GPL-3.0 ([LICENSE](LICENSE)). Contract sources under `contracts/` keep their own licenses.
