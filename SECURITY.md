# Security

QEDefi proves properties of deployed contracts, so working on it can uncover a real
vulnerability: a statement that turns out false for mainnet bytecode, or a counterexample found
while proving.

**Do not open a public issue or pull request for it.** Report it privately through
[GitHub's private vulnerability reporting](https://github.com/qedefi/qedefi/security/advisories/new)
for this repository. Include the contract, its address and block, and the Lean statement or the
transaction that shows the problem. We coordinate disclosure with the contract's maintainers
(through their own security contact or bug-bounty program) before anything is published.

A bug in `EvmLean` itself (a divergence from the EVM) is not sensitive: open an issue with the
fixture or transaction that shows it.
