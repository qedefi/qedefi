# Quickstart for agents

This file is the working contract for coding agents in this repository. The [README](README.md)
says why the repository exists; [docs/status.md](docs/status.md) lists what is proved, what comes
next, and the layout. Background: [docs/architecture.md](docs/architecture.md),
[docs/proving.md](docs/proving.md), [docs/conventions.md](docs/conventions.md).

QEDefi proves theorems about deployed EVM bytecode in Lean 4: an executable EVM semantics
(`EvmLean`), a proof library (`EvmLogic`), and DeFi models with verified contracts (`qedefi/`).

## Goal of a session

Close one open problem, or bring one measurably closer: a new theorem, a missing lemma, a faster
proof. The Lean kernel decides whether a proof is right, so nobody has to trust you, or your user.

## The loop

```bash
export PATH="$HOME/.elan/bin:$PATH"          # elan: https://github.com/leanprover/elan
lake build                                    # root package, about a minute
(cd qedefi && lake exe cache get && lake build)   # Mathlib cache, then a few minutes
```

1. **Pick.** An item from [CONTRIBUTING.md's open problems](CONTRIBUTING.md#open-problems) or the
   [Next list](docs/status.md#next). Check the open pull requests first: one titled
   `[wip] <item>` means someone is on it. Prefer a small, well-delimited piece (one function's
   summary, one token's refinement) over a whole row.
2. **Claim.** If you can open pull requests, push a branch named `<area>/<item>`
   (`tokens/usdt-transfer`) and open a **draft** pull request titled `[wip] <item>`. Push at
   least once a day; a draft with no push for 72 hours is free for anyone to take over. Without
   GitHub access, work anyway and say so to your user.
3. **Read before you write.** The document the item links to, then the closest finished proof:
   the Solmate vault (`qedefi/Verified/Solmate/`), WETH9 (`qedefi/Verified/WETH9/`)
   and the proxy guard (`qedefi/Verified/OpenZeppelin/Proxy/`) are the templates.
   [docs/proving.md](docs/proving.md) is the manual.
4. **Prove.** Lemmas worth reusing go into the libraries (`EvmLogic`, `QEDefi`); contract-specific
   proofs into `qedefi/Verified/<Project>/`, one directory per deployed system.
5. **Check.** `lake build --wfail` for the modules you touched, `scripts/check-trust.sh`, and for
   any refactor `scripts/compare-statements.py` (0 missing, 0 changed, 0 axiom changes).
6. **Submit.** Retitle the pull request as its final commit subject (see Commits), fill the
   credit section of the template (your user's handle, your model, the approximate agent hours),
   mark it ready and turn on auto-merge: `gh pr merge --auto --squash`. It merges when CI passes.
   If `main` moved under you and the pull request no longer builds on it, rebase on `main`, fix,
   and push again.

A session that ends without closing the item is still worth a push: commit the lemmas you
proved to the draft pull request and list the dead ends in its description, so the next agent
starts from there.

## Authorities

| What | Status |
|---|---|
| `EvmLean/` (the semantics) | **trusted**: change only in an issue-first pull request, then rerun conformance |
| Statements of existing theorems | **frozen**: a refactor never changes one (`scripts/compare-statements.py`) |
| `scripts/`, `.github/`, `tests/`, `contracts/` artifacts | **trusted**: the tools that check you |
| `EvmLogic/`, `qedefi/QEDefi/`, `qedefi/Verified/`, `qedefi/Examples/`, `docs/` | editable |

The rule behind the table: code that **proves** is yours to change; code that **defines** what
is being proved, or **checks** it, is not.

## Rules

- **Never** `sorry`, `axiom`, `native_decide`, `bv_decide` (it adds `Lean.ofReduceBool`),
  `debug.skipKernelTC` or any option that skips the kernel. The allowed axioms are `propext`,
  `Classical.choice` and `Quot.sound`.
- **Never weaken a statement** to make a proof go through. A new theorem's hypotheses are listed
  and justified in its docstring and must be satisfiable together; a theorem with contradictory
  hypotheses proves nothing.
- **You found a way to take funds from a deployed contract?** Stop. Do not commit it, do not put
  it in an issue or a pull request. Tell your user to report it privately ([SECURITY.md](SECURITY.md)).
- **Builds are incremental:** `lake build <Module>` from the package that owns the file
  (`qedefi/` for `qedefi/...`). Never delete `.lake/build`. One heavy build at a time.
- **Parallel agents on one machine:** one git worktree each
  (`git worktree add -b <branch> <path> main`), then copy the caches
  (`cp -cR .lake <wt>/.lake && cp -cR qedefi/.lake <wt>/qedefi/.lake`).
- **Keep notes** (what worked, what the kernel refused) in `notes.local.md`, which git ignores.
- **Stay out of shared files:** one item per pull request, in its own files. Do not edit the
  table in `docs/status.md` or the README; put the result in the pull request description and
  the maintainer updates them. New modules under `Verified/`, `Examples/` and `Difftest/` need no
  import list (the lakefile builds every file there).

## Commits

Pull requests are squash-merged: the title becomes the commit subject on `main`, the description
its body. So the title is an imperative line of at most 72 characters
(`Prove WETH9 withdraw for any gas`), and the description says why. Commits on your branch:

- The same style: an imperative summary line, a blank line, a body that says why.
- No `Co-Authored-By` or other attribution trailers for AI tools (Claude, Codex, Copilot), and no
  "Generated with" footers. Credit your model in the pull request template instead.
- Work-in-progress commits on your branch are fine: the squash merge drops them.

## Tools

The [`lean-lsp-mcp`](https://github.com/oOo0oOo/lean-lsp-mcp) server in `.mcp.json` gives goals,
diagnostics of one file and name search without builds: prefer it to `lake build` while proving.
For any Lean work, read [`.claude/skills/lean-evm/SKILL.md`](.claude/skills/lean-evm/SKILL.md)
first: the checklist of tactics, pitfalls and performance fixes, written for agents of any vendor.

## Prompt for your user

People contributing compute paste this into their agent:

```text
Clone https://github.com/totomanov/qedefi and follow AGENTS.md: pick one open problem nobody has
claimed, claim it with a draft pull request, and work until it is proved with
scripts/check-trust.sh passing or you run out of budget. Push what you have either way.
Never add sorry or axioms, never weaken a statement.
```
