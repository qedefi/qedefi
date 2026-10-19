# `name()` / `symbol()`: string getters of the compiled vault and asset

Solmate's `ERC20` declares `string public name; string public symbol;` (slots 0 and 1). The
theorems here cover the compiled getters of **both** contracts (`SolmateVault.runtimeCodeWith i`,
`SolmateAsset.runtimeCodeWith ia`, arbitrary immutables), for **every** string the storage can
hold (short and long), for every `Crypto`, with only the standard axioms.

| view | frame form (any frame, `Halts`) | top level (`processMessageCall`) | canonical string |
|---|---|---|---|
| vault `name()` | `vaultName_refines` | `vaultName_call` | `vaultName_canonical` (`"Solmate Vault"`) |
| vault `symbol()` | `vaultSymbol_refines` | `vaultSymbol_call` | `vaultSymbol_canonical` (`"svSAST"`) |
| asset `name()` | `assetName_refines` | `assetName_call` | `assetName_canonical` (`"Solmate Asset"`) |
| asset `symbol()` | `assetSymbol_refines` | `assetSymbol_call` | `assetSymbol_canonical` (`"SAST"`) |

## Statements

* **Abstraction** (`EvmLeanProofs/Solidity/Strings.lean`): `stringAt crypto w a p : Option ByteArray`
  is `Str.decode crypto (w.sload a) p`, exactly what the compiled getter reads: the slot word
  `S`; its length `Str.slotLen S` (`S >> 1`, masked with `0x7f` when `S` is even);
  `none` when `extract_byte_array_length` panics (`Str.slotOk`: even with length ≥ 32 or odd
  with length < 32); a short string is the first `len` bytes of `S`; a long one the first `len`
  bytes of the words at `arrayDataSlot crypto p + j = keccak256(p) + j` (`Str.longData`).
* **ABI**: `Abi.encodeString s = ofWord 0x20 ‖ ofWord |s| ‖ s ‖ zeros` (padded to 32 bytes).
* **Frame form**: `X_refines m (h : StringPre code slot m) (hd : NoArgCall m.frame.msg.data sel) :
  Halts m (StringPost m (stringAt m.ctx.crypto m.world m.frame.msg.currentTarget slot))`;
  `StringPost`: world unchanged, and `o = .success (Abi.encodeString s)` for `some s`, a revert
  for `none`. `StringPre`: fresh frame of the code, no value,
  `Str.getterGas (Str.slotLen (sload slot)) ≤ gas < 2⁶⁴`, calldata `< 2⁶⁴` bytes.
* **Top level**: `X_call (hdep : Deployed w vault asset) (hdeleg) (hgas : Str.getterGas (Str.slotLen
  (w.sload a slot)) ≤ gas) (hgas' : gas < 2⁶⁴) : ∃ n, ∀ fuel ≥ n, ∃ res, processMessageCall … (callMsg
  (w.code a) a caller (Abi.encodeCall sel []) gas wa wk) = .ok res ∧ res.world = w ∧
  StringResult res (stringAt ctx.crypto w a slot)`.
* **Canonical**: if the slot holds `Str.shortWord "Solmate Vault".toUTF8` (Solidity's short
  form; `#guard`-checked against the constructor arguments) and `10430 ≤ gas < 2⁶⁴`, the call
  succeeds with output `Abi.encodeString "Solmate Vault".toUTF8`.

**Hypotheses.** Gas: `Str.getterGas L = 8000 + 2400 ⌈L/32⌉ + Gas.memoryCost (256 + 64 ⌈L/32⌉)`
(one cold `SLOAD` per data word, the copy and the return buffer); the interpreter tests check
it against measured usage (e.g. 72 144 ≤ 85 026 for 1000 bytes). **No Keccak hypothesis**:
reading a long string touches `keccak256(slot) + j` for whatever `Crypto` is, and the
abstraction is defined through the same slots. Freshness would only matter for *writes*
(none here) or for relating `stringAt` to another storage view.

**Encoding lemmas** (`EvmLeanProofs/Solidity/StringsEncoding.lean`): `Str.decode_shortWord`
(`s.size ≤ 31`, slot = `Str.shortWord s` ⇒ decodes to `s`), `Str.decode_of_storesLong`
(`Str.StoresLong`: `2|s|+1` in the slot, `Str.chunk s j` at `keccak256(p) + j` ⇒ decodes to `s`),
`Str.slotLen_shortWord`, `Bytes.ofWord_toWord`, `Bytes.toNat_div_mod`.

## Files

| file | contents |
|---|---|
| `EvmLeanProofs/Solidity/StringsStep.lean` | `step_mcopy`, `step_mcopy_zero`, `mcopyCost`, `Memory.mcopy` |
| `EvmLeanProofs/Solidity/StringsTactic.lean` | `pwp_mcopy`, `pwp_mcopy_zero`, `pwp_msteps`; `psol_mcopy`, `psol_mcopy_zero`, `psol_msteps` (after a copy, `mcopy_size_facts` records the memory size for `evm_gas`); `wp_generalize_mem`; `pwp_mload_in`, `pwp_return_in` (accesses inside a memory of symbolic size); `Memory.getD_bytes_mcopy`, `read_mcopy(_of_disjoint)`, `size_mcopy`; `Gas.extendMemory_one/_two`, `memoryCost_eq`, `mcopyCost_eq`, `memoryCost_of_le`, `Gas.memoryCost_mono` |
| `EvmLeanProofs/Solidity/Strings.lean` | `Str.slotLen`, `slotOk`, `decode`, `longData`, `wordsFrom`, `shortWord`, `chunk`, `StoresLong`, `getterGas`; `stringAt`; `Abi.encodeString` |
| `EvmLeanProofs/Solidity/StringsWord.lean` | word facts of `extract_byte_array_length` and the copy (`and_one_of_even`, `shr_one_and_127`, `div_32_mul_32`, `and_notMask31`, …) |
| `EvmLeanProofs/Solidity/StringsEncoding.lean` | the encoding lemmas above |
| `EvmLeanProofs/Solidity/StringsExamples.lean` | `copy42_output` (`psol_msteps`), `copy42_wp` (`pwp_msteps`): a program with an `MCOPY` |
| `StringsVault.lean` | `StringPost`; short strings: `vaultEncodeShort_wp` (encoder from its `MCOPY`), `vaultStringShort_wp` |
| `StringsVaultLong.lean` | long strings: `VaultCopy` (loop invariant, gas as the potential `gasLeft + memoryCost size`), `vaultCopyBody_wp`, `vaultCopyLoop_wp` (`WP.loop_nat`), `vaultLongTail_wp` (encoder with symbolic head), `vaultStringLong_wp` |
| `StringsVaultSpec.lean` | `StringPre`, `vaultString_wp`, `vaultName/Symbol_refines`, `StringResult`, `string_call`, `vaultName/Symbol_call` |
| `StringsAsset*.lean` | the same for the asset (same code at other offsets) |
| `StringsCanonical.lean` | `stringAt_shortWord`, `getterGas_shortWord`, the four `*_canonical` corollaries |
| `EvmLeanTest/Strings.lean` | canonical slot words and encodings; the compiled getters run in the interpreter (real Keccak) against `Str.decode`, short/empty/long/inconsistent slots, gas within `getterGas` |

## Notes for the coordinator

* The step-lemma registries (`Program.stepLemmasFor`, `Exec.stepTactics`) are closed lists, so
  `MCOPY` is added by wrapper tactics (`pwp_msteps`, `psol_msteps`) rather than by editing them.
  Adding `0x5e ↦ step_mcopy, step_mcopy_zero` to both tables (and `mcopyCost` to the
  normalization) would make plain `pwp_steps`/`psol_steps` handle literal-length copies.
* `Shares.lean`'s module doc says `name()`/`symbol()` are not covered for lack of an `MCOPY`
  step lemma; this is now superseded (not edited, per ownership).
* Two pitfalls met on the way (worth knowing for other symbolic-memory proofs):
  `omega` hits "maximum recursion depth" on `(n - k) * 2300` (write `2300 * (n - k)`), and a
  `WP` postcondition that mentions a large structure predicate slows `pwp_steps` to a crawl
  (generalize it first: `generalize hQ : (fun m' => …) = Q`).
* Memory costs with symbolic sizes are not handled by `evm_gas`; the proofs state each
  expansion as `Gas.memoryCost new - Gas.memoryCost old` (`Gas.extendMemory_one/_two`),
  generalize the `Gas.memoryCost` atoms and let `omega` telescope them.

## Build

`cd specs && lake build`. Times (M-series laptop): `StringsVault` 63 s, `StringsVaultLong` 55 s,
`StringsAsset` 50 s, `StringsAssetLong` 44 s, `StringsVaultSpec` 42 s, `StringsAssetSpec` 15 s,
`StringsCanonical` 4 s; about 3 min wall clock in parallel. Root files (`EvmLeanProofs/Solidity/Strings*`,
`EvmLeanTest/Strings`) build in a few seconds each.
