import Examples.Solmate.ERC20.StringsAssetSpec
import EvmLogic.Solidity.StringsEncoding

/-!
# `name()` / `symbol()` for the canonical deployment strings

The canonical deployment (`contracts/artifacts/deployment.json`) constructs the asset with
`("Solmate Asset", "SAST")` and the vault with `("Solmate Vault", "svSAST")`; Solidity stores
these short strings (at most 31 bytes) in their slots in the short form `Str.shortWord`. When
a slot holds that word, the getter returns its ABI encoding: corollaries of the `*_call`
theorems and of `Str.decode_shortWord`. Short strings live in the slot itself, so no Keccak
is involved at all (the theorems hold for every `Crypto`).

`stringAt_shortWord` is the general step: a slot holding `Str.shortWord s` reads as `s`.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

variable {ctx : Context} {w : World} {tr : TransientStorage} {vault asset caller : Address}
  {gas : Nat} {wa : AddressSet} {wk : StorageKeySet}

/-- A slot holding the short form of `s` reads as `s`. -/
theorem stringAt_shortWord {crypto : Crypto} {a : Address} {p : Word} {s : ByteArray}
    (hs : s.size ≤ 31) (h : w.sload a p = Str.shortWord s) : stringAt crypto w a p = some s :=
  Str.decode_shortWord crypto hs h

/-- The getter's gas for a short string slot. -/
theorem getterGas_shortWord {s : ByteArray} (hs : s.size ≤ 31) :
    Str.getterGas (Str.slotLen (Str.shortWord s)) ≤ 10430 := by
  rw [Str.slotLen_shortWord hs, Str.getterGas]
  by_cases h0 : s.size = 0
  · rw [h0]; decide
  · rw [show (s.size + 31) / 32 = 1 by omega]; decide

/-- A string getter call returning the short string `s`. -/
theorem stringResult_some {res : MessageResult} {s : ByteArray}
    (h : StringResult res (some s)) : res.success = true ∧ res.output = Abi.encodeString s := h

/-- **`name()` of the vault holding `"Solmate Vault"`** returns its ABI encoding. -/
theorem vaultName_canonical (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hslot : w.sload vault 0#256 = Str.shortWord "Solmate Vault".toUTF8)
    (hgas : 10430 ≤ gas) (hgas' : gas < 2 ^ 64) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller (Abi.encodeCall 0x06fdde03 []) gas wa wk) = .ok res ∧
      res.world = w ∧ res.success = true ∧ res.output = Abi.encodeString "Solmate Vault".toUTF8 := by
  have hs : ("Solmate Vault".toUTF8).size ≤ 31 := by decide
  obtain ⟨n, hn⟩ := vaultName_call (ctx := ctx) (tr := tr) (caller := caller) (wa := wa)
    (wk := wk) hdep hdeleg (by rw [hslot]; exact Nat.le_trans (getterGas_shortWord hs) hgas) hgas'
  refine ⟨n, fun fuel hle => ?_⟩
  obtain ⟨res, hrun, hw, hres⟩ := hn fuel hle
  rw [stringAt_shortWord hs hslot] at hres
  exact ⟨res, hrun, hw, stringResult_some hres⟩

/-- **`symbol()` of the vault holding `"svSAST"`** returns its ABI encoding. -/
theorem vaultSymbol_canonical (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hslot : w.sload vault 1#256 = Str.shortWord "svSAST".toUTF8)
    (hgas : 10430 ≤ gas) (hgas' : gas < 2 ^ 64) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller (Abi.encodeCall 0x95d89b41 []) gas wa wk) = .ok res ∧
      res.world = w ∧ res.success = true ∧ res.output = Abi.encodeString "svSAST".toUTF8 := by
  have hs : ("svSAST".toUTF8).size ≤ 31 := by decide
  obtain ⟨n, hn⟩ := vaultSymbol_call (ctx := ctx) (tr := tr) (caller := caller) (wa := wa)
    (wk := wk) hdep hdeleg (by rw [hslot]; exact Nat.le_trans (getterGas_shortWord hs) hgas) hgas'
  refine ⟨n, fun fuel hle => ?_⟩
  obtain ⟨res, hrun, hw, hres⟩ := hn fuel hle
  rw [stringAt_shortWord hs hslot] at hres
  exact ⟨res, hrun, hw, stringResult_some hres⟩

/-- **`name()` of the asset holding `"Solmate Asset"`** returns its ABI encoding. -/
theorem assetName_canonical (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hslot : w.sload asset 0#256 = Str.shortWord "Solmate Asset".toUTF8)
    (hgas : 10430 ≤ gas) (hgas' : gas < 2 ^ 64) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code asset) asset caller (Abi.encodeCall 0x06fdde03 []) gas wa wk) = .ok res ∧
      res.world = w ∧ res.success = true ∧ res.output = Abi.encodeString "Solmate Asset".toUTF8 := by
  have hs : ("Solmate Asset".toUTF8).size ≤ 31 := by decide
  obtain ⟨n, hn⟩ := assetName_call (ctx := ctx) (tr := tr) (caller := caller) (wa := wa)
    (wk := wk) hdep hdeleg (by rw [hslot]; exact Nat.le_trans (getterGas_shortWord hs) hgas) hgas'
  refine ⟨n, fun fuel hle => ?_⟩
  obtain ⟨res, hrun, hw, hres⟩ := hn fuel hle
  rw [stringAt_shortWord hs hslot] at hres
  exact ⟨res, hrun, hw, stringResult_some hres⟩

/-- **`symbol()` of the asset holding `"SAST"`** returns its ABI encoding. -/
theorem assetSymbol_canonical (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hslot : w.sload asset 1#256 = Str.shortWord "SAST".toUTF8)
    (hgas : 10430 ≤ gas) (hgas' : gas < 2 ^ 64) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code asset) asset caller (Abi.encodeCall 0x95d89b41 []) gas wa wk) = .ok res ∧
      res.world = w ∧ res.success = true ∧ res.output = Abi.encodeString "SAST".toUTF8 := by
  have hs : ("SAST".toUTF8).size ≤ 31 := by decide
  obtain ⟨n, hn⟩ := assetSymbol_call (ctx := ctx) (tr := tr) (caller := caller) (wa := wa)
    (wk := wk) hdep hdeleg (by rw [hslot]; exact Nat.le_trans (getterGas_shortWord hs) hgas) hgas'
  refine ⟨n, fun fuel hle => ?_⟩
  obtain ⟨res, hrun, hw, hres⟩ := hn fuel hle
  rw [stringAt_shortWord hs hslot] at hres
  exact ⟨res, hrun, hw, stringResult_some hres⟩

end EvmLeanSpecs.Refinement
