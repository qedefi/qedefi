import Examples.Solmate.ERC20.Strings
import Examples.Solmate.ERC4626.Strings

/-!
# `name()` / `symbol()` of the deployed vault holding its canonical strings

The vault's canonical getters (`vaultName_canonical`, `vaultSymbol_canonical`), from
`vaultName_call`/`vaultSymbol_call` and the short-string facts of `ERC20/Strings.lean`.
-/

section

namespace Examples.Solmate.ERC20
open Examples.Solmate.ERC4626 Defi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts

variable {ctx : Context} {w : World} {tr : TransientStorage} {vault asset caller : Address}
  {gas : Nat} {wa : AddressSet} {wk : StorageKeySet}

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

end Examples.Solmate.ERC20

end
