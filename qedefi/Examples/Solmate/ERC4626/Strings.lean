import Examples.Solmate.ERC4626.StringsCode
import Examples.Solmate.ERC4626.ViewsSpec

/-!
# `name()` / `symbol()` of the compiled vault as top-level transactions

`vaultName_call`, `vaultSymbol_call`: the getters of `StringsCode.lean` run on the deployed vault.
See `docs/erc4626/details.md` §8.
-/

section

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 QEDefi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts EvmLean.Bytes

/-! ## Top-level transactions -/

variable {ctx : Context} {w : World} {tr : TransientStorage} {vault asset caller : Address}
  {data : ByteArray} {gas : Nat} {wa : AddressSet} {wk : StorageKeySet}

/-- **`name()` as a top-level transaction** on the deployed vault: the string at slot 0. -/
theorem vaultName_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hgas : Str.getterGas (Str.slotLen (w.sload vault 0#256)) ≤ gas) (hgas' : gas < 2 ^ 64) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller (Abi.encodeCall 0x06fdde03 []) gas wa wk) = .ok res ∧
      res.world = w ∧ StringResult res (stringAt ctx.crypto w vault 0#256) := by
  obtain ⟨i, -, hcode⟩ := hdep.vaultCode
  rw [hcode]
  exact string_call hdeleg (Shares.delegatedAddress?_code i) (hdep.vaultNotPrecompile _)
    (vaultName_refines _ (stringPre_start hgas hgas' (by rw [Abi.size_encodeCall]; simp))
      (noArgCall_encodeCall (by decide)))

/-- **`symbol()` as a top-level transaction** on the deployed vault: the string at slot 1. -/
theorem vaultSymbol_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hgas : Str.getterGas (Str.slotLen (w.sload vault 1#256)) ≤ gas) (hgas' : gas < 2 ^ 64) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller (Abi.encodeCall 0x95d89b41 []) gas wa wk) = .ok res ∧
      res.world = w ∧ StringResult res (stringAt ctx.crypto w vault 1#256) := by
  obtain ⟨i, -, hcode⟩ := hdep.vaultCode
  rw [hcode]
  exact string_call hdeleg (Shares.delegatedAddress?_code i) (hdep.vaultNotPrecompile _)
    (vaultSymbol_refines _ (stringPre_start hgas hgas' (by rw [Abi.size_encodeCall]; simp))
      (noArgCall_encodeCall (by decide)))

end Examples.Solmate.ERC4626

end
