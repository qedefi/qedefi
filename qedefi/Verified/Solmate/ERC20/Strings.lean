import Verified.Solmate.ERC20.StringsCode
import Verified.Solmate.ERC4626.ViewsSpec

/-!
# `name()` / `symbol()` of the compiled asset as top-level transactions

`assetName_call`, `assetSymbol_call` and the canonical strings, from the getters of
`StringsCode.lean`.
-/

section

namespace Verified.Solmate.ERC20
open Verified.Solmate.ERC4626 QEDefi.ERC4626

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts EvmLean.Bytes

variable {ctx : Context} {w : World} {tr : TransientStorage} {vault asset caller : Address}
  {gas : Nat} {wa : AddressSet} {wk : StorageKeySet}

/-- **`name()` as a top-level transaction** on the deployed asset. -/
theorem assetName_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hgas : Str.getterGas (Str.slotLen (w.sload asset 0#256)) ≤ gas) (hgas' : gas < 2 ^ 64) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code asset) asset caller (Abi.encodeCall 0x06fdde03 []) gas wa wk) = .ok res ∧
      res.world = w ∧ StringResult res (stringAt ctx.crypto w asset 0#256) := by
  obtain ⟨ia, hcode⟩ := hdep.assetCode
  rw [hcode]
  exact string_call hdeleg (delegatedAddress?_assetCode ia) (hdep.assetNotPrecompile _)
    (assetName_refines _ (stringPre_start hgas hgas' (by rw [Abi.size_encodeCall]; simp))
      (noArgCall_encodeCall (by decide)))

/-- **`symbol()` as a top-level transaction** on the deployed asset. -/
theorem assetSymbol_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hgas : Str.getterGas (Str.slotLen (w.sload asset 1#256)) ≤ gas) (hgas' : gas < 2 ^ 64) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code asset) asset caller (Abi.encodeCall 0x95d89b41 []) gas wa wk) = .ok res ∧
      res.world = w ∧ StringResult res (stringAt ctx.crypto w asset 1#256) := by
  obtain ⟨ia, hcode⟩ := hdep.assetCode
  rw [hcode]
  exact string_call hdeleg (delegatedAddress?_assetCode ia) (hdep.assetNotPrecompile _)
    (assetSymbol_refines _ (stringPre_start hgas hgas' (by rw [Abi.size_encodeCall]; simp))
      (noArgCall_encodeCall (by decide)))

end Verified.Solmate.ERC20

end

section

/-!
## The canonical deployment strings

`("Solmate Asset", "SAST")` and `("Solmate Vault", "svSAST")` are stored in short form
(`Str.shortWord`), so the getters return their encoding with no Keccak involved.
-/

namespace Verified.Solmate.ERC20
open Verified.Solmate.ERC4626 QEDefi.ERC4626

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts

variable {ctx : Context} {w : World} {tr : TransientStorage} {vault asset caller : Address}
  {gas : Nat} {wa : AddressSet} {wk : StorageKeySet}

theorem stringAt_shortWord {crypto : Crypto} {a : Address} {p : Word} {s : ByteArray}
    (hs : s.size ≤ 31) (h : w.sload a p = Str.shortWord s) : stringAt crypto w a p = some s :=
  Str.decode_shortWord crypto hs h

theorem getterGas_shortWord {s : ByteArray} (hs : s.size ≤ 31) :
    Str.getterGas (Str.slotLen (Str.shortWord s)) ≤ 10430 := by
  rw [Str.slotLen_shortWord hs, Str.getterGas]
  by_cases h0 : s.size = 0
  · rw [h0]; decide
  · rw [show (s.size + 31) / 32 = 1 by omega]; decide

theorem stringResult_some {res : MessageResult} {s : ByteArray}
    (h : StringResult res (some s)) : res.success = true ∧ res.output = Abi.encodeString s := h

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

end Verified.Solmate.ERC20

end
