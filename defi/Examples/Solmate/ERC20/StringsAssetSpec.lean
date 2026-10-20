import Examples.Solmate.ERC4626.StringsVaultSpec
import Examples.Solmate.ERC20.Strings

/-!
# `name()` / `symbol()` of the compiled asset refine the storage strings

The asset's counterparts of `StringsVaultSpec` (`SolmateAsset.runtimeCodeWith ia`, any
immutables): `assetName_refines`, `assetSymbol_refines` (any frame) and `assetName_call`,
`assetSymbol_call` (top level, the asset of a `Deployed` vault): the call returns
`Abi.encodeString s` for `stringAt crypto world asset slot = some s` (slot 0: `name`, slot 1:
`symbol`), reverts for `none`, and leaves the world unchanged.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts Bytes

variable {ctx : Context} {w : World} {tr : TransientStorage} {vault asset caller : Address}
  {gas : Nat} {wa : AddressSet} {wk : StorageKeySet}

set_option maxHeartbeats 0 in
/-- **The asset's string getter** from the entry of `extract_byte_array_length` (`0xa07`),
any slot word. -/
theorem assetString_wp {ia : SolmateAsset.Immutables} (m : Machine) {S slot : Word}
    {rest : List Word}
    (hc : m.frame.code = SolmateAsset.runtimeCodeWith ia)
    (hj : JumpTable m.frame.jumpDests (SolmateAsset.runtimeCodeWith ia))
    (hpc : m.frame.pc = 0xa07)
    (hs : m.frame.stack = S :: 607#256 :: slot :: 241#256 :: rest)
    (hS : m.world.sload m.frame.msg.currentTarget slot = S)
    (hmem : m.frame.memory = initMemory) (hlen : rest.length ≤ 1000)
    (hg : 5000 + 2400 * ((Str.slotLen S + 31) / 32) +
      Gas.memoryCost (256 + 64 * ((Str.slotLen S + 31) / 32)) ≤ m.frame.gasLeft)
    (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun _ => False)
      (StringPost m (Str.decode m.ctx.crypto (m.world.sload m.frame.msg.currentTarget) slot)) := by
  rcases Nat.mod_two_eq_zero_or_one S.toNat with hev | hodd
  · exact assetStringShort_wp m hc hj hpc hs hS hev hmem hlen (by omega)
  · exact assetStringLong_wp m hc hj hpc hs hS hodd hmem hlen hg hg'

set_option maxHeartbeats 0 in
/-- **`name()` of the asset refines the storage string at slot 0**, in any frame. -/
theorem assetName_refines {ia : SolmateAsset.Immutables} (m : Machine)
    (h : StringPre (SolmateAsset.runtimeCodeWith ia) 0#256 m)
    (hd : NoArgCall m.frame.msg.data 0x06fdde03) :
    Halts m (StringPost m (stringAt m.ctx.crypto m.world m.frame.msg.currentTarget 0#256)) := by
  obtain ⟨hf, hval, hg, hg', hsz'⟩ := h
  obtain ⟨hsel, hsz4⟩ := hd
  have hsel' := Dispatch.selector_eq hsel
  apply WP.halts_of_false
  have hagree := assetJumpDestsAgree ia
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsz4 (by omega)
  have hg0 : 8000 ≤ m.frame.gasLeft := by unfold Str.getterGas at hg; omega
  fresh_intro
  pwp_run_to 0xa07 [hval, hsel', hlt, Abi.shr_calldataload_zero]
  refine WP.mono (assetString_wp _ rfl hj rfl rfl rfl rfl (by simp) ?_ (by dsimp only; omega))
    (fun _ _ h => h.elim) (fun _ _ _ h => h)
  have hsl := sloadCost_le (storageKeyWarm m_sub.accessedStorageKeys m_msg.currentTarget 0#256)
  dsimp only
  generalize sloadCost _ = sl at *
  exact getterGas_le hg _ (by omega)

set_option maxHeartbeats 0 in
/-- **`symbol()` of the asset refines the storage string at slot 1**, in any frame. -/
theorem assetSymbol_refines {ia : SolmateAsset.Immutables} (m : Machine)
    (h : StringPre (SolmateAsset.runtimeCodeWith ia) 1#256 m)
    (hd : NoArgCall m.frame.msg.data 0x95d89b41) :
    Halts m (StringPost m (stringAt m.ctx.crypto m.world m.frame.msg.currentTarget 1#256)) := by
  obtain ⟨hf, hval, hg, hg', hsz'⟩ := h
  obtain ⟨hsel, hsz4⟩ := hd
  have hsel' := Dispatch.selector_eq hsel
  apply WP.halts_of_false
  have hagree := assetJumpDestsAgree ia
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsz4 (by omega)
  have hg0 : 8000 ≤ m.frame.gasLeft := by unfold Str.getterGas at hg; omega
  fresh_intro
  pwp_run_to 0xa07 [hval, hsel', hlt, Abi.shr_calldataload_zero]
  refine WP.mono (assetString_wp _ rfl hj rfl rfl rfl rfl (by simp) ?_ (by dsimp only; omega))
    (fun _ _ h => h.elim) (fun _ _ _ h => h)
  have hsl := sloadCost_le (storageKeyWarm m_sub.accessedStorageKeys m_msg.currentTarget 1#256)
  dsimp only
  generalize sloadCost _ = sl at *
  exact getterGas_le hg _ (by omega)

/-- **`name()` as a top-level transaction** on the deployed asset: the string at slot 0. -/
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

/-- **`symbol()` as a top-level transaction** on the deployed asset: the string at slot 1. -/
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

end EvmLeanSpecs.Refinement
