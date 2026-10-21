import Examples.Solmate.ERC4626.StringsCodeShort
import Examples.Solmate.ERC4626.StringsCodeLong
import Examples.Solmate.ERC4626.Views

/-!
# `name()` / `symbol()` of the compiled vault: the getters

The getters return `Abi.encodeString s` for the storage string `stringAt … slot = some s` (short
or long form, any `Crypto`, no Keccak hypothesis since they only read), or revert when the slot
is inconsistent, with gas `Str.getterGas L`. See `docs/erc4626/details.md` §8.
-/

section

/-! ## `name()` / `symbol()` refine the storage strings (slots 0 and 1) -/

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 QEDefi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts EvmLean.Bytes

set_option maxHeartbeats 0 in
/-- The vault's string getter from the entry of `extract_byte_array_length` (`0x1339`). -/
theorem vaultString_wp {i : SolmateVault.Immutables} (m : Machine) {S slot : Word}
    {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hpc : m.frame.pc = 0x1339)
    (hs : m.frame.stack = S :: 1300#256 :: slot :: 504#256 :: rest)
    (hS : m.world.sload m.frame.msg.currentTarget slot = S)
    (hmem : m.frame.memory = initMemory) (hlen : rest.length ≤ 1000)
    (hg : 5000 + 2400 * ((Str.slotLen S + 31) / 32) +
      Gas.memoryCost (256 + 64 * ((Str.slotLen S + 31) / 32)) ≤ m.frame.gasLeft)
    (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun _ => False)
      (StringPost m (Str.decode m.ctx.crypto (m.world.sload m.frame.msg.currentTarget) slot)) := by
  rcases Nat.mod_two_eq_zero_or_one S.toNat with hev | hodd
  · exact vaultStringShort_wp m hc hj hpc hs hS hev hmem hlen (by omega)
  · exact vaultStringLong_wp m hc hj hpc hs hS hodd hmem hlen hg hg'

set_option maxHeartbeats 0 in
/-- **`name()` of the vault refines the storage string at slot 0**, in any frame. -/
theorem vaultName_refines {i : SolmateVault.Immutables} (m : Machine)
    (h : StringPre (SolmateVault.runtimeCodeWith i) 0#256 m)
    (hd : NoArgCall m.frame.msg.data 0x06fdde03) :
    Halts m (StringPost m (stringAt m.ctx.crypto m.world m.frame.msg.currentTarget 0#256)) := by
  obtain ⟨hf, hval, hg, hg', hsz'⟩ := h
  obtain ⟨hsel, hsz4⟩ := hd
  have hsel' := Dispatch.selector_eq hsel
  apply WP.halts_of_false
  have hagree := Shares.jumpDestsAgree i
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsz4 (by omega)
  have hg0 : 8000 ≤ m.frame.gasLeft := by unfold Str.getterGas at hg; omega
  fresh_intro
  pwp_run_to 0x1339 [hval, hsel', hlt, Abi.shr_calldataload_zero]
  refine WP.mono (vaultString_wp _ rfl hj rfl rfl rfl rfl (by simp) ?_ (by dsimp only; omega))
    (fun _ _ h => h.elim) (fun _ _ _ h => h)
  have hsl := sloadCost_le (storageKeyWarm m_sub.accessedStorageKeys m_msg.currentTarget 0#256)
  dsimp only
  generalize sloadCost _ = sl at *
  exact getterGas_le hg _ (by omega)

set_option maxHeartbeats 0 in
/-- **`symbol()` of the vault refines the storage string at slot 1**, in any frame. -/
theorem vaultSymbol_refines {i : SolmateVault.Immutables} (m : Machine)
    (h : StringPre (SolmateVault.runtimeCodeWith i) 1#256 m)
    (hd : NoArgCall m.frame.msg.data 0x95d89b41) :
    Halts m (StringPost m (stringAt m.ctx.crypto m.world m.frame.msg.currentTarget 1#256)) := by
  obtain ⟨hf, hval, hg, hg', hsz'⟩ := h
  obtain ⟨hsel, hsz4⟩ := hd
  have hsel' := Dispatch.selector_eq hsel
  apply WP.halts_of_false
  have hagree := Shares.jumpDestsAgree i
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsz4 (by omega)
  have hg0 : 8000 ≤ m.frame.gasLeft := by unfold Str.getterGas at hg; omega
  fresh_intro
  pwp_run_to 0x1339 [hval, hsel', hlt, Abi.shr_calldataload_zero]
  refine WP.mono (vaultString_wp _ rfl hj rfl rfl rfl rfl (by simp) ?_ (by dsimp only; omega))
    (fun _ _ h => h.elim) (fun _ _ _ h => h)
  have hsl := sloadCost_le (storageKeyWarm m_sub.accessedStorageKeys m_msg.currentTarget 1#256)
  dsimp only
  generalize sloadCost _ = sl at *
  exact getterGas_le hg _ (by omega)

end Examples.Solmate.ERC4626

end
