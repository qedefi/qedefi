import EvmLeanSpecs.Refinement.StringsVaultLong
import EvmLeanSpecs.Refinement.VaultViewsSpec

/-!
# `name()` / `symbol()` of the compiled vault refine the storage strings

Solmate's `ERC20` stores `name` at slot 0 and `symbol` at slot 1 (`string public`). For the
compiled vault (`SolmateVault.runtimeCodeWith i`, any immutables):

* `vaultName_refines`, `vaultSymbol_refines` (any frame, `Halts`): from a fresh frame of the
  vault's code with `NoArgCall` calldata and enough gas (`StringPre`: `Str.getterGas` of the
  length the slot encodes), the call returns `Abi.encodeString s` where
  `stringAt crypto world vault slot = some s`, or reverts (`Panic(0x22)`) when the slot is
  inconsistent (`none`); the world is unchanged (`StringPost`).
* `vaultName_call`, `vaultSymbol_call`: the same for a top-level transaction
  (`processMessageCall`) on a `Deployed` vault (`StringResult`).

Both short (≤ 31 bytes, in the slot) and long strings (data at `keccak256(slot) + j`) are
covered, for every `Crypto`: the long-string data slots are whatever `arrayDataSlot` gives, so
no hypothesis on Keccak is needed to *read*.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts Bytes

/-- The start of a call frame of a string getter: fresh frame of `code`, no value, enough gas
for the string at `slot` of the executing account (`Str.getterGas`, below `2⁶⁴`), calldata
shorter than `2⁶⁴` bytes. -/
structure StringPre (code : ByteArray) (slot : Word) (m : Machine) : Prop where
  /-- A fresh frame of the code. -/
  fresh : Fresh code m
  /-- No value is sent (the getters are not payable). -/
  value : m.frame.msg.value = 0
  /-- Enough gas for the copy. -/
  gas : Str.getterGas (Str.slotLen (m.world.sload m.frame.msg.currentTarget slot)) ≤
    m.frame.gasLeft
  /-- Gas fits 64 bits. -/
  gasLt : m.frame.gasLeft < 2 ^ 64
  /-- Calldata length fits 64 bits. -/
  sizeLt : m.frame.msg.data.size < 2 ^ 64

set_option maxHeartbeats 0 in
/-- **The vault's string getter** from the entry of `extract_byte_array_length` (`0x1339`),
any slot word. -/
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

/-- The gas of `StringPre` covers the getter after the dispatcher. -/
theorem getterGas_le {L g : Nat} (h : Str.getterGas L ≤ g) (c : Nat) (hc : c ≤ 3000) :
    5000 + 2400 * ((L + 31) / 32) + Gas.memoryCost (256 + 64 * ((L + 31) / 32)) ≤ g - c := by
  unfold Str.getterGas at h; omega

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

end EvmLeanSpecs.Refinement

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts Bytes

/-! ## Top-level transactions -/

/-- What a top-level call of a string getter returns: success with `Abi.encodeString s` for
`some s`, a revert for `none`. -/
def StringResult (res : MessageResult) (r : Option ByteArray) : Prop :=
  match r with
  | some s => res.success = true ∧ res.output = Abi.encodeString s
  | none => res.success = false ∧ res.reverted = true

variable {ctx : Context} {w : World} {tr : TransientStorage} {vault asset caller : Address}
  {data : ByteArray} {gas : Nat} {wa : AddressSet} {wk : StorageKeySet}

/-- A string-getter summary of the start machine of a top-level call gives the result of
`processMessageCall`: the world is unchanged and the result is `StringResult`. -/
theorem string_call {code : ByteArray} {a : Address} {r : Option ByteArray}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hdel : delegatedAddress? code = none) (hpre : Precompile.isPrecompile ctx.fork a = false)
    (h : Halts (startMachine ctx w tr (callMsg code a caller data gas wa wk))
      (StringPost (startMachine ctx w tr (callMsg code a caller data gas wa wk)) r)) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg code a caller data gas wa wk) = .ok res ∧ res.world = w ∧ StringResult res r := by
  obtain ⟨n, hn⟩ := processMessageCall_of_halts (a := a)
    (msg := callMsg code a caller data gas wa wk) hdeleg hdel rfl rfl hpre rfl rfl h
  refine ⟨n, fun fuel hle => ?_⟩
  obtain ⟨mf, o, ⟨hw, ho⟩, hs, hrun⟩ := hn fuel hle
  have hk : mf.frame.kind = .call 0 0 := hs.kind
  refine ⟨_, hrun, ?_⟩
  cases r with
  | some v =>
    simp only at ho
    subst ho
    obtain ⟨h1, h2, h3, -⟩ := topLevelResult_success_call
      (t := (callMsg code a caller data gas wa wk).target) (out := Abi.encodeString v) hk
    exact ⟨h3.trans hw, h1, h2⟩
  | none =>
    obtain ⟨out, ho⟩ := ho
    subst ho
    have hsnap : mf.frame.snapshot.1 = w := by rw [hs.snapshot]; rfl
    simp only [frameResult_revert, topLevelResult_world, topLevelResult_success,
      topLevelResult_reverted, StringResult, ChildResult.success, hsnap]
    decide

/-- The start of a top-level call satisfies `StringPre` when the gas covers the string. -/
theorem stringPre_start {code : ByteArray} {a : Address} {slot : Word}
    (hgas : Str.getterGas (Str.slotLen (w.sload a slot)) ≤ gas) (hgas' : gas < 2 ^ 64)
    (hsize : data.size < 2 ^ 64) :
    StringPre code slot (startMachine ctx w tr (callMsg code a caller data gas wa wk)) where
  fresh := fresh_startMachine ctx w tr (callMsg code a caller data gas wa wk)
  value := rfl
  gas := hgas
  gasLt := hgas'
  sizeLt := hsize

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

end EvmLeanSpecs.Refinement
