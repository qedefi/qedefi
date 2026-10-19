import EvmLeanSpecs.Refinement.InvariantsSystem

/-!
# Per-call refinement obligations proved on `main`

`OpRefinesAt` (the abs-level per-call refinement statement of `InvariantsSystem.lean`) for the
calls whose bytecode refinement exists today:

* the vault's share-token functions `transfer`, `transferFrom`, `approve`, from the top-level
  theorems `Shares.transfer_refines`, `Shares.transferFrom_refines`, `Shares.approve_refines`;
* the asset's `transfer` (in particular donations to the vault) and `transferFrom`, from the
  frame-level (callee) theorems `assetTransfer_refines`, `assetTransferFrom_refines`, lifted to
  a top-level call by `call_of_halts`.

Each proof: the terminating call's result is the one the refinement theorem describes (the
interpreter is deterministic in the fuel, `Terminates`); on success the written storage
represents the model's new ledger on the allowances whose slots are not written, which
includes every actor pair under `SlotsOk`; the other contract's storage and the hook-counter
slots are untouched; the codes are unchanged (`SSTORE` only). Reverts keep the world.

All five need only `100000 ≤ minGas`.
-/

namespace EvmLeanSpecs.Refinement.Invariants

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Vault EvmLeanSpecs.Vault.Solmate EvmLeanSpecs.Refinement.Lift

/-! ## World lemmas -/

theorem code_transferWorld (crypto : Crypto) (w : World) (token src dst : Address) (v : Word)
    (b : Address) :
    (Examples.SolmateAssetTransfer.transferWorld crypto w token src dst v).code b = w.code b := by
  simp [Examples.SolmateAssetTransfer.transferWorld]

theorem code_spendWorld (crypto : Crypto) (w : World) (token o sp : Address) (v : Word)
    (b : Address) : (Erc20.spendWorld crypto w token o sp v).code b = w.code b := by
  unfold Erc20.spendWorld; dsimp only; split <;> simp

theorem code_transferFromWorld (crypto : Crypto) (w : World) (token sp src dst : Address)
    (v : Word) (b : Address) :
    (Erc20.transferFromWorld crypto w token sp src dst v).code b = w.code b := by
  simp only [Erc20.transferFromWorld, Erc20.transferWorld, code_transferWorld, code_spendWorld]

theorem code_approveWorld (crypto : Crypto) (w : World) (token o sp : Address) (v : Word)
    (b : Address) : (Erc20.approveWorld crypto w token o sp v).code b = w.code b := by
  simp [Erc20.approveWorld]

theorem sload_transferFromWorld_other {crypto : Crypto} {w : World} {token sp src dst b : Address}
    {v : Word} (hb : b ≠ token) (k : Word) :
    (Erc20.transferFromWorld crypto w token sp src dst v).sload b k = w.sload b k := by
  simp only [Erc20.transferFromWorld, Erc20.transferWorld]
  rw [Shares.sload_transferWorld (.inl hb), Shares.sload_spendWorld (.inl hb)]

/-! ## Top-level glue -/

/-- A frame summary of a top-level call gives the result of `processMessageCall`: on success
the result's world is the final frame's, on revert it is the initial world. -/
theorem call_of_halts {ctx : Context} {w : World} {tr : TransientStorage} {code : ByteArray}
    {a caller : Address} {data : ByteArray} {gas : Nat} {wa : AddressSet} {wk : StorageKeySet}
    {H : Machine → Outcome → Prop} (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hdel : delegatedAddress? code = none) (hpre : Precompile.isPrecompile ctx.fork a = false)
    (h : Halts (startMachine ctx w tr (callMsg code a caller data gas wa wk)) H) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ mf o r, H mf o ∧
      processMessageCall fuel ctx w tr (callMsg code a caller data gas wa wk) = .ok r ∧
      (∀ out, o = .success out → r.world = mf.world) ∧ (∀ out, o = .revert out → r.world = w) := by
  obtain ⟨n, hn⟩ := processMessageCall_of_halts (a := a)
    (msg := callMsg code a caller data gas wa wk) hdeleg hdel rfl rfl hpre rfl rfl h
  refine ⟨n, fun fuel hle => ?_⟩
  obtain ⟨mf, o, hH, hs, hrun⟩ := hn fuel hle
  refine ⟨mf, o, _, hH, hrun, fun out ho => ?_, fun out ho => ?_⟩
  · subst ho
    have hk : mf.frame.kind = .call 0 0 := hs.kind
    exact (topLevelResult_success_call (t := (callMsg code a caller data gas wa wk).target)
      (out := out) hk).2.2.1
  · subst ho
    have hsnap : mf.frame.snapshot.1 = w := by rw [hs.snapshot]; rfl
    simp only [frameResult_revert, topLevelResult_world, hsnap]

/-- `Abi.encodeCall sel [x, y]` is a `TwoWordCall`. -/
theorem twoWordCall_encodeCall {sel : Nat} (hsel : sel < 2 ^ 32) (x y : Word) :
    TwoWordCall (Abi.encodeCall sel [x, y]) sel x y :=
  ⟨by rw [Abi.selectorOf_encodeCall, Nat.mod_eq_of_lt hsel],
   by rw [Abi.size_encodeCall]; simp, Abi.calldataload_encodeCall_0 _ _ _,
   Abi.calldataload_encodeCall_1 _ _ _ _⟩

/-- `Abi.encodeCall sel [x, y, z]` is a `ThreeWordCall`. -/
theorem threeWordCall_encodeCall {sel : Nat} (hsel : sel < 2 ^ 32) (x y z : Word) :
    ThreeWordCall (Abi.encodeCall sel [x, y, z]) sel x y z :=
  ⟨by rw [Abi.selectorOf_encodeCall, Nat.mod_eq_of_lt hsel],
   by rw [Abi.size_encodeCall]; simp, Abi.calldataload_encodeCall_0 _ _ _,
   Abi.calldataload_encodeCall_1 _ _ _ _, Abi.calldataload_encodeCall_2 _ _ _ _ _⟩

/-- Unpacking `CallStep`: deterministic results. -/
theorem terminates_unique {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    {r r' : MessageResult} {n fuel : Nat} (hn : ∀ fuel, n ≤ fuel → processMessageCall fuel ctx w tr msg = .ok r)
    (hle : n ≤ fuel) (h : processMessageCall fuel ctx w tr msg = .ok r') : r' = r := by
  rw [hn fuel hle] at h; cases h; rfl

variable {crypto : Crypto} {vault asset : Address} {minGas : Nat} {Act : List Address}

/-- `CallRefines` from a successful model step. -/
theorem callRefines_some {w w' : World} {c : VCall} {s' : State Address}
    (hop : Solmate.step (abs crypto w vault asset) c.op = some s')
    (h : AgreeOn (ActorPairs Act) (abs crypto w' vault asset) s') :
    CallRefines crypto vault asset Act w c w' := by
  unfold CallRefines; rw [hop]; exact h

/-- `CallRefines` from a reverting model step. -/
theorem callRefines_none {w w' : World} {c : VCall}
    (hop : Solmate.step (abs crypto w vault asset) c.op = none) (h : w' = w) :
    CallRefines crypto vault asset Act w c w' := by
  unfold CallRefines; rw [hop]; exact h

/-! ## The vault's share-token functions -/

set_option maxHeartbeats 1000000 in
/-- **`vault.transfer`** refines `Op.transfer`. -/
theorem opRefines_transfer (hmin : 100000 ≤ minGas) (caller dst : Address) (amount : Word) :
    OpRefinesAt crypto vault asset minGas Act (.transfer caller dst amount) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, -, -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  have hne := hdep.vault_ne_asset
  obtain ⟨i, -, hcode⟩ := hdep.vaultCode
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, Bool.false_eq_true,
    ite_false, hcode] at hn
  have hc : caller ∈ Act := hact caller (by simp [VCall.actors])
  have hd : dst ∈ Act := hact dst (by simp [VCall.actors])
  obtain ⟨r', hr', hres⟩ := Shares.transfer_refines (i := i) (tr := tr) (gas := gas) (warmAddrs := wa)
    (warmKeys := wk) (w := w) (vault := vault) (caller := caller) (dst := dst) (amount := amount)
    hdeleg (hdep.vaultNotPrecompile _) (by omega) (hs.bal caller hc) (hs.bal dst hd)
    (rep_toToken _) hinv.2 (max n 400) (le_max_right _ _)
  obtain rfl := terminates_unique hn (le_max_left _ _) hr'
  split at hres
  · rename_i t' ht
    obtain ⟨-, -, hwld, hrep, hframe⟩ := hres
    refine ⟨hdep.of_code (by rw [hwld]; exact code_transferWorld ..)
      (by rw [hwld]; exact code_transferWorld ..), callRefines_some (s' := { abs ctx.crypto w vault asset with shares := t' }) ?_ ?_⟩
    · show Option.map _ ((abs ctx.crypto w vault asset).shares.transfer _ _ _) = _
      rw [show (abs ctx.crypto w vault asset).shares.transfer caller dst amount.toNat = some t'
        from ht]; rfl
    exact agree_of_shares hrep
      (fun o sp ⟨ho, hsp⟩ => ⟨Erc20.balanceSlot_ne_allowanceSlot (hs.allow o ho sp hsp) _ |>.symm,
        Erc20.balanceSlot_ne_allowanceSlot (hs.allow o ho sp hsp) _ |>.symm⟩)
      (fun k => hframe asset k (.inl hne.symm))
      (hframe vault 6#256 (.inr ⟨(hs.balFixed caller hc).1.symm, (hs.balFixed dst hd).1.symm⟩))
      (hframe vault 7#256 (.inr ⟨(hs.balFixed caller hc).2.symm, (hs.balFixed dst hd).2.symm⟩))
  · rename_i ht
    obtain ⟨-, -, hwld⟩ := hres
    refine ⟨hwld ▸ hdep, callRefines_none ?_ hwld⟩
    show Option.map _ ((abs ctx.crypto w vault asset).shares.transfer _ _ _) = _
    rw [show (abs ctx.crypto w vault asset).shares.transfer caller dst amount.toNat = none
      from ht]; rfl

/-- Actor pairs avoid the slot of another actor pair's allowance, unless they are that pair. -/
theorem SlotsOk.allowP {crypto : Crypto} {vault : Address} {Act : List Address}
    (hs : SlotsOk crypto vault Act) {o sp a b : Address} (ho : o ∈ Act) (hsp : sp ∈ Act)
    (ha : a ∈ Act) (hb : b ∈ Act) :
    (o = a ∧ sp = b) ∨ Erc20.allowanceSlot crypto Erc20.Layout.solmate o sp ≠
      Erc20.allowanceSlot crypto Erc20.Layout.solmate a b := by
  by_cases h : o = a ∧ sp = b
  · exact .inl h
  · exact .inr fun e => h (hs.allowInj o ho sp hsp a ha b hb e)

/-- Actor pairs avoid every actor's balance slot. -/
theorem SlotsOk.balP {crypto : Crypto} {vault : Address} {Act : List Address}
    (hs : SlotsOk crypto vault Act) {o sp : Address} (ho : o ∈ Act) (hsp : sp ∈ Act) (a : Address) :
    Erc20.allowanceSlot crypto Erc20.Layout.solmate o sp ≠
      Erc20.balanceSlot crypto Erc20.Layout.solmate a :=
  (Erc20.balanceSlot_ne_allowanceSlot (hs.allow o ho sp hsp) a).symm

set_option maxHeartbeats 1000000 in
/-- **`vault.transferFrom`** refines `Op.transferFrom`. -/
theorem opRefines_transferFrom (hmin : 100000 ≤ minGas) (caller src dst : Address)
    (amount : Word) :
    OpRefinesAt crypto vault asset minGas Act (.transferFrom caller src dst amount) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, -, -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  have hne := hdep.vault_ne_asset
  obtain ⟨i, -, hcode⟩ := hdep.vaultCode
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, Bool.false_eq_true,
    ite_false, hcode] at hn
  have hc : caller ∈ Act := hact caller (by simp [VCall.actors])
  have hsr : src ∈ Act := hact src (by simp [VCall.actors])
  have hd : dst ∈ Act := hact dst (by simp [VCall.actors])
  obtain ⟨r', hr', hres⟩ := Shares.transferFrom_refines (i := i) (tr := tr) (gas := gas)
    (warmAddrs := wa) (warmKeys := wk) (w := w) (vault := vault) (caller := caller) (src := src)
    (dst := dst) (amount := amount)
    hdeleg (hdep.vaultNotPrecompile _) (by omega) (hs.bal src hsr) (hs.bal dst hd)
    (hs.allow src hsr caller hc) (rep_toToken _) hinv.2 (max n 500) (le_max_right _ _)
  obtain rfl := terminates_unique hn (le_max_left _ _) hr'
  split at hres
  · rename_i t' ht
    obtain ⟨-, -, hwld, hrep, hframe⟩ := hres
    refine ⟨hdep.of_code (by rw [hwld]; exact code_transferFromWorld ..)
      (by rw [hwld]; exact code_transferFromWorld ..),
      callRefines_some (s' := { abs ctx.crypto w vault asset with shares := t' }) ?_ ?_⟩
    · show Option.map _ ((abs ctx.crypto w vault asset).shares.transferFrom _ _ _ _) = _
      rw [show (abs ctx.crypto w vault asset).shares.transferFrom caller src dst amount.toNat =
        some t' from ht]; rfl
    exact agree_of_shares hrep
      (fun o sp ⟨ho, hsp⟩ => ⟨hs.balP ho hsp src, hs.balP ho hsp dst,
        hs.allowP ho hsp hsr hc⟩)
      (fun k => hframe asset k (.inl hne.symm))
      (hframe vault 6#256 (.inr ⟨(hs.balFixed src hsr).1.symm, (hs.balFixed dst hd).1.symm,
        (hs.allowFixed src hsr caller hc).1.symm⟩))
      (hframe vault 7#256 (.inr ⟨(hs.balFixed src hsr).2.symm, (hs.balFixed dst hd).2.symm,
        (hs.allowFixed src hsr caller hc).2.symm⟩))
  · rename_i ht
    obtain ⟨-, -, hwld⟩ := hres
    refine ⟨hwld ▸ hdep, callRefines_none ?_ hwld⟩
    show Option.map _ ((abs ctx.crypto w vault asset).shares.transferFrom _ _ _ _) = _
    rw [show (abs ctx.crypto w vault asset).shares.transferFrom caller src dst amount.toNat = none
      from ht]; rfl

set_option maxHeartbeats 1000000 in
/-- **`vault.approve`** refines `Op.approve`. -/
theorem opRefines_approve (hmin : 100000 ≤ minGas) (caller spender : Address) (amount : Word) :
    OpRefinesAt crypto vault asset minGas Act (.approve caller spender amount) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, -, -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  have hne := hdep.vault_ne_asset
  obtain ⟨i, -, hcode⟩ := hdep.vaultCode
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, Bool.false_eq_true,
    ite_false, hcode] at hn
  have hc : caller ∈ Act := hact caller (by simp [VCall.actors])
  have hsp : spender ∈ Act := hact spender (by simp [VCall.actors])
  obtain ⟨r', hr', -, -, hwld, hrep, hframe⟩ := Shares.approve_refines (i := i) (tr := tr)
    (gas := gas) (warmAddrs := wa) (warmKeys := wk) (w := w) (vault := vault) (caller := caller)
    (spender := spender) (amount := amount)
    hdeleg (hdep.vaultNotPrecompile _) (by omega) (hs.allow caller hc spender hsp)
    (rep_toToken _) (max n 300) (le_max_right _ _)
  obtain rfl := terminates_unique hn (le_max_left _ _) hr'
  refine ⟨hdep.of_code (by rw [hwld]; exact code_approveWorld ..)
    (by rw [hwld]; exact code_approveWorld ..),
    callRefines_some (s' := { abs ctx.crypto w vault asset with
      shares := (abs ctx.crypto w vault asset).shares.approve caller spender amount.toNat }) rfl ?_⟩
  exact agree_of_shares hrep (fun o sp ⟨ho, hsp'⟩ => hs.allowP ho hsp' hc hsp)
    (fun k => hframe asset k (.inl hne.symm))
    (hframe vault 6#256 (.inr (hs.allowFixed caller hc spender hsp).1.symm))
    (hframe vault 7#256 (.inr (hs.allowFixed caller hc spender hsp).2.symm))

/-! ## The asset's `transfer` and `transferFrom`, top level -/

set_option maxHeartbeats 1000000 in
/-- **`asset.transfer`** (a donation when `dst` is the vault) refines `Op.assetTransfer`. -/
theorem opRefines_assetTransfer (hmin : 100000 ≤ minGas) (caller dst : Address) (amount : Word) :
    OpRefinesAt crypto vault asset minGas Act (.assetTransfer caller dst amount) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, -, -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  have hne := hdep.vault_ne_asset
  obtain ⟨ia, hcode⟩ := hdep.assetCode
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, ite_true, hcode] at hn
  have hc : caller ∈ Act := hact caller (by simp [VCall.actors])
  have hd : dst ∈ Act := hact dst (by simp [VCall.actors])
  have hm := assetTransfer_refines (ia := ia) (dst := dst) (amount := amount)
    (startMachine ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
      (Shares.transferData dst amount) gas wa wk))
    (fresh_startMachine ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
      (Shares.transferData dst amount) gas wa wk)) rfl rfl
    (twoWordCall_encodeCall (by decide) _ _)
    (show (Shares.transferData dst amount).size < 2 ^ 64 by
      rw [Shares.transferData, Abi.size_encodeCall]; simp)
    (show 60000 ≤ gas by omega) (hs.bal caller hc) (hs.bal dst hd) (rep_toToken _) hinv.1
  split at hm
  · rename_i t' ht
    obtain ⟨n', hn'⟩ := call_of_halts hdeleg (delegatedAddress?_assetCode ia)
      (hdep.assetNotPrecompile _) hm
    obtain ⟨mf, o, r', ⟨⟨ho, hwld, -⟩, hrep⟩, hrun, hsucc, -⟩ := hn' (max n n') (le_max_right _ _)
    obtain rfl := terminates_unique hn (le_max_left _ _) hrun
    have hw : r'.world = Erc20.transferWorld ctx.crypto w asset caller dst amount :=
      (hsucc _ ho).trans hwld
    rw [← hsucc _ ho] at hrep
    refine ⟨hdep.of_code (by rw [hw]; exact code_transferWorld ..)
      (by rw [hw]; exact code_transferWorld ..),
      callRefines_some (s' := { abs ctx.crypto w vault asset with asset := t' }) ?_ ?_⟩
    · show Option.map _ ((abs ctx.crypto w vault asset).asset.transfer _ _ _) = _
      rw [show (abs ctx.crypto w vault asset).asset.transfer caller dst amount.toNat = some t'
        from ht]; rfl
    exact agree_of_asset hrep (fun o sp ⟨ho, hsp⟩ => ⟨hs.balP ho hsp caller, hs.balP ho hsp dst⟩)
      (fun k => by rw [hw]; exact Shares.sload_transferWorld (.inl hne))
  · rename_i ht
    obtain ⟨n', hn'⟩ := call_of_halts hdeleg (delegatedAddress?_assetCode ia)
      (hdep.assetNotPrecompile _) hm
    obtain ⟨mf, o, r', ⟨⟨out, ho⟩, -⟩, hrun, -, hrev⟩ := hn' (max n n') (le_max_right _ _)
    obtain rfl := terminates_unique hn (le_max_left _ _) hrun
    have hw := hrev out ho
    refine ⟨hw ▸ hdep, callRefines_none ?_ hw⟩
    show Option.map _ ((abs ctx.crypto w vault asset).asset.transfer _ _ _) = _
    rw [show (abs ctx.crypto w vault asset).asset.transfer caller dst amount.toNat = none
      from ht]; rfl

set_option maxHeartbeats 1000000 in
/-- **`asset.transferFrom`** refines `Op.assetTransferFrom`. -/
theorem opRefines_assetTransferFrom (hmin : 100000 ≤ minGas) (caller src dst : Address)
    (amount : Word) :
    OpRefinesAt crypto vault asset minGas Act (.assetTransferFrom caller src dst amount) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, -, -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  have hne := hdep.vault_ne_asset
  obtain ⟨ia, hcode⟩ := hdep.assetCode
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, ite_true, hcode] at hn
  have hc : caller ∈ Act := hact caller (by simp [VCall.actors])
  have hsr : src ∈ Act := hact src (by simp [VCall.actors])
  have hd : dst ∈ Act := hact dst (by simp [VCall.actors])
  have hm := assetTransferFrom_refines (ia := ia) (src := src) (dst := dst) (amount := amount)
    (startMachine ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
      (Shares.transferFromData src dst amount) gas wa wk))
    (fresh_startMachine ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
      (Shares.transferFromData src dst amount) gas wa wk)) rfl rfl
    (threeWordCall_encodeCall (by decide) _ _ _)
    (show (Shares.transferFromData src dst amount).size < 2 ^ 64 by
      rw [Shares.transferFromData, Abi.size_encodeCall]; simp)
    (show 90000 ≤ gas by omega) (hs.bal src hsr) (hs.bal dst hd) (hs.allow src hsr caller hc)
    (rep_toToken _) hinv.1
  split at hm
  · rename_i t' ht
    obtain ⟨n', hn'⟩ := call_of_halts hdeleg (delegatedAddress?_assetCode ia)
      (hdep.assetNotPrecompile _) hm
    obtain ⟨mf, o, r', ⟨⟨ho, hwld, -⟩, hrep⟩, hrun, hsucc, -⟩ := hn' (max n n') (le_max_right _ _)
    obtain rfl := terminates_unique hn (le_max_left _ _) hrun
    have hw : r'.world = Erc20.transferFromWorld ctx.crypto w asset caller src dst amount :=
      (hsucc _ ho).trans hwld
    rw [← hsucc _ ho] at hrep
    refine ⟨hdep.of_code (by rw [hw]; exact code_transferFromWorld ..)
      (by rw [hw]; exact code_transferFromWorld ..),
      callRefines_some (s' := { abs ctx.crypto w vault asset with asset := t' }) ?_ ?_⟩
    · show Option.map _ ((abs ctx.crypto w vault asset).asset.transferFrom _ _ _ _) = _
      rw [show (abs ctx.crypto w vault asset).asset.transferFrom caller src dst amount.toNat =
        some t' from ht]; rfl
    exact agree_of_asset hrep (fun o sp ⟨ho, hsp⟩ =>
        ⟨⟨hs.balP ho hsp src, hs.balP ho hsp dst⟩, hs.allowP ho hsp hsr hc⟩)
      (fun k => by rw [hw]; exact sload_transferFromWorld_other hne k)
  · rename_i ht
    obtain ⟨n', hn'⟩ := call_of_halts hdeleg (delegatedAddress?_assetCode ia)
      (hdep.assetNotPrecompile _) hm
    obtain ⟨mf, o, r', ⟨⟨out, ho⟩, -⟩, hrun, -, hrev⟩ := hn' (max n n') (le_max_right _ _)
    obtain rfl := terminates_unique hn (le_max_left _ _) hrun
    have hw := hrev out ho
    refine ⟨hw ▸ hdep, callRefines_none ?_ hw⟩
    show Option.map _ ((abs ctx.crypto w vault asset).asset.transferFrom _ _ _ _) = _
    rw [show (abs ctx.crypto w vault asset).asset.transferFrom caller src dst amount.toNat = none
      from ht]; rfl

/-- **Every call on `main` today refines its operation** (`VCall.Proven`). -/
theorem opRefines_proven (hmin : 100000 ≤ minGas) (c : VCall) (hc : c.Proven) :
    OpRefinesAt crypto vault asset minGas Act c := by
  cases c with
  | transfer c d v => exact opRefines_transfer hmin c d v
  | transferFrom c s d v => exact opRefines_transferFrom hmin c s d v
  | approve c sp v => exact opRefines_approve hmin c sp v
  | assetTransfer c d v => exact opRefines_assetTransfer hmin c d v
  | assetTransferFrom c s d v => exact opRefines_assetTransferFrom hmin c s d v
  | deposit => exact hc.elim
  | mint => exact hc.elim
  | withdraw => exact hc.elim
  | redeem => exact hc.elim
  | assetApprove => exact hc.elim
  | assetMint => exact hc.elim
  | assetBurn => exact hc.elim

end EvmLeanSpecs.Refinement.Invariants
