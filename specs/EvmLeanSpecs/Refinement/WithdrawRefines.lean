import EvmLeanSpecs.Refinement.Redeem
import EvmLeanSpecs.Refinement.VaultViewsSpec

/-!
# `withdraw` and `redeem` refine the model

For the compiled Solmate vault deployed with any immutables `i` (any asset address):

* **Frame form** (`withdraw_refines`, `redeem_refines`): run in any fresh frame that `OutPre i`
  describes (top level or called by another contract, any `Crypto`), from a world whose model
  state `absOf i.asset m` satisfies the model's invariant (`Solmate.Inv`: both ledgers well
  formed), under the Keccak hypotheses `Out.OutSlots`, the function ends the frame by cases on
  the model's `Solmate.withdraw` / `Solmate.redeem`: on `some (s', v)` it returns the ABI word
  of `v` and the final world refines `s'` (`Out.RefinesOn`: both ledgers, every balance and the
  total supplies, allowances outside the written slots, the hook counters); on `none` it
  reverts (so the caller sees the world unchanged).
* **Top-level form** (`withdraw_call`, `redeem_call`): `processMessageCall` of a transaction
  calling the `Deployed` vault with `Abi.encodeCall` calldata: on `some` it succeeds with the
  ABI word, a deployed world refining `s'`; on `none` it reverts with the world unchanged.

Both cover `caller = owner` and the third-party path (allowance spend, finite or infinite).
The proofs combine the bytecode summaries `withdraw_halts` / `redeem_halts` (the world chains
`Out.withdrawWorld?` / `Out.redeemWorld?`) with the model-level `Out.withdrawWorld?_refines` /
`Out.redeemWorld?_refines`.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Refinement.Out
open Vault

/-- What `withdraw` / `redeem` end with, against the model's result `r` from caller `caller`
paying `receiver` for `owner`: success with the ABI word and a world refining the model's state,
or a revert. -/
def OutRefPost (crypto : Crypto) (vault asset caller receiver owner : Address)
    (r : Option (Solmate.State Address × ℕ)) (mf : Machine) (o : Outcome) : Prop :=
  match r with
  | some (s', v) => o = .success (Bytes.ofWord (BitVec.ofNat 256 v)) ∧
      RefinesOn (OutAllowances crypto caller owner) (TransferAllowances crypto vault receiver)
        crypto mf.world vault asset s'
  | none => ∃ out, o = .revert out

/-- From the bytecode-level result to the model-level one. -/
theorem outRefPost_of {crypto : Crypto} {vault asset caller receiver owner : Address}
    {r : Option (Solmate.State Address × ℕ)} {rw : Option (World × Word)}
    (hW : match r with
      | some (s', v) => ∃ w', rw = some (w', BitVec.ofNat 256 v) ∧
          RefinesOn (OutAllowances crypto caller owner) (TransferAllowances crypto vault receiver)
            crypto w' vault asset s'
      | none => rw = none)
    {mf : Machine} {o : Outcome} (h : OutPost rw mf o) :
    OutRefPost crypto vault asset caller receiver owner r mf o := by
  unfold OutRefPost
  split at hW
  · obtain ⟨w', rfl, hR⟩ := hW
    obtain ⟨ho, hw⟩ := h
    exact ⟨ho, hw ▸ hR⟩
  · subst hW
    exact h

/-- **`withdraw(assets, receiver, owner)` refines `Solmate.withdraw`**, in any frame. -/
theorem withdraw_refines {i : SolmateVault.Immutables} (m : Machine) (h : OutPre i m)
    {assets : Word} {receiver owner : Address}
    (hd : ThreeWordCall m.frame.msg.data 0xb460af94 assets (Word.ofAddress receiver)
      (Word.ofAddress owner))
    (hk : OutSlots m.ctx.crypto m.frame.msg.currentTarget m.frame.msg.caller owner receiver)
    (hinv : Solmate.Inv (absOf i.asset m)) :
    Halts m (OutRefPost m.ctx.crypto m.frame.msg.currentTarget i.asset m.frame.msg.caller
      receiver owner (Solmate.withdraw (absOf i.asset m) m.frame.msg.caller assets.toNat
        receiver owner)) :=
  (withdraw_halts m h hd).mono fun _ _ _ hp =>
    outRefPost_of (withdrawWorld?_refines (refines_iff.2 rfl) hinv h.assetNe hk assets) hp

/-- **`redeem(shares, receiver, owner)` refines `Solmate.redeem`**, in any frame. -/
theorem redeem_refines {i : SolmateVault.Immutables} (m : Machine) (h : OutPre i m)
    {shares : Word} {receiver owner : Address}
    (hd : ThreeWordCall m.frame.msg.data 0xba087652 shares (Word.ofAddress receiver)
      (Word.ofAddress owner))
    (hk : OutSlots m.ctx.crypto m.frame.msg.currentTarget m.frame.msg.caller owner receiver)
    (hinv : Solmate.Inv (absOf i.asset m)) :
    Halts m (OutRefPost m.ctx.crypto m.frame.msg.currentTarget i.asset m.frame.msg.caller
      receiver owner (Solmate.redeem (absOf i.asset m) m.frame.msg.caller shares.toNat
        receiver owner)) :=
  (redeem_halts m h hd).mono fun _ _ _ hp =>
    outRefPost_of (redeemWorld?_refines (refines_iff.2 rfl) hinv h.assetNe hk shares) hp

/-! ## Top-level transactions -/

/-- What a top-level `withdraw` / `redeem` returns, against the model's result `r`. -/
def OutResult (crypto : Crypto) (w : World) (vault asset caller receiver owner : Address)
    (res : MessageResult) (r : Option (Solmate.State Address × ℕ)) : Prop :=
  match r with
  | some (s', v) => res.success = true ∧ res.output = Bytes.ofWord (BitVec.ofNat 256 v) ∧
      RefinesOn (OutAllowances crypto caller owner) (TransferAllowances crypto vault receiver)
        crypto res.world vault asset s'
  | none => res.success = false ∧ res.reverted = true ∧ res.world = w

variable {ctx : Context} {w : World} {tr : TransientStorage} {vault asset caller : Address}
  {data : ByteArray} {gas : Nat} {wa : AddressSet} {wk : StorageKeySet}

/-- In a deployment the asset is not the vault (the codes have different sizes). -/
theorem Deployed.asset_ne {w : World} {vault asset : Address} (h : Deployed w vault asset) :
    asset ≠ vault := by
  rintro rfl
  obtain ⟨i, -, hi⟩ := h.vaultCode
  obtain ⟨ia, hia⟩ := h.assetCode
  have := congrArg ByteArray.size (hi.symm.trans hia)
  rw [SolmateAsset.runtimeCodeWith, size_patchWords, SolmateAsset.size_runtimeCode] at this
  have h2 := Shares.size_code i
  simp only [Shares.code] at h2
  omega

/-- The start of a top-level call to the deployed vault satisfies `OutPre`. -/
theorem outPre_start {i : SolmateVault.Immutables} (hdep : Deployed w vault i.asset)
    (hgas : 200000 ≤ gas) (hgas' : gas < 2 ^ 64) (hsize : data.size < 2 ^ 64) :
    OutPre i (startMachine ctx w tr
      (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk)) where
  fresh := fresh_startMachine ctx w tr
    (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk)
  value := rfl
  static := rfl
  assetCode := hdep.assetCode
  assetNotPrecompile := hdep.assetNotPrecompile ctx.fork
  assetNe := hdep.asset_ne
  depth := by simp [startMachine, callMsg, Frame.init, Gas.stackDepthLimit]
  gas := hgas
  gasLt := hgas'
  sizeLt := hsize

/-- `Abi.encodeCall sel [x, y, z]` is a `ThreeWordCall`. -/
theorem threeWordCall_encodeCall' {sel : Nat} (hsel : sel < 2 ^ 32) (x y z : Word) :
    ThreeWordCall (Abi.encodeCall sel [x, y, z]) sel x y z :=
  ⟨by rw [Abi.selectorOf_encodeCall, Nat.mod_eq_of_lt hsel],
   by rw [Abi.size_encodeCall]; simp, Abi.calldataload_encodeCall_0 _ _ _,
   Abi.calldataload_encodeCall_1 _ _ _ _, Abi.calldataload_encodeCall_2 _ _ _ _ _⟩

set_option maxHeartbeats 1000000 in
/-- A frame summary of a top-level call to the vault, in the form `OutRefPost`, gives the
result of `processMessageCall`. -/
theorem out_call {i : SolmateVault.Immutables} {receiver owner : Address}
    {r : Option (Solmate.State Address × ℕ)}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork vault = false)
    (h : Halts (startMachine ctx w tr
        (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk))
      (OutRefPost ctx.crypto vault i.asset caller receiver owner r)) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk) = .ok res ∧
      OutResult ctx.crypto w vault i.asset caller receiver owner res r := by
  have hdel : delegatedAddress?
      (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk).code = none :=
    Shares.delegatedAddress?_code i
  obtain ⟨n, hn⟩ := processMessageCall_of_halts (a := vault) hdeleg hdel rfl rfl hpre rfl rfl h
  refine ⟨n, fun fuel hle => ?_⟩
  obtain ⟨mf, o, hH, hs, hrun⟩ := hn fuel hle
  have hk : mf.frame.kind = .call 0 0 := hs.kind
  refine ⟨_, hrun, ?_⟩
  unfold OutRefPost at hH
  unfold OutResult
  split at hH
  · obtain ⟨ho, hR⟩ := hH
    subst ho
    obtain ⟨h1, h2, h3, -⟩ := topLevelResult_success_call (t := (callMsg
      (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk).target)
      (out := Bytes.ofWord _) hk
    exact ⟨h1, h2, h3 ▸ hR⟩
  · obtain ⟨out, ho⟩ := hH
    subst ho
    have hsnap : mf.frame.snapshot.1 = w := by rw [hs.snapshot]; rfl
    simp only [frameResult_revert, topLevelResult_world, topLevelResult_success,
      topLevelResult_reverted, ChildResult.success, hsnap]
    decide

/-- **`withdraw(assets, receiver, owner)` as a top-level transaction** on the deployed vault:
refines `Solmate.withdraw` of the model state read from the world. -/
theorem withdraw_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 200000 ≤ gas)
    (hgas' : gas < 2 ^ 64) {receiver owner : Address}
    (hk : OutSlots ctx.crypto vault caller owner receiver)
    (hinv : Solmate.Inv (abs ctx.crypto w vault asset)) (assets : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller
          (Abi.encodeCall 0xb460af94 [assets, Word.ofAddress receiver, Word.ofAddress owner])
          gas wa wk) = .ok res ∧
      OutResult ctx.crypto w vault asset caller receiver owner res
        (Solmate.withdraw (abs ctx.crypto w vault asset) caller assets.toNat receiver owner) := by
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have hm := withdraw_refines _ (outPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep hgas hgas'
    (by rw [Abi.size_encodeCall]; simp))
    (threeWordCall_encodeCall' (by decide) assets _ _) hk hinv
  exact out_call hdeleg (hdep.vaultNotPrecompile _) hm

/-- **`redeem(shares, receiver, owner)` as a top-level transaction** on the deployed vault:
refines `Solmate.redeem` of the model state read from the world. -/
theorem redeem_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 200000 ≤ gas)
    (hgas' : gas < 2 ^ 64) {receiver owner : Address}
    (hk : OutSlots ctx.crypto vault caller owner receiver)
    (hinv : Solmate.Inv (abs ctx.crypto w vault asset)) (shares : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller
          (Abi.encodeCall 0xba087652 [shares, Word.ofAddress receiver, Word.ofAddress owner])
          gas wa wk) = .ok res ∧
      OutResult ctx.crypto w vault asset caller receiver owner res
        (Solmate.redeem (abs ctx.crypto w vault asset) caller shares.toNat receiver owner) := by
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have hm := redeem_refines _ (outPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep hgas hgas'
    (by rw [Abi.size_encodeCall]; simp))
    (threeWordCall_encodeCall' (by decide) shares _ _) hk hinv
  exact out_call hdeleg (hdep.vaultNotPrecompile _) hm

end EvmLeanSpecs.Refinement
