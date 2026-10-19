import EvmLeanSpecs.Refinement.Abstraction

/-!
# The vault's views refine the model

For every view of the compiled vault: run in **any** frame that `ViewPre` describes (a fresh
frame of the vault's code, top level or called by another contract, for any `Crypto`, any
world with the asset deployed, enough gas), it returns exactly the model's value
(`Vault.Solmate.State.convertToShares` …, at `absOf m`, the model state read from the frame's
world) when the model returns `some v`, and reverts with empty data when it returns `none`
(`mulDiv` overflow or division by zero); the world is unchanged in both cases (`ViewPost`).
These are `Halts` statements, so they serve as callee summaries for `WP.call` /
`WP.staticcall` as well.

`*_call` restate them for a top-level transaction calling the vault at `vault` with
`Abi.encodeCall` calldata, in a world where the vault is `Deployed`.

`asset()` has no model counterpart: it returns the asset address (`asset_refines`).
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open Vault

/-! ## Callee role: any frame -/

/-- **`convertToShares(uint256)` refines the model**, in any frame. -/
theorem convertToShares_refines (m : Machine) (h : ViewPre m) {x : Word} (hd : WordCall m.frame.msg.data 0xc6e6f592 x) :
    Halts m (ViewPost m ((absOf m).convertToShares x.toNat)) := by
  simp only [absOf_convertToShares]
  exact convertToShares_halts m h hd

/-- **`convertToAssets(uint256)` refines the model**, in any frame. -/
theorem convertToAssets_refines (m : Machine) (h : ViewPre m) {x : Word} (hd : WordCall m.frame.msg.data 0x07a2d13a x) :
    Halts m (ViewPost m ((absOf m).convertToAssets x.toNat)) := by
  simp only [absOf_convertToAssets]
  exact convertToAssets_halts m h hd

/-- **`previewDeposit(uint256)` refines the model**, in any frame. -/
theorem previewDeposit_refines (m : Machine) (h : ViewPre m) {x : Word} (hd : WordCall m.frame.msg.data 0xef8b30f7 x) :
    Halts m (ViewPost m ((absOf m).previewDeposit x.toNat)) := by
  simp only [Solmate.State.previewDeposit, absOf_convertToShares]
  exact previewDeposit_halts m h hd

/-- **`previewMint(uint256)` refines the model**, in any frame. -/
theorem previewMint_refines (m : Machine) (h : ViewPre m) {x : Word} (hd : WordCall m.frame.msg.data 0xb3d7f6b9 x) :
    Halts m (ViewPost m ((absOf m).previewMint x.toNat)) := by
  simp only [absOf_previewMint]
  exact previewMint_halts m h hd

/-- **`previewWithdraw(uint256)` refines the model**, in any frame. -/
theorem previewWithdraw_refines (m : Machine) (h : ViewPre m) {x : Word} (hd : WordCall m.frame.msg.data 0x0a28a477 x) :
    Halts m (ViewPost m ((absOf m).previewWithdraw x.toNat)) := by
  simp only [absOf_previewWithdraw]
  exact previewWithdraw_halts m h hd

/-- **`previewRedeem(uint256)` refines the model**, in any frame. -/
theorem previewRedeem_refines (m : Machine) (h : ViewPre m) {x : Word} (hd : WordCall m.frame.msg.data 0x4cdad506 x) :
    Halts m (ViewPost m ((absOf m).previewRedeem x.toNat)) := by
  simp only [Solmate.State.previewRedeem, absOf_convertToAssets]
  exact previewRedeem_halts m h hd

/-- **`maxDeposit(address)` refines the model**, in any frame. -/
theorem maxDeposit_refines (m : Machine) (h : ViewPre m) {a : Address} (hd : AddrCall m.frame.msg.data 0x402d267d a) :
    Halts m (ViewPost m (some ((absOf m).maxDeposit a))) := by
  simp only [Solmate.State.maxDeposit]
  exact maxDeposit_halts m h hd

/-- **`maxMint(address)` refines the model**, in any frame. -/
theorem maxMint_refines (m : Machine) (h : ViewPre m) {a : Address} (hd : AddrCall m.frame.msg.data 0xc63d75b6 a) :
    Halts m (ViewPost m (some ((absOf m).maxMint a))) := by
  simp only [Solmate.State.maxMint]
  exact maxMint_halts m h hd

/-- **`maxWithdraw(address)` refines the model**, in any frame. -/
theorem maxWithdraw_refines (m : Machine) (h : ViewPre m) {a : Address} (hd : AddrCall m.frame.msg.data 0xce96cb77 a) :
    Halts m (ViewPost m ((absOf m).maxWithdraw a)) := by
  simp only [Solmate.State.maxWithdraw, absOf_sharesOf, absOf_convertToAssets]
  exact maxWithdraw_halts m h hd

/-- **`maxRedeem(address)` refines the model**, in any frame. -/
theorem maxRedeem_refines (m : Machine) (h : ViewPre m) {a : Address} (hd : AddrCall m.frame.msg.data 0xd905777e a) :
    Halts m (ViewPost m (some ((absOf m).maxRedeem a))) := by
  simp only [Solmate.State.maxRedeem, absOf_sharesOf]
  exact maxRedeem_halts m h hd

/-- **`totalAssets()` refines the model**, in any frame. -/
theorem totalAssets_refines (m : Machine) (h : ViewPre m) (hd : NoArgCall m.frame.msg.data 0x01e1d114) :
    Halts m (ViewPost m (some (absOf m).totalAssets)) := by
  simp only [absOf_totalAssets]
  exact totalAssets_halts m h hd

/-- **`asset()`** returns the asset address, in any frame. -/
theorem asset_refines (m : Machine) (h : ViewPre m) (hd : NoArgCall m.frame.msg.data 0x38d52e0f) :
    Halts m (ViewPost m (some assetAddr.toNat)) :=
  asset_halts m h hd

/-! ## Top-level transactions -/

/-- What a top-level view call returns: success with the ABI word of `v` for `some v`, a
revert for `none`. -/
def ViewResult (res : MessageResult) (r : Option ℕ) : Prop :=
  match r with
  | some v => res.success = true ∧ res.output = Bytes.ofWord (BitVec.ofNat 256 v)
  | none => res.success = false ∧ res.reverted = true

/-- A view summary of the start machine of a top-level call to the vault gives the result of
`processMessageCall`: the world is unchanged and the result is `ViewResult`. -/
theorem view_call {ctx : Context} {w : World} {tr : TransientStorage} {vault caller : Address}
    {data : ByteArray} {gas : Nat} {wa : AddressSet} {wk : StorageKeySet} {r : Option ℕ}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork vault = false)
    (h : Halts (startMachine ctx w tr (callMsg SolmateVault.runtimeCode vault caller data gas wa wk))
      (ViewPost (startMachine ctx w tr (callMsg SolmateVault.runtimeCode vault caller data gas wa wk))
        r)) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg SolmateVault.runtimeCode vault caller data gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res r := by
  have hdel : delegatedAddress?
      (callMsg SolmateVault.runtimeCode vault caller data gas wa wk).code = none := by
    rw [show (callMsg SolmateVault.runtimeCode vault caller data gas wa wk).code =
      SolmateVault.runtimeCode from rfl]
    exact delegatedAddress?_vault
  obtain ⟨n, hn⟩ := processMessageCall_of_halts (a := vault) hdeleg hdel rfl rfl hpre rfl rfl h
  refine ⟨n, fun fuel hle => ?_⟩
  obtain ⟨mf, o, ⟨hw, ho⟩, hs, hrun⟩ := hn fuel hle
  have hk : mf.frame.kind = .call 0 0 := hs.kind
  refine ⟨_, hrun, ?_⟩
  cases r with
  | some v =>
    simp only at ho
    subst ho
    obtain ⟨h1, h2, h3, -⟩ := topLevelResult_success_call (t := (callMsg SolmateVault.runtimeCode
      vault caller data gas wa wk).target) (out := Bytes.ofWord (BitVec.ofNat 256 v)) hk
    exact ⟨h3.trans hw, h1, h2⟩
  | none =>
    simp only at ho
    subst ho
    have hsnap : mf.frame.snapshot.1 = w := by rw [hs.snapshot]; rfl
    simp only [frameResult_revert, topLevelResult_world, topLevelResult_success,
      topLevelResult_reverted, ViewResult, ChildResult.success, hsnap]
    decide

/-- The start of a top-level call to the deployed vault satisfies `ViewPre`. -/
theorem viewPre_start {ctx : Context} {w : World} {tr : TransientStorage}
    {vault asset caller : Address} {data : ByteArray} {gas : Nat} {wa : AddressSet}
    {wk : StorageKeySet} (hdep : Deployed w vault asset) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) (hsize : data.size < 2 ^ 64) :
    ViewPre (startMachine ctx w tr (callMsg SolmateVault.runtimeCode vault caller data gas wa wk)) where
  fresh := fresh_startMachine _ _ _ _
  value := rfl
  assetCode := hdep.asset_eq ▸ hdep.assetCode
  assetNotPrecompile := assetAddr_not_precompile ctx.fork
  depth := by simp [startMachine, callMsg, Frame.init, Gas.stackDepthLimit]
  gas := hgas
  gasLt := hgas'
  sizeLt := hsize

/-- `absOf` at the start of a top-level call is `abs` of the world. -/
theorem absOf_start {ctx : Context} {w : World} {tr : TransientStorage}
    {vault asset caller : Address} {data : ByteArray} {gas : Nat} {wa : AddressSet}
    {wk : StorageKeySet} (hdep : Deployed w vault asset) :
    absOf (startMachine ctx w tr (callMsg SolmateVault.runtimeCode vault caller data gas wa wk)) =
      abs ctx.crypto w vault asset := by
  rw [hdep.asset_eq]; rfl

/-- `Abi.encodeCall sel [x]` is a `WordCall`. -/
theorem wordCall_encodeCall {sel : Nat} (hsel : sel < 2 ^ 32) (x : Word) :
    WordCall (Abi.encodeCall sel [x]) sel x :=
  ⟨by rw [Abi.selectorOf_encodeCall, Nat.mod_eq_of_lt hsel],
   by rw [Abi.size_encodeCall]; simp, Abi.calldataload_encodeCall_0 _ _ _⟩

/-- `Abi.encodeCall sel [a]` is an `AddrCall`. -/
theorem addrCall_encodeCall {sel : Nat} (hsel : sel < 2 ^ 32) (a : Address) :
    AddrCall (Abi.encodeCall sel [Word.ofAddress a]) sel a :=
  ⟨by rw [Abi.selectorOf_encodeCall, Nat.mod_eq_of_lt hsel],
   by rw [Abi.size_encodeCall]; simp, Abi.calldataload_encodeCall_0 _ _ _⟩

/-- `Abi.encodeCall sel []` is a `NoArgCall`. -/
theorem noArgCall_encodeCall {sel : Nat} (hsel : sel < 2 ^ 32) :
    NoArgCall (Abi.encodeCall sel []) sel :=
  ⟨by rw [Abi.selectorOf_encodeCall, Nat.mod_eq_of_lt hsel], by rw [Abi.size_encodeCall]; simp⟩

variable {ctx : Context} {w : World} {tr : TransientStorage} {vault asset caller : Address}
  {gas : Nat} {wa : AddressSet} {wk : StorageKeySet}

/-- **`convertToShares(uint256)` as a top-level transaction** on the deployed vault. -/
theorem convertToShares_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) (x : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg SolmateVault.runtimeCode vault caller (Abi.encodeCall 0xc6e6f592 [x]) gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res ((abs ctx.crypto w vault asset).convertToShares x.toNat) := by
  have h := convertToShares_refines _ (viewPre_start (ctx := ctx) (tr := tr) (caller := caller) (wa := wa)
    (wk := wk) (data := Abi.encodeCall _ _) hdep hgas hgas' (by rw [Abi.size_encodeCall]; simp))
    (wordCall_encodeCall (by decide) x)
  rw [absOf_start hdep] at h
  exact view_call hdeleg (hdep.vaultNotPrecompile _) h

/-- **`convertToAssets(uint256)` as a top-level transaction** on the deployed vault. -/
theorem convertToAssets_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) (x : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg SolmateVault.runtimeCode vault caller (Abi.encodeCall 0x07a2d13a [x]) gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res ((abs ctx.crypto w vault asset).convertToAssets x.toNat) := by
  have h := convertToAssets_refines _ (viewPre_start (ctx := ctx) (tr := tr) (caller := caller) (wa := wa)
    (wk := wk) (data := Abi.encodeCall _ _) hdep hgas hgas' (by rw [Abi.size_encodeCall]; simp))
    (wordCall_encodeCall (by decide) x)
  rw [absOf_start hdep] at h
  exact view_call hdeleg (hdep.vaultNotPrecompile _) h

/-- **`previewDeposit(uint256)` as a top-level transaction** on the deployed vault. -/
theorem previewDeposit_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) (x : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg SolmateVault.runtimeCode vault caller (Abi.encodeCall 0xef8b30f7 [x]) gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res ((abs ctx.crypto w vault asset).previewDeposit x.toNat) := by
  have h := previewDeposit_refines _ (viewPre_start (ctx := ctx) (tr := tr) (caller := caller) (wa := wa)
    (wk := wk) (data := Abi.encodeCall _ _) hdep hgas hgas' (by rw [Abi.size_encodeCall]; simp))
    (wordCall_encodeCall (by decide) x)
  rw [absOf_start hdep] at h
  exact view_call hdeleg (hdep.vaultNotPrecompile _) h

/-- **`previewMint(uint256)` as a top-level transaction** on the deployed vault. -/
theorem previewMint_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) (x : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg SolmateVault.runtimeCode vault caller (Abi.encodeCall 0xb3d7f6b9 [x]) gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res ((abs ctx.crypto w vault asset).previewMint x.toNat) := by
  have h := previewMint_refines _ (viewPre_start (ctx := ctx) (tr := tr) (caller := caller) (wa := wa)
    (wk := wk) (data := Abi.encodeCall _ _) hdep hgas hgas' (by rw [Abi.size_encodeCall]; simp))
    (wordCall_encodeCall (by decide) x)
  rw [absOf_start hdep] at h
  exact view_call hdeleg (hdep.vaultNotPrecompile _) h

/-- **`previewWithdraw(uint256)` as a top-level transaction** on the deployed vault. -/
theorem previewWithdraw_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) (x : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg SolmateVault.runtimeCode vault caller (Abi.encodeCall 0x0a28a477 [x]) gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res ((abs ctx.crypto w vault asset).previewWithdraw x.toNat) := by
  have h := previewWithdraw_refines _ (viewPre_start (ctx := ctx) (tr := tr) (caller := caller) (wa := wa)
    (wk := wk) (data := Abi.encodeCall _ _) hdep hgas hgas' (by rw [Abi.size_encodeCall]; simp))
    (wordCall_encodeCall (by decide) x)
  rw [absOf_start hdep] at h
  exact view_call hdeleg (hdep.vaultNotPrecompile _) h

/-- **`previewRedeem(uint256)` as a top-level transaction** on the deployed vault. -/
theorem previewRedeem_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) (x : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg SolmateVault.runtimeCode vault caller (Abi.encodeCall 0x4cdad506 [x]) gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res ((abs ctx.crypto w vault asset).previewRedeem x.toNat) := by
  have h := previewRedeem_refines _ (viewPre_start (ctx := ctx) (tr := tr) (caller := caller) (wa := wa)
    (wk := wk) (data := Abi.encodeCall _ _) hdep hgas hgas' (by rw [Abi.size_encodeCall]; simp))
    (wordCall_encodeCall (by decide) x)
  rw [absOf_start hdep] at h
  exact view_call hdeleg (hdep.vaultNotPrecompile _) h

/-- **`maxDeposit(address)` as a top-level transaction** on the deployed vault. -/
theorem maxDeposit_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) (a : Address) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg SolmateVault.runtimeCode vault caller (Abi.encodeCall 0x402d267d [Word.ofAddress a]) gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res (some ((abs ctx.crypto w vault asset).maxDeposit a)) := by
  have h := maxDeposit_refines _ (viewPre_start (ctx := ctx) (tr := tr) (caller := caller) (wa := wa)
    (wk := wk) (data := Abi.encodeCall _ _) hdep hgas hgas' (by rw [Abi.size_encodeCall]; simp))
    (addrCall_encodeCall (by decide) a)
  rw [absOf_start hdep] at h
  exact view_call hdeleg (hdep.vaultNotPrecompile _) h

/-- **`maxMint(address)` as a top-level transaction** on the deployed vault. -/
theorem maxMint_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) (a : Address) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg SolmateVault.runtimeCode vault caller (Abi.encodeCall 0xc63d75b6 [Word.ofAddress a]) gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res (some ((abs ctx.crypto w vault asset).maxMint a)) := by
  have h := maxMint_refines _ (viewPre_start (ctx := ctx) (tr := tr) (caller := caller) (wa := wa)
    (wk := wk) (data := Abi.encodeCall _ _) hdep hgas hgas' (by rw [Abi.size_encodeCall]; simp))
    (addrCall_encodeCall (by decide) a)
  rw [absOf_start hdep] at h
  exact view_call hdeleg (hdep.vaultNotPrecompile _) h

/-- **`maxWithdraw(address)` as a top-level transaction** on the deployed vault. -/
theorem maxWithdraw_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) (a : Address) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg SolmateVault.runtimeCode vault caller (Abi.encodeCall 0xce96cb77 [Word.ofAddress a]) gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res ((abs ctx.crypto w vault asset).maxWithdraw a) := by
  have h := maxWithdraw_refines _ (viewPre_start (ctx := ctx) (tr := tr) (caller := caller) (wa := wa)
    (wk := wk) (data := Abi.encodeCall _ _) hdep hgas hgas' (by rw [Abi.size_encodeCall]; simp))
    (addrCall_encodeCall (by decide) a)
  rw [absOf_start hdep] at h
  exact view_call hdeleg (hdep.vaultNotPrecompile _) h

/-- **`maxRedeem(address)` as a top-level transaction** on the deployed vault. -/
theorem maxRedeem_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) (a : Address) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg SolmateVault.runtimeCode vault caller (Abi.encodeCall 0xd905777e [Word.ofAddress a]) gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res (some ((abs ctx.crypto w vault asset).maxRedeem a)) := by
  have h := maxRedeem_refines _ (viewPre_start (ctx := ctx) (tr := tr) (caller := caller) (wa := wa)
    (wk := wk) (data := Abi.encodeCall _ _) hdep hgas hgas' (by rw [Abi.size_encodeCall]; simp))
    (addrCall_encodeCall (by decide) a)
  rw [absOf_start hdep] at h
  exact view_call hdeleg (hdep.vaultNotPrecompile _) h

/-- **`totalAssets()` as a top-level transaction** on the deployed vault. -/
theorem totalAssets_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg SolmateVault.runtimeCode vault caller (Abi.encodeCall 0x01e1d114 []) gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res (some (abs ctx.crypto w vault asset).totalAssets) := by
  have h := totalAssets_refines _ (viewPre_start (ctx := ctx) (tr := tr) (caller := caller) (wa := wa)
    (wk := wk) (data := Abi.encodeCall _ _) hdep hgas hgas' (by rw [Abi.size_encodeCall]; simp))
    (noArgCall_encodeCall (by decide))
  rw [absOf_start hdep] at h
  exact view_call hdeleg (hdep.vaultNotPrecompile _) h

end EvmLeanSpecs.Refinement
