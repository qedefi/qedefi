import Examples.Solmate.ERC4626.Abstraction
import Examples.Solmate.ERC4626.SharesFrame
import Examples.Solmate.ERC20.BalanceOf

/-!
# The vault's views refine the model

For every view of the compiled vault, deployed with any immutables `i` (any asset address):
run in **any** frame that `ViewPre i` describes (a fresh frame of the vault's code, top level
or called by another contract, for any `Crypto`, any world with the asset deployed, enough
gas), it returns exactly the model's value (`Vault.Solmate.State.convertToShares` …, at
`absOf i.asset m`, the model state read from the frame's world) when the model returns
`some v`, and reverts with empty data when it returns `none` (`mulDiv` overflow or division by
zero); the world is unchanged in both cases (`ViewPost`). These are `Halts` statements, so they
also serve as callee summaries for `WP.call` / `WP.staticcall`.

`*_call` restate them for a top-level transaction (`processMessageCall`) calling the vault at
`vault` with `Abi.encodeCall` calldata, in a world where the vault is `Deployed`.

`asset()` has no model counterpart: it returns the asset address (`asset_refines`).
-/

section

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open Vault

/-! ## Callee role: any frame -/

/-- **`convertToShares(uint256)` refines the model**, in any frame. -/
theorem convertToShares_refines {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m) {x : Word}
    (hd : WordCall m.frame.msg.data 0xc6e6f592 x) :
    Halts m (ViewPost m ((absOf i.asset m).convertToShares x.toNat)) := by
  simp only [absOf_convertToShares]
  exact convertToShares_halts m h hd

/-- **`convertToAssets(uint256)` refines the model**, in any frame. -/
theorem convertToAssets_refines {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m) {x : Word}
    (hd : WordCall m.frame.msg.data 0x07a2d13a x) :
    Halts m (ViewPost m ((absOf i.asset m).convertToAssets x.toNat)) := by
  simp only [absOf_convertToAssets]
  exact convertToAssets_halts m h hd

/-- **`previewDeposit(uint256)` refines the model**, in any frame. -/
theorem previewDeposit_refines {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m) {x : Word}
    (hd : WordCall m.frame.msg.data 0xef8b30f7 x) :
    Halts m (ViewPost m ((absOf i.asset m).previewDeposit x.toNat)) := by
  simp only [Solmate.State.previewDeposit, absOf_convertToShares]
  exact previewDeposit_halts m h hd

/-- **`previewMint(uint256)` refines the model**, in any frame. -/
theorem previewMint_refines {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m) {x : Word}
    (hd : WordCall m.frame.msg.data 0xb3d7f6b9 x) :
    Halts m (ViewPost m ((absOf i.asset m).previewMint x.toNat)) := by
  simp only [absOf_previewMint]
  exact previewMint_halts m h hd

/-- **`previewWithdraw(uint256)` refines the model**, in any frame. -/
theorem previewWithdraw_refines {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m) {x : Word}
    (hd : WordCall m.frame.msg.data 0x0a28a477 x) :
    Halts m (ViewPost m ((absOf i.asset m).previewWithdraw x.toNat)) := by
  simp only [absOf_previewWithdraw]
  exact previewWithdraw_halts m h hd

/-- **`previewRedeem(uint256)` refines the model**, in any frame. -/
theorem previewRedeem_refines {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m) {x : Word}
    (hd : WordCall m.frame.msg.data 0x4cdad506 x) :
    Halts m (ViewPost m ((absOf i.asset m).previewRedeem x.toNat)) := by
  simp only [Solmate.State.previewRedeem, absOf_convertToAssets]
  exact previewRedeem_halts m h hd

/-- **`maxDeposit(address)` refines the model**, in any frame. -/
theorem maxDeposit_refines {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m) {a : Address}
    (hd : AddrCall m.frame.msg.data 0x402d267d a) :
    Halts m (ViewPost m (some ((absOf i.asset m).maxDeposit a))) := by
  simp only [Solmate.State.maxDeposit]
  exact maxDeposit_halts m h hd

/-- **`maxMint(address)` refines the model**, in any frame. -/
theorem maxMint_refines {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m) {a : Address}
    (hd : AddrCall m.frame.msg.data 0xc63d75b6 a) :
    Halts m (ViewPost m (some ((absOf i.asset m).maxMint a))) := by
  simp only [Solmate.State.maxMint]
  exact maxMint_halts m h hd

/-- **`maxWithdraw(address)` refines the model**, in any frame. -/
theorem maxWithdraw_refines {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m) {a : Address}
    (hd : AddrCall m.frame.msg.data 0xce96cb77 a) :
    Halts m (ViewPost m ((absOf i.asset m).maxWithdraw a)) := by
  simp only [Solmate.State.maxWithdraw, absOf_sharesOf, absOf_convertToAssets]
  exact maxWithdraw_halts m h hd

/-- **`maxRedeem(address)` refines the model**, in any frame. -/
theorem maxRedeem_refines {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m) {a : Address}
    (hd : AddrCall m.frame.msg.data 0xd905777e a) :
    Halts m (ViewPost m (some ((absOf i.asset m).maxRedeem a))) := by
  simp only [Solmate.State.maxRedeem, absOf_sharesOf]
  exact maxRedeem_halts m h hd

/-- **`totalAssets()` refines the model**, in any frame. -/
theorem totalAssets_refines {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m) 
    (hd : NoArgCall m.frame.msg.data 0x01e1d114) :
    Halts m (ViewPost m (some (absOf i.asset m).totalAssets)) := by
  simp only [absOf_totalAssets]
  exact totalAssets_halts m h hd

/-- **`asset()`** returns the asset address, in any frame. -/
theorem asset_refines {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m) 
    (hd : NoArgCall m.frame.msg.data 0x38d52e0f) :
    Halts m (ViewPost m (some i.asset.toNat)) := by
  exact asset_halts m h hd

/-! ## Top-level transactions -/

/-- What a top-level view call returns: success with the ABI word of `v` for `some v`, a
revert for `none`. -/
def ViewResult (res : MessageResult) (r : Option ℕ) : Prop :=
  match r with
  | some v => res.success = true ∧ res.output = Bytes.ofWord (BitVec.ofNat 256 v)
  | none => res.success = false ∧ res.reverted = true

variable {ctx : Context} {w : World} {tr : TransientStorage} {vault asset caller : Address}
  {data : ByteArray} {gas : Nat} {wa : AddressSet} {wk : StorageKeySet}

/-- A view summary of the start machine of a top-level call to the vault gives the result of
`processMessageCall`: the world is unchanged and the result is `ViewResult`. -/
theorem view_call {i : SolmateVault.Immutables} {r : Option ℕ}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork vault = false)
    (h : Halts (startMachine ctx w tr
        (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk))
      (ViewPost (startMachine ctx w tr
        (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk)) r)) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res r := by
  have hdel : delegatedAddress?
      (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk).code = none :=
    Shares.delegatedAddress?_code i
  obtain ⟨n, hn⟩ := processMessageCall_of_halts (a := vault) hdeleg hdel rfl rfl hpre rfl rfl h
  refine ⟨n, fun fuel hle => ?_⟩
  obtain ⟨mf, o, ⟨hw, ho⟩, hs, hrun⟩ := hn fuel hle
  have hk : mf.frame.kind = .call 0 0 := hs.kind
  refine ⟨_, hrun, ?_⟩
  cases r with
  | some v =>
    simp only at ho
    subst ho
    obtain ⟨h1, h2, h3, -⟩ := topLevelResult_success_call (t := (callMsg
      (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk).target)
      (out := Bytes.ofWord (BitVec.ofNat 256 v)) hk
    exact ⟨h3.trans hw, h1, h2⟩
  | none =>
    simp only at ho
    subst ho
    have hsnap : mf.frame.snapshot.1 = w := by rw [hs.snapshot]; rfl
    simp only [frameResult_revert, topLevelResult_world, topLevelResult_success,
      topLevelResult_reverted, ViewResult, ChildResult.success, hsnap]
    decide

/-- The start of a top-level call to the vault (immutables `i`) satisfies `ViewPre`. -/
theorem viewPre_start {i : SolmateVault.Immutables}
    (hasset : ∃ ia, w.code i.asset = SolmateAsset.runtimeCodeWith ia)
    (hapre : ∀ fork, Precompile.isPrecompile fork i.asset = false) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) (hsize : data.size < 2 ^ 64) :
    ViewPre i (startMachine ctx w tr
      (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk)) where
  fresh := fresh_startMachine ctx w tr
    (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk)
  value := rfl
  assetCode := hasset
  assetNotPrecompile := hapre ctx.fork
  depth := by simp [startMachine, callMsg, Frame.init, Gas.stackDepthLimit]
  gas := hgas
  gasLt := hgas'
  sizeLt := hsize

/-- `absOf` at the start of a top-level call is `abs` of the world. -/
theorem absOf_start {code : ByteArray} :
    absOf asset (startMachine ctx w tr (callMsg code vault caller data gas wa wk)) =
      abs ctx.crypto w vault asset := rfl

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

/-- **`convertToShares(uint256)` as a top-level transaction** on the deployed vault. -/
theorem convertToShares_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) (x : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller (Abi.encodeCall 0xc6e6f592 [x]) gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res ((abs ctx.crypto w vault asset).convertToShares x.toNat) := by
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have h := convertToShares_refines _ (viewPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep.assetCode
    hdep.assetNotPrecompile hgas hgas' (by rw [Abi.size_encodeCall]; simp))
    (wordCall_encodeCall (by decide) x)
  rw [absOf_start] at h
  exact view_call hdeleg (hdep.vaultNotPrecompile _) h

/-- **`convertToAssets(uint256)` as a top-level transaction** on the deployed vault. -/
theorem convertToAssets_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) (x : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller (Abi.encodeCall 0x07a2d13a [x]) gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res ((abs ctx.crypto w vault asset).convertToAssets x.toNat) := by
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have h := convertToAssets_refines _ (viewPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep.assetCode
    hdep.assetNotPrecompile hgas hgas' (by rw [Abi.size_encodeCall]; simp))
    (wordCall_encodeCall (by decide) x)
  rw [absOf_start] at h
  exact view_call hdeleg (hdep.vaultNotPrecompile _) h

/-- **`previewDeposit(uint256)` as a top-level transaction** on the deployed vault. -/
theorem previewDeposit_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) (x : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller (Abi.encodeCall 0xef8b30f7 [x]) gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res ((abs ctx.crypto w vault asset).previewDeposit x.toNat) := by
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have h := previewDeposit_refines _ (viewPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep.assetCode
    hdep.assetNotPrecompile hgas hgas' (by rw [Abi.size_encodeCall]; simp))
    (wordCall_encodeCall (by decide) x)
  rw [absOf_start] at h
  exact view_call hdeleg (hdep.vaultNotPrecompile _) h

/-- **`previewMint(uint256)` as a top-level transaction** on the deployed vault. -/
theorem previewMint_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) (x : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller (Abi.encodeCall 0xb3d7f6b9 [x]) gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res ((abs ctx.crypto w vault asset).previewMint x.toNat) := by
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have h := previewMint_refines _ (viewPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep.assetCode
    hdep.assetNotPrecompile hgas hgas' (by rw [Abi.size_encodeCall]; simp))
    (wordCall_encodeCall (by decide) x)
  rw [absOf_start] at h
  exact view_call hdeleg (hdep.vaultNotPrecompile _) h

/-- **`previewWithdraw(uint256)` as a top-level transaction** on the deployed vault. -/
theorem previewWithdraw_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) (x : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller (Abi.encodeCall 0x0a28a477 [x]) gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res ((abs ctx.crypto w vault asset).previewWithdraw x.toNat) := by
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have h := previewWithdraw_refines _ (viewPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep.assetCode
    hdep.assetNotPrecompile hgas hgas' (by rw [Abi.size_encodeCall]; simp))
    (wordCall_encodeCall (by decide) x)
  rw [absOf_start] at h
  exact view_call hdeleg (hdep.vaultNotPrecompile _) h

/-- **`previewRedeem(uint256)` as a top-level transaction** on the deployed vault. -/
theorem previewRedeem_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) (x : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller (Abi.encodeCall 0x4cdad506 [x]) gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res ((abs ctx.crypto w vault asset).previewRedeem x.toNat) := by
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have h := previewRedeem_refines _ (viewPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep.assetCode
    hdep.assetNotPrecompile hgas hgas' (by rw [Abi.size_encodeCall]; simp))
    (wordCall_encodeCall (by decide) x)
  rw [absOf_start] at h
  exact view_call hdeleg (hdep.vaultNotPrecompile _) h

/-- **`maxDeposit(address)` as a top-level transaction** on the deployed vault. -/
theorem maxDeposit_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) (a : Address) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller (Abi.encodeCall 0x402d267d [Word.ofAddress a]) gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res (some ((abs ctx.crypto w vault asset).maxDeposit a)) := by
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have h := maxDeposit_refines _ (viewPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep.assetCode
    hdep.assetNotPrecompile hgas hgas' (by rw [Abi.size_encodeCall]; simp))
    (addrCall_encodeCall (by decide) a)
  rw [absOf_start] at h
  exact view_call hdeleg (hdep.vaultNotPrecompile _) h

/-- **`maxMint(address)` as a top-level transaction** on the deployed vault. -/
theorem maxMint_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) (a : Address) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller (Abi.encodeCall 0xc63d75b6 [Word.ofAddress a]) gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res (some ((abs ctx.crypto w vault asset).maxMint a)) := by
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have h := maxMint_refines _ (viewPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep.assetCode
    hdep.assetNotPrecompile hgas hgas' (by rw [Abi.size_encodeCall]; simp))
    (addrCall_encodeCall (by decide) a)
  rw [absOf_start] at h
  exact view_call hdeleg (hdep.vaultNotPrecompile _) h

/-- **`maxWithdraw(address)` as a top-level transaction** on the deployed vault. -/
theorem maxWithdraw_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) (a : Address) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller (Abi.encodeCall 0xce96cb77 [Word.ofAddress a]) gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res ((abs ctx.crypto w vault asset).maxWithdraw a) := by
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have h := maxWithdraw_refines _ (viewPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep.assetCode
    hdep.assetNotPrecompile hgas hgas' (by rw [Abi.size_encodeCall]; simp))
    (addrCall_encodeCall (by decide) a)
  rw [absOf_start] at h
  exact view_call hdeleg (hdep.vaultNotPrecompile _) h

/-- **`maxRedeem(address)` as a top-level transaction** on the deployed vault. -/
theorem maxRedeem_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) (a : Address) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller (Abi.encodeCall 0xd905777e [Word.ofAddress a]) gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res (some ((abs ctx.crypto w vault asset).maxRedeem a)) := by
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have h := maxRedeem_refines _ (viewPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep.assetCode
    hdep.assetNotPrecompile hgas hgas' (by rw [Abi.size_encodeCall]; simp))
    (addrCall_encodeCall (by decide) a)
  rw [absOf_start] at h
  exact view_call hdeleg (hdep.vaultNotPrecompile _) h

/-- **`totalAssets()` as a top-level transaction** on the deployed vault. -/
theorem totalAssets_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller (Abi.encodeCall 0x01e1d114 []) gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res (some (abs ctx.crypto w vault asset).totalAssets) := by
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have h := totalAssets_refines _ (viewPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep.assetCode
    hdep.assetNotPrecompile hgas hgas' (by rw [Abi.size_encodeCall]; simp))
    (noArgCall_encodeCall (by decide))
  rw [absOf_start] at h
  exact view_call hdeleg (hdep.vaultNotPrecompile _) h

/-- **`asset()` as a top-level transaction** on the deployed vault. -/
theorem asset_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (hgas' : gas < 2 ^ 64) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller (Abi.encodeCall 0x38d52e0f []) gas wa wk) = .ok res ∧
      res.world = w ∧ ViewResult res (some asset.toNat) := by
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have h := asset_refines _ (viewPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep.assetCode
    hdep.assetNotPrecompile hgas hgas' (by rw [Abi.size_encodeCall]; simp))
    (noArgCall_encodeCall (by decide))
  exact view_call hdeleg (hdep.vaultNotPrecompile _) h

end EvmLeanSpecs.Refinement

end

section

/-!
## The remaining views of the vault and the asset, in any frame

Frame forms (fresh frame, any parents) of the getters not covered by `SharesFrameViews.lean`,
`VaultViews*.lean`, `AssetBalanceOf.lean`, `Strings*Spec.lean` and `Permit*DS.lean`:

* the vault's hook counters of `MockERC4626`: `beforeWithdrawHookCalledCounter()` (slot 6) and
  `afterDepositHookCalledCounter()` (slot 7): `vaultBeforeWithdrawCounter_halts`,
  `vaultAfterDepositCounter_halts`;
* the asset's `totalSupply()`, `allowance(owner, spender)` and `decimals()`:
  `assetTotalSupply_halts`, `assetAllowance_halts`, `assetDecimals_halts`.

Each returns the ABI word of the value read from storage (`decimals`: the immutable masked to
`uint8`) and leaves the world unchanged (`SharesViewPost`).
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

/-! ## The vault's hook counters -/

set_option maxHeartbeats 0 in
/-- **`beforeWithdrawHookCalledCounter()` of the vault** (slot 6), in any frame. -/
theorem vaultBeforeWithdrawCounter_halts {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hd : NoArgCall m.frame.msg.data 0xbc368a8a) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (SharesViewPost (m.world.sload m.frame.msg.currentTarget 6#256) m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Solidity.eq_self, Memory.read_64]
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 0 in
/-- **`afterDepositHookCalledCounter()` of the vault** (slot 7), in any frame. -/
theorem vaultAfterDepositCounter_halts {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hd : NoArgCall m.frame.msg.data 0xfc407ae7) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (SharesViewPost (m.world.sload m.frame.msg.currentTarget 7#256) m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Solidity.eq_self, Memory.read_64]
  exact ⟨rfl, rfl⟩

/-! ## The asset's views -/

/-- The asset's `decimals` immutable, as its `PUSH32` reads it. -/
theorem readBytes_assetCode_decimals (ia : SolmateAsset.Immutables) :
    readBytes (SolmateAsset.runtimeCodeWith ia) 345 32 = Bytes.ofWord ia.decimals := by
  have hp : ia.patches = [(1063, ia.initialChainId), (1116, ia.initialDomainSeparator)] ++
      (345, ia.decimals) :: [] := rfl
  simp only [SolmateAsset.runtimeCodeWith, hp]
  exact readBytes_patchWords_last _ _ _ _ _ (by rw [SolmateAsset.size_runtimeCode]; decide)
    (by simp)

set_option maxHeartbeats 0 in
/-- **`totalSupply()` of the asset**, in any frame. -/
theorem assetTotalSupply_halts {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hd : NoArgCall m.frame.msg.data 0x18160ddd) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (SharesViewPost (m.world.sload m.frame.msg.currentTarget 2#256) m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Solidity.eq_self, Memory.read_64]
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 0 in
/-- **`allowance(owner, spender)` of the asset**, in any frame. -/
theorem assetAllowance_halts {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    {owner spender : Address}
    (hd : TwoWordCall m.frame.msg.data 0xdd62ed3e (Word.ofAddress owner) (Word.ofAddress spender))
    (hsize' : m.frame.msg.data.size < 2 ^ 64) (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (SharesViewPost (m.world.sload m.frame.msg.currentTarget
      (Erc20.allowanceSlot m.ctx.crypto Erc20.Layout.solmate owner spender)) m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, Solidity.eq_self, Memory.read_64]
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 0 in
/-- **`decimals()` of the asset**, in any frame: the immutable as a `uint8`. -/
theorem assetDecimals_halts {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hd : NoArgCall m.frame.msg.data 0x313ce567) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (SharesViewPost (ia.decimals &&& 255#256) m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Solidity.eq_self, Memory.read_64,
    readBytes_assetCode_decimals]
  exact ⟨rfl, rfl⟩

end EvmLeanSpecs.Refinement

end
