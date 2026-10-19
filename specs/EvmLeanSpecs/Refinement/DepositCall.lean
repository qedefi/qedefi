import EvmLeanSpecs.Refinement.Mint
import EvmLeanSpecs.Refinement.WithdrawRefines

/-!
# `deposit` and `mint` as top-level transactions

`deposit_call`, `mint_call`: a top-level call (`processMessageCall`, any `Crypto`, any context
before Prague or without EIP-7702 authorizations, any transient storage and warm sets, enough
fuel) of `deposit(assets, receiver)` / `mint(shares, receiver)` on the vault `Deployed` at
`vault` (any immutables) over the asset at `asset`, with `Abi.encodeCall` calldata, refines the
model operation on `abs ctx.crypto w vault asset` (`EntryResult`):

* model `some (s', v)`: the call succeeds, returns the ABI word of `v` (shares minted /
  assets pulled), the world is `depositWorld` (exact), and it represents `s'`
  (`Out.RefinesOn`);
* model `none`: the call reverts and the world is unchanged.

They are `deposit_refines` / `mint_refines` (frame form) at the start machine, through
`entry_call` (as `view_call` and `out_call` do for the views and withdraw/redeem).
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open Vault Shares

/-- What a top-level `deposit` / `mint` returns, against the model's result `r`: on
`some (s', v)` success with the ABI word of `v`, the world `W v`, representing `s'`; on `none`
a revert with the world unchanged. -/
def EntryResult (crypto : Crypto) (w : World) (vault asset : Address)
    (P Q : Address → Address → Prop) (W : ℕ → World) (res : MessageResult)
    (r : Option (Solmate.State Address × ℕ)) : Prop :=
  match r with
  | some (s', v) => res.success = true ∧ res.output = Bytes.ofWord (BitVec.ofNat 256 v) ∧
      res.world = W v ∧ Out.RefinesOn P Q crypto res.world vault asset s'
  | none => res.success = false ∧ res.reverted = true ∧ res.world = w

variable {ctx : Context} {w : World} {tr : TransientStorage} {vault asset caller : Address}
  {data : ByteArray} {gas : Nat} {wa : AddressSet} {wk : StorageKeySet}

set_option maxHeartbeats 1000000 in
/-- A frame summary of a top-level call to the vault, in the form `EntryPost`, gives the
result of `processMessageCall`. -/
theorem entry_call {i : SolmateVault.Immutables} {P Q : Address → Address → Prop}
    {W : ℕ → World} {r : Option (Solmate.State Address × ℕ)}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork vault = false)
    (h : Halts (startMachine ctx w tr
        (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk))
      (EntryPost (startMachine ctx w tr
        (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk)) asset P Q W r)) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk) = .ok res ∧
      EntryResult ctx.crypto w vault asset P Q W res r := by
  have hdel : delegatedAddress?
      (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk).code = none :=
    Shares.delegatedAddress?_code i
  obtain ⟨n, hn⟩ := processMessageCall_of_halts (a := vault) hdeleg hdel rfl rfl hpre rfl rfl h
  refine ⟨n, fun fuel hle => ?_⟩
  obtain ⟨mf, o, hH, hs, hrun⟩ := hn fuel hle
  have hk : mf.frame.kind = .call 0 0 := hs.kind
  refine ⟨_, hrun, ?_⟩
  unfold EntryPost at hH
  unfold EntryResult
  split at hH
  · obtain ⟨ho, hW, hR⟩ := hH
    subst ho
    obtain ⟨h1, h2, h3, -⟩ := topLevelResult_success_call (t := (callMsg
      (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk).target)
      (out := Bytes.ofWord _) hk
    exact ⟨h1, h2, h3.trans hW, h3 ▸ hR⟩
  · obtain ⟨out, ho⟩ := hH
    subst ho
    have hsnap : mf.frame.snapshot.1 = w := by rw [hs.snapshot]; rfl
    simp only [frameResult_revert, topLevelResult_world, topLevelResult_success,
      topLevelResult_reverted, ChildResult.success, hsnap]
    decide

/-- `Abi.encodeCall sel [x, y]` is a `TwoWordCall`. -/
theorem twoWordCall_encodeCall' {sel : Nat} (hsel : sel < 2 ^ 32) (x y : Word) :
    TwoWordCall (Abi.encodeCall sel [x, y]) sel x y :=
  ⟨by rw [Abi.selectorOf_encodeCall, Nat.mod_eq_of_lt hsel],
   by rw [Abi.size_encodeCall]; simp, Abi.calldataload_encodeCall_0 _ _ _,
   Abi.calldataload_encodeCall_1 _ _ _ _⟩

/-- **`deposit(assets, receiver)` as a top-level transaction** on the deployed vault: refines
`Solmate.deposit` of the model state read from the world. -/
theorem deposit_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 250000 ≤ gas)
    (hgas' : gas < 2 ^ 64) {receiver : Address}
    (hk : KeccakAvoids ctx.crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hbc : Erc20.BalanceSlotOk ctx.crypto Erc20.Layout.solmate caller)
    (hbv : Erc20.BalanceSlotOk ctx.crypto Erc20.Layout.solmate vault)
    (hbr : Erc20.BalanceSlotOk ctx.crypto Erc20.Layout.solmate receiver)
    (ha : Erc20.AllowanceSlotOk ctx.crypto Erc20.Layout.solmate caller vault)
    (hinv : Solmate.Inv (abs ctx.crypto w vault asset)) (assets : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller
          (Abi.encodeCall 0x6e553f65 [assets, Word.ofAddress receiver]) gas wa wk) = .ok res ∧
      EntryResult ctx.crypto w vault asset (DepositAllowances ctx.crypto receiver)
        (TransferFromAllowances ctx.crypto vault caller vault)
        (fun v => depositWorld ctx.crypto w vault asset caller receiver assets
          (BitVec.ofNat 256 v)) res
        (Solmate.deposit (abs ctx.crypto w vault asset) caller assets.toNat receiver) := by
  have hne := hdep.asset_ne
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have hm := deposit_refines _ (viewPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep.assetCode
    hdep.assetNotPrecompile (by omega) hgas' (by rw [Abi.size_encodeCall]; simp))
    rfl hgas (twoWordCall_encodeCall' (by decide) assets _) hne.symm hk hbc hbv hbr ha hinv
  exact entry_call hdeleg (hdep.vaultNotPrecompile _) hm

/-- **`mint(shares, receiver)` as a top-level transaction** on the deployed vault: refines
`Solmate.mint` of the model state read from the world. -/
theorem mint_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 250000 ≤ gas)
    (hgas' : gas < 2 ^ 64) {receiver : Address}
    (hk : KeccakAvoids ctx.crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hbc : Erc20.BalanceSlotOk ctx.crypto Erc20.Layout.solmate caller)
    (hbv : Erc20.BalanceSlotOk ctx.crypto Erc20.Layout.solmate vault)
    (hbr : Erc20.BalanceSlotOk ctx.crypto Erc20.Layout.solmate receiver)
    (ha : Erc20.AllowanceSlotOk ctx.crypto Erc20.Layout.solmate caller vault)
    (hinv : Solmate.Inv (abs ctx.crypto w vault asset)) (shares : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller
          (Abi.encodeCall 0x94bf804d [shares, Word.ofAddress receiver]) gas wa wk) = .ok res ∧
      EntryResult ctx.crypto w vault asset (DepositAllowances ctx.crypto receiver)
        (TransferFromAllowances ctx.crypto vault caller vault)
        (fun v => depositWorld ctx.crypto w vault asset caller receiver (BitVec.ofNat 256 v)
          shares) res
        (Solmate.mint (abs ctx.crypto w vault asset) caller shares.toNat receiver) := by
  have hne := hdep.asset_ne
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have hm := mint_refines _ (viewPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep.assetCode
    hdep.assetNotPrecompile (by omega) hgas' (by rw [Abi.size_encodeCall]; simp))
    rfl hgas (twoWordCall_encodeCall' (by decide) shares _) hne.symm hk hbc hbv hbr ha hinv
  exact entry_call hdeleg (hdep.vaultNotPrecompile _) hm

end EvmLeanSpecs.Refinement
