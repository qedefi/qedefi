import Examples.OpenZeppelin.ERC20.CalleeSpec
import Examples.OpenZeppelin.ERC20.Transfer
import Examples.OpenZeppelin.ERC20.Approve
import Examples.OpenZeppelin.ERC20.TransferFrom
import Examples.OpenZeppelin.ERC20.MintBurn

/-!
# `OzAsset`'s events at the top level

The logs of a top-level call (`processMessageCall`) of `transfer`, `approve`, `transferFrom`,
`mint` and `burn`: exactly the event of the model's operation when it succeeds
(`Transfer(caller, dst, amount)`, `Approval(caller, spender, amount)`,
`Transfer(src, dst, amount)` with no `Approval` for the spent allowance, `Transfer(0, dst,
amount)`, `Transfer(src, 0, amount)`), and none when it fails. Each composes the callee
summary, whose success post fixes the frame's logs, with `processMessageCall_of_halts`.
-/

namespace Examples.OpenZeppelin.ERC20
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Solidity.ERC20
open EvmLean.Interpreter QEDefi.ERC4626 Examples.OpenZeppelin.Contracts
open Examples.Solmate.ERC20 (TwoWordCall ThreeWordCall Reverts)

/-! ## Glue -/

/-- How a top-level call ends with respect to logs: success with the logs `L`, or a revert
while `L = #[]`; never an exceptional halt. -/
def LogsPost (L : Array Log) (mf : Machine) (o : Outcome) : Prop :=
  match o with
  | .success _ => mf.frame.sub.logs = L
  | .revert _ => L = #[]
  | .halt _ => False

variable {ctx : Context} {w : World} {tr : TransientStorage} {token caller : Address}
  {gas : Nat} {warmAddrs : AddressSet} {warmKeys : StorageKeySet}

/-- A frame summary `LogsPost L` of a top-level call to the token gives the logs of
`processMessageCall`, for all large enough fuel. -/
theorem logs_call (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) {data : ByteArray} {L : Array Log}
    (h : Halts (startMachine ctx w tr
      (callMsg OzAsset.runtimeCode token caller data gas warmAddrs warmKeys)) (LogsPost L)) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ r, processMessageCall fuel ctx w tr
        (callMsg OzAsset.runtimeCode token caller data gas warmAddrs warmKeys) = .ok r ∧
      r.logs = L := by
  obtain ⟨n, hn⟩ := processMessageCall_of_halts (a := token)
    (msg := callMsg OzAsset.runtimeCode token caller data gas warmAddrs warmKeys) hdeleg
    delegatedAddress?_runtimeCode rfl rfl hpre rfl rfl h
  refine ⟨n, fun fuel hle => ?_⟩
  obtain ⟨mf, o, hH, hs, hrun⟩ := hn fuel hle
  refine ⟨_, hrun, ?_⟩
  have hk : mf.frame.kind = .call 0 0 := hs.kind
  unfold LogsPost at hH
  split at hH
  · rw [topLevelResult_logs_success hk, hH]
  · subst hH; rfl
  · exact hH.elim

theorem twoWordCall_of_encodeCall {sel : Nat} (hsel : sel < 2 ^ 32) (x y : Word) :
    TwoWordCall (Abi.encodeCall sel [x, y]) sel x y :=
  ⟨by rw [Abi.selectorOf_encodeCall, Nat.mod_eq_of_lt hsel],
   by rw [Abi.size_encodeCall]; simp, Abi.calldataload_encodeCall_0 _ _ _,
   Abi.calldataload_encodeCall_1 _ _ _ _⟩

theorem threeWordCall_of_encodeCall {sel : Nat} (hsel : sel < 2 ^ 32) (x y z : Word) :
    ThreeWordCall (Abi.encodeCall sel [x, y, z]) sel x y z :=
  ⟨by rw [Abi.selectorOf_encodeCall, Nat.mod_eq_of_lt hsel],
   by rw [Abi.size_encodeCall]; simp, Abi.calldataload_encodeCall_0 _ _ _,
   Abi.calldataload_encodeCall_1 _ _ _ _, Abi.calldataload_encodeCall_2 _ _ _ _ _⟩

theorem push_empty_logs {L : Array Log} {mf : Machine} {e : Log}
    (h : mf.frame.sub.logs = L.push e) (hL : L = #[]) : mf.frame.sub.logs = #[e] := by
  rw [h, hL]; rfl

/-! ## The events -/

/-- **`transfer(dst, amount)` logs `Transfer(caller, dst, amount)`** when `Model.ozTransfer`
succeeds, and nothing otherwise. -/
theorem transfer_logs (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 60000 ≤ gas)
    (dst : Address) (amount : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ r, processMessageCall fuel ctx w tr
        (transferCall token caller dst amount gas warmAddrs warmKeys) = .ok r ∧
      r.logs = if (Model.ozTransfer (view ctx.crypto Layout.oz w token) caller dst amount).isSome
        then #[transferLog token caller dst amount] else #[] := by
  refine logs_call hdeleg hpre ?_
  have hf := fresh_startMachine ctx w tr
    (callMsg OzAsset.runtimeCode token caller (transferCalldata dst amount) gas warmAddrs warmKeys)
  have hd := twoWordCall_of_encodeCall (sel := 0xa9059cbb) (by decide) (Word.ofAddress dst) amount
  have hsz : (transferCalldata dst amount).size < 2 ^ 64 := by
    rw [size_transferCalldata]; decide
  cases hm : Model.ozTransfer (view ctx.crypto Layout.oz w token) caller dst amount with
  | some s' =>
    have hm' := hm
    unfold Model.ozTransfer at hm'
    split at hm'
    · cases hm'
    rename_i hc0
    split at hm'
    · cases hm'
    rename_i hd0
    have hbal : amount.toNat ≤ ((view ctx.crypto Layout.oz w token).balanceOf caller).toNat := by
      unfold Model.transfer at hm'
      split at hm'
      · assumption
      · cases hm'
    refine (transfer_halts_ok _ hf rfl rfl hd hsz hgas hc0 hd0 hbal).mono
      fun mf o _ hok => ?_
    rw [hok.1]
    exact push_empty_logs hok.2.2.2.2.1 rfl
  | none =>
    refine (transfer_halts_revert _ hf rfl hd hsz (show 10000 ≤ gas by omega) hm).mono fun mf o _ hrev => ?_
    obtain ⟨out, rfl⟩ := hrev.1
    rfl

/-- **`approve(spender, amount)` logs `Approval(caller, spender, amount)`** when
`Model.ozApprove` succeeds, and nothing otherwise. -/
theorem approve_logs (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 40000 ≤ gas)
    (spender : Address) (amount : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ r, processMessageCall fuel ctx w tr
        (approveCall token caller spender amount gas warmAddrs warmKeys) = .ok r ∧
      r.logs =
        if (Model.ozApprove (view ctx.crypto Layout.oz w token) caller spender amount).isSome
        then #[approvalLog token caller spender amount] else #[] := by
  refine logs_call hdeleg hpre ?_
  have hf := fresh_startMachine ctx w tr (callMsg OzAsset.runtimeCode token caller
    (approveCalldata spender amount) gas warmAddrs warmKeys)
  have hd := twoWordCall_of_encodeCall (sel := 0x095ea7b3) (by decide) (Word.ofAddress spender)
    amount
  have hsz : (approveCalldata spender amount).size < 2 ^ 64 := by
    rw [size_approveCalldata]; decide
  cases hm : Model.ozApprove (view ctx.crypto Layout.oz w token) caller spender amount with
  | some s' =>
    have hm' := hm
    unfold Model.ozApprove at hm'
    split at hm'
    · cases hm'
    rename_i hc0
    split at hm'
    · cases hm'
    rename_i hs0
    refine (approve_halts_ok _ hf rfl rfl hd hsz hgas hc0 hs0).mono fun mf o _ hok => ?_
    rw [hok.1]
    exact push_empty_logs hok.2.2.2.2.1 rfl
  | none =>
    refine (approve_halts_revert _ hf rfl hd hsz (show 10000 ≤ gas by omega) hm).mono
      fun mf o _ hrev => ?_
    obtain ⟨out, rfl⟩ := hrev.1
    rfl

/-- **`transferFrom(src, dst, amount)` logs only `Transfer(src, dst, amount)`** when
`Model.ozTransferFrom` succeeds (no `Approval` for the spent allowance), and nothing otherwise
(`AllowanceSlotOk`: the balance is read after the allowance write). -/
theorem transferFrom_logs (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 90000 ≤ gas)
    {src : Address} (ha : AllowanceSlotOk ctx.crypto Layout.oz src caller)
    (dst : Address) (amount : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ r, processMessageCall fuel ctx w tr
        (transferFromCall token caller src dst amount gas warmAddrs warmKeys) = .ok r ∧
      r.logs =
        if (Model.ozTransferFrom (view ctx.crypto Layout.oz w token) caller src dst amount).isSome
        then #[transferLog token src dst amount] else #[] := by
  refine logs_call hdeleg hpre ?_
  have hf := fresh_startMachine ctx w tr (callMsg OzAsset.runtimeCode token caller
    (transferFromCalldata src dst amount) gas warmAddrs warmKeys)
  have hd := threeWordCall_of_encodeCall (sel := 0x23b872dd) (by decide) (Word.ofAddress src)
    (Word.ofAddress dst) amount
  have hsz : (transferFromCalldata src dst amount).size < 2 ^ 64 := by
    rw [size_transferFromCalldata]; decide
  have hc := transferFromCond_iff (startMachine ctx w tr (callMsg OzAsset.runtimeCode token caller
    (transferFromCalldata src dst amount) gas warmAddrs warmKeys)) src dst amount ha
  cases hm : Model.ozTransferFrom (view ctx.crypto Layout.oz w token) caller src dst amount with
  | some s' =>
    refine (transferFrom_halts_ok _ hf rfl rfl hd hsz hgas
      (hc.2 (by simp only [assetView, startMachine, Frame.init, callMsg, hm,
        Option.isSome_some]))).mono fun mf o _ hok => ?_
    rw [hok.1]
    exact push_empty_logs hok.2.2.2.2.1 rfl
  | none =>
    refine (transferFrom_halts_revert _ hf rfl rfl hd hsz hgas fun h => ?_).mono
      fun mf o _ hrev => ?_
    · have := hc.1 h
      simp only [assetView, startMachine, Frame.init, callMsg, hm, Option.isSome_none,
        Bool.false_eq_true] at this
    · obtain ⟨out, rfl⟩ := hrev.1
      rfl

/-- **`mint(dst, amount)` logs `Transfer(0, dst, amount)`** when `Model.ozMint` succeeds, and
nothing otherwise. -/
theorem mint_logs (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 60000 ≤ gas)
    (dst : Address) (amount : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ r, processMessageCall fuel ctx w tr
        (mintCall token caller dst amount gas warmAddrs warmKeys) = .ok r ∧
      r.logs = if (Model.ozMint (view ctx.crypto Layout.oz w token) dst amount).isSome
        then #[transferLog token 0 dst amount] else #[] := by
  refine logs_call hdeleg hpre ?_
  have hf := fresh_startMachine ctx w tr
    (callMsg OzAsset.runtimeCode token caller (mintCalldata dst amount) gas warmAddrs warmKeys)
  have hd := twoWordCall_of_encodeCall (sel := 0x40c10f19) (by decide) (Word.ofAddress dst) amount
  have hsz : (mintCalldata dst amount).size < 2 ^ 64 := by
    rw [size_mintCalldata]; decide
  cases hm : Model.ozMint (view ctx.crypto Layout.oz w token) dst amount with
  | some s' =>
    have hm' := hm
    unfold Model.ozMint at hm'
    split at hm'
    · cases hm'
    rename_i hd0
    split at hm'
    · rename_i hov
      refine (mint_halts_ok _ hf rfl rfl hd hsz hgas hd0 hov).mono fun mf o _ hok => ?_
      rw [hok.1]
      exact push_empty_logs hok.2.2.2.2.1 rfl
    · cases hm'
  | none =>
    refine (mint_halts_revert _ hf rfl hd hsz (show 10000 ≤ gas by omega) hm).mono
      fun mf o _ hrev => ?_
    obtain ⟨out, rfl⟩ := hrev.1
    rfl

/-- **`burn(src, amount)` logs `Transfer(src, 0, amount)`** when `Model.ozBurn` succeeds, and
nothing otherwise. -/
theorem burn_logs (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 60000 ≤ gas)
    (src : Address) (amount : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ r, processMessageCall fuel ctx w tr
        (burnCall token caller src amount gas warmAddrs warmKeys) = .ok r ∧
      r.logs = if (Model.ozBurn (view ctx.crypto Layout.oz w token) src amount).isSome
        then #[transferLog token src 0 amount] else #[] := by
  refine logs_call hdeleg hpre ?_
  have hf := fresh_startMachine ctx w tr
    (callMsg OzAsset.runtimeCode token caller (burnCalldata src amount) gas warmAddrs warmKeys)
  have hd := twoWordCall_of_encodeCall (sel := 0x9dc29fac) (by decide) (Word.ofAddress src) amount
  have hsz : (burnCalldata src amount).size < 2 ^ 64 := by
    rw [size_burnCalldata]; decide
  cases hm : Model.ozBurn (view ctx.crypto Layout.oz w token) src amount with
  | some s' =>
    have hm' := hm
    unfold Model.ozBurn at hm'
    split at hm'
    · cases hm'
    rename_i hs0
    split at hm'
    · rename_i hv
      refine (burn_halts_ok _ hf rfl rfl hd hsz hgas hs0 hv).mono fun mf o _ hok => ?_
      rw [hok.1]
      exact push_empty_logs hok.2.2.2.2.1 rfl
    · cases hm'
  | none =>
    refine (burn_halts_revert _ hf rfl hd hsz (show 10000 ≤ gas by omega) hm).mono
      fun mf o _ hrev => ?_
    obtain ⟨out, rfl⟩ := hrev.1
    rfl

end Examples.OpenZeppelin.ERC20
