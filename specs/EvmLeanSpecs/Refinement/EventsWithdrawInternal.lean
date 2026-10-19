import EvmLeanSpecs.Refinement.WithdrawSpend
import EvmLeanSpecs.Refinement.EventsAssetTransfer
import EvmLeanSpecs.Refinement.EventsTactic

/-!
# Logs of `withdraw` / `redeem`'s internal functions

Companions of `bump_wp`, `burn_wp` (`WithdrawCode.lean`), `withdrawSpend_wp`,
`redeemSpend_wp` (`WithdrawSpend.lean`) and `safeTransfer_wp` (`AssetCallOut.lean`) that also
determine the logs of the substate each returns with: the hook and the allowance steps emit
nothing (no `Approval` on spending), `_burn` appends the vault's `Transfer(from, 0, amount)`,
and `safeTransfer` appends the asset's `Transfer(vault, to, amount)` (the callee's log, merged
on return).
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Refinement.Out
open EvmLean.Solidity.Examples.SolmateAssetTransfer (transferWorld)

/-- `OutPost` with the frame's final logs: on `some (w', v)` the call returns the ABI word `v`
with the world `w'` and the frame's logs `L v`; on `none` it reverts. -/
def OutPostLogs (L : Word → Array Log) (r : Option (World × Word)) (mf : Machine) (o : Outcome) :
    Prop :=
  match r with
  | some (w', v) => o = .success (Bytes.ofWord v) ∧ mf.world = w' ∧ mf.frame.sub.logs = L v
  | none => ∃ out, o = .revert out

set_option maxHeartbeats 0 in
/-- **Without logs** (`bump_wp`, and the frame's logs are unchanged): **`beforeWithdraw` (internal, entry `0x104b`, stack `a :: b :: r :: rest`)**:
`beforeWithdrawHookCalledCounter++` (checked) — returns to `r` with `bumpStep` applied, or
panics. -/
theorem bump_wp_logs {i : SolmateVault.Immutables} (m : Machine) {a b r : Word} {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hpc : m.frame.pc = 0x104b) (hs : m.frame.stack = a :: b :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hstatic : m.frame.msg.isStatic = false) (hmem : FmpOk m.frame.memory)
    (hg : 30000 ≤ m.frame.gasLeft) :
    WP m (fun m' => ∃ w', bumpStep m.world m.frame.msg.currentTarget = some w' ∧ ∃ g sub,
        m' = resumeWorld m r.toNat rest m.frame.memory g m.frame.returnData sub w' ∧
        m.frame.gasLeft ≤ g + 25000 ∧ g ≤ m.frame.gasLeft ∧ sub.logs = m.frame.sub.logs)
      (fun _ o => bumpStep m.world m.frame.msg.currentTarget = none ∧ ∃ out, o = .revert out) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  by_cases hmax : m_world.sload m_msg.currentTarget 6#256 = MAXW
  · have hz : m_world.sload m_msg.currentTarget 6#256 + 1#256 = 0#256 := by rw [hmax]; decide
    rcases hmem with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
    all_goals
      pwp_steps [hsize, hz]
      exact ⟨by simp [bumpStep, hmax], _, rfl⟩
  · have hnz : m_world.sload m_msg.currentTarget 6#256 + 1#256 ≠ 0#256 := by
      intro h; apply hmax
      have := congrArg (· - 1#256) h
      simpa [MAXW] using this
    have hnz' : m_world.sload m_msg.currentTarget 6#256 + 1#256 ≠ 0 := hnz
    pwp_steps
    apply WP.ret
    exact ⟨_, by simp [bumpStep, hmax], _, _, rfl, by evm_gas, by evm_gas, by rfl⟩

set_option maxHeartbeats 0 in
/-- **With its log** (`burn_wp`, and the frame's logs gain `Transfer(from, 0, amount)`):
**`_burn(from, amount)` (internal, entry `0x105a`, stack `amount :: from :: r :: rest`)**:
returns to `r` with `burnStep` applied (and a `Transfer` log), or panics when the balance does
not cover `amount`. -/
theorem burn_wp_logs {i : SolmateVault.Immutables} (m : Machine) {amount r : Word} {src : Address}
    {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hpc : m.frame.pc = 0x105a) (hs : m.frame.stack = amount :: Word.ofAddress src :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hstatic : m.frame.msg.isStatic = false) (hmem : FmpOk m.frame.memory)
    (hg : 60000 ≤ m.frame.gasLeft) :
    WP m (fun m' => ∃ w', burnStep m.ctx.crypto m.world m.frame.msg.currentTarget src amount =
          some w' ∧ ∃ mem g rd sub,
        m' = resumeWorld m r.toNat rest mem g rd sub w' ∧ FmpBurnt mem ∧
        m.frame.gasLeft ≤ g + 55000 ∧ g ≤ m.frame.gasLeft ∧
        sub.logs = m.frame.sub.logs.push (transferLog m.frame.msg.currentTarget src 0 amount))
      (fun _ o => burnStep m.ctx.crypto m.world m.frame.msg.currentTarget src amount = none ∧
        ∃ out, o = .revert out) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  simp only [burnStep, balanceSlot_solmate]
  by_cases hbal : amount.toNat ≤ (m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 3#256))).toNat
  · rcases hmem with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
    all_goals
      pwp_steps [hsize, hfmp, ofAddress_and_addressMask, addressMask_and_ofAddress,
        Memory.read_64]
      simp only [gt_sub_self_of_le hbal, iszero_zero]
      pwp_steps [hsize, hfmp, ofAddress_and_addressMask, addressMask_and_ofAddress,
        Memory.read_64]
      pwp_codecopy
      pwp_steps [hsize, hfmp, ofAddress_and_addressMask, addressMask_and_ofAddress,
        Memory.read_64]
      apply WP.ret
      refine ⟨_, by simp only [Nat.not_lt.2 hbal, ↓reduceIte], _, _, _, _, rfl, ?_, by evm_gas,
        by evm_gas, ?_⟩
      first
        | refine .inl ⟨?_, ?_⟩
          · simp only [Memory.loadWord_expand,
              Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
              Memory.loadWord_storeWord_of_disjoint _ 32 64 _ (by decide),
              Memory.loadWord_storeWord_of_disjoint _ 128 64 _ (by decide), hfmp]
          · simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words,
              hsize]
            decide
        | refine .inr ⟨?_, ?_⟩
          · simp only [Memory.loadWord_expand,
              Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
              Memory.loadWord_storeWord_of_disjoint _ 32 64 _ (by decide),
              Memory.loadWord_storeWord_of_disjoint _ 160 64 _ (by decide), hfmp]
          · simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words,
              hsize]
            decide
      event_log [amount]
  · rw [Nat.not_le] at hbal
    rcases hmem with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
    all_goals
      pwp_steps [hsize, hfmp, ofAddress_and_addressMask, addressMask_and_ofAddress,
        Memory.read_64]
      simp only [gt_sub_self_of_lt hbal, iszero_one]
      pwp_steps [hsize, hfmp]
      exact ⟨by simp only [hbal, ↓reduceIte], _, rfl⟩

set_option maxHeartbeats 0 in
/-- **Without logs** (the summary of the same name without `_logs`, and the frame's logs are
unchanged: Solmate emits no `Approval` when it spends an allowance): **The allowance step of `withdraw`** (pc `0x0993`, stack `v :: x :: owner :: rest`, `v` the
shares of `previewWithdraw`): continues at `0x0a00` with stack `v :: owner :: rest` and the world
of `spendStep`, or panics. -/
theorem withdrawSpend_wp_logs {i : SolmateVault.Immutables} (m : Machine) {v x : Word}
    {owner : Address} {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hpc : m.frame.pc = 0x993) (hs : m.frame.stack = v :: x :: Word.ofAddress owner :: rest)
    (hlen : rest.length ≤ 1000) (hstatic : m.frame.msg.isStatic = false)
    (hmem : FmpOk m.frame.memory) (hg : 30000 ≤ m.frame.gasLeft) :
    WP m (fun m' => ∃ w₁, spendStep m.ctx.crypto m.world m.frame.msg.currentTarget owner
          m.frame.msg.caller v = some w₁ ∧ ∃ mem g sub,
        m' = resumeWorld m 0xa00 (v :: Word.ofAddress owner :: rest) mem g m.frame.returnData sub
          w₁ ∧
        mem.loadWord 64 = m.frame.memory.loadWord 64 ∧ mem.size = m.frame.memory.size ∧
        m.frame.gasLeft ≤ g + 26000 ∧ g ≤ m.frame.gasLeft ∧ sub.logs = m.frame.sub.logs)
      (fun _ o => spendStep m.ctx.crypto m.world m.frame.msg.currentTarget owner
          m.frame.msg.caller v = none ∧ ∃ out, o = .revert out) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  by_cases hco : m_msg.caller = owner
  · subst hco
    pwp_run_to 0xa00 [ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self]
    apply WP.ret
    exact ⟨_, by simp [spendStep], _, _, _, rfl, rfl, rfl, by evm_gas, by evm_gas, by rfl⟩
  · have hne1 := eq_ofAddress_of_ne hco
    have hne2 := eq_ofAddress_of_ne (Ne.symm hco)
    have hsp : spendStep m_ctx.crypto m_world m_msg.currentTarget owner m_msg.caller v =
        let a := m_world.sload m_msg.currentTarget
          (Erc20.allowanceSlot m_ctx.crypto Erc20.Layout.solmate owner m_msg.caller)
        if a ≠ Erc20.maxWord ∧ a.toNat < v.toNat then none
        else some (Erc20.spendWorld m_ctx.crypto m_world m_msg.currentTarget owner m_msg.caller v) := by
      simp only [spendStep, hco, ↓reduceIte]
    rw [hsp]
    simp only [Erc20.spendWorld, allowanceSlot_solmate, maxWord_eq_MAXW]
    rcases hmem with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
    all_goals
      pwp_steps [hsize, ofAddress_and_addressMask, addressMask_and_ofAddress, hne1, hne2,
        Memory.read_64]
      by_cases hmax : m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
          (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord (m_ctx.crypto.keccak256
            (Bytes.ofWord (Word.ofAddress owner) ++ Bytes.ofWord 4#256)))) = MAXW
      · simp only [hmax, Solidity.eq_self]
        pwp_run_to 0xa00 [hsize]
        apply WP.ret
        refine ⟨_, by simp, _, _, _, rfl, ?_, ?_, by evm_gas, by evm_gas, by rfl⟩
        · simp only [Memory.loadWord_expand,
            Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 32 64 _ (by decide)]
        · simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words,
            hsize]
          decide
      · simp only [eq_of_ne hmax, hmax]
        pwp_steps [hsize]
        by_cases hle : v.toNat ≤ (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
            (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord (m_ctx.crypto.keccak256
              (Bytes.ofWord (Word.ofAddress owner) ++ Bytes.ofWord 4#256))))).toNat
        · simp only [gt_sub_self_of_le hle, iszero_zero]
          pwp_run_to 0xa00 [hsize, ofAddress_and_addressMask, addressMask_and_ofAddress,
            Memory.read_64]
          apply WP.ret
          refine ⟨_, by simp [Nat.not_lt.2 hle], _, _, _, rfl, ?_, ?_, by evm_gas, by evm_gas, by rfl⟩
          · simp only [Memory.loadWord_expand,
              Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
              Memory.loadWord_storeWord_of_disjoint _ 32 64 _ (by decide)]
          · simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter,
              Memory.words, hsize]
            decide
        · rw [Nat.not_le] at hle
          simp only [gt_sub_self_of_lt hle, iszero_one]
          pwp_steps [hsize]
          exact ⟨by simp [hmax, hle], _, rfl⟩

set_option maxHeartbeats 0 in
/-- **Without logs** (the summary of the same name without `_logs`, and the frame's logs are
unchanged: Solmate emits no `Approval` when it spends an allowance): **The allowance step of `redeem`** (pc `0x0a93`, stack `owner :: y :: v :: rest`, `v` the
`shares` argument): continues at `0x0aff` with stack `0 :: owner :: y :: v :: rest` and the
world of `spendStep`, or panics. -/
theorem redeemSpend_wp_logs {i : SolmateVault.Immutables} (m : Machine) {v y : Word}
    {owner : Address} {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hpc : m.frame.pc = 0xa93) (hs : m.frame.stack = Word.ofAddress owner :: y :: v :: rest)
    (hlen : rest.length ≤ 1000) (hstatic : m.frame.msg.isStatic = false)
    (hmem : FmpOk m.frame.memory) (hg : 30000 ≤ m.frame.gasLeft) :
    WP m (fun m' => ∃ w₁, spendStep m.ctx.crypto m.world m.frame.msg.currentTarget owner
          m.frame.msg.caller v = some w₁ ∧ ∃ mem g sub,
        m' = resumeWorld m 0xaff (0#256 :: Word.ofAddress owner :: y :: v :: rest) mem g
          m.frame.returnData sub w₁ ∧
        mem.loadWord 64 = m.frame.memory.loadWord 64 ∧ mem.size = m.frame.memory.size ∧
        m.frame.gasLeft ≤ g + 26000 ∧ g ≤ m.frame.gasLeft ∧ sub.logs = m.frame.sub.logs)
      (fun _ o => spendStep m.ctx.crypto m.world m.frame.msg.currentTarget owner
          m.frame.msg.caller v = none ∧ ∃ out, o = .revert out) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  by_cases hco : m_msg.caller = owner
  · subst hco
    pwp_run_to 0xaff [ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self]
    apply WP.ret
    exact ⟨_, by simp [spendStep], _, _, _, rfl, rfl, rfl, by evm_gas, by evm_gas, by rfl⟩
  · have hne1 := eq_ofAddress_of_ne hco
    have hne2 := eq_ofAddress_of_ne (Ne.symm hco)
    have hsp : spendStep m_ctx.crypto m_world m_msg.currentTarget owner m_msg.caller v =
        let a := m_world.sload m_msg.currentTarget
          (Erc20.allowanceSlot m_ctx.crypto Erc20.Layout.solmate owner m_msg.caller)
        if a ≠ Erc20.maxWord ∧ a.toNat < v.toNat then none
        else some (Erc20.spendWorld m_ctx.crypto m_world m_msg.currentTarget owner m_msg.caller v) := by
      simp only [spendStep, hco, ↓reduceIte]
    rw [hsp]
    simp only [Erc20.spendWorld, allowanceSlot_solmate, maxWord_eq_MAXW]
    rcases hmem with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
    all_goals
      pwp_steps [hsize, ofAddress_and_addressMask, addressMask_and_ofAddress, hne1, hne2,
        Memory.read_64]
      by_cases hmax : m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
          (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord (m_ctx.crypto.keccak256
            (Bytes.ofWord (Word.ofAddress owner) ++ Bytes.ofWord 4#256)))) = MAXW
      · simp only [hmax, Solidity.eq_self]
        pwp_run_to 0xaff [hsize]
        apply WP.ret
        refine ⟨_, by simp, _, _, _, rfl, ?_, ?_, by evm_gas, by evm_gas, by rfl⟩
        · simp only [Memory.loadWord_expand,
            Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 32 64 _ (by decide)]
        · simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words,
            hsize]
          decide
      · simp only [eq_of_ne hmax, hmax]
        pwp_steps [hsize]
        by_cases hle : v.toNat ≤ (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
            (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord (m_ctx.crypto.keccak256
              (Bytes.ofWord (Word.ofAddress owner) ++ Bytes.ofWord 4#256))))).toNat
        · simp only [gt_sub_self_of_le hle, iszero_zero]
          pwp_run_to 0xaff [hsize, ofAddress_and_addressMask, addressMask_and_ofAddress,
            Memory.read_64]
          apply WP.ret
          refine ⟨_, by simp [Nat.not_lt.2 hle], _, _, _, rfl, ?_, ?_, by evm_gas, by evm_gas, by rfl⟩
          · simp only [Memory.loadWord_expand,
              Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
              Memory.loadWord_storeWord_of_disjoint _ 32 64 _ (by decide)]
          · simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter,
              Memory.words, hsize]
            decide
        · rw [Nat.not_le] at hle
          simp only [gt_sub_self_of_lt hle, iszero_one]
          pwp_steps [hsize]
          exact ⟨by simp [hmax, hle], _, rfl⟩

set_option maxHeartbeats 0 in
/-- **With its log** (`safeTransfer_wp`, and on success the frame's logs gain the asset's
`Transfer(vault, to, amount)`, emitted in the child frame): **`safeTransfer(asset, to, amount)` (internal, entry `0x10b9`, stack
`amount :: to :: asset :: r :: rest`)**: when the vault's asset balance covers `amount`,
returns to `r` with the asset's `transfer` applied to the world; otherwise reverts. -/
theorem safeTransfer_wp_logs {i : SolmateVault.Immutables} (m : Machine) {amount r : Word}
    {rcv : Address} {rest : List Word} (hv : VaultFrame i m) (hpc : m.frame.pc = 0x10b9)
    (hs : m.frame.stack = amount :: Word.ofAddress rcv :: Word.ofAddress i.asset :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hstatic : m.frame.msg.isStatic = false) (hne : i.asset ≠ m.frame.msg.currentTarget)
    (hmem : FmpCall m.frame.memory)
    (hg : 70000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun m' => amount.toNat ≤ (assetsOf i.asset m).toNat ∧ ∃ mem g rd sub,
        m' = resumeWorld m r.toNat rest mem g rd sub
          (transferWorld m.ctx.crypto m.world i.asset m.frame.msg.currentTarget rcv amount) ∧
        mem.loadWord 64 = m.frame.memory.loadWord 64 ∧ mem.size = m.frame.memory.size + 32 ∧
        m.frame.gasLeft ≤ g + 60000 ∧
        sub.logs = m.frame.sub.logs.push (transferLog i.asset m.frame.msg.currentTarget rcv amount))
      (fun _ o => (assetsOf i.asset m).toNat < amount.toNat ∧ ∃ out, o = .revert out) := by
  obtain ⟨hc, hj, ⟨ia, hcode⟩, hpre, hdepth⟩ := hv
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  simp only [assetsOf]
  have hto : Word.toAddress (Word.ofAddress i.asset) = i.asset := Word.toAddress_ofAddress _
  have hdel := delegatedAddress?_assetCode ia
  have hacc := accessCost_le (m_sub.accessedAddresses.contains i.asset)
  rcases hmem with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
  · pwp_run_to 0x10e6 [hfmp, hsize, ofAddress_and_addressMask, addressMask_and_ofAddress]
    by_cases hbal : amount.toNat ≤ (m_world.sload i.asset
        (Erc20.balanceSlot m_ctx.crypto Erc20.Layout.solmate m_msg.currentTarget)).toNat
    · refine WP.callNoValue (by pcode_fact) rfl ?_ ?_ hdepth ?_
        (transfer_halts_ok_events (ia := ia) (dst := rcv) (amount := amount) _ ?_ rfl ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_) ?_
      · exact .inr (by dsimp only; rw [hto, hcode]; exact hdel)
      · simp only [callCost, callGas, callExt, hto, ofNat, BitVec.toNat_ofNat,
          Nat.reducePow, Nat.reduceMod]
        rw [messageCallGas_zero (by evm_gas)]
        simp only [Gas.maxMessageCallGas]
        evm_gas
      · rw [hto]; exact hpre
      · exact ⟨_, _, _, rfl, by dsimp only [childMsg]; rw [hto, hcode]⟩
      · simp [Frame.init, childMsg, hstatic]
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Abi.selectorOf]
        rw [Memory.readBytes_read _ 128 68 0 4 (by decide)]
        simp only [Memory.read_expand, Nat.add_zero,
          Memory.read_storeWord_of_disjoint _ 164 128 4 _ (by decide),
          Memory.read_storeWord_of_disjoint _ 132 128 4 _ (by decide),
          Memory.read_storeWord_prefix _ _ 4 _ (by decide)]
        decide +kernel
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
        decide
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes]
        rw [Memory.readBytes_read _ 128 68 4 32 (by decide)]
        simp only [Nat.reduceAdd, Memory.read_expand,
          Memory.read_storeWord_of_disjoint _ 164 132 32 _ (by decide), Memory.read_storeWord,
          Bytes.toWord_ofWord]
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes]
        rw [Memory.readBytes_read _ 128 68 36 32 (by decide)]
        simp only [Nat.reduceAdd, Memory.read_expand, Memory.read_storeWord, Bytes.toWord_ofWord]
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
        decide
      · dsimp only [Frame.init, childMsg]
        simp only [callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod]
        rw [messageCallGas_zero (by evm_gas)]
        simp only [Gas.maxMessageCallGas]
        evm_gas
      · dsimp only [Frame.init, childMsg]
        rw [hto]
        exact hbal
      · intro mf o ⟨⟨ho, hw, ht, hca, hgasB⟩, hlogs⟩ hsame
        have hk : mf.frame.kind = .call 0 32 := hsame.kind
        subst ho
        rw [resumeAfter_success hk]
        dsimp only [Frame.init, childMsg] at hw ht hca hgasB hlogs
        rw [hto] at hw hlogs
        have hs1 : mf.ctx = m_ctx := hsame.ctx
        have hs2 : mf.precompiles = m_pre := hsame.precompiles
        have hs3 : mf.originalWorld = m_originalWorld := hsame.originalWorld
        clear hsame
        simp only [hw, ht, hca, hs1, hs2, hs3, hto]
        dsimp only [callerFrame, callMemory, Frame.init, childMsg] at hgasB ⊢
        simp only [hto, returnMemory_ofWord, callCost, callGas, callExt, ofNat,
          BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hgasB ⊢
        rw [messageCallGas_zero (by evm_gas)] at hgasB ⊢
        simp only [Gas.maxMessageCallGas] at hgasB ⊢
        wp_generalize_gas g1 hg1
        have hg1' : m_gasLeft ≤ g1 + 58000 := by
          subst hg1
          generalize Gas.accessCost (Std.ExtTreeSet.contains m_sub.accessedAddresses i.asset) = acc
            at hacc hgasB ⊢
          evm_gas
        clear hg1 hgasB hdel hto hcode hpre
        pwp_steps [Bytes.size_ofWord]
        apply WP.ret
        refine ⟨hbal, _, _, _, _, rfl, ?_, ?_, ?_, ?_⟩
        · simp only [Memory.loadWord_expand,
            Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 164 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 132 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 128 64 _ (by decide), hfmp]
        · rw_mem_sizes
          evm_gas_norm
          rw_mem_sizes
          evm_gas_norm
        · evm_gas
        · logs_simp [hlogs]
          try rfl
    · rw [Nat.not_le] at hbal
      refine WP.callNoValue (by pcode_fact) rfl ?_ ?_ hdepth ?_
        (transfer_halts_revert (ia := ia) («to» := rcv) (amount := amount) _ ?_ rfl
          ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_) ?_
      · exact .inr (by dsimp only; rw [hto, hcode]; exact hdel)
      · simp only [callCost, callGas, callExt, hto, ofNat, BitVec.toNat_ofNat,
          Nat.reducePow, Nat.reduceMod]
        rw [messageCallGas_zero (by evm_gas)]
        simp only [Gas.maxMessageCallGas]
        evm_gas
      · rw [hto]; exact hpre
      · exact ⟨_, _, _, rfl, by dsimp only [childMsg]; rw [hto, hcode]⟩
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Abi.selectorOf]
        rw [Memory.readBytes_read _ 128 68 0 4 (by decide)]
        simp only [Memory.read_expand, Nat.add_zero,
          Memory.read_storeWord_of_disjoint _ 164 128 4 _ (by decide),
          Memory.read_storeWord_of_disjoint _ 132 128 4 _ (by decide),
          Memory.read_storeWord_prefix _ _ 4 _ (by decide)]
        decide +kernel
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
        decide
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes]
        rw [Memory.readBytes_read _ 128 68 4 32 (by decide)]
        simp only [Nat.reduceAdd, Memory.read_expand,
          Memory.read_storeWord_of_disjoint _ 164 132 32 _ (by decide), Memory.read_storeWord,
          Bytes.toWord_ofWord]
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes]
        rw [Memory.readBytes_read _ 128 68 36 32 (by decide)]
        simp only [Nat.reduceAdd, Memory.read_expand, Memory.read_storeWord, Bytes.toWord_ofWord]
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
        decide
      · dsimp only [Frame.init, childMsg]
        simp only [callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod]
        rw [messageCallGas_zero (by evm_gas)]
        simp only [Gas.maxMessageCallGas]
        evm_gas
      · dsimp only [Frame.init, childMsg]
        rw [hto]
        exact hbal
      · intro mf o ⟨⟨out, ho⟩, hgasB⟩ hsame
        have hk : mf.frame.kind = .call 0 32 := hsame.kind
        have hsnap : mf.frame.snapshot = (m_world, m_transient) := hsame.snapshot
        subst ho
        rw [resumeAfter_revert hk]
        have hs1 : mf.ctx = m_ctx := hsame.ctx
        have hs2 : mf.precompiles = m_pre := hsame.precompiles
        have hs3 : mf.originalWorld = m_originalWorld := hsame.originalWorld
        clear hsame
        simp only [hs1, hs2, hs3, hsnap]
        dsimp only [callerFrame, callMemory, Frame.init, childMsg] at hgasB ⊢
        simp only [hto, callCost, callGas, callExt, ofNat,
          BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hgasB ⊢
        rw [messageCallGas_zero (by evm_gas)] at hgasB ⊢
        simp only [Gas.maxMessageCallGas] at hgasB ⊢
        generalize hM : returnMemory _ 0 32 out = M
        obtain ⟨hm1, hm2⟩ := returnMemory_zero_word_eq hM (by clear hgasB; simp only [Memory.size_storeWord, Memory.size_expand]; omega)
        simp only [Memory.loadWord_expand,
          Memory.loadWord_storeWord_of_disjoint _ 164 64 _ (by decide),
          Memory.loadWord_storeWord_of_disjoint _ 132 64 _ (by decide),
          Memory.loadWord_storeWord_of_disjoint _ 128 64 _ (by decide), hfmp] at hm1
        have hm2' : M.size = 224 := by
          rw [hm2]
          simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words,
            hsize]
          decide
        clear hM hm2
        wp_generalize_gas g1 hg1
        have hg1' : m_gasLeft ≤ g1 + 15000 := by
          subst hg1
          generalize Gas.accessCost (Std.ExtTreeSet.contains m_sub.accessedAddresses i.asset) = acc
            at hacc hgasB ⊢
          evm_gas
        clear hg1 hgasB hdel hto hcode hpre
        pwp_steps [hm1, hm2', and_zero_word]
        exact ⟨hbal, _, rfl⟩
  · pwp_run_to 0x10e6 [hfmp, hsize, ofAddress_and_addressMask, addressMask_and_ofAddress]
    by_cases hbal : amount.toNat ≤ (m_world.sload i.asset
        (Erc20.balanceSlot m_ctx.crypto Erc20.Layout.solmate m_msg.currentTarget)).toNat
    · refine WP.callNoValue (by pcode_fact) rfl ?_ ?_ hdepth ?_
        (transfer_halts_ok_events (ia := ia) (dst := rcv) (amount := amount) _ ?_ rfl ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_) ?_
      · exact .inr (by dsimp only; rw [hto, hcode]; exact hdel)
      · simp only [callCost, callGas, callExt, hto, ofNat, BitVec.toNat_ofNat,
          Nat.reducePow, Nat.reduceMod]
        rw [messageCallGas_zero (by evm_gas)]
        simp only [Gas.maxMessageCallGas]
        evm_gas
      · rw [hto]; exact hpre
      · exact ⟨_, _, _, rfl, by dsimp only [childMsg]; rw [hto, hcode]⟩
      · simp [Frame.init, childMsg, hstatic]
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Abi.selectorOf]
        rw [Memory.readBytes_read _ 160 68 0 4 (by decide)]
        simp only [Memory.read_expand, Nat.add_zero,
          Memory.read_storeWord_of_disjoint _ 196 160 4 _ (by decide),
          Memory.read_storeWord_of_disjoint _ 164 160 4 _ (by decide),
          Memory.read_storeWord_prefix _ _ 4 _ (by decide)]
        decide +kernel
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
        decide
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes]
        rw [Memory.readBytes_read _ 160 68 4 32 (by decide)]
        simp only [Nat.reduceAdd, Memory.read_expand,
          Memory.read_storeWord_of_disjoint _ 196 164 32 _ (by decide), Memory.read_storeWord,
          Bytes.toWord_ofWord]
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes]
        rw [Memory.readBytes_read _ 160 68 36 32 (by decide)]
        simp only [Nat.reduceAdd, Memory.read_expand, Memory.read_storeWord, Bytes.toWord_ofWord]
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
        decide
      · dsimp only [Frame.init, childMsg]
        simp only [callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod]
        rw [messageCallGas_zero (by evm_gas)]
        simp only [Gas.maxMessageCallGas]
        evm_gas
      · dsimp only [Frame.init, childMsg]
        rw [hto]
        exact hbal
      · intro mf o ⟨⟨ho, hw, ht, hca, hgasB⟩, hlogs⟩ hsame
        have hk : mf.frame.kind = .call 0 32 := hsame.kind
        subst ho
        rw [resumeAfter_success hk]
        dsimp only [Frame.init, childMsg] at hw ht hca hgasB hlogs
        rw [hto] at hw hlogs
        have hs1 : mf.ctx = m_ctx := hsame.ctx
        have hs2 : mf.precompiles = m_pre := hsame.precompiles
        have hs3 : mf.originalWorld = m_originalWorld := hsame.originalWorld
        clear hsame
        simp only [hw, ht, hca, hs1, hs2, hs3, hto]
        dsimp only [callerFrame, callMemory, Frame.init, childMsg] at hgasB ⊢
        simp only [hto, returnMemory_ofWord, callCost, callGas, callExt, ofNat,
          BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hgasB ⊢
        rw [messageCallGas_zero (by evm_gas)] at hgasB ⊢
        simp only [Gas.maxMessageCallGas] at hgasB ⊢
        wp_generalize_gas g1 hg1
        have hg1' : m_gasLeft ≤ g1 + 58000 := by
          subst hg1
          generalize Gas.accessCost (Std.ExtTreeSet.contains m_sub.accessedAddresses i.asset) = acc
            at hacc hgasB ⊢
          evm_gas
        clear hg1 hgasB hdel hto hcode hpre
        pwp_steps [Bytes.size_ofWord]
        apply WP.ret
        refine ⟨hbal, _, _, _, _, rfl, ?_, ?_, ?_, ?_⟩
        · simp only [Memory.loadWord_expand,
            Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 196 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 164 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 160 64 _ (by decide), hfmp]
        · rw_mem_sizes
          evm_gas_norm
          rw_mem_sizes
          evm_gas_norm
        · evm_gas
        · logs_simp [hlogs]
          try rfl
    · rw [Nat.not_le] at hbal
      refine WP.callNoValue (by pcode_fact) rfl ?_ ?_ hdepth ?_
        (transfer_halts_revert (ia := ia) («to» := rcv) (amount := amount) _ ?_ rfl
          ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_) ?_
      · exact .inr (by dsimp only; rw [hto, hcode]; exact hdel)
      · simp only [callCost, callGas, callExt, hto, ofNat, BitVec.toNat_ofNat,
          Nat.reducePow, Nat.reduceMod]
        rw [messageCallGas_zero (by evm_gas)]
        simp only [Gas.maxMessageCallGas]
        evm_gas
      · rw [hto]; exact hpre
      · exact ⟨_, _, _, rfl, by dsimp only [childMsg]; rw [hto, hcode]⟩
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Abi.selectorOf]
        rw [Memory.readBytes_read _ 160 68 0 4 (by decide)]
        simp only [Memory.read_expand, Nat.add_zero,
          Memory.read_storeWord_of_disjoint _ 196 160 4 _ (by decide),
          Memory.read_storeWord_of_disjoint _ 164 160 4 _ (by decide),
          Memory.read_storeWord_prefix _ _ 4 _ (by decide)]
        decide +kernel
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
        decide
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes]
        rw [Memory.readBytes_read _ 160 68 4 32 (by decide)]
        simp only [Nat.reduceAdd, Memory.read_expand,
          Memory.read_storeWord_of_disjoint _ 196 164 32 _ (by decide), Memory.read_storeWord,
          Bytes.toWord_ofWord]
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes]
        rw [Memory.readBytes_read _ 160 68 36 32 (by decide)]
        simp only [Nat.reduceAdd, Memory.read_expand, Memory.read_storeWord, Bytes.toWord_ofWord]
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
        decide
      · dsimp only [Frame.init, childMsg]
        simp only [callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod]
        rw [messageCallGas_zero (by evm_gas)]
        simp only [Gas.maxMessageCallGas]
        evm_gas
      · dsimp only [Frame.init, childMsg]
        rw [hto]
        exact hbal
      · intro mf o ⟨⟨out, ho⟩, hgasB⟩ hsame
        have hk : mf.frame.kind = .call 0 32 := hsame.kind
        have hsnap : mf.frame.snapshot = (m_world, m_transient) := hsame.snapshot
        subst ho
        rw [resumeAfter_revert hk]
        have hs1 : mf.ctx = m_ctx := hsame.ctx
        have hs2 : mf.precompiles = m_pre := hsame.precompiles
        have hs3 : mf.originalWorld = m_originalWorld := hsame.originalWorld
        clear hsame
        simp only [hs1, hs2, hs3, hsnap]
        dsimp only [callerFrame, callMemory, Frame.init, childMsg] at hgasB ⊢
        simp only [hto, callCost, callGas, callExt, ofNat,
          BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hgasB ⊢
        rw [messageCallGas_zero (by evm_gas)] at hgasB ⊢
        simp only [Gas.maxMessageCallGas] at hgasB ⊢
        generalize hM : returnMemory _ 0 32 out = M
        obtain ⟨hm1, hm2⟩ := returnMemory_zero_word_eq hM (by clear hgasB; simp only [Memory.size_storeWord, Memory.size_expand]; omega)
        simp only [Memory.loadWord_expand,
          Memory.loadWord_storeWord_of_disjoint _ 196 64 _ (by decide),
          Memory.loadWord_storeWord_of_disjoint _ 164 64 _ (by decide),
          Memory.loadWord_storeWord_of_disjoint _ 160 64 _ (by decide), hfmp] at hm1
        have hm2' : M.size = 256 := by
          rw [hm2]
          simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words,
            hsize]
          decide
        clear hM hm2
        wp_generalize_gas g1 hg1
        have hg1' : m_gasLeft ≤ g1 + 15000 := by
          subst hg1
          generalize Gas.accessCost (Std.ExtTreeSet.contains m_sub.accessedAddresses i.asset) = acc
            at hacc hgasB ⊢
          evm_gas
        clear hg1 hgasB hdel hto hcode hpre
        pwp_steps [hm1, hm2', and_zero_word]
        exact ⟨hbal, _, rfl⟩

end EvmLeanSpecs.Refinement
