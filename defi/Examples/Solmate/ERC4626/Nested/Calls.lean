import Examples.Solmate.ERC4626.Nested.System
import Examples.Solmate.ERC4626.SharesFrame

/-!
# Frame summaries of every modelled call, in any frame

`FrameOk` (`NestedSystem.lean`) for a dangerous frame of the vault or the asset that executes
a modelled state-changing call (`Executes`: caller, target and ABI calldata of a `VCall`, as
the decoder reads it — calldata assembled in memory by a calling contract included) with
enough gas and no value (`Funded`), from the frame-level refinement theorems:

* vault: `deposit_refines`, `mint_refines` (`Deposit.lean`, `Mint.lean`), `withdraw_refines`,
  `redeem_refines` (`WithdrawRefines.lean`), `sharesTransfer_refines`,
  `sharesTransferFrom_refines`, `sharesApprove_refines` (`SharesFrameSpec.lean`);
* asset: `assetTransfer_refines`, `assetTransferFrom_refines` (`AssetSpec.lean`),
  `assetApprove_refines`, `assetMint_refines`, `assetBurn_refines`.

`frameOk_of_executes` dispatches on the call. Hypotheses: the trace-level `SlotsOk` for the
actors (the call admitted, `Admitted`), the fixed-slot hypothesis `hk` (no balance slot is
slot 2, 6 or 7), at least 250000 gas.
-/

namespace Examples.Solmate.ERC4626.Nested
open Examples.Solmate.ERC20 Defi.ERC4626 Defi.Trace

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic Examples.Solmate.Contracts
open Defi.ERC4626 Defi.Math Defi.ERC20 Defi.ERC4626.Solmate Defi.Trace.Lift
open Examples.Solmate.ERC4626.Invariants Defi.ERC4626
open EvmLogic.Program.Nested (Keep KeepP GoodOk DangerStart Danger TopOk Reaches bottom)

variable {crypto : Crypto} {vault asset : Address} {Act : List Address} {K : VCall → Prop}

/-! ## Frames executing a modelled call -/

/-- The calldata of call `c`, as the ABI decoder reads it. -/
def CallData : VCall → ByteArray → Prop
  | .deposit _ a r, d => TwoWordCall d 0x6e553f65 a (Word.ofAddress r)
  | .mint _ n r, d => TwoWordCall d 0x94bf804d n (Word.ofAddress r)
  | .withdraw _ a r o, d =>
    ThreeWordCall d 0xb460af94 a (Word.ofAddress r) (Word.ofAddress o)
  | .redeem _ n r o, d =>
    ThreeWordCall d 0xba087652 n (Word.ofAddress r) (Word.ofAddress o)
  | .transfer _ dst v, d => TwoWordCall d 0xa9059cbb (Word.ofAddress dst) v
  | .transferFrom _ s dst v, d =>
    ThreeWordCall d 0x23b872dd (Word.ofAddress s) (Word.ofAddress dst) v
  | .approve _ sp v, d => TwoWordCall d 0x095ea7b3 (Word.ofAddress sp) v
  | .assetTransfer _ dst v, d => TwoWordCall d 0xa9059cbb (Word.ofAddress dst) v
  | .assetTransferFrom _ s dst v, d =>
    ThreeWordCall d 0x23b872dd (Word.ofAddress s) (Word.ofAddress dst) v
  | .assetApprove _ sp v, d => TwoWordCall d 0x095ea7b3 (Word.ofAddress sp) v
  | .assetMint _ dst v, d => TwoWordCall d 0x40c10f19 (Word.ofAddress dst) v
  | .assetBurn _ s v, d => TwoWordCall d 0x9dc29fac (Word.ofAddress s) v

/-- The frame `m` executes the modelled call `c`: its caller, its account and its calldata. -/
structure Executes (vault asset : Address) (m : Machine) (c : VCall) : Prop where
  /-- The caller. -/
  caller : m.frame.msg.caller = c.caller
  /-- The called account. -/
  target : m.frame.msg.currentTarget = c.target vault asset
  /-- The calldata. -/
  data : CallData c m.frame.msg.data

/-- A non-static frame that has just started running the code of the vault or the asset,
called from another account (what `DangerStart` provides, independently of the simulation's
`Good`). -/
structure VaultStart (vault asset : Address) (m : Machine) : Prop where
  /-- Fresh, running the account's own code. -/
  fresh : Fresh (m.world.code m.frame.msg.currentTarget) m
  /-- Not static. -/
  static : m.frame.msg.isStatic = false
  /-- At the vault or the asset. -/
  prot : Prot vault asset m.frame.msg.currentTarget
  /-- Standard precompiles. -/
  pre : m.precompiles = PrecompileImpl.standard m.ctx
  /-- Called from another account. -/
  caller : ¬ Prot vault asset m.frame.msg.caller

/-- The frame is funded: no value, at least `minGas` and below `2⁶⁴` gas, room for the vault's
call into the asset (a frame of the vault below the depth limit), calldata below `2⁶⁴`
bytes. -/
structure Funded (vault : Address) (minGas : Nat) (m : Machine) : Prop where
  /-- No value. -/
  value : m.frame.msg.value = 0
  /-- Enough gas. -/
  gas : minGas ≤ m.frame.gasLeft
  /-- Gas fits 64 bits. -/
  gasLt : m.frame.gasLeft < 2 ^ 64
  /-- A frame of the vault has room for one more call level. -/
  depth : m.frame.msg.currentTarget = vault → m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit
  /-- Calldata length fits 64 bits. -/
  size : m.frame.msg.data.size < 2 ^ 64

/-- A dangerous frame of the simulation is a `VaultStart`. -/
theorem DangerStart.vaultStart {Good : World → Prop} {G : Nat} {m : Machine}
    (h : DangerStart (Prot vault asset) Good G m) : VaultStart vault asset m where
  fresh := by
    obtain ⟨o, s, hf⟩ := h.fresh
    exact ⟨m.frame.msg, _, _, hf, h.code⟩
  static := h.danger.2
  prot := h.danger.1
  pre := h.pre
  caller := h.caller

/-- The common hypotheses of the frame summaries. -/
structure FrameHyp (crypto : Crypto) (vault asset : Address) (Act : List Address)
    (minGas : Nat) (m : Machine) : Prop where
  /-- The frame. -/
  start : VaultStart vault asset m
  /-- Deployed. -/
  dep : Deployed m.world vault asset
  /-- Well-formed ledgers. -/
  inv : Solmate.Inv (abs crypto m.world vault asset)
  /-- The chain's hash. -/
  hash : m.ctx.crypto = crypto
  /-- Funded. -/
  funded : Funded vault minGas m
  /-- The trace-level hash hypothesis. -/
  slots : SlotsOk crypto vault Act

/-- `FrameOk` from a one-call summary. -/
theorem frameOk_one {m : Machine} {c : VCall} (hadm : Admitted Act K c)
    (h : Halts m (fun mf o => ∀ out, o = .success out → Deployed mf.world vault asset ∧
      AgreeOn (ActorPairs Act) (abs crypto mf.world vault asset)
        (Lift.stepD step (abs crypto m.world vault asset) c.op))) :
    FrameOk crypto vault asset Act K m :=
  h.mono fun _ _ _ hp out ho => by
    obtain ⟨hd, ha⟩ := hp out ho
    exact ⟨hd, [c], fun c' hc' => by rw [List.mem_singleton.1 hc']; exact hadm, ha⟩

/-- `stepD` of a successful step. -/
theorem stepD_of_some {s s' : State Address} {op : Op Address} (h : step s op = some s') :
    Lift.stepD step s op = s' := by
  unfold Lift.stepD; rw [h]; rfl

/-! ## The vault's entry points -/

/-- The vault frame's code and immutables. -/
theorem vault_fresh {m : Machine} (hv : VaultStart vault asset m) (hdep : Deployed m.world vault asset)
    (ht : m.frame.msg.currentTarget = vault) :
    ∃ i : SolmateVault.Immutables, i.asset = asset ∧ Fresh (SolmateVault.runtimeCodeWith i) m := by
  obtain ⟨i, hia, hc⟩ := hdep.vaultCode
  exact ⟨i, hia, by have := hv.fresh; rw [ht, hc] at this; exact this⟩

/-- The view preconditions of a funded vault frame. -/
theorem viewPre_of {minGas : Nat} {m : Machine} {i : SolmateVault.Immutables}
    (hmin : 60000 ≤ minGas) (h : FrameHyp crypto vault asset Act minGas m)
    (hi : i.asset = asset) (ht : m.frame.msg.currentTarget = vault)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) : ViewPre i m where
  fresh := hf
  value := h.funded.value
  assetCode := by rw [hi]; exact h.dep.assetCode
  assetNotPrecompile := by rw [h.start.pre, hi]; exact h.dep.assetNotPrecompile _
  depth := h.funded.depth ht
  gas := Nat.le_trans hmin h.funded.gas
  gasLt := h.funded.gasLt
  sizeLt := h.funded.size

set_option maxHeartbeats 1000000 in
/-- **`vault.deposit`, in any frame.** -/
theorem frameOk_deposit {minGas : Nat} {m : Machine} (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (h : FrameHyp crypto vault asset Act minGas m) {c : Address} {a : Word} {r : Address}
    (hx : Executes vault asset m (.deposit c a r)) (hadm : Admitted Act K (.deposit c a r)) :
    FrameOk crypto vault asset Act K m := by
  have ht : m.frame.msg.currentTarget = vault := hx.target
  have hcl : m.frame.msg.caller = c := hx.caller
  obtain ⟨i, hia, hf⟩ := vault_fresh h.start h.dep ht
  have hs := h.slots
  have hc : c ∈ Act := hadm.1 c (by simp [VCall.actors])
  have hr : r ∈ Act := hadm.1 r (by simp [VCall.actors])
  have hne : m.frame.msg.currentTarget ≠ i.asset := by
    rw [ht, hia]; exact h.dep.vault_ne_asset
  have hcr := h.hash
  have hdep := h.dep
  have hinv : Solmate.Inv (absOf i.asset m) := by
    simp only [absOf, hcr, ht, hia]; exact h.inv
  have hD := deposit_refines m (viewPre_of (by omega) h hia ht hf) h.start.static
    (Nat.le_trans hmin h.funded.gas) hx.data hne (hcr ▸ hk)
    (by rw [hcr, hcl]; exact hs.bal c hc) (by rw [hcr, ht]; exact hs.bal vault hs.vault_mem)
    (by rw [hcr]; exact hs.bal r hr) (by rw [hcr, hcl, ht]; exact hs.allow c hc vault hs.vault_mem)
    hinv
  refine frameOk_one hadm (hD.mono fun mf o _ hp out ho => ?_)
  simp only [absOf, hcr, ht, hia, hcl] at hp
  unfold EntryPost at hp
  split at hp
  · rename_i s' v hW
    obtain ⟨-, hw, hR⟩ := hp
    refine ⟨hdep.of_code (by rw [hw]; exact code_depositWorld ..)
      (by rw [hw]; exact code_depositWorld ..), ?_⟩
    rw [stepD_of_some (show step _ (VCall.deposit c a r).op = some s' by
      show Option.map Prod.fst (Solmate.deposit _ _ _ _) = _; rw [hW]; rfl)]
    simp only [hcr, ht] at hR
    exact agree_of_entry hs hc hR
  · obtain ⟨out', ho'⟩ := hp; rw [ho] at ho'; cases ho'

set_option maxHeartbeats 1000000 in
/-- **`vault.mint`, in any frame.** -/
theorem frameOk_mint {minGas : Nat} {m : Machine} (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (h : FrameHyp crypto vault asset Act minGas m) {c : Address} {n : Word} {r : Address}
    (hx : Executes vault asset m (.mint c n r)) (hadm : Admitted Act K (.mint c n r)) :
    FrameOk crypto vault asset Act K m := by
  have ht : m.frame.msg.currentTarget = vault := hx.target
  have hcl : m.frame.msg.caller = c := hx.caller
  obtain ⟨i, hia, hf⟩ := vault_fresh h.start h.dep ht
  have hs := h.slots
  have hc : c ∈ Act := hadm.1 c (by simp [VCall.actors])
  have hr : r ∈ Act := hadm.1 r (by simp [VCall.actors])
  have hne : m.frame.msg.currentTarget ≠ i.asset := by
    rw [ht, hia]; exact h.dep.vault_ne_asset
  have hcr := h.hash
  have hdep := h.dep
  have hinv : Solmate.Inv (absOf i.asset m) := by
    simp only [absOf, hcr, ht, hia]; exact h.inv
  have hD := mint_refines m (viewPre_of (by omega) h hia ht hf) h.start.static
    (Nat.le_trans hmin h.funded.gas) hx.data hne (hcr ▸ hk)
    (by rw [hcr, hcl]; exact hs.bal c hc) (by rw [hcr, ht]; exact hs.bal vault hs.vault_mem)
    (by rw [hcr]; exact hs.bal r hr) (by rw [hcr, hcl, ht]; exact hs.allow c hc vault hs.vault_mem)
    hinv
  refine frameOk_one hadm (hD.mono fun mf o _ hp out ho => ?_)
  simp only [absOf, hcr, ht, hia, hcl] at hp
  unfold EntryPost at hp
  split at hp
  · rename_i s' v hW
    obtain ⟨-, hw, hR⟩ := hp
    refine ⟨hdep.of_code (by rw [hw]; exact code_depositWorld ..)
      (by rw [hw]; exact code_depositWorld ..), ?_⟩
    rw [stepD_of_some (show step _ (VCall.mint c n r).op = some s' by
      show Option.map Prod.fst (Solmate.mint _ _ _ _) = _; rw [hW]; rfl)]
    simp only [hcr, ht] at hR
    exact agree_of_entry hs hc hR
  · obtain ⟨out', ho'⟩ := hp; rw [ho] at ho'; cases ho'

/-- The withdraw preconditions of a funded vault frame. -/
theorem outPre_of {minGas : Nat} {m : Machine} {i : SolmateVault.Immutables}
    (hmin : 200000 ≤ minGas) (h : FrameHyp crypto vault asset Act minGas m)
    (hi : i.asset = asset) (ht : m.frame.msg.currentTarget = vault)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) : OutPre i m where
  fresh := hf
  value := h.funded.value
  static := h.start.static
  assetCode := by rw [hi]; exact h.dep.assetCode
  assetNotPrecompile := by rw [h.start.pre, hi]; exact h.dep.assetNotPrecompile _
  assetNe := by rw [hi, ht]; exact h.dep.vault_ne_asset.symm
  depth := h.funded.depth ht
  gas := Nat.le_trans hmin h.funded.gas
  gasLt := h.funded.gasLt
  sizeLt := h.funded.size

set_option maxHeartbeats 1000000 in
/-- **`vault.withdraw`, in any frame.** -/
theorem frameOk_withdraw {minGas : Nat} {m : Machine} (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (h : FrameHyp crypto vault asset Act minGas m) {c : Address} {a : Word} {r o : Address}
    (hx : Executes vault asset m (.withdraw c a r o)) (hadm : Admitted Act K (.withdraw c a r o)) :
    FrameOk crypto vault asset Act K m := by
  have ht : m.frame.msg.currentTarget = vault := hx.target
  have hcl : m.frame.msg.caller = c := hx.caller
  obtain ⟨i, hia, hf⟩ := vault_fresh h.start h.dep ht
  have hs := h.slots
  have hc : c ∈ Act := hadm.1 c (by simp [VCall.actors])
  have hr : r ∈ Act := hadm.1 r (by simp [VCall.actors])
  have ho : o ∈ Act := hadm.1 o (by simp [VCall.actors])
  have hcr := h.hash
  have hdep := h.dep
  have hinv : Solmate.Inv (absOf i.asset m) := by
    simp only [absOf, hcr, ht, hia]; exact h.inv
  have hD := withdraw_refines m (outPre_of (by omega) h hia ht hf) hx.data
    (by rw [hcr, ht, hcl]; exact outSlots_of hs (KeccakAvoids.sub hk (by simp)) hc hr ho) hinv
  refine frameOk_one hadm (hD.mono fun mf o' _ hp out ho' => ?_)
  simp only [absOf, hcr, ht, hia, hcl] at hp
  unfold OutRefPost at hp
  split at hp
  · rename_i s' v hW
    obtain ⟨-, hR, hC⟩ := hp
    refine ⟨hdep.of_code (hC vault) (hC asset), ?_⟩
    rw [stepD_of_some (show step _ (VCall.withdraw c a r o).op = some s' by
      show Option.map Prod.fst (Solmate.withdraw _ _ _ _ _) = _; rw [hW]; rfl)]
    exact agree_of_refinesOn hs hc ho hR
  · obtain ⟨out', h'⟩ := hp; rw [ho'] at h'; cases h'

set_option maxHeartbeats 1000000 in
/-- **`vault.redeem`, in any frame.** -/
theorem frameOk_redeem {minGas : Nat} {m : Machine} (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (h : FrameHyp crypto vault asset Act minGas m) {c : Address} {n : Word} {r o : Address}
    (hx : Executes vault asset m (.redeem c n r o)) (hadm : Admitted Act K (.redeem c n r o)) :
    FrameOk crypto vault asset Act K m := by
  have ht : m.frame.msg.currentTarget = vault := hx.target
  have hcl : m.frame.msg.caller = c := hx.caller
  obtain ⟨i, hia, hf⟩ := vault_fresh h.start h.dep ht
  have hs := h.slots
  have hc : c ∈ Act := hadm.1 c (by simp [VCall.actors])
  have hr : r ∈ Act := hadm.1 r (by simp [VCall.actors])
  have ho : o ∈ Act := hadm.1 o (by simp [VCall.actors])
  have hcr := h.hash
  have hdep := h.dep
  have hinv : Solmate.Inv (absOf i.asset m) := by
    simp only [absOf, hcr, ht, hia]; exact h.inv
  have hD := redeem_refines m (outPre_of (by omega) h hia ht hf) hx.data
    (by rw [hcr, ht, hcl]; exact outSlots_of hs (KeccakAvoids.sub hk (by simp)) hc hr ho) hinv
  refine frameOk_one hadm (hD.mono fun mf o' _ hp out ho' => ?_)
  simp only [absOf, hcr, ht, hia, hcl] at hp
  unfold OutRefPost at hp
  split at hp
  · rename_i s' v hW
    obtain ⟨-, hR, hC⟩ := hp
    refine ⟨hdep.of_code (hC vault) (hC asset), ?_⟩
    rw [stepD_of_some (show step _ (VCall.redeem c n r o).op = some s' by
      show Option.map Prod.fst (Solmate.redeem _ _ _ _ _) = _; rw [hW]; rfl)]
    exact agree_of_refinesOn hs hc ho hR
  · obtain ⟨out', h'⟩ := hp; rw [ho'] at h'; cases h'

/-! ## The vault's share-token functions -/

set_option maxHeartbeats 1000000 in
/-- **`vault.transfer`, in any frame.** -/
theorem frameOk_transfer {minGas : Nat} {m : Machine} (hmin : 100000 ≤ minGas)
    (h : FrameHyp crypto vault asset Act minGas m) {c d : Address} {v : Word}
    (hx : Executes vault asset m (.transfer c d v)) (hadm : Admitted Act K (.transfer c d v)) :
    FrameOk crypto vault asset Act K m := by
  have ht : m.frame.msg.currentTarget = vault := hx.target
  have hcl : m.frame.msg.caller = c := hx.caller
  obtain ⟨i, hia, hf⟩ := vault_fresh h.start h.dep ht
  have hs := h.slots
  have hc : c ∈ Act := hadm.1 c (by simp [VCall.actors])
  have hd : d ∈ Act := hadm.1 d (by simp [VCall.actors])
  have hcr := h.hash
  have hdep := h.dep
  have hne := hdep.vault_ne_asset
  have hT := sharesTransfer_refines m hf h.funded.value h.start.static hx.data h.funded.size
    (by have := h.funded.gas; omega) (by rw [hcr, hcl]; exact hs.bal c hc)
    (by rw [hcr]; exact hs.bal d hd) (rep_toToken _) (by simp only [assetView, hcr, ht]; exact h.inv.2)
  rw [hcl] at hT
  have hsh : toToken (assetView m) = (abs crypto m.world vault asset).shares := by
    simp only [assetView, hcr, ht]; rfl
  rw [hsh] at hT
  refine frameOk_one hadm ?_
  split at hT
  · rename_i t' hT'
    refine hT.mono fun mf o _ ⟨⟨ho, hw, _⟩, hrep⟩ out ho' => ?_
    simp only [hcr, ht, hcl] at hw hrep
    refine ⟨hdep.of_code (by rw [hw]; exact code_transferWorld ..)
      (by rw [hw]; exact code_transferWorld ..), ?_⟩
    rw [stepD_of_some (s' := { abs crypto m.world vault asset with shares := t' }) (by
      show Option.map _ ((abs crypto m.world vault asset).shares.transfer _ _ _) = _
      rw [hT']; rfl)]
    exact agree_of_shares hrep
      (fun o sp ⟨ho, hsp⟩ => ⟨hs.balP ho hsp c, hs.balP ho hsp d⟩)
      (fun k => by rw [hw]; exact Shares.sload_transferWorld (.inl hne.symm))
      (hw ▸ Shares.sload_transferWorld
        (.inr ⟨(hs.balFixed c hc).1.symm, (hs.balFixed d hd).1.symm⟩))
      (hw ▸ Shares.sload_transferWorld
        (.inr ⟨(hs.balFixed c hc).2.symm, (hs.balFixed d hd).2.symm⟩))
  · exact hT.mono fun mf o _ hp out ho' => by
      obtain ⟨⟨out', ho⟩, -⟩ := hp; rw [ho] at ho'; cases ho'

/-- `transferFrom` writes only the allowance and the two balance slots. -/
theorem sload_transferFromWorld_slot {w : World} {token sp src dst : Address} {v k : Word}
    (h1 : k ≠ ERC20.balanceSlot crypto ERC20.Layout.solmate src)
    (h2 : k ≠ ERC20.balanceSlot crypto ERC20.Layout.solmate dst)
    (h3 : k ≠ ERC20.allowanceSlot crypto ERC20.Layout.solmate src sp) :
    (ERC20.transferFromWorld crypto w token sp src dst v).sload token k = w.sload token k := by
  simp only [ERC20.transferFromWorld]
  rw [Shares.sload_transferWorld (.inr ⟨h1, h2⟩), Shares.sload_spendWorld (.inr h3)]

set_option maxHeartbeats 1000000 in
/-- **`vault.transferFrom`, in any frame.** -/
theorem frameOk_transferFrom {minGas : Nat} {m : Machine} (hmin : 100000 ≤ minGas)
    (h : FrameHyp crypto vault asset Act minGas m) {c src d : Address} {v : Word}
    (hx : Executes vault asset m (.transferFrom c src d v))
    (hadm : Admitted Act K (.transferFrom c src d v)) :
    FrameOk crypto vault asset Act K m := by
  have ht : m.frame.msg.currentTarget = vault := hx.target
  have hcl : m.frame.msg.caller = c := hx.caller
  obtain ⟨i, hia, hf⟩ := vault_fresh h.start h.dep ht
  have hs := h.slots
  have hc : c ∈ Act := hadm.1 c (by simp [VCall.actors])
  have hsr : src ∈ Act := hadm.1 src (by simp [VCall.actors])
  have hd : d ∈ Act := hadm.1 d (by simp [VCall.actors])
  have hcr := h.hash
  have hdep := h.dep
  have hne := hdep.vault_ne_asset
  have hT := sharesTransferFrom_refines m hf h.funded.value h.start.static hx.data h.funded.size
    (by have := h.funded.gas; omega) (by rw [hcr]; exact hs.bal src hsr)
    (by rw [hcr]; exact hs.bal d hd) (by rw [hcr, hcl]; exact hs.allow src hsr c hc)
    (rep_toToken _) (by simp only [assetView, hcr, ht]; exact h.inv.2)
  rw [hcl] at hT
  have hsh : toToken (assetView m) = (abs crypto m.world vault asset).shares := by
    simp only [assetView, hcr, ht]; rfl
  rw [hsh] at hT
  refine frameOk_one hadm ?_
  split at hT
  · rename_i t' hT'
    refine hT.mono fun mf o _ ⟨⟨ho, hw, _⟩, hrep⟩ out ho' => ?_
    simp only [hcr, ht, hcl] at hw hrep
    refine ⟨hdep.of_code (by rw [hw]; exact code_transferFromWorld ..)
      (by rw [hw]; exact code_transferFromWorld ..), ?_⟩
    rw [stepD_of_some (s' := { abs crypto m.world vault asset with shares := t' }) (by
      show Option.map _ ((abs crypto m.world vault asset).shares.transferFrom _ _ _ _) = _
      rw [hT']; rfl)]
    exact agree_of_shares hrep
      (fun o sp ⟨ho, hsp⟩ => ⟨⟨hs.balP ho hsp src, hs.balP ho hsp d⟩, hs.allowP ho hsp hsr hc⟩)
      (fun k => by rw [hw]; exact sload_transferFromWorld_other hne.symm k)
      (hw ▸ sload_transferFromWorld_slot (hs.balFixed src hsr).1.symm (hs.balFixed d hd).1.symm
        (hs.allowFixed src hsr c hc).1.symm)
      (hw ▸ sload_transferFromWorld_slot (hs.balFixed src hsr).2.symm (hs.balFixed d hd).2.symm
        (hs.allowFixed src hsr c hc).2.symm)
  · exact hT.mono fun mf o _ hp out ho' => by
      obtain ⟨⟨out', ho⟩, -⟩ := hp; rw [ho] at ho'; cases ho'

set_option maxHeartbeats 1000000 in
/-- **`vault.approve`, in any frame.** -/
theorem frameOk_approve {minGas : Nat} {m : Machine} (hmin : 100000 ≤ minGas)
    (h : FrameHyp crypto vault asset Act minGas m) {c sp : Address} {v : Word}
    (hx : Executes vault asset m (.approve c sp v)) (hadm : Admitted Act K (.approve c sp v)) :
    FrameOk crypto vault asset Act K m := by
  have ht : m.frame.msg.currentTarget = vault := hx.target
  have hcl : m.frame.msg.caller = c := hx.caller
  obtain ⟨i, hia, hf⟩ := vault_fresh h.start h.dep ht
  have hs := h.slots
  have hc : c ∈ Act := hadm.1 c (by simp [VCall.actors])
  have hsp : sp ∈ Act := hadm.1 sp (by simp [VCall.actors])
  have hcr := h.hash
  have hdep := h.dep
  have hne := hdep.vault_ne_asset
  have hT := sharesApprove_refines m hf h.funded.value h.start.static hx.data h.funded.size
    (by have := h.funded.gas; omega) (by rw [hcr, hcl]; exact hs.allow c hc sp hsp)
    (rep_toToken _)
  rw [hcl] at hT
  have hsh : toToken (assetView m) = (abs crypto m.world vault asset).shares := by
    simp only [assetView, hcr, ht]; rfl
  rw [hsh] at hT
  refine frameOk_one hadm (hT.mono fun mf o _ ⟨⟨ho, hw, _⟩, hrep⟩ out ho' => ?_)
  simp only [hcr, ht, hcl] at hw hrep
  refine ⟨hdep.of_code (by rw [hw]; exact code_approveWorld ..)
    (by rw [hw]; exact code_approveWorld ..), ?_⟩
  rw [stepD_of_some (s' := { abs crypto m.world vault asset with
    shares := (abs crypto m.world vault asset).shares.approve c sp v.toNat }) rfl]
  exact agree_of_shares hrep (fun o sp' ⟨ho, hsp'⟩ => hs.allowP ho hsp' hc hsp)
    (fun k => by rw [hw]; exact World.sload_sstore_ne_addr _ _ _ _ hne.symm)
    (by rw [hw]; exact World.sload_sstore_ne_key _ _ _ (hs.allowFixed c hc sp hsp).1.symm)
    (by rw [hw]; exact World.sload_sstore_ne_key _ _ _ (hs.allowFixed c hc sp hsp).2.symm)

/-! ## The asset's functions -/

/-- The asset frame's code and immutables. -/
theorem asset_fresh {m : Machine} (hv : VaultStart vault asset m)
    (hdep : Deployed m.world vault asset) (ht : m.frame.msg.currentTarget = asset) :
    ∃ ia : SolmateAsset.Immutables, Fresh (SolmateAsset.runtimeCodeWith ia) m := by
  obtain ⟨ia, hc⟩ := hdep.assetCode
  exact ⟨ia, by have := hv.fresh; rw [ht, hc] at this; exact this⟩

set_option maxHeartbeats 1000000 in
/-- **`asset.transfer` (a donation when `d` is the vault), in any frame.** -/
theorem frameOk_assetTransfer {minGas : Nat} {m : Machine} (hmin : 100000 ≤ minGas)
    (h : FrameHyp crypto vault asset Act minGas m) {c d : Address} {v : Word}
    (hx : Executes vault asset m (.assetTransfer c d v))
    (hadm : Admitted Act K (.assetTransfer c d v)) :
    FrameOk crypto vault asset Act K m := by
  have ht : m.frame.msg.currentTarget = asset := hx.target
  have hcl : m.frame.msg.caller = c := hx.caller
  obtain ⟨ia, hf⟩ := asset_fresh h.start h.dep ht
  have hs := h.slots
  have hc : c ∈ Act := hadm.1 c (by simp [VCall.actors])
  have hd : d ∈ Act := hadm.1 d (by simp [VCall.actors])
  have hcr := h.hash
  have hdep := h.dep
  have hne := hdep.vault_ne_asset
  have hT := assetTransfer_refines m hf h.funded.value h.start.static hx.data h.funded.size
    (by have := h.funded.gas; omega) (by rw [hcr, hcl]; exact hs.bal c hc)
    (by rw [hcr]; exact hs.bal d hd) (rep_toToken _)
    (by simp only [assetView, hcr, ht]; exact h.inv.1)
  rw [hcl] at hT
  have hsh : toToken (assetView m) = (abs crypto m.world vault asset).asset := by
    simp only [assetView, hcr, ht]; rfl
  rw [hsh] at hT
  refine frameOk_one hadm ?_
  split at hT
  · rename_i t' hT'
    refine hT.mono fun mf o _ ⟨⟨ho, hw, _⟩, hrep⟩ out ho' => ?_
    simp only [hcr, ht, hcl] at hw hrep
    refine ⟨hdep.of_code (by rw [hw]; exact code_transferWorld ..)
      (by rw [hw]; exact code_transferWorld ..), ?_⟩
    rw [stepD_of_some (s' := { abs crypto m.world vault asset with asset := t' }) (by
      show Option.map _ ((abs crypto m.world vault asset).asset.transfer _ _ _) = _
      rw [hT']; rfl)]
    exact agree_of_asset hrep (fun o sp ⟨ho, hsp⟩ => ⟨hs.balP ho hsp c, hs.balP ho hsp d⟩)
      (fun k => by rw [hw]; exact Shares.sload_transferWorld (.inl hne))
  · exact hT.mono fun mf o _ hp out ho' => by
      obtain ⟨⟨out', ho⟩, -⟩ := hp; rw [ho] at ho'; cases ho'

set_option maxHeartbeats 1000000 in
/-- **`asset.transferFrom`, in any frame.** -/
theorem frameOk_assetTransferFrom {minGas : Nat} {m : Machine} (hmin : 100000 ≤ minGas)
    (h : FrameHyp crypto vault asset Act minGas m) {c src d : Address} {v : Word}
    (hx : Executes vault asset m (.assetTransferFrom c src d v))
    (hadm : Admitted Act K (.assetTransferFrom c src d v)) :
    FrameOk crypto vault asset Act K m := by
  have ht : m.frame.msg.currentTarget = asset := hx.target
  have hcl : m.frame.msg.caller = c := hx.caller
  obtain ⟨ia, hf⟩ := asset_fresh h.start h.dep ht
  have hs := h.slots
  have hc : c ∈ Act := hadm.1 c (by simp [VCall.actors])
  have hsr : src ∈ Act := hadm.1 src (by simp [VCall.actors])
  have hd : d ∈ Act := hadm.1 d (by simp [VCall.actors])
  have hcr := h.hash
  have hdep := h.dep
  have hne := hdep.vault_ne_asset
  have hT := assetTransferFrom_refines m hf h.funded.value h.start.static hx.data h.funded.size
    (by have := h.funded.gas; omega) (by rw [hcr]; exact hs.bal src hsr)
    (by rw [hcr]; exact hs.bal d hd) (by rw [hcr, hcl]; exact hs.allow src hsr c hc)
    (rep_toToken _) (by simp only [assetView, hcr, ht]; exact h.inv.1)
  rw [hcl] at hT
  have hsh : toToken (assetView m) = (abs crypto m.world vault asset).asset := by
    simp only [assetView, hcr, ht]; rfl
  rw [hsh] at hT
  refine frameOk_one hadm ?_
  split at hT
  · rename_i t' hT'
    refine hT.mono fun mf o _ ⟨⟨ho, hw, _⟩, hrep⟩ out ho' => ?_
    simp only [hcr, ht, hcl] at hw hrep
    refine ⟨hdep.of_code (by rw [hw]; exact code_transferFromWorld ..)
      (by rw [hw]; exact code_transferFromWorld ..), ?_⟩
    rw [stepD_of_some (s' := { abs crypto m.world vault asset with asset := t' }) (by
      show Option.map _ ((abs crypto m.world vault asset).asset.transferFrom _ _ _ _) = _
      rw [hT']; rfl)]
    exact agree_of_asset hrep (fun o sp ⟨ho, hsp⟩ =>
        ⟨⟨hs.balP ho hsp src, hs.balP ho hsp d⟩, hs.allowP ho hsp hsr hc⟩)
      (fun k => by rw [hw]; exact sload_transferFromWorld_other hne k)
  · exact hT.mono fun mf o _ hp out ho' => by
      obtain ⟨⟨out', ho⟩, -⟩ := hp; rw [ho] at ho'; cases ho'

set_option maxHeartbeats 1000000 in
/-- **`asset.approve`, in any frame.** -/
theorem frameOk_assetApprove {minGas : Nat} {m : Machine} (hmin : 100000 ≤ minGas)
    (h : FrameHyp crypto vault asset Act minGas m) {c sp : Address} {v : Word}
    (hx : Executes vault asset m (.assetApprove c sp v))
    (hadm : Admitted Act K (.assetApprove c sp v)) :
    FrameOk crypto vault asset Act K m := by
  have ht : m.frame.msg.currentTarget = asset := hx.target
  have hcl : m.frame.msg.caller = c := hx.caller
  obtain ⟨ia, hf⟩ := asset_fresh h.start h.dep ht
  have hs := h.slots
  have hc : c ∈ Act := hadm.1 c (by simp [VCall.actors])
  have hsp : sp ∈ Act := hadm.1 sp (by simp [VCall.actors])
  have hcr := h.hash
  have hdep := h.dep
  have hne := hdep.vault_ne_asset
  have hT := assetApprove_refines m hf h.funded.value h.start.static hx.data h.funded.size
    (by have := h.funded.gas; omega) (by rw [hcr, hcl]; exact hs.allow c hc sp hsp)
    (rep_toToken _)
  rw [hcl] at hT
  have hsh : toToken (assetView m) = (abs crypto m.world vault asset).asset := by
    simp only [assetView, hcr, ht]; rfl
  rw [hsh] at hT
  refine frameOk_one hadm (hT.mono fun mf o _ ⟨⟨ho, hw, _⟩, hrep⟩ out ho' => ?_)
  simp only [hcr, ht, hcl] at hw hrep
  refine ⟨hdep.of_code (by rw [hw]; exact code_approveWorld ..)
    (by rw [hw]; exact code_approveWorld ..), ?_⟩
  rw [stepD_of_some (s' := { abs crypto m.world vault asset with
    asset := (abs crypto m.world vault asset).asset.approve c sp v.toNat }) rfl]
  exact agree_of_asset hrep (fun o sp' ⟨ho, hsp'⟩ => hs.allowP ho hsp' hc hsp)
    (fun k => by rw [hw]; exact World.sload_sstore_ne_addr _ _ _ _ hne)

set_option maxHeartbeats 1000000 in
/-- **`asset.mint` (unrestricted in `MockERC20`: yield when `d` is the vault), in any frame.** -/
theorem frameOk_assetMint {minGas : Nat} {m : Machine} (hmin : 100000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256])
    (h : FrameHyp crypto vault asset Act minGas m) {c d : Address} {v : Word}
    (hx : Executes vault asset m (.assetMint c d v)) (hadm : Admitted Act K (.assetMint c d v)) :
    FrameOk crypto vault asset Act K m := by
  have ht : m.frame.msg.currentTarget = asset := hx.target
  obtain ⟨ia, hf⟩ := asset_fresh h.start h.dep ht
  have hs := h.slots
  have hd : d ∈ Act := hadm.1 d (by simp [VCall.actors])
  have hcr := h.hash
  have hdep := h.dep
  have hne := hdep.vault_ne_asset
  have hT := assetMint_refines m hf h.funded.value h.start.static hx.data h.funded.size
    (by have := h.funded.gas; omega) (hcr ▸ hk) (by rw [hcr]; exact hs.bal d hd)
    (rep_toToken _) (by simp only [assetView, hcr, ht]; exact h.inv.1)
  have hsh : toToken (assetView m) = (abs crypto m.world vault asset).asset := by
    simp only [assetView, hcr, ht]; rfl
  rw [hsh] at hT
  refine frameOk_one hadm ?_
  split at hT
  · rename_i t' hT'
    refine hT.mono fun mf o _ ⟨⟨ho, hw, _⟩, hrep⟩ out ho' => ?_
    simp only [hcr, ht] at hw hrep
    refine ⟨hdep.of_code (by rw [hw]; exact code_mintWorld ..)
      (by rw [hw]; exact code_mintWorld ..), ?_⟩
    rw [stepD_of_some (s' := { abs crypto m.world vault asset with asset := t' }) (by
      show Option.map _ ((abs crypto m.world vault asset).asset.mint _ _) = _
      rw [hT']; rfl)]
    exact agree_of_asset hrep (fun o sp ⟨ho, hsp⟩ => hs.mintP ho hsp d)
      (fun k => by rw [hw]; exact sload_mintWorld (.inl hne))
  · exact hT.mono fun mf o _ hp out ho' => by
      obtain ⟨⟨out', ho⟩, -⟩ := hp; rw [ho] at ho'; cases ho'

set_option maxHeartbeats 1000000 in
/-- **`asset.burn` (unrestricted in `MockERC20`), in any frame.** -/
theorem frameOk_assetBurn {minGas : Nat} {m : Machine} (hmin : 100000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256])
    (h : FrameHyp crypto vault asset Act minGas m) {c src : Address} {v : Word}
    (hx : Executes vault asset m (.assetBurn c src v)) (hadm : Admitted Act K (.assetBurn c src v)) :
    FrameOk crypto vault asset Act K m := by
  have ht : m.frame.msg.currentTarget = asset := hx.target
  obtain ⟨ia, hf⟩ := asset_fresh h.start h.dep ht
  have hs := h.slots
  have hsr : src ∈ Act := hadm.1 src (by simp [VCall.actors])
  have hcr := h.hash
  have hdep := h.dep
  have hne := hdep.vault_ne_asset
  have hT := assetBurn_refines m hf h.funded.value h.start.static hx.data h.funded.size
    (by have := h.funded.gas; omega) (hcr ▸ hk) (by rw [hcr]; exact hs.bal src hsr)
    (rep_toToken _) (by simp only [assetView, hcr, ht]; exact h.inv.1)
  have hsh : toToken (assetView m) = (abs crypto m.world vault asset).asset := by
    simp only [assetView, hcr, ht]; rfl
  rw [hsh] at hT
  refine frameOk_one hadm ?_
  split at hT
  · rename_i t' hT'
    refine hT.mono fun mf o _ ⟨⟨ho, hw, _⟩, hrep⟩ out ho' => ?_
    simp only [hcr, ht] at hw hrep
    refine ⟨hdep.of_code (by rw [hw]; exact code_burnWorld ..)
      (by rw [hw]; exact code_burnWorld ..), ?_⟩
    rw [stepD_of_some (s' := { abs crypto m.world vault asset with asset := t' }) (by
      show Option.map _ ((abs crypto m.world vault asset).asset.burn _ _) = _
      rw [hT']; rfl)]
    exact agree_of_asset hrep (fun o sp ⟨ho, hsp⟩ => hs.mintP ho hsp src)
      (fun k => by rw [hw]; exact sload_burnWorld (.inl hne))
  · exact hT.mono fun mf o _ hp out ho' => by
      obtain ⟨⟨out', ho⟩, -⟩ := hp; rw [ho] at ho'; cases ho'

/-! ## Every modelled call -/

/-- **Every modelled call, in any frame**: a funded frame of the vault or the asset executing
an admitted modelled call satisfies its frame summary. -/
theorem frameOk_of_executes {minGas : Nat} {m : Machine} (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (h : FrameHyp crypto vault asset Act minGas m) {c : VCall}
    (hx : Executes vault asset m c) (hadm : Admitted Act K c) :
    FrameOk crypto vault asset Act K m := by
  have hk2 : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256] := KeccakAvoids.sub hk (by simp)
  cases c with
  | deposit => exact frameOk_deposit hmin hk h hx hadm
  | mint => exact frameOk_mint hmin hk h hx hadm
  | withdraw => exact frameOk_withdraw hmin hk h hx hadm
  | redeem => exact frameOk_redeem hmin hk h hx hadm
  | transfer => exact frameOk_transfer (by omega) h hx hadm
  | transferFrom => exact frameOk_transferFrom (by omega) h hx hadm
  | approve => exact frameOk_approve (by omega) h hx hadm
  | assetTransfer => exact frameOk_assetTransfer (by omega) h hx hadm
  | assetTransferFrom => exact frameOk_assetTransferFrom (by omega) h hx hadm
  | assetApprove => exact frameOk_assetApprove (by omega) h hx hadm
  | assetMint => exact frameOk_assetMint (by omega) hk2 h hx hadm
  | assetBurn => exact frameOk_assetBurn (by omega) hk2 h hx hadm

end Examples.Solmate.ERC4626.Nested
