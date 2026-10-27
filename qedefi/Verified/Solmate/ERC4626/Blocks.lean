import Verified.Solmate.ERC4626.Process
import EvmLogic.Chain.Lift

/-!
# The vault invariants along a chain of valid blocks

`Verified.Solmate.ERC4626.Time` runs blocks as lists of top-level calls and assumed environment
steps. Here the step is the real block function `EvmLean.Block.stateTransition`, decomposed by
`EvmLogic.Chain` (`stateTransition_bodyRun`): the EIP-4788 system call, from Prague the EIP-2935
one, the transactions through `Tx.process` (`TxRun`), the withdrawals, and from Prague the
EIP-7002/7251 request dequeues. Each kind of world transition keeps `Follows`:

* **transactions**: `follows_process_anyGas`, with the gas cap discharged by the block: a valid
  header's gas limit is at most `2⁶³ - 1` (EIP-1985, `gasLimit_envOf_le`), and every
  transaction runs with at most that much gas available;
* **withdrawals**: balance credits keep the storage and code of every account holding code
  (`EvmLogic.Chain.good_applyWithdrawals`), no hypothesis;
* **system calls**: `TopOk` messages from `SYSTEM_ADDRESS` (`topOk_systemMessage`) without
  authorizations and with `SYSTEM_TRANSACTION_GAS < 2⁶⁴`, so the nested simulation applies
  (`follows_tx_anyGas`) given the coverage of the vault/asset frames they reach (`SysCovered`,
  the frame-summary obligation `hsum` of `EvmLogic.Chain.systemCall_good`; vacuous for the
  deployed system contracts, which call no other contract); the EIP-161 clean-up erases only
  empty accounts.

`EvmLogic.Chain.BlockPreserves` asks the transaction obligation for *every* transaction (and
`blockPreserves_good` the system-call one from *every* world), which the vault cannot give: a
transaction committing a call by an actor outside `Act` is not admitted, and `Act` cannot be
every address (pairwise distinct allowance slots for all `2³²⁰` pairs is false for every hash
function); a world where a system contract's code mints the asset to a non-actor is a
`Follows` world. So coverage is stated for the system calls and transactions the chain
actually runs, at the world each runs in (`TxsCovered`, `BodyCovered`, `BlockCovered`), along a
`CoveredChain` — a chain of valid blocks (`CoveredChain.applies`) with that coverage. No
environment step remains; the only hypothesis beyond those of the transaction theorems is that
`SYSTEM_ADDRESS` is neither the vault nor the asset.
-/

namespace Verified.Solmate.ERC4626.Nested
open Verified.Solmate.ERC20 QEDefi.ERC4626 QEDefi.Trace
open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open Verified.Solmate.Contracts
open QEDefi.Math QEDefi.ERC20 QEDefi.ERC4626.Solmate QEDefi.Trace.Lift
open Verified.Solmate.ERC4626.Invariants Verified.Solmate.ERC4626.LowGas
open EvmLean.Tx (TxOutput process)
open EvmLean.Block (ChainHead stateTransition systemAddress systemTransactionGas maxGasLimit
  validateHeader)
open EvmLogic.Chain (TxRun BodyRun CheckedCall systemContracts systemContext systemMessage txsOf
  Applies)
open EvmLogic.Program.Nested (Keep KeepP GoodOk DangerStart Danger TopOk Reaches)

variable {crypto : Crypto} {vault asset : Address} {Act : List Address} {K : VCall → Prop}

/-! ## The block gas limit -/

private theorem ok_of_ite_throw {ε α β : Type} {c : Prop} [Decidable c] {e : ε}
    {jp : β → Except ε α} {B : Except ε α} {x : α}
    (h : (if c then (throw e >>= jp) else B : Except ε α) = .ok x) : ¬c ∧ B = .ok x := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte] at h; cases h
  · simp only [hc, ↓reduceIte] at h; exact ⟨hc, h⟩

/-- A valid header's gas limit is at most `2⁶³ - 1` (EIP-1985). -/
theorem validateHeader_gasLimit {keccak256 : ByteArray → Word} {fork : Fork}
    {parent : Header} {parentHash : Word} {h : Header}
    (hv : validateHeader keccak256 fork parent parentHash h = .ok ()) :
    h.gasLimit ≤ maxGasLimit := by
  unfold validateHeader at hv
  dsimp only at hv
  obtain ⟨-, hv⟩ := ok_of_ite_throw hv
  obtain ⟨-, hv⟩ := ok_of_ite_throw hv
  obtain ⟨-, hv⟩ := ok_of_ite_throw hv
  obtain ⟨h4, -⟩ := ok_of_ite_throw hv
  omega

/-- **The gas limit of a valid block's environment is at most `2⁶³ - 1`.** -/
theorem gasLimit_envOf_le {fuel : Nat} {fork : Fork} {chainId : Nat} {head head' : ChainHead}
    {block : Block} {hints : List (Option Address)} {rs : Array Receipt}
    (h : stateTransition fuel crypto fork chainId head block hints = .ok (head', rs)) :
    (envOf chainId head block).gasLimit ≤ maxGasLimit :=
  validateHeader_gasLimit (EvmLogic.Program.stateTransition_head h).2.2.2

/-! ## Transactions of a block -/

/-- **Every transaction a block runs is covered at the world it runs in.** From world `w`, with
block gas `g` and blob gas `bg` used so far, the transactions `txs` are processed in order as
`Block.applyTxs` does (`TxRun`); each must be `TxCoveredAnyGas` with the gas still available,
in the world reached by the transactions before it. Only successful prefixes are constrained
(a block whose transaction fails is invalid). -/
def TxsCovered (vault asset : Address) (Act : List Address) (K : VCall → Prop) (fuel : Nat)
    (crypto : Crypto) (fork : Fork) (env : BlockEnv) :
    Nat → Nat → List (Transaction × Option Address) → World → Prop
  | _, _, [], _ => True
  | g, bg, (tx, hint) :: rest, w =>
    TxCoveredAnyGas vault asset Act K crypto fork env (env.gasLimit - g)
        ((EvmLean.Tx.blobParams fork).maxGasPerBlock - bg) w tx hint ∧
      ∀ r : TxOutput, process fuel crypto fork env (env.gasLimit - g)
          ((EvmLean.Tx.blobParams fork).maxGasPerBlock - bg) w tx hint = .ok r →
        TxsCovered vault asset Act K fuel crypto fork env (g + r.gasUsed) (bg + r.blobGasUsed)
          rest r.world

/-- **The transactions of a block keep `Follows`**, when each is covered at the world it runs
in and the block gas limit is below `2⁶⁴`. -/
theorem follows_txRun
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ : World} (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    {fuel : Nat} {fork : Fork} {env : BlockEnv} (hgl : env.gasLimit < 2 ^ 64) {g bg : Nat}
    {txs : List (Transaction × Option Address)} {w w' : World}
    (hrun : TxRun fuel crypto fork env g bg txs w w')
    (hcov : TxsCovered vault asset Act K fuel crypto fork env g bg txs w)
    (hw : Follows crypto vault asset Act K w₀ w) : Follows crypto vault asset Act K w₀ w' := by
  induction hrun with
  | nil => exact hw
  | cons hp _ ih =>
    obtain ⟨hc, hrest⟩ := hcov
    exact ih (hrest _ hp) (follows_process_anyGas hk hs hinv hw (.inr (by omega)) hc hp)

/-! ## System calls -/

/-- **A system call covered at any gas**: the message of the system call to `target` with
calldata `data` from `world` (`systemMessage`, in `systemContext`) is `TxOkAnyGas` — every
vault/asset frame it reaches from other code is covered at any gas and commits admitted calls,
exactly as for a transaction. Vacuous when the call reaches no vault/asset frame, as with the
deployed system contracts, which call no other contract. This is the frame-summary (`hsum`)
obligation of `EvmLogic.Chain.systemCall_good`, stated at the world the call runs in. -/
def SysCovered (vault asset : Address) (Act : List Address) (K : VCall → Prop) (crypto : Crypto)
    (fork : Fork) (env : BlockEnv) (world : World) (target : Address) (data : ByteArray) : Prop :=
  TxOkAnyGas vault asset Act K (systemContext crypto fork env) world ∅
    (systemMessage world target data)

/-- **A covered system call keeps `Follows`**, when `SYSTEM_ADDRESS` is neither the vault nor
the asset: the system message is `TopOk` (`topOk_systemMessage`), carries no authorization and
`SYSTEM_TRANSACTION_GAS < 2⁶⁴`, so the nested simulation applies; the EIP-161 clean-up erases
only empty accounts. -/
theorem follows_systemCall
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ : World} (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (hP : ¬ Prot vault asset systemAddress) {fuel : Nat} {fork : Fork} {env : BlockEnv}
    {world w' : World} {target : Address} {data : ByteArray} {res : MessageResult}
    (hcov : SysCovered vault asset Act K crypto fork env world target data)
    (hw : Follows crypto vault asset Act K w₀ world)
    (h : EvmLean.Block.systemCall fuel crypto fork env world target data = .ok (w', res)) :
    Follows crypto vault asset Act K w₀ w' := by
  obtain ⟨hr, rfl⟩ := EvmLogic.Chain.systemCall_ok.1 h
  have hg := follows_tx_anyGas hk hs hinv hw rfl (.inr rfl)
    (EvmLogic.Chain.topOk_systemMessage hP world target data)
    (by simp [systemTransactionGas]) hcov hr
  exact EvmLogic.Chain.good_destroyTouchedEmpty goodOk hg _

/-- `SYSTEM_ADDRESS` is neither the canonical vault nor its asset. -/
theorem not_prot_systemAddress :
    ¬ Prot SolmateVault.address SolmateVault.deployment.asset systemAddress := by
  unfold Prot; decide

/-! ## One block -/

/-- **A block body whose system calls and transactions are covered**, at the worlds of its run
(`BodyRun`, from `world` through `w₁`, `w₂`, `w₃`): the EIP-4788 call from `world`; from Prague
the EIP-2935 call from `w₁`; every transaction at the world it runs in (`TxsCovered` from
`w₂`); from Prague the EIP-7002 dequeue after the withdrawals and the EIP-7251 dequeue after
it. -/
def BodyCovered (vault asset : Address) (Act : List Address) (K : VCall → Prop) (fuel : Nat)
    (crypto : Crypto) (fork : Fork) (env : BlockEnv) (txs : List (Transaction × Option Address))
    (ws : List Withdrawal) (world w₁ w₂ w₃ : World) : Prop :=
  SysCovered vault asset Act K crypto fork env world EvmLean.Block.beaconRootsAddress
      (Bytes.ofWord env.parentBeaconBlockRoot) ∧
    (fork ≥ .prague → SysCovered vault asset Act K crypto fork env w₁
      EvmLean.Block.historyStorageAddress (Bytes.ofWord (env.blockHashes[0]?.getD 0))) ∧
    TxsCovered vault asset Act K fuel crypto fork env 0 0 txs w₂ ∧
    (fork ≥ .prague →
      SysCovered vault asset Act K crypto fork env (EvmLean.Block.applyWithdrawals w₃ ws)
          EvmLean.Block.withdrawalRequestAddress .empty ∧
        ∀ w, CheckedCall fuel crypto fork env (EvmLean.Block.applyWithdrawals w₃ ws)
            EvmLean.Block.withdrawalRequestAddress .empty w →
          SysCovered vault asset Act K crypto fork env w
            EvmLean.Block.consolidationRequestAddress .empty)

/-- **A block body keeps `Follows`**: its system calls and transactions when covered
(`BodyCovered`, with a block gas limit below `2⁶⁴`), its withdrawals with no hypothesis. -/
theorem follows_bodyRun
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ : World} (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (hP : ¬ Prot vault asset systemAddress) {fuel : Nat} {fork : Fork} {env : BlockEnv}
    (hgl : env.gasLimit < 2 ^ 64) {txs : List (Transaction × Option Address)}
    {ws : List Withdrawal} {world w₁ w₂ w₃ w₄ : World}
    (hrun : BodyRun fuel crypto fork env txs ws world w₁ w₂ w₃ w₄)
    (hcov : BodyCovered vault asset Act K fuel crypto fork env txs ws world w₁ w₂ w₃)
    (hw : Follows crypto vault asset Act K w₀ world) : Follows crypto vault asset Act K w₀ w₄ := by
  obtain ⟨⟨r₁, h₁⟩, hh, ht, hp⟩ := hrun
  obtain ⟨c₁, c₂, c₃, c₄⟩ := hcov
  have e₁ := follows_systemCall hk hs hinv hP c₁ hw h₁
  have e₂ : Follows crypto vault asset Act K w₀ w₂ := by
    split at hh
    · obtain ⟨r, hr⟩ := hh
      exact follows_systemCall hk hs hinv hP (c₂ ‹_›) e₁ hr
    · rw [hh]; exact e₁
  have e₃ := follows_txRun hk hs hinv hgl ht c₃ e₂
  have ew := EvmLogic.Chain.good_applyWithdrawals goodOk e₃ ws
  split at hp
  · obtain ⟨w, hw₁, hw₂⟩ := hp
    obtain ⟨d₁, d₂⟩ := c₄ ‹_›
    obtain ⟨-, r, hr, -⟩ := id hw₁
    obtain ⟨-, r', hr', -⟩ := hw₂
    exact follows_systemCall hk hs hinv hP (d₂ w hw₁) (follows_systemCall hk hs hinv hP d₁ ew hr)
      hr'
  · rw [hp]; exact ew

/-- **A block whose system calls and transactions are covered**: `BodyCovered` for the body run
of `block` on top of `head` (the run is unique; a block without one is invalid). -/
def BlockCovered (vault asset : Address) (Act : List Address) (K : VCall → Prop) (fuel : Nat)
    (crypto : Crypto) (fork : Fork) (chainId : Nat) (head : ChainHead) (block : Block)
    (hints : List (Option Address)) : Prop :=
  ∀ w₁ w₂ w₃ w₄, BodyRun fuel crypto fork (envOf chainId head block) (txsOf block hints)
      block.withdrawals head.world w₁ w₂ w₃ w₄ →
    BodyCovered vault asset Act K fuel crypto fork (envOf chainId head block) (txsOf block hints)
      block.withdrawals head.world w₁ w₂ w₃

/-- **A valid block whose system calls and transactions are covered keeps `Follows`.** -/
theorem follows_stateTransition
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ : World} (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (hP : ¬ Prot vault asset systemAddress) {fuel : Nat} {fork : Fork} {chainId : Nat}
    {head head' : ChainHead} {block : Block} {hints : List (Option Address)}
    {rs : Array Receipt}
    (hcov : BlockCovered vault asset Act K fuel crypto fork chainId head block hints)
    (h : stateTransition fuel crypto fork chainId head block hints = .ok (head', rs))
    (hw : Follows crypto vault asset Act K w₀ head.world) :
    Follows crypto vault asset Act K w₀ head'.world := by
  obtain ⟨w₁, w₂, w₃, hrun⟩ := EvmLogic.Chain.stateTransition_bodyRun h
  have hgl := gasLimit_envOf_le h
  exact follows_bodyRun hk hs hinv hP (by simp only [maxGasLimit] at hgl; omega) hrun
    (hcov _ _ _ _ hrun) hw

/-! ## Chains of valid blocks -/

/-- **A chain of valid blocks whose system calls and transactions are covered**: `Applies`
(`CoveredChain.applies`) with `BlockCovered` for each block. -/
inductive CoveredChain (crypto : Crypto) (vault asset : Address) (Act : List Address)
    (K : VCall → Prop) (chainId : Nat) :
    ChainHead → List (Nat × Fork × BlockEnv) → ChainHead → Prop
  /-- No block. -/
  | nil (head : ChainHead) : CoveredChain crypto vault asset Act K chainId head [] head
  /-- A valid covered block, then the rest of the chain. -/
  | cons {fuel : Nat} {fork : Fork} {head head₁ head₂ : ChainHead} {block : Block}
      {hints : List (Option Address)} {rs : Array Receipt}
      {bs : List (Nat × Fork × BlockEnv)} :
      stateTransition fuel crypto fork chainId head block hints = .ok (head₁, rs) →
      BlockCovered vault asset Act K fuel crypto fork chainId head block hints →
      CoveredChain crypto vault asset Act K chainId head₁ bs head₂ →
      CoveredChain crypto vault asset Act K chainId head
        ((fuel, fork, envOf chainId head block) :: bs) head₂

/-- A covered chain is a chain of valid blocks. -/
theorem CoveredChain.applies {chainId : Nat} {head head' : ChainHead}
    {bs : List (Nat × Fork × BlockEnv)}
    (h : CoveredChain crypto vault asset Act K chainId head bs head') :
    Applies crypto chainId head bs head' := by
  induction h with
  | nil => exact .nil _
  | cons hst _ _ ih => exact .cons hst ih

/-- **Every covered chain of valid blocks keeps `Follows`**, when `SYSTEM_ADDRESS` is neither the
vault nor the asset. -/
theorem follows_coveredChain
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ : World} (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (hP : ¬ Prot vault asset systemAddress) {chainId : Nat} {head head' : ChainHead}
    {bs : List (Nat × Fork × BlockEnv)}
    (hc : CoveredChain crypto vault asset Act K chainId head bs head')
    (hw : Follows crypto vault asset Act K w₀ head.world) :
    Follows crypto vault asset Act K w₀ head'.world := by
  induction hc with
  | nil => exact hw
  | cons hst hcov _ ih =>
    exact ih (follows_stateTransition hk hs hinv hP hcov hst hw)

/-! ## Headline theorems -/

/-- **The lifting theorem along a chain of valid blocks.** From a head whose world is deployed
with well-formed ledgers, after any chain of valid blocks (`Block.stateTransition`, any forks,
EIP-7702 included) whose system calls and transactions are covered at any gas (`CoveredChain`):
deployed, well formed, and `abs` agrees (up to non-actor allowances) with the model's execution
of admitted calls. The only hypothesis beyond the transaction theorems': `SYSTEM_ADDRESS` is
neither the vault nor the asset (`not_prot_systemAddress` for the canonical deployment). -/
theorem lift_coveredChain
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) (hP : ¬ Prot vault asset systemAddress) {chainId : Nat}
    {head head' : ChainHead} {bs : List (Nat × Fork × BlockEnv)}
    (hdep : Deployed head.world vault asset) (hinv : Solmate.Inv (abs crypto head.world vault asset))
    (hc : CoveredChain crypto vault asset Act K chainId head bs head') :
    Deployed head'.world vault asset ∧ Solmate.Inv (abs crypto head'.world vault asset) ∧
      ∃ cs : List VCall, (∀ c ∈ cs, Admitted Act K c) ∧
        AgreeOn (ActorPairs Act) (abs crypto head'.world vault asset)
          (Solmate.exec (abs crypto head.world vault asset) (cs.map VCall.op)) :=
  (follows_coveredChain hk hs hinv hP hc (follows_refl hdep)).lift hs hinv

/-- **Invariants transfer along a chain of valid blocks**: every model invariant preserved by
every successful step and insensitive to non-actor allowances holds. -/
theorem invariant_coveredChain
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) (hP : ¬ Prot vault asset systemAddress)
    {I : State Address → Prop} (hI : ∀ s op s', Solmate.Inv s → I s → step s op = some s' → I s')
    (hIa : ∀ s t, AgreeOn (ActorPairs Act) s t → I s → I t) {chainId : Nat}
    {head head' : ChainHead} {bs : List (Nat × Fork × BlockEnv)}
    (hdep : Deployed head.world vault asset) (hinv : Solmate.Inv (abs crypto head.world vault asset))
    (hc : CoveredChain crypto vault asset Act K chainId head bs head')
    (hI₀ : I (abs crypto head.world vault asset)) : I (abs crypto head'.world vault asset) :=
  (follows_coveredChain hk hs hinv hP hc (follows_refl hdep)).invariant hinv hI hIa hI₀

/-- **`totalSupply` = Σ `balanceOf` along a chain of valid blocks**, for the shares and for the
asset, read from storage. -/
theorem supply_eq_sum_coveredChain
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) (hP : ¬ Prot vault asset systemAddress) {chainId : Nat}
    {head head' : ChainHead} {bs : List (Nat × Fork × BlockEnv)}
    (hdep : Deployed head.world vault asset) (hinv : Solmate.Inv (abs crypto head.world vault asset))
    (hc : CoveredChain crypto vault asset Act K chainId head bs head') :
    (head'.world.sload vault 2#256).toNat = ∑ a : Address,
        (head'.world.sload vault (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat ∧
      (head'.world.sload asset 2#256).toNat = ∑ a : Address,
        (head'.world.sload asset (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat :=
  (follows_coveredChain hk hs hinv hP hc (follows_refl hdep)).supply_eq_sum hs hinv

/-- **Solvency along a chain of valid blocks**: `Σₐ ⌊shares[a]·T/S⌋ ≤ T`, read from storage. -/
theorem solvent_coveredChain
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) (hP : ¬ Prot vault asset systemAddress) {chainId : Nat}
    {head head' : ChainHead} {bs : List (Nat × Fork × BlockEnv)}
    (hdep : Deployed head.world vault asset) (hinv : Solmate.Inv (abs crypto head.world vault asset))
    (hc : CoveredChain crypto vault asset Act K chainId head bs head') :
    ∑ a : Address, sharesAt crypto head'.world vault a * assetsAt crypto head'.world vault asset /
        supplyAt head'.world vault ≤ assetsAt crypto head'.world vault asset :=
  (follows_coveredChain hk hs hinv hP hc (follows_refl hdep)).solvent hs hinv

/-- **Price monotonicity along a chain of valid blocks** whose committed calls `cs` are user
operations: unless a prefix of `cs` empties the vault, `T/S` never decreased. -/
theorem price_mono_coveredChain
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) (hP : ¬ Prot vault asset systemAddress) {chainId : Nat}
    {head head' : ChainHead} {bs : List (Nat × Fork × BlockEnv)}
    (hdep : Deployed head.world vault asset) (hinv : Solmate.Inv (abs crypto head.world vault asset))
    (hc : CoveredChain crypto vault asset Act (fun c => UserOp vault c.op) chainId head bs head') :
    ∃ cs : List VCall, (∀ c ∈ cs, (∀ a ∈ c.actors, a ∈ Act) ∧ UserOp vault c.op) ∧
      ((∀ k ≤ cs.length,
          (Solmate.exec (abs crypto head.world vault asset) ((cs.take k).map VCall.op)).totalSupply
            ≠ 0) →
        (assetsAt crypto head.world vault asset : ℚ) / supplyAt head.world vault ≤
          (assetsAt crypto head'.world vault asset : ℚ) / supplyAt head'.world vault) :=
  (follows_coveredChain hk hs hinv hP hc (follows_refl hdep)).price_mono hinv

end Verified.Solmate.ERC4626.Nested
