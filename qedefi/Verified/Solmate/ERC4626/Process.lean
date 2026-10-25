import Verified.Solmate.ERC4626.LowGas.AnyGas
import Verified.Solmate.ERC4626.Nested.Invariants7702
import EvmLogic.Tx.Lift

/-!
# The vault invariants after whole transactions, EIP-7702 included

The trace theorems of `Nested.Invariants`, `Nested.Invariants7702` and `LowGas.AnyGas` run over
top-level `processMessageCall`s and *assumed* environment steps (`EnvStep`: anything keeping the
vault's and the asset's storage and code), which stood for the rest of a transaction (nonce,
fee purchase, refund, coinbase reward, `SELFDESTRUCT` deletions, EIP-161 clean-up). Here the
step is the real transaction function `EvmLean.Tx.process`, any type (EIP-7702 included), and
nothing about it is assumed:

* the **prefix** (`txWorld`: nonce incremented, fees debited) keeps storage and code of every
  account (`EvmLogic.Tx.keep_prefixWorld`);
* the **message** (`txMsg`, in `txContext`) is `TopOk` because `check` enforces EIP-3607 and the
  vault and the asset hold real code (`topOk_prepareMessage`), its gas is below `2⁶⁴` (from
  Osaka by EIP-7825, otherwise from the block gas limit, see `GasCapped`), and it keeps
  `Follows` given the coverage of its vault/asset frames;
* the **suffix** keeps storage and code of every account holding code that the message did not
  self-destruct, and the message never self-destructs the vault or the asset
  (`processMessageCall_realCode`, `keep_suffixWorld`).

The coverage hypothesis is the message-level one (`TxOkAnyGas`, or `TxOk` with
`minGas ≥ 250000`), stated for the transaction's own message in its own prefix world
(`TxCoveredAnyGas`, `TxCovered`). `ProcessTrace` is a sequence of such transactions — a
sub-relation of `EvmLogic.Tx.Steps` (`ProcessTrace.steps`) with **no other transition**: the
headline theorems `*_processTrace` hold with no environment step at all.
-/

namespace Verified.Solmate.ERC4626.Nested
open Verified.Solmate.ERC20 QEDefi.ERC4626 QEDefi.Trace
open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts
open QEDefi.Math QEDefi.ERC20 QEDefi.ERC4626.Solmate QEDefi.Trace.Lift
open Verified.Solmate.ERC4626.Invariants Verified.Solmate.ERC4626.LowGas
open EvmLean.Tx (Checked IntrinsicGas TxOutput validate check process prepareMessage
  txMaxGasLimit)
open EvmLogic.Tx (prefixWorld txContext upfrontFee)
open EvmLogic.Program.Nested (Keep KeepP GoodOk DangerStart Danger TopOk Reaches)

variable {crypto : Crypto} {vault asset : Address} {Act : List Address} {K : VCall → Prop}
  {minGas : Nat}

/-! ## The message of a transaction -/

/-- The world in which transaction `tx`, checked as `c` from world `w`, runs its message: the
sender's nonce incremented and the upfront fees debited (`EvmLogic.Tx.prefixWorld`). -/
def txWorld (fork : Fork) (env : BlockEnv) (w : World) (tx : Transaction) (c : Checked) : World :=
  prefixWorld w c.sender
    (BitVec.ofNat 256 ((w.account c.sender).balance.toNat - upfrontFee fork env tx c))

/-- The top-level message of transaction `tx`, checked as `c` with intrinsic gas `i`, from
world `w` (`EvmLean.Tx.prepareMessage` in the prefix world). -/
def txMsg (crypto : Crypto) (fork : Fork) (env : BlockEnv) (w : World) (tx : Transaction)
    (c : Checked) (i : IntrinsicGas) : Message :=
  prepareMessage crypto fork env (txWorld fork env w tx c) tx c.sender (w.account c.sender).nonce
    (tx.gas - i.regular)

/-- **The gas bound of a transaction's message**: from Osaka EIP-7825 caps every transaction's
gas at `2²⁴`; before Osaka nothing in `validate`/`check` bounds `tx.gas` except the block gas
still available (`gasAvail`), which a valid block keeps below `2⁶³` (EIP-1985, see
`Verified.Solmate.ERC4626.Nested.gasLimit_envOf_le`). -/
def GasCapped (fork : Fork) (gasAvail : Nat) : Prop := fork ≥ .osaka ∨ gasAvail < 2 ^ 64

theorem txMsg_gas_lt {fork : Fork} {env : BlockEnv} {gasAvail blobAvail : Nat} {w : World}
    {tx : Transaction} {hint : Option Address} {i : IntrinsicGas} {c : Checked}
    (hgas : GasCapped fork gasAvail) (hv : validate fork tx = .ok i)
    (hc : check crypto fork env gasAvail blobAvail w tx hint = .ok c) :
    (txMsg crypto fork env w tx c i).gas < 2 ^ 64 := by
  simp only [txMsg, EvmLogic.Tx.prepareMessage_gas]
  have h1 := (EvmLogic.Tx.check_ok hc).2.2.2.2.2.2
  rcases hgas with ho | hg
  · have := (EvmLogic.Tx.validate_ok hv).2.2.2 ho
    simp only [txMaxGasLimit] at this
    omega
  · omega

/-- The vault and the asset hold real code (non-empty, not an EIP-7702 designator) in every
world `Follows` relates. -/
theorem realCode_of_follows {w₀ w : World} (hw : Follows crypto vault asset Act K w₀ w) :
    ∀ p, Prot vault asset p → EvmLogic.Tx.RealCode (w.code p) := fun p hp =>
  EvmLogic.Tx.realCode_of_deleg (goodOk.code w hw p hp) (goodOk.deleg w hw p hp)

/-! ## One transaction -/

/-- **A transaction keeps `Follows` when its message does.** If the top-level message of a
successful transaction keeps `Follows` from its prefix world (`hmsg`, given that it is `TopOk`
and has less than `2⁶⁴` gas), the transaction keeps `Follows`: the prefix and the suffix keep
the storage and code of the vault and the asset. -/
theorem follows_process_of {w₀ w : World} (hw : Follows crypto vault asset Act K w₀ w)
    {fuel : Nat} {fork : Fork} {env : BlockEnv} {gasAvail blobAvail : Nat} {tx : Transaction}
    {hint : Option Address} {out : TxOutput} (hgas : GasCapped fork gasAvail)
    (hmsg : ∀ (i : IntrinsicGas) (c : Checked) (r : MessageResult), validate fork tx = .ok i →
      check crypto fork env gasAvail blobAvail w tx hint = .ok c →
      Follows crypto vault asset Act K w₀ (txWorld fork env w tx c) →
      TopOk (Prot vault asset) (txWorld fork env w tx c) (txMsg crypto fork env w tx c i) →
      (txMsg crypto fork env w tx c i).gas < 2 ^ 64 →
      processMessageCall fuel (txContext crypto fork env tx c) (txWorld fork env w tx c) ∅
        (txMsg crypto fork env w tx c i) = .ok r →
      Follows crypto vault asset Act K w₀ r.world)
    (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    Follows crypto vault asset Act K w₀ out.world := by
  obtain ⟨i, c, r, gu, hv, hc, hr, -, hout, -, -⟩ := EvmLogic.Tx.process_ok h
  have hreal := realCode_of_follows hw
  have h1 : Follows crypto vault asset Act K w₀ (txWorld fork env w tx c) :=
    goodOk.keep _ _ hw fun p _ => EvmLogic.Tx.keep_prefixWorld w c.sender _ p
  have htop : TopOk (Prot vault asset) (txWorld fork env w tx c) (txMsg crypto fork env w tx c i) :=
    EvmLogic.Tx.topOk_prepareMessage hreal hc _ _ _
  have h2 := hmsg i c r hv hc h1 htop (txMsg_gas_lt hgas hv hc) hr
  rw [hout]
  refine goodOk.keep _ _ h2 fun p hp => ?_
  have hreal1 : EvmLogic.Tx.RealCode ((txWorld fork env w tx c).code p) := by
    simp only [txWorld, EvmLogic.Tx.code_prefixWorld]; exact hreal p hp
  obtain ⟨hd, hs⟩ := EvmLogic.Tx.processMessageCall_realCode hr hreal1
  exact EvmLogic.Tx.keep_suffixWorld hs hd _ _ _ _

/-- **The environment steps around a transaction's message are derived, not assumed**: from a
world where the vault and the asset are deployed, a successful transaction is an `EnvStep`
(its prefix), its top-level message call from the prefix world, and an `EnvStep` (its suffix:
refund, coinbase reward, `SELFDESTRUCT` deletions, EIP-161 clean-up). -/
theorem process_envSteps {w : World} (hdep : Deployed w vault asset) {fuel : Nat} {fork : Fork}
    {env : BlockEnv} {gasAvail blobAvail : Nat} {tx : Transaction} {hint : Option Address}
    {out : TxOutput} (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    ∃ (i : IntrinsicGas) (c : Checked) (r : MessageResult), validate fork tx = .ok i ∧
      check crypto fork env gasAvail blobAvail w tx hint = .ok c ∧
      EnvStep vault asset w (txWorld fork env w tx c) ∧
      processMessageCall fuel (txContext crypto fork env tx c) (txWorld fork env w tx c) ∅
        (txMsg crypto fork env w tx c i) = .ok r ∧
      EnvStep vault asset r.world out.world := by
  obtain ⟨i, c, r, gu, hv, hc, hr, -, hout, -, -⟩ := EvmLogic.Tx.process_ok h
  have hreal := realCode_of_follows (crypto := crypto) (Act := []) (K := fun _ => True)
    (follows_refl hdep)
  have env_of : ∀ {w w' : World}, (∀ p, Prot vault asset p → Keep p w w') →
      EnvStep vault asset w w' := fun hk =>
    ⟨(hk vault (.inl rfl)).sload, (hk asset (.inr rfl)).sload, (hk vault (.inl rfl)).code,
      (hk asset (.inr rfl)).code⟩
  refine ⟨i, c, r, hv, hc, env_of fun p _ => EvmLogic.Tx.keep_prefixWorld w c.sender _ p, hr, ?_⟩
  rw [hout]
  refine env_of fun p hp => ?_
  have hreal1 : EvmLogic.Tx.RealCode ((txWorld fork env w tx c).code p) := by
    simp only [txWorld, EvmLogic.Tx.code_prefixWorld]; exact hreal p hp
  obtain ⟨hd, hs⟩ := EvmLogic.Tx.processMessageCall_realCode hr hreal1
  exact EvmLogic.Tx.keep_suffixWorld hs hd _ _ _ _

/-- **One message covered at any gas keeps `Follows`**, any fork, EIP-7702 authorizations
included: `follows_tx_anyGas` without `hdeleg`. -/
theorem follows_tx_anyGas_7702
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (hw : Follows crypto vault asset Act K w₀ w) {ctx : Context} {tr : TransientStorage}
    {msg : Message} {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hmsg : TopOk (Prot vault asset) w msg) (hgas : msg.gas < 2 ^ 64)
    (hok : TxOkAnyGas vault asset Act K ctx w tr msg)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    Follows crypto vault asset Act K w₀ r.world := by
  refine processMessageCall_follows_7702 hs hinv hw hmsg (le_refl _) (fun m hm hd hp => ?_) hr
  have hv := DangerStart.vaultStart hd
  have hwm : Follows crypto vault asset Act K w₀ m.world := goodOk.keep _ _ hd.snapshot hd.keep
  have hcr' : m.ctx.crypto = crypto := by rw [hm.ctx]; exact hcr
  obtain ⟨ko, ks, hf⟩ := hd.fresh
  have hkind : m.frame.kind = .call ko ks := by rw [hf]; rfl
  obtain ⟨hcov, hadm⟩ := hok m hm hv hp
  exact frameOk_of_coveredAnyGas hk hs hv hkind hwm.1 (hwm.inv hs hinv) hcr'
    (DangerStart.gasLt hd hgas) hcov (hcr ▸ hadm)

/-- **A transaction covered at any gas**: the top-level message of `tx` from `w` (checked as
`c`, intrinsic gas `i`), in its prefix world and context, is `TxOkAnyGas` — every vault/asset
frame it reaches from other code is covered at any gas and commits admitted model calls. Since
`validate` and `check` are functions, the quantifiers range over the one pair a successful
transaction has. -/
def TxCoveredAnyGas (vault asset : Address) (Act : List Address) (K : VCall → Prop)
    (crypto : Crypto) (fork : Fork) (env : BlockEnv) (gasAvail blobAvail : Nat) (w : World)
    (tx : Transaction) (hint : Option Address) : Prop :=
  ∀ (i : IntrinsicGas) (c : Checked), validate fork tx = .ok i →
    check crypto fork env gasAvail blobAvail w tx hint = .ok c →
    TxOkAnyGas vault asset Act K (txContext crypto fork env tx c) (txWorld fork env w tx c) ∅
      (txMsg crypto fork env w tx c i)

/-- **A transaction covered with `minGas`**: `TxCoveredAnyGas` with `TxOk` (every vault/asset
frame has at least `minGas` gas) instead of `TxOkAnyGas`. -/
def TxCovered (vault asset : Address) (minGas : Nat) (Act : List Address) (K : VCall → Prop)
    (crypto : Crypto) (fork : Fork) (env : BlockEnv) (gasAvail blobAvail : Nat) (w : World)
    (tx : Transaction) (hint : Option Address) : Prop :=
  ∀ (i : IntrinsicGas) (c : Checked), validate fork tx = .ok i →
    check crypto fork env gasAvail blobAvail w tx hint = .ok c →
    TxOk vault asset minGas Act K (txContext crypto fork env tx c) (txWorld fork env w tx c) ∅
      (txMsg crypto fork env w tx c i)

/-- Every transaction covered with `minGas ≥ 250000` is covered at any gas. -/
theorem TxCovered.anyGas (hmin : 250000 ≤ minGas) {fork : Fork} {env : BlockEnv}
    {gasAvail blobAvail : Nat} {w : World} {tx : Transaction} {hint : Option Address}
    (h : TxCovered vault asset minGas Act K crypto fork env gasAvail blobAvail w tx hint) :
    TxCoveredAnyGas vault asset Act K crypto fork env gasAvail blobAvail w tx hint :=
  fun i c hv hc => txOkAnyGas_of_txOk hmin (h i c hv hc)

/-- **One transaction covered at any gas keeps `Follows`**: any successful `Tx.process` (any
type, EIP-7702 authorizations included; any fork, block, sender, fees, value, calldata and
fuel) from a world `Follows` relates, whose message is covered (`TxCoveredAnyGas`) and has a
capped gas (`GasCapped`: from Osaka always; before, the block gas still available is below
`2⁶⁴`). Nothing about the rest of the transaction is assumed. -/
theorem follows_process_anyGas
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (hw : Follows crypto vault asset Act K w₀ w) {fuel : Nat} {fork : Fork} {env : BlockEnv}
    {gasAvail blobAvail : Nat} {tx : Transaction} {hint : Option Address} {out : TxOutput}
    (hgas : GasCapped fork gasAvail)
    (hcov : TxCoveredAnyGas vault asset Act K crypto fork env gasAvail blobAvail w tx hint)
    (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    Follows crypto vault asset Act K w₀ out.world :=
  follows_process_of hw hgas (fun i c _ hv hc h1 htop hg hr =>
    follows_tx_anyGas_7702 hk hs hinv h1 rfl htop hg (hcov i c hv hc) hr) h

/-- **One covered transaction keeps `Follows`** (`follows_process_anyGas` with `TxCovered` and
`minGas ≥ 250000`). -/
theorem follows_process (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (hw : Follows crypto vault asset Act K w₀ w) {fuel : Nat} {fork : Fork} {env : BlockEnv}
    {gasAvail blobAvail : Nat} {tx : Transaction} {hint : Option Address} {out : TxOutput}
    (hgas : GasCapped fork gasAvail)
    (hcov : TxCovered vault asset minGas Act K crypto fork env gasAvail blobAvail w tx hint)
    (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    Follows crypto vault asset Act K w₀ out.world :=
  follows_process_of hw hgas (fun i c _ hv hc h1 htop hg hr =>
    follows_tx_7702 hmin hk hs hinv h1 rfl htop hg (hcov i c hv hc) hr) h

/-! ## Sequences of transactions -/

/-- **One covered transaction**, executed by the real transaction function with the vault's
hash functions `crypto`: any fuel, fork, block, gas and blob gas available (gas capped,
`GasCapped`), any transaction and sender hint, covered at any gas (`TxCoveredAnyGas`). -/
inductive ProcessStep (crypto : Crypto) (vault asset : Address) (Act : List Address)
    (K : VCall → Prop) : World → World → Prop
  | tx {fuel : Nat} {fork : Fork} {env : BlockEnv} {gasAvail blobAvail : Nat} {w : World}
      {tx : Transaction} {hint : Option Address} {out : TxOutput} :
      GasCapped fork gasAvail →
      TxCoveredAnyGas vault asset Act K crypto fork env gasAvail blobAvail w tx hint →
      process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out →
      ProcessStep crypto vault asset Act K w out.world

/-- **Sequences of covered transactions**, and nothing else. -/
def ProcessTrace (crypto : Crypto) (vault asset : Address) (Act : List Address)
    (K : VCall → Prop) : World → World → Prop :=
  Relation.ReflTransGen (ProcessStep crypto vault asset Act K)

/-- A covered transaction is a successful transaction (`EvmLogic.Tx.Step`). -/
theorem ProcessStep.step {w w' : World} (h : ProcessStep crypto vault asset Act K w w') :
    EvmLogic.Tx.Step w w' := by
  obtain ⟨_, _, h⟩ := h
  exact ⟨_, _, _, _, _, _, _, _, _, h, rfl⟩

/-- **A `ProcessTrace` is a sequence of successful transactions** (`EvmLogic.Tx.Steps`): no
transition other than `Tx.process`. -/
theorem ProcessTrace.steps {w w' : World} (h : ProcessTrace crypto vault asset Act K w w') :
    EvmLogic.Tx.Steps w w' := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih => exact .tail ih hs.step

/-- A transaction covered with `minGas ≥ 250000` is a `ProcessStep`. -/
theorem ProcessStep.of_covered (hmin : 250000 ≤ minGas) {fuel : Nat} {fork : Fork}
    {env : BlockEnv} {gasAvail blobAvail : Nat} {w : World} {tx : Transaction}
    {hint : Option Address} {out : TxOutput} (hgas : GasCapped fork gasAvail)
    (hcov : TxCovered vault asset minGas Act K crypto fork env gasAvail blobAvail w tx hint)
    (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    ProcessStep crypto vault asset Act K w out.world :=
  .tx hgas (hcov.anyGas hmin) h

/-- **Every sequence of covered transactions keeps `Follows`.** -/
theorem follows_processTrace
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : ProcessTrace crypto vault asset Act K w₀ w) :
    Follows crypto vault asset Act K w₀ w := by
  induction htr with
  | refl => exact follows_refl hdep
  | tail _ hst ih =>
    obtain ⟨hgas, hcov, h⟩ := hst
    exact follows_process_anyGas hk hs hinv ih hgas hcov h

/-! ## Consequences of `Follows` -/

section Consequences
variable {w₀ w : World}

theorem Follows.lift (hs : SlotsOk crypto vault Act)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) (h : Follows crypto vault asset Act K w₀ w) :
    Deployed w vault asset ∧ Solmate.Inv (abs crypto w vault asset) ∧
      ∃ cs : List VCall, (∀ c ∈ cs, Admitted Act K c) ∧
        AgreeOn (ActorPairs Act) (abs crypto w vault asset)
          (Solmate.exec (abs crypto w₀ vault asset) (cs.map VCall.op)) :=
  ⟨h.1, h.inv hs hinv, h.2⟩

theorem Follows.invariant
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) (h : Follows crypto vault asset Act K w₀ w)
    {I : State Address → Prop} (hI : ∀ s op s', Solmate.Inv s → I s → step s op = some s' → I s')
    (hIa : ∀ s t, AgreeOn (ActorPairs Act) s t → I s → I t) (hI₀ : I (abs crypto w₀ vault asset)) :
    I (abs crypto w vault asset) := by
  obtain ⟨-, cs, -, ha⟩ := h
  have := (exec_induction (step := step) (Inv := Solmate.Inv) (fun _ _ _ hi h => Inv_step hi h)
    hI hinv hI₀ (cs.map VCall.op)).2
  rw [← exec_eq] at this
  exact hIa _ _ ha.symm this

theorem Follows.supply_eq_sum (hs : SlotsOk crypto vault Act)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) (h : Follows crypto vault asset Act K w₀ w) :
    (w.sload vault 2#256).toNat =
        ∑ a : Address, (w.sload vault (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat ∧
      (w.sload asset 2#256).toNat =
        ∑ a : Address, (w.sload asset (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat := by
  have hi := h.inv hs hinv
  exact ⟨supply_eq_sum_of_wf hi.2, supply_eq_sum_of_wf hi.1⟩

theorem Follows.solvent (hs : SlotsOk crypto vault Act)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) (h : Follows crypto vault asset Act K w₀ w) :
    ∑ a : Address, sharesAt crypto w vault a * assetsAt crypto w vault asset / supplyAt w vault ≤
      assetsAt crypto w vault asset := by
  have := Solmate.solvent _ (h.inv hs hinv)
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp)] at this
  simpa only [abs_sharesOf, abs_totalAssets', abs_totalSupply'] using this

theorem Follows.price_mono (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (h : Follows crypto vault asset Act (fun c => UserOp vault c.op) w₀ w) :
    ∃ cs : List VCall, (∀ c ∈ cs, (∀ a ∈ c.actors, a ∈ Act) ∧ UserOp vault c.op) ∧
      ((∀ k ≤ cs.length,
          (Solmate.exec (abs crypto w₀ vault asset) ((cs.take k).map VCall.op)).totalSupply ≠ 0) →
        (assetsAt crypto w₀ vault asset : ℚ) / supplyAt w₀ vault ≤
          (assetsAt crypto w vault asset : ℚ) / supplyAt w vault) := by
  obtain ⟨-, cs, hcs, ha⟩ := h
  refine ⟨cs, hcs, fun hS => ?_⟩
  have hmodel := price_exec_mono (s := abs crypto w₀ vault asset) hinv
    (ops := cs.map VCall.op) (fun op hop => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hop
      exact (hcs c hc).2) (fun k hk' => by
        have := hS k (by simpa using hk')
        rw [exec_eq, List.map_take] at this
        exact this)
  rw [exec_eq] at ha
  have hp := ha.price
  unfold State.price at hp hmodel
  rw [abs_totalAssets', abs_totalSupply'] at hp hmodel
  rw [hp]; exact hmodel

end Consequences

/-! ## Headline theorems -/

/-- **The lifting theorem for sequences of whole transactions.** After any sequence of
successful transactions (`Tx.process`, any type, EIP-7702 included), each covered at any gas,
from a deployed world with well-formed ledgers: deployed, well formed, and `abs` agrees (up to
non-actor allowances) with the model's execution of the admitted calls they committed. No
environment step. -/
theorem lift_processTrace
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : ProcessTrace crypto vault asset Act K w₀ w) :
    Deployed w vault asset ∧ Solmate.Inv (abs crypto w vault asset) ∧
      ∃ cs : List VCall, (∀ c ∈ cs, Admitted Act K c) ∧
        AgreeOn (ActorPairs Act) (abs crypto w vault asset)
          (Solmate.exec (abs crypto w₀ vault asset) (cs.map VCall.op)) :=
  (follows_processTrace hk hs hdep hinv htr).lift hs hinv

/-- **Invariants transfer, for sequences of whole transactions**: every model invariant
preserved by every successful step and insensitive to non-actor allowances holds. -/
theorem invariant_processTrace
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {I : State Address → Prop}
    (hI : ∀ s op s', Solmate.Inv s → I s → step s op = some s' → I s')
    (hIa : ∀ s t, AgreeOn (ActorPairs Act) s t → I s → I t)
    {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : ProcessTrace crypto vault asset Act K w₀ w) (hI₀ : I (abs crypto w₀ vault asset)) :
    I (abs crypto w vault asset) :=
  (follows_processTrace hk hs hdep hinv htr).invariant hinv hI hIa hI₀

/-- **`totalSupply` = Σ `balanceOf`, for sequences of whole transactions**, for the shares and
for the asset, read from storage. -/
theorem supply_eq_sum_processTrace
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : ProcessTrace crypto vault asset Act K w₀ w) :
    (w.sload vault 2#256).toNat =
        ∑ a : Address, (w.sload vault (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat ∧
      (w.sload asset 2#256).toNat =
        ∑ a : Address, (w.sload asset (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat :=
  (follows_processTrace hk hs hdep hinv htr).supply_eq_sum hs hinv

/-- **Solvency, for sequences of whole transactions**: `Σₐ ⌊shares[a]·T/S⌋ ≤ T`, read from
storage. -/
theorem solvent_processTrace
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : ProcessTrace crypto vault asset Act K w₀ w) :
    ∑ a : Address, sharesAt crypto w vault a * assetsAt crypto w vault asset / supplyAt w vault ≤
      assetsAt crypto w vault asset :=
  (follows_processTrace hk hs hdep hinv htr).solvent hs hinv

/-- **Price monotonicity, for sequences of whole transactions** whose committed calls `cs` are
user operations: unless a prefix of `cs` empties the vault, `T/S` never decreased. -/
theorem price_mono_processTrace
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : ProcessTrace crypto vault asset Act (fun c => UserOp vault c.op) w₀ w) :
    ∃ cs : List VCall, (∀ c ∈ cs, (∀ a ∈ c.actors, a ∈ Act) ∧ UserOp vault c.op) ∧
      ((∀ k ≤ cs.length,
          (Solmate.exec (abs crypto w₀ vault asset) ((cs.take k).map VCall.op)).totalSupply ≠ 0) →
        (assetsAt crypto w₀ vault asset : ℚ) / supplyAt w₀ vault ≤
          (assetsAt crypto w vault asset : ℚ) / supplyAt w vault) :=
  (follows_processTrace hk hs hdep hinv htr).price_mono hinv

/-- **`totalSupply` = Σ `balanceOf` after one whole transaction** covered at any gas. -/
theorem supply_eq_sum_process
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) {fuel : Nat} {fork : Fork} {env : BlockEnv}
    {gasAvail blobAvail : Nat} {tx : Transaction} {hint : Option Address} {out : TxOutput}
    (hgas : GasCapped fork gasAvail)
    (hcov : TxCoveredAnyGas vault asset Act K crypto fork env gasAvail blobAvail w₀ tx hint)
    (h : process fuel crypto fork env gasAvail blobAvail w₀ tx hint = .ok out) :
    (out.world.sload vault 2#256).toNat = ∑ a : Address,
        (out.world.sload vault (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat ∧
      (out.world.sload asset 2#256).toNat = ∑ a : Address,
        (out.world.sload asset (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat :=
  (follows_process_anyGas hk hs hinv (follows_refl (K := K) hdep) hgas hcov h).supply_eq_sum
    hs hinv

/-- **Solvency after one whole transaction** covered at any gas. -/
theorem solvent_process
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) {fuel : Nat} {fork : Fork} {env : BlockEnv}
    {gasAvail blobAvail : Nat} {tx : Transaction} {hint : Option Address} {out : TxOutput}
    (hgas : GasCapped fork gasAvail)
    (hcov : TxCoveredAnyGas vault asset Act K crypto fork env gasAvail blobAvail w₀ tx hint)
    (h : process fuel crypto fork env gasAvail blobAvail w₀ tx hint = .ok out) :
    ∑ a : Address, sharesAt crypto out.world vault a * assetsAt crypto out.world vault asset /
        supplyAt out.world vault ≤ assetsAt crypto out.world vault asset :=
  (follows_process_anyGas hk hs hinv (follows_refl (K := K) hdep) hgas hcov h).solvent hs hinv

end Verified.Solmate.ERC4626.Nested
