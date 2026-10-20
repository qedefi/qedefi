import Examples.Solmate.ERC4626.LowGas.Targets
import EvmLogic.AbsInt.Code
import EvmLogic.GasMono.Depth

/-!
# The invariants for arbitrary transactions, at any gas

The headline theorems of `NestedInvariants.lean` (`follows_tx`, `lift_any_tx`, …) ask every
frame of the vault or the asset that other code starts to be covered with at least
`minGas ≥ 250000` gas. With the gas-monotonicity of both codes (`LowGasFrames.lean`) and its
call-target premises discharged by the certified abstract interpreter (`LowGasTargets.lean`:
`assetCallsPrecompile`, `vaultCallsAsset`), **the gas requirement is gone**: a frame with any
gas is covered as soon as it would be covered with more (`CoveredAnyGas`): a successful
low-gas frame commits exactly what the high-gas frame commits.

* `CoveredAnyGas vault asset m`: `Covered` with its own gas (≥ 250000), or `0x01` not
  EIP-7702-delegated (`EcrecoverOk`, always true before Prague) and covered with some gas
  `G` between its own and `2⁶⁴` (`CoveredAtSomeGas`). `coveredAnyGas_of` gives a gas-free
  sufficient condition: value (any gas), or no value, room for one more call level for the
  vault, calldata below `2⁶⁴` bytes, and `CoverOkAnyGas` (the `name`/`symbol` getter's gas
  fits 64 bits, `DomainOk` for `DOMAIN_SEPARATOR()`, `PermitFrame` for `permit`).
* `TxOkAnyGas`: `TxOk` with `CoveredAnyGas` (no `minGas`); `txOkAnyGas_of_txOk`: every
  transaction covered in the old sense (`minGas ≥ 250000`) is covered.
* The headline theorems without `hmin`: `follows_tx_anyGas`, `follows_trace_anyGas`,
  `lift_any_tx_anyGas`, `lift_nested_anyGas`, `invariant_any_tx_anyGas`,
  `invariant_nested_anyGas`, `supply_eq_sum_any_tx_anyGas`, `supply_eq_sum_nested_anyGas`,
  `solvent_any_tx_anyGas`, `solvent_nested_anyGas`, `price_mono_any_tx_anyGas`,
  `price_mono_nested_anyGas`, over `TxTraceAnyGas`. The old statements (`Examples.Solmate.ERC4626.Nested.Invariants`)
  keep their names and proofs; they are special cases (`txTraceAnyGas_of_txTrace`).
-/

namespace Examples.Solmate.ERC4626.LowGas
open Examples.Solmate.ERC20 Defi.ERC4626 Defi.Trace

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity Examples.Solmate.Contracts EvmLogic.GasMono
open EvmLogic.Solidity EvmLogic.Tactic
open EvmLogic.Program.Nested (bump Reaches Danger DangerStart TopOk)
open Defi.ERC4626 Defi.Math Defi.ERC20 Defi.ERC4626.Solmate Defi.Trace.Lift
open Examples.Solmate.ERC4626.Nested Examples.Solmate.ERC4626.Invariants Defi.ERC4626

variable {crypto : Crypto} {vault asset : Address} {Act : List Address} {K : VCall → Prop}

/-! ## The depth limit -/

/-- `VaultStart` survives changing the depth. -/
theorem _root_.Examples.Solmate.ERC4626.Nested.VaultStart.setDepth {m : Machine}
    (hv : VaultStart vault asset m) (d : Nat) : VaultStart vault asset (setDepth d m) := by
  obtain ⟨msg, k, s, hf, hc⟩ := hv.fresh
  refine ⟨⟨{ msg with depth := d }, k, s, ?_, hc⟩, hv.static, hv.prot, hv.pre, hv.caller⟩
  simp only [GasMono.setDepth, hf, Frame.init]

/-- The admitted calls of a frame only depend on its caller, account and calldata. -/
theorem _root_.Examples.Solmate.ERC4626.Nested.FrameAdmitted.congr {m m' : Machine}
    (h : FrameAdmitted crypto vault asset Act K m) (hc : m'.frame.msg.caller = m.frame.msg.caller)
    (ht : m'.frame.msg.currentTarget = m.frame.msg.currentTarget)
    (hd : m'.frame.msg.data = m.frame.msg.data) : FrameAdmitted crypto vault asset Act K m' := by
  refine ⟨fun c hx => h.calls c ⟨hc ▸ hx.caller, ht ▸ hx.target, hd ▸ hx.data⟩,
    fun c hx => h.permits c ?_⟩
  cases c <;> simp only [PermitData] at hx ⊢ <;> rw [ht, hd] at hx <;> exact hx

/-- **A frame summary transfers to the call-depth limit and any lower gas**: for a frame of the
vault or the asset at depth 1024, `FrameOk` of the same frame with gas `G` at another depth (at
the top level) gives `FrameOk` of the frame. Every call of a frame at the limit fails, and a
failed call makes the frame fail (`depth_lockstep`). -/
theorem frameOk_of_depth {m : Machine} (hv : VaultStart vault asset m)
    (hdep : Deployed m.world vault asset) (hnd : EcrecoverOk m) {ko ks : Nat}
    (hk : m.frame.kind = .call ko ks) (hd : Gas.stackDepthLimit < m.frame.msg.depth + 1) {G : Nat}
    (hG : m.frame.gasLeft ≤ G) (hG' : G < 2 ^ 256) {d' : Nat}
    (h : FrameOk crypto vault asset Act K (setDepth d' (topBump G m))) :
    FrameOk crypto vault asset Act K m := by
  refine frameOk_of_topBump assetCallsPrecompile (vaultCallsAsset vault asset) hv hdep hnd hk hG hG'
    ?_
  let P : World → Prop := fun w => Deployed w vault asset ∧ ∃ cs : List VCall,
    (∀ c ∈ cs, Admitted Act K c) ∧ AgreeOn (ActorPairs Act) (abs crypto w vault asset)
      (Solmate.exec (abs crypto m.world vault asset) (cs.map VCall.op))
  have h' : Halts (setDepth d' (topBump G m)) (fun mf o => ∀ out, o = .success out → P mf.world) :=
    h
  show Halts (topBump G m) (fun mf o => ∀ out, o = .success out → P mf.world)
  rcases high_of_vaultStart hv hdep hnd hG hG' with ⟨i, hi⟩ | ⟨ia, hi⟩
  · exact halts_world_of_depth (vault_codeOk i) rfl hi.code (hi.jd.trans (by rw [hi.code]))
      (by rw [hi.pc]; exact pcOk_zero (vault_codeOk i).region) hd hk h'
  · exact halts_world_of_depth (asset_codeOk ia) rfl hi.code (hi.jd.trans (by rw [hi.code]))
      (by rw [hi.pc]; exact pcOk_zero (asset_codeOk ia).region) hd hk h'

/-- **Covered at the depth limit**: a frame at depth 1024 that, with some more gas below `2⁶⁴`
and one level up, would be covered. -/
def CoveredAtLimit (vault asset : Address) (m : Machine) : Prop :=
  Gas.stackDepthLimit < m.frame.msg.depth + 1 ∧ ∃ G, m.frame.gasLeft ≤ G ∧ G < 2 ^ 64 ∧
    Covered vault asset 250000 (setDepth (Gas.stackDepthLimit - 1) (topBump G m))

/-! ## Frames covered at any gas -/

/-- **A frame covered at any gas**: covered with its own gas, or (with `0x01` not delegated)
covered with some more gas below `2⁶⁴` (`CoveredAtSomeGas`), or at the depth limit and covered
one level up with some more gas (`CoveredAtLimit`). -/
def CoveredAnyGas (vault asset : Address) (m : Machine) : Prop :=
  Covered vault asset 250000 m ∨
    (EcrecoverOk m ∧ (CoveredAtSomeGas vault asset 250000 m ∨ CoveredAtLimit vault asset m))

/-- **The frame summary of a frame covered at any gas.** -/
theorem frameOk_of_coveredAnyGas
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {m : Machine} (hv : VaultStart vault asset m)
    {ko ks : Nat} (hkind : m.frame.kind = .call ko ks)
    (hdep : Deployed m.world vault asset) (hinv : Solmate.Inv (abs crypto m.world vault asset))
    (hcr : m.ctx.crypto = crypto) (hlt : m.frame.gasLeft < 2 ^ 64)
    (hc : CoveredAnyGas vault asset m) (hadm : FrameAdmitted crypto vault asset Act K m) :
    FrameOk crypto vault asset Act K m := by
  rcases hc with hc | ⟨hnd, hc | ⟨hd, G, hG, hG64, hc⟩⟩
  · exact frameOk_of_covered (le_refl _) hk hs hv hdep hinv hcr hlt hc hadm
  · exact frameOk_of_coveredAtSomeGas assetCallsPrecompile (vaultCallsAsset vault asset)
      (le_refl _) hk hs hv hkind hdep hinv hcr hnd hc hadm
  · refine frameOk_of_depth (d' := Gas.stackDepthLimit - 1) hv hdep hnd hkind hd hG
      (Nat.lt_of_lt_of_le hG64 (by decide)) ?_
    have hgas : (setDepth (Gas.stackDepthLimit - 1) (topBump G m)).frame.gasLeft < 2 ^ 64 := by
      show (topBump G m).frame.gasLeft < 2 ^ 64
      simp only [topBump, bump_frame, bumpF]; omega
    exact frameOk_of_covered (le_refl _) hk hs ((hv.topBump hG).setDepth _) hdep hinv hcr hgas hc
      (hadm.congr rfl rfl rfl)

/-- The conditions of `CoverOk` that do not depend on the gas: the getter of a stored string
needs less than `2⁶⁴` gas, `DOMAIN_SEPARATOR()` is a covered case, `permit` has its frame
conditions. -/
structure CoverOkAnyGas (m : Machine) : Prop where
  /-- `name()`: the getter's gas fits 64 bits. -/
  name : Abi.selectorOf m.frame.msg.data = 0x06fdde03 →
    Str.getterGas (Str.slotLen (m.world.sload m.frame.msg.currentTarget 0#256)) < 2 ^ 64
  /-- `symbol()`: the getter's gas fits 64 bits. -/
  symbol : Abi.selectorOf m.frame.msg.data = 0x95d89b41 →
    Str.getterGas (Str.slotLen (m.world.sload m.frame.msg.currentTarget 1#256)) < 2 ^ 64
  /-- `DOMAIN_SEPARATOR()`: a covered case. -/
  domain : Abi.selectorOf m.frame.msg.data = 0x3644e515 → DomainOk m
  /-- `permit`: the domain separator is computed in a covered case (the other permit frame
  conditions, `0x01` not delegated and room for the precompile call, are taken care of by
  `EcrecoverOk` and the depth-limit argument). -/
  permit : Abi.selectorOf m.frame.msg.data = 0xd505accf → DomainOk m

/-- The gas a frame is lifted to: at least 250000, and enough for the stored string of
`name()`/`symbol()`. -/
def liftGas (m : Machine) : Nat :=
  max (max m.frame.gasLeft 250000)
    (max (if Abi.selectorOf m.frame.msg.data = 0x06fdde03 then
        Str.getterGas (Str.slotLen (m.world.sload m.frame.msg.currentTarget 0#256)) else 0)
      (if Abi.selectorOf m.frame.msg.data = 0x95d89b41 then
        Str.getterGas (Str.slotLen (m.world.sload m.frame.msg.currentTarget 1#256)) else 0))

/-- A frame `M` with the calldata, account, world and context of `m`, no value, room for one
more call level and the lifted gas (`liftGas m`) is covered, given `CoverOkAnyGas m`. -/
theorem covered_of_lift {m M : Machine} (hvM : VaultStart vault asset M)
    (hdM : Deployed M.world vault asset) (hw : M.world = m.world)
    (ht : M.frame.msg.currentTarget = m.frame.msg.currentTarget)
    (hdata : M.frame.msg.data = m.frame.msg.data) (hctx : M.ctx = m.ctx)
    (hval : M.frame.msg.value = 0) (hg : M.frame.gasLeft = liftGas m)
    (hdepth : M.frame.msg.depth + 1 ≤ Gas.stackDepthLimit) (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hc : CoverOkAnyGas m) (hnd : EcrecoverOk m) : Covered vault asset 250000 M := by
  have hdom : Abi.selectorOf M.frame.msg.data = 0x3644e515 ∨
      Abi.selectorOf M.frame.msg.data = 0xd505accf → DomainOk M := by
    intro hs
    have hd : DomainOk m := by
      rw [hdata] at hs
      rcases hs with hs | hs
      · exact hc.domain hs
      · exact hc.permit hs
    unfold DomainOk at hd ⊢
    rw [hw, ht, hctx]
    exact hd
  refine covered_of_funded hvM hdM ⟨hval, ?_, fun _ => hdepth, hdata ▸ hsz⟩ ⟨?_, ?_,
    fun h => hdom (.inl h), fun h => ⟨hdom (.inr h), ?_, hdepth⟩⟩
  · rw [hg]; exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  · intro hs
    rw [hdata] at hs
    rw [hg, hw, ht]
    refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
    simp only [hs, ↓reduceIte]
    exact Nat.le_refl _
  · intro hs
    rw [hdata] at hs
    rw [hg, hw, ht]
    refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
    simp only [hs, ↓reduceIte]
    exact Nat.le_refl _
  · unfold EcrecoverOk at hnd
    rw [hctx, hw]
    exact hnd

/-- **A gas-free sufficient condition for `CoveredAnyGas`**, at any depth: value, or no value,
calldata below `2⁶⁴` bytes and `CoverOkAnyGas`; and `0x01` not delegated. -/
theorem coveredAnyGas_of {m : Machine} (hv : VaultStart vault asset m)
    (hdep : Deployed m.world vault asset) (hlt : m.frame.gasLeft < 2 ^ 64) (hnd : EcrecoverOk m)
    (h : m.frame.msg.value ≠ 0 ∨
      (m.frame.msg.value = 0 ∧ m.frame.msg.data.size < 2 ^ 64 ∧ CoverOkAnyGas m)) :
    CoveredAnyGas vault asset m := by
  refine .inr ⟨hnd, ?_⟩
  have hgas : ∀ G, m.frame.gasLeft ≤ G → (topBump G m).frame.gasLeft = G := by
    intro G hG; simp only [topBump, bump_frame, bumpF]; omega
  rcases h with hval | ⟨hval, hsz, hc⟩
  · refine .inl ⟨max m.frame.gasLeft 100, Nat.le_max_left _ _, ?_, .inl ⟨hval, ?_⟩⟩
    · have : 100 < 2 ^ 64 := by decide
      omega
    · rw [hgas _ (Nat.le_max_left _ _)]; exact Nat.le_max_right _ _
  · have hG : m.frame.gasLeft ≤ liftGas m :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    have hG64 : liftGas m < 2 ^ 64 := by
      unfold liftGas
      have h1 : (250000 : Nat) < 2 ^ 64 := by decide
      have h2 : (if Abi.selectorOf m.frame.msg.data = 0x06fdde03 then
          Str.getterGas (Str.slotLen (m.world.sload m.frame.msg.currentTarget 0#256)) else 0) <
          2 ^ 64 := by
        split
        · exact hc.name (by assumption)
        · decide
      have h3 : (if Abi.selectorOf m.frame.msg.data = 0x95d89b41 then
          Str.getterGas (Str.slotLen (m.world.sload m.frame.msg.currentTarget 1#256)) else 0) <
          2 ^ 64 := by
        split
        · exact hc.symbol (by assumption)
        · decide
      omega
    have hgl := hgas _ hG
    by_cases hd : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit
    · exact .inl ⟨liftGas m, hG, hG64, covered_of_lift (m := m) (hv.topBump hG) hdep rfl rfl rfl rfl hval
        hgl hd hsz hc hnd⟩
    · refine .inr ⟨by omega, liftGas m, hG, hG64, ?_⟩
      exact covered_of_lift (m := m) ((hv.topBump hG).setDepth _) hdep rfl rfl rfl rfl hval hgl
        (by simp [GasMono.setDepth, Gas.stackDepthLimit]) hsz hc hnd

/-- **A transaction covered at any gas**: every frame of the vault or the asset that other
code starts is covered at any gas, and the model calls it commits are admitted. -/
def TxOkAnyGas (vault asset : Address) (Act : List Address) (K : VCall → Prop)
    (ctx : Context) (w : World) (tr : TransientStorage) (msg : Message) : Prop :=
  ∀ m, Reaches ctx w tr msg m → VaultStart vault asset m →
    (∀ f ∈ m.parents, ¬ Danger (Prot vault asset) f) →
    CoveredAnyGas vault asset m ∧ FrameAdmitted ctx.crypto vault asset Act K m

/-- `Covered` is monotone in the minimum gas. -/
theorem Covered.mono {minGas minGas' : Nat} (h : minGas' ≤ minGas) {m : Machine}
    (hc : Covered vault asset minGas m) : Covered vault asset minGas' m := by
  rcases hc with hc | ⟨hf, hx⟩
  · exact .inl hc
  · exact .inr ⟨⟨hf.value, Nat.le_trans h hf.gas, hf.depth, hf.size⟩, hx⟩

/-- **Every transaction covered with `minGas ≥ 250000` is covered at any gas.** -/
theorem txOkAnyGas_of_txOk {minGas : Nat} (hmin : 250000 ≤ minGas) {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} (h : TxOk vault asset minGas Act K ctx w tr msg) :
    TxOkAnyGas vault asset Act K ctx w tr msg := fun m hm hv hp =>
  ⟨.inl (Covered.mono hmin (h m hm hv hp).1), (h m hm hv hp).2⟩

/-- **A transaction is covered at any gas** when `0x01` holds no EIP-7702 designator before it
(always true before Prague; no step of the transaction can create one, `reaches_allWorlds`),
and every frame of the vault or the asset that other code starts satisfies the gas-free
conditions of `coveredAnyGas_of`, with the model calls it commits admitted. -/
theorem txOkAnyGas_of {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (h1 : AbsInt.NoDesignator ctx.fork 1 w) (hgas : msg.gas < 2 ^ 64)
    (h : ∀ m, Reaches ctx w tr msg m → VaultStart vault asset m → Deployed m.world vault asset →
      (∀ f ∈ m.parents, ¬ Danger (Prot vault asset) f) →
      (m.frame.msg.value ≠ 0 ∨
        (m.frame.msg.value = 0 ∧ m.frame.msg.data.size < 2 ^ 64 ∧ CoverOkAnyGas m)) ∧
      FrameAdmitted ctx.crypto vault asset Act K m)
    (hdep : ∀ m, Reaches ctx w tr msg m → VaultStart vault asset m → Deployed m.world vault asset) :
    TxOkAnyGas vault asset Act K ctx w tr msg := by
  intro m hm hv hp
  have hd := hdep m hm hv
  obtain ⟨hc, hadm⟩ := h m hm hv hd hp
  have hnd : EcrecoverOk m := by
    have := (AbsInt.reaches_allWorlds (AbsInt.noDesignator ctx.fork 1) hdeleg h1 hm).1
    unfold EcrecoverOk; rw [hm.ctx]; exact this
  exact ⟨coveredAnyGas_of hv hd (Nat.lt_of_le_of_lt (AbsInt.Reaches.gas_le hm) hgas) hnd hc, hadm⟩

/-! ## One transaction -/

/-- **One transaction covered at any gas keeps `Follows`.** -/
theorem follows_tx_anyGas
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (hw : Follows crypto vault asset Act K w₀ w) {ctx : Context} {tr : TransientStorage}
    {msg : Message} {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : TopOk (Prot vault asset) w msg) (hgas : msg.gas < 2 ^ 64)
    (hok : TxOkAnyGas vault asset Act K ctx w tr msg)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    Follows crypto vault asset Act K w₀ r.world := by
  refine processMessageCall_follows hs hinv hw hdeleg hmsg (le_refl _) (fun m hm hd hp => ?_) hr
  have hv := DangerStart.vaultStart hd
  have hwm : Follows crypto vault asset Act K w₀ m.world := goodOk.keep _ _ hd.snapshot hd.keep
  have hcr' : m.ctx.crypto = crypto := by rw [hm.ctx]; exact hcr
  obtain ⟨ko, ks, hf⟩ := hd.fresh
  have hkind : m.frame.kind = .call ko ks := by rw [hf]; rfl
  obtain ⟨hcov, hadm⟩ := hok m hm hv hp
  exact frameOk_of_coveredAnyGas hk hs hv hkind hwm.1 (hwm.inv hs hinv) hcr'
    (DangerStart.gasLt hd hgas) hcov (hcr ▸ hadm)

/-! ## Sequences of transactions -/

/-- One step of a sequence of arbitrary transactions covered at any gas. -/
inductive TxStepAnyGas (crypto : Crypto) (vault asset : Address) (Act : List Address)
    (K : VCall → Prop) : World → World → Prop
  /-- A top-level message call covered at any gas. -/
  | call {w : World} {ctx : Context} {tr : TransientStorage} {msg : Message} {fuel : Nat}
      {r : MessageResult} : ctx.crypto = crypto →
      (ctx.fork < .prague ∨ ctx.tx.authorizations = []) → TopOk (Prot vault asset) w msg →
      msg.gas < 2 ^ 64 → TxOkAnyGas vault asset Act K ctx w tr msg →
      processMessageCall fuel ctx w tr msg = .ok r → TxStepAnyGas crypto vault asset Act K w r.world
  /-- Anything else that keeps the vault's and the asset's storage and code. -/
  | env {w w' : World} : EnvStep vault asset w w' → TxStepAnyGas crypto vault asset Act K w w'

/-- **Sequences of arbitrary transactions covered at any gas.** -/
def TxTraceAnyGas (crypto : Crypto) (vault asset : Address) (Act : List Address)
    (K : VCall → Prop) : World → World → Prop :=
  Relation.ReflTransGen (TxStepAnyGas crypto vault asset Act K)

/-- **The old traces are traces at any gas.** -/
theorem txTraceAnyGas_of_txTrace {minGas : Nat} (hmin : 250000 ≤ minGas) {w₀ w : World}
    (h : TxTrace crypto vault asset minGas Act K w₀ w) : TxTraceAnyGas crypto vault asset Act K w₀ w := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih =>
    refine .tail ih ?_
    cases hst with
    | call hcr hdeleg hmsg hgas hok hr =>
      exact .call hcr hdeleg hmsg hgas (txOkAnyGas_of_txOk hmin hok) hr
    | env he => exact .env he

/-- **Every sequence of transactions covered at any gas keeps `Follows`.** -/
theorem follows_trace_anyGas
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : TxTraceAnyGas crypto vault asset Act K w₀ w) :
    Follows crypto vault asset Act K w₀ w := by
  induction htr with
  | refl => exact follows_refl hdep
  | tail _ hst ih =>
    cases hst with
    | call hcr hdeleg hmsg hgas hok hr => exact follows_tx_anyGas hk hs hinv ih hcr hdeleg hmsg hgas hok hr
    | env he => exact ih.env he

/-! ## Headline theorems -/

/-- **The lifting theorem for arbitrary transactions, at any gas.** -/
theorem lift_any_tx_anyGas
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) {ctx : Context} {tr : TransientStorage}
    {msg : Message} {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : TopOk (Prot vault asset) w₀ msg) (hgas : msg.gas < 2 ^ 64)
    (hok : TxOkAnyGas vault asset Act K ctx w₀ tr msg)
    (hr : processMessageCall fuel ctx w₀ tr msg = .ok r) :
    Deployed r.world vault asset ∧ Solmate.Inv (abs crypto r.world vault asset) ∧
      ∃ cs : List VCall, (∀ c ∈ cs, Admitted Act K c) ∧
        AgreeOn (ActorPairs Act) (abs crypto r.world vault asset)
          (Solmate.exec (abs crypto w₀ vault asset) (cs.map VCall.op)) := by
  have h := follows_tx_anyGas hk hs hinv (follows_refl hdep) hcr hdeleg hmsg hgas hok hr
  exact ⟨h.1, h.inv hs hinv, h.2⟩

/-- **The lifting theorem for sequences of arbitrary transactions, at any gas.** -/
theorem lift_nested_anyGas
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : TxTraceAnyGas crypto vault asset Act K w₀ w) :
    Deployed w vault asset ∧ Solmate.Inv (abs crypto w vault asset) ∧
      ∃ cs : List VCall, (∀ c ∈ cs, Admitted Act K c) ∧
        AgreeOn (ActorPairs Act) (abs crypto w vault asset)
          (Solmate.exec (abs crypto w₀ vault asset) (cs.map VCall.op)) := by
  have h := follows_trace_anyGas hk hs hdep hinv htr
  exact ⟨h.1, h.inv hs hinv, h.2⟩

/-- **Invariants transfer, for sequences of arbitrary transactions, at any gas.** -/
theorem invariant_nested_anyGas
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {I : State Address → Prop}
    (hI : ∀ s op s', Solmate.Inv s → I s → step s op = some s' → I s')
    (hIa : ∀ s t, AgreeOn (ActorPairs Act) s t → I s → I t)
    {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : TxTraceAnyGas crypto vault asset Act K w₀ w) (hI₀ : I (abs crypto w₀ vault asset)) :
    I (abs crypto w vault asset) := by
  obtain ⟨-, -, cs, -, ha⟩ := lift_nested_anyGas hk hs hdep hinv htr
  have := (exec_induction (step := step) (Inv := Solmate.Inv) (fun _ _ _ hi h => Inv_step hi h)
    hI hinv hI₀ (cs.map VCall.op)).2
  rw [← exec_eq] at this
  exact hIa _ _ ha.symm this

/-- **`totalSupply` = Σ `balanceOf`, for sequences of arbitrary transactions, at any gas**,
for the shares and for the asset, read from storage. -/
theorem supply_eq_sum_nested_anyGas
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : TxTraceAnyGas crypto vault asset Act K w₀ w) :
    (w.sload vault 2#256).toNat =
        ∑ a : Address, (w.sload vault (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat ∧
      (w.sload asset 2#256).toNat =
        ∑ a : Address, (w.sload asset (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat := by
  obtain ⟨-, hi, -⟩ := lift_nested_anyGas hk hs hdep hinv htr
  exact ⟨supply_eq_sum_of_wf hi.2, supply_eq_sum_of_wf hi.1⟩

/-- **Solvency, for sequences of arbitrary transactions, at any gas.** -/
theorem solvent_nested_anyGas
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : TxTraceAnyGas crypto vault asset Act K w₀ w) :
    ∑ a : Address, sharesAt crypto w vault a * assetsAt crypto w vault asset / supplyAt w vault ≤
      assetsAt crypto w vault asset := by
  obtain ⟨-, hi, -⟩ := lift_nested_anyGas hk hs hdep hinv htr
  have := Solmate.solvent _ hi
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp)] at this
  simpa only [abs_sharesOf, abs_totalAssets', abs_totalSupply'] using this

/-- **Price monotonicity, for sequences of arbitrary transactions, at any gas.** -/
theorem price_mono_nested_anyGas
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : TxTraceAnyGas crypto vault asset Act (fun c => UserOp vault c.op) w₀ w) :
    ∃ cs : List VCall, (∀ c ∈ cs, (∀ a ∈ c.actors, a ∈ Act) ∧ UserOp vault c.op) ∧
      ((∀ k ≤ cs.length,
          (Solmate.exec (abs crypto w₀ vault asset) ((cs.take k).map VCall.op)).totalSupply ≠ 0) →
        (assetsAt crypto w₀ vault asset : ℚ) / supplyAt w₀ vault ≤
          (assetsAt crypto w vault asset : ℚ) / supplyAt w vault) := by
  obtain ⟨-, -, cs, hcs, ha⟩ := lift_nested_anyGas hk hs hdep hinv htr
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

/-- One transaction covered at any gas is a `TxTraceAnyGas`. -/
theorem txTraceAnyGas_single {w : World} {ctx : Context} {tr : TransientStorage} {msg : Message}
    {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : TopOk (Prot vault asset) w msg) (hgas : msg.gas < 2 ^ 64)
    (hok : TxOkAnyGas vault asset Act K ctx w tr msg)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    TxTraceAnyGas crypto vault asset Act K w r.world :=
  Relation.ReflTransGen.single (.call hcr hdeleg hmsg hgas hok hr)

/-- **`totalSupply` = Σ `balanceOf` after one arbitrary transaction, at any gas.** -/
theorem supply_eq_sum_any_tx_anyGas
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) {ctx : Context} {tr : TransientStorage}
    {msg : Message} {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : TopOk (Prot vault asset) w₀ msg) (hgas : msg.gas < 2 ^ 64)
    (hok : TxOkAnyGas vault asset Act K ctx w₀ tr msg)
    (hr : processMessageCall fuel ctx w₀ tr msg = .ok r) :
    (r.world.sload vault 2#256).toNat = ∑ a : Address,
        (r.world.sload vault (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat ∧
      (r.world.sload asset 2#256).toNat = ∑ a : Address,
        (r.world.sload asset (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat :=
  supply_eq_sum_nested_anyGas hk hs hdep hinv (txTraceAnyGas_single hcr hdeleg hmsg hgas hok hr)

/-- **Solvency after one arbitrary transaction, at any gas.** -/
theorem solvent_any_tx_anyGas
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) {ctx : Context} {tr : TransientStorage}
    {msg : Message} {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : TopOk (Prot vault asset) w₀ msg) (hgas : msg.gas < 2 ^ 64)
    (hok : TxOkAnyGas vault asset Act K ctx w₀ tr msg)
    (hr : processMessageCall fuel ctx w₀ tr msg = .ok r) :
    ∑ a : Address, sharesAt crypto r.world vault a * assetsAt crypto r.world vault asset /
        supplyAt r.world vault ≤ assetsAt crypto r.world vault asset :=
  solvent_nested_anyGas hk hs hdep hinv (txTraceAnyGas_single hcr hdeleg hmsg hgas hok hr)

/-- **Invariants transfer, after one arbitrary transaction, at any gas.** -/
theorem invariant_any_tx_anyGas
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {I : State Address → Prop}
    (hI : ∀ s op s', Solmate.Inv s → I s → step s op = some s' → I s')
    (hIa : ∀ s t, AgreeOn (ActorPairs Act) s t → I s → I t)
    {w₀ : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) {ctx : Context} {tr : TransientStorage}
    {msg : Message} {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : TopOk (Prot vault asset) w₀ msg) (hgas : msg.gas < 2 ^ 64)
    (hok : TxOkAnyGas vault asset Act K ctx w₀ tr msg)
    (hr : processMessageCall fuel ctx w₀ tr msg = .ok r) (hI₀ : I (abs crypto w₀ vault asset)) :
    I (abs crypto r.world vault asset) :=
  invariant_nested_anyGas hk hs hI hIa hdep hinv
    (txTraceAnyGas_single hcr hdeleg hmsg hgas hok hr) hI₀

/-- **Price monotonicity, after one arbitrary transaction, at any gas.** -/
theorem price_mono_any_tx_anyGas
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) {ctx : Context} {tr : TransientStorage}
    {msg : Message} {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : TopOk (Prot vault asset) w₀ msg) (hgas : msg.gas < 2 ^ 64)
    (hok : TxOkAnyGas vault asset Act (fun c => UserOp vault c.op) ctx w₀ tr msg)
    (hr : processMessageCall fuel ctx w₀ tr msg = .ok r) :
    ∃ cs : List VCall, (∀ c ∈ cs, (∀ a ∈ c.actors, a ∈ Act) ∧ UserOp vault c.op) ∧
      ((∀ k ≤ cs.length,
          (Solmate.exec (abs crypto w₀ vault asset) ((cs.take k).map VCall.op)).totalSupply ≠ 0) →
        (assetsAt crypto w₀ vault asset : ℚ) / supplyAt w₀ vault ≤
          (assetsAt crypto r.world vault asset : ℚ) / supplyAt r.world vault) :=
  price_mono_nested_anyGas hk hs hdep hinv (txTraceAnyGas_single hcr hdeleg hmsg hgas hok hr)

end Examples.Solmate.ERC4626.LowGas
