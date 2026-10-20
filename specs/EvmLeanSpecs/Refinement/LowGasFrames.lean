import EvmLeanSpecs.Refinement.LowGasMono
import EvmLeanSpecs.Refinement.NestedCoverage
import EvmLeanSpecs.Refinement.NestedInvariants

/-!
# Low gas: the Solmate frames are gas-monotone

The gas-lockstep theorem (`EvmLeanProofs/Program/GasMono/Lockstep.lean`, `monoFrom_of_code`)
instantiated for the compiled Solmate asset and vault (`CodeOk`: `LowGasMono.lean`):

* `assetHigh_mono`: frames of the asset's code (any immutables, standard precompiles) are
  gas-monotone, given `AssetCallsPrecompile` (every child an asset frame starts is a precompile
  call — its only call is `ecrecover` in `permit`);
* `vaultHigh_mono`: frames of the vault's code in a deployed world are gas-monotone, given
  moreover `VaultCallsAsset` (every non-precompile child a vault frame starts runs the asset's
  code — its calls are `asset.balanceOf`, `asset.transferFrom`, `asset.transfer` and the
  `ecrecover` of `permit`).

The two call-target conditions are **the remaining hypotheses**: they are facts about the
paths of the two codes (which address is on the stack at each call site), not provided by the
code scans. They are stated for the high-gas frame up to its real end (`Exit`), which is the
run the lockstep follows.

`frameOk_of_topBump`: **a frame summary transfers to every lower gas.** If the same frame
with gas `G` (at the top level, `topBump G m`) satisfies `FrameOk`, so does `m`, for every
`m.frame.gasLeft ≤ G < 2⁶⁴`. `frameOk_anyGas`: hence every frame of the vault or the asset that
would be covered with more gas (`Covered` of `topBump G m`) satisfies its frame summary.
-/

namespace EvmLeanSpecs.Refinement.LowGas

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Contracts EvmLean.Program.GasMono
open EvmLean.Solidity
open EvmLean.Program.Nested (bump Reaches Danger)
open EvmLeanSpecs.Vault EvmLeanSpecs.Refinement.Lift
open EvmLeanSpecs.Refinement.Nested EvmLeanSpecs.Refinement.Invariants

/-! ## The frames -/

/-- `0x01` (the `ECRECOVER` precompile) is not EIP-7702-delegated in the machine's world (always
true before Prague; on a real chain nobody holds the key of `0x01`). Both codes call it in
`permit`; delegated, the call would run the delegate's code. -/
def EcrecoverOk (m : Machine) : Prop :=
  m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none

/-- A high-gas frame of the asset's code, from its start. -/
structure AssetHigh (ia : SolmateAsset.Immutables) (mh : Machine) : Prop where
  /-- The asset's code. -/
  code : mh.frame.code = SolmateAsset.runtimeCodeWith ia
  /-- Its jump table. -/
  jd : mh.frame.jumpDests = validJumpDests mh.frame.code
  /-- From the start. -/
  pc : mh.frame.pc = 0
  /-- Gas fits a word. -/
  gasLt : mh.frame.gasLeft < 2 ^ 256
  /-- Standard precompiles. -/
  pre : mh.precompiles = PrecompileImpl.standard mh.ctx
  /-- An empty stack. -/
  stack : mh.frame.stack = []
  /-- `0x01` is not delegated. -/
  ecrecover : EcrecoverOk mh

/-- A high-gas frame of the vault's code, with the asset immutable `asset`, from its start, in a
deployed world. -/
structure VaultHigh (vault asset : Address) (i : SolmateVault.Immutables) (mh : Machine) :
    Prop where
  /-- The vault's code. -/
  code : mh.frame.code = SolmateVault.runtimeCodeWith i
  /-- Its asset immutable. -/
  assetEq : i.asset = asset
  /-- Deployed. -/
  dep : Deployed mh.world vault asset
  /-- Its jump table. -/
  jd : mh.frame.jumpDests = validJumpDests mh.frame.code
  /-- From the start. -/
  pc : mh.frame.pc = 0
  /-- Gas fits a word. -/
  gasLt : mh.frame.gasLeft < 2 ^ 256
  /-- Standard precompiles. -/
  pre : mh.precompiles = PrecompileImpl.standard mh.ctx
  /-- An empty stack. -/
  stack : mh.frame.stack = []
  /-- `0x01` is not delegated. -/
  ecrecover : EcrecoverOk mh

/-- **Call targets of the asset** (remaining hypothesis): every child an asset frame starts
before its end is a precompile call. -/
def AssetCallsPrecompile : Prop :=
  ∀ ia mh N mfh oh, AssetHigh ia mh → Exit mh N mfh oh → CallsTo (fun _ => False) mh N

/-- **Call targets of the vault** (remaining hypothesis): every non-precompile child a vault
frame starts before its end runs the asset's code. -/
def VaultCallsAsset (vault asset : Address) : Prop :=
  ∀ i mh N mfh oh, VaultHigh vault asset i mh → Exit mh N mfh oh →
    CallsTo (fun mc => ∃ ia, AssetHigh ia mc) mh N

/-- Gas monotonicity of a union. -/
theorem monoFrom_exists {ι : Type} {S : ι → Machine → Prop} (h : ∀ i, MonoFrom (S i)) :
    MonoFrom (fun mh => ∃ i, S i mh) := by
  intro ml mh N mfh oh ⟨i, hi⟩ hb hex
  exact h i ml mh N mfh oh hi hb hex

/-- **The asset's frames are gas-monotone.** -/
theorem assetHigh_mono (hA : AssetCallsPrecompile) : MonoFrom (fun mh => ∃ ia, AssetHigh ia mh) :=
  monoFrom_exists fun ia => monoFrom_of_code (asset_codeOk ia) monoFrom_false
    (fun mh h => ⟨h.code, h.jd.trans (by rw [h.code]),
      (by rw [h.pc]; exact pcOk_zero (asset_codeOk ia).region), h.gasLt,
      (by rw [h.pre]; exact Nested.precompilesOk_standard _), (by rw [h.pre]; exact preMono_standard _)⟩)
    (fun mh N mfh oh h hex => hA ia mh N mfh oh h hex)

/-- **The vault's frames are gas-monotone.** -/
theorem vaultHigh_mono {vault asset : Address} (hA : AssetCallsPrecompile)
    (hV : VaultCallsAsset vault asset) :
    MonoFrom (fun mh => ∃ i, VaultHigh vault asset i mh) :=
  monoFrom_exists fun i => monoFrom_of_code (vault_codeOk i) (assetHigh_mono hA)
    (fun mh h => ⟨h.code, h.jd.trans (by rw [h.code]),
      (by rw [h.pc]; exact pcOk_zero (vault_codeOk i).region), h.gasLt,
      (by rw [h.pre]; exact Nested.precompilesOk_standard _), (by rw [h.pre]; exact preMono_standard _)⟩)
    (fun mh N mfh oh h hex => hV i mh N mfh oh h hex)

/-! ## Frame summaries for any gas -/

/-- The top-level bump of a fresh frame is fresh, with message gas `G`. -/
theorem topBump_frame {m : Machine} {msg : Message} {k : FrameKind}
    {s : World × TransientStorage} (hf : m.frame = Frame.init msg k s) {G : Nat}
    (hG : m.frame.gasLeft ≤ G) :
    (topBump G m).frame = Frame.init { msg with gas := G } k s := by
  have hg : m.frame.gasLeft = msg.gas := by rw [hf]; rfl
  simp only [topBump, bump_frame, bumpF, hf, Frame.init, Frame.mk.injEq, and_true, true_and]
  rw [hf] at hG; simp only [Frame.init] at hG; omega

/-- `VaultStart` survives the top-level bump. -/
theorem _root_.EvmLeanSpecs.Refinement.Nested.VaultStart.topBump {vault asset : Address} {m : Machine} (hv : VaultStart vault asset m)
    {G : Nat} (hG : m.frame.gasLeft ≤ G) : VaultStart vault asset (topBump G m) := by
  obtain ⟨msg, k, s, hf, hc⟩ := hv.fresh
  exact ⟨⟨{ msg with gas := G }, k, s, topBump_frame hf hG, hc⟩, hv.static, hv.prot, hv.pre,
    hv.caller⟩

/-- The high-gas version of a frame of the vault or the asset is one of the gas-monotone
frames. -/
theorem high_of_vaultStart {vault asset : Address} {m : Machine} (hv : VaultStart vault asset m)
    (hdep : Deployed m.world vault asset) (hnd : EcrecoverOk m) {G : Nat}
    (hG : m.frame.gasLeft ≤ G) (hG' : G < 2 ^ 256) :
    (∃ i, VaultHigh vault asset i (topBump G m)) ∨ (∃ ia, AssetHigh ia (topBump G m)) := by
  have hv' := hv.topBump hG
  obtain ⟨hcode, hjd, hpc, hstk, -, hgas, -⟩ := hv'.fresh.frame
  have hgasG : (topBump G m).frame.gasLeft = G := by
    simp only [topBump, bump_frame, bumpF]; omega
  rcases hv.prot with ht | ht
  · obtain ⟨i, hi, hci⟩ := hdep.vaultCode
    refine .inl ⟨i, ?_, hi, hdep, ?_, hpc, by omega, hv'.pre, hstk, hnd⟩
    · rw [hcode]; show m.world.code m.frame.msg.currentTarget = _; rw [ht]; exact hci
    · rw [hjd, hcode]
  · obtain ⟨ia, hci⟩ := hdep.assetCode
    refine .inr ⟨ia, ?_, ?_, hpc, by omega, hv'.pre, hstk, hnd⟩
    · rw [hcode]; show m.world.code m.frame.msg.currentTarget = _; rw [ht]; exact hci
    · rw [hjd, hcode]

/-- **A frame summary transfers to every lower gas.** -/
theorem frameOk_of_topBump {crypto : Crypto} {vault asset : Address} {Act : List Address}
    {K : VCall → Prop} (hA : AssetCallsPrecompile) (hV : VaultCallsAsset vault asset)
    {m : Machine} (hv : VaultStart vault asset m) (hdep : Deployed m.world vault asset)
    (hnd : EcrecoverOk m) {ko ks : Nat} (hk : m.frame.kind = .call ko ks) {G : Nat}
    (hG : m.frame.gasLeft ≤ G)
    (hG' : G < 2 ^ 256) (h : FrameOk crypto vault asset Act K (topBump G m)) :
    FrameOk crypto vault asset Act K m := by
  have key : ∀ {S : Machine → Prop}, MonoFrom S → S (topBump G m) →
      FrameOk crypto vault asset Act K m := fun hmono hS =>
    halts_world_of_mono (P := fun w => Deployed w vault asset ∧ ∃ cs : List VCall,
      (∀ c ∈ cs, Admitted Act K c) ∧ AgreeOn (ActorPairs Act) (abs crypto w vault asset)
        (EvmLeanSpecs.Vault.Solmate.exec (abs crypto m.world vault asset) (cs.map VCall.op))) hmono hk hS h
  rcases high_of_vaultStart hv hdep hnd hG hG' with hS | hS
  · exact key (vaultHigh_mono hA hV) hS
  · exact key (assetHigh_mono hA) hS

/-! ## Covered at some gas -/

/-- **Covered at some gas**: with some gas `G ≥` its own (below `2⁶⁴`), the same frame would be
covered (`Covered`, which asks for at least `minGas`). Every frame of the vault or the asset is
covered at some gas unless it fails for a reason other than gas (value with less than 100 gas
excepted, these are covered by `Covered` itself). -/
def CoveredAtSomeGas (vault asset : Address) (minGas : Nat) (m : Machine) : Prop :=
  ∃ G, m.frame.gasLeft ≤ G ∧ G < 2 ^ 64 ∧ Covered vault asset minGas (topBump G m)

/-- **The frame summary of a frame covered at some gas**, for any gas of its own. -/
theorem frameOk_of_coveredAtSomeGas {crypto : Crypto} {vault asset : Address}
    {Act : List Address} {K : VCall → Prop} {minGas : Nat} (hA : AssetCallsPrecompile)
    (hV : VaultCallsAsset vault asset) (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {m : Machine} (hv : VaultStart vault asset m)
    {ko ks : Nat} (hkind : m.frame.kind = .call ko ks)
    (hdep : Deployed m.world vault asset) (hinv : Solmate.Inv (abs crypto m.world vault asset))
    (hcr : m.ctx.crypto = crypto) (hnd : EcrecoverOk m) (hc : CoveredAtSomeGas vault asset minGas m)
    (hadm : FrameAdmitted crypto vault asset Act K m) : FrameOk crypto vault asset Act K m := by
  obtain ⟨G, hG, hG64, hcov⟩ := hc
  refine frameOk_of_topBump hA hV hv hdep hnd hkind hG (Nat.lt_of_lt_of_le hG64 (by decide)) ?_
  have hgas : (topBump G m).frame.gasLeft < 2 ^ 64 := by
    simp only [topBump, bump_frame, bumpF]; omega
  exact frameOk_of_covered hmin hk hs (hv.topBump hG) hdep hinv hcr hgas hcov
    ⟨fun c hx => hadm.calls c ⟨hx.caller, hx.target, hx.data⟩,
      fun c hx => hadm.permits c (by cases c <;> exact hx)⟩

/-- A transaction whose vault/asset frames are covered at some gas. -/
def TxOkAtSomeGas (vault asset : Address) (minGas : Nat) (Act : List Address) (K : VCall → Prop)
    (ctx : Context) (w : World) (tr : TransientStorage) (msg : Message) : Prop :=
  ∀ m, Reaches ctx w tr msg m → VaultStart vault asset m →
    (∀ f ∈ m.parents, ¬ Danger (Prot vault asset) f) →
    EcrecoverOk m ∧ CoveredAtSomeGas vault asset minGas m ∧
      FrameAdmitted ctx.crypto vault asset Act K m

/-- **One transaction, frames covered at some gas** (given the call-target hypotheses). -/
theorem follows_tx_atSomeGas {crypto : Crypto} {vault asset : Address} {Act : List Address}
    {K : VCall → Prop} {minGas : Nat} (hA : AssetCallsPrecompile)
    (hV : VaultCallsAsset vault asset) (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (hw : Follows crypto vault asset Act K w₀ w) {ctx : Context} {tr : TransientStorage}
    {msg : Message} {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : EvmLean.Program.Nested.TopOk (Prot vault asset) w msg)
    (hok : TxOkAtSomeGas vault asset minGas Act K ctx w tr msg)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    Follows crypto vault asset Act K w₀ r.world := by
  refine processMessageCall_follows hs hinv hw hdeleg hmsg (le_refl _) (fun m hm hd hp => ?_) hr
  have hv := DangerStart.vaultStart hd
  have hwm : Follows crypto vault asset Act K w₀ m.world := goodOk.keep _ _ hd.snapshot hd.keep
  have hcr' : m.ctx.crypto = crypto := by rw [hm.ctx]; exact hcr
  obtain ⟨ko, ks, hf⟩ := hd.fresh
  have hkind : m.frame.kind = .call ko ks := by rw [hf]; rfl
  obtain ⟨hnd, hcov, hadm⟩ := hok m hm hv hp
  exact frameOk_of_coveredAtSomeGas hA hV hmin hk hs hv hkind hwm.1 (hwm.inv hs hinv) hcr' hnd
    hcov (hcr ▸ hadm)

end EvmLeanSpecs.Refinement.LowGas
