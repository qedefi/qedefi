import Verified.Solmate.Constructor.VaultDeploy
import Verified.Solmate.Constructor.CodeFor
import Verified.Solmate.ERC4626.Nested.Invariants
import Verified.Solmate.ERC4626.LowGas.AnyGas

/-!
# The Solmate invariants, anchored at deployment

The trace theorems (`Invariants.lift`, `Nested.lift_nested`, …) assume a starting world that is
`Deployed` and whose ledgers are well formed (`Solmate.Inv (abs …)`). Here that world is
produced by running the constructors: the asset's creation (`asset_create`), then the vault's
over it (`vault_create`). `deployed_inv_of_create`: the world after both creations is
`Deployed` and satisfies `Solmate.Inv` (both supplies and all balances are zero). The
`*_anchored` theorems compose this with the trace theorems, so the invariants hold after
deployment followed by any trace, with no assumption on the starting invariant.

Hash hypothesis: no balance slot (`keccak(pad(a) ‖ 3)`) is slot 0 or 1, where the constructors
store the token names (`KeccakAvoids crypto (AddressKeyed [3]) [0, 1]`), of the same kind as the
`[2]` and `[2, 6, 7]` hypotheses of the trace theorems.
-/

namespace Verified.Solmate.Constructor
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Solidity
open Verified.Solmate.Contracts Verified.Solmate.ERC4626 QEDefi.ERC4626 QEDefi.ERC20 QEDefi.Math

/-! ## Determinism of a top-level message -/

theorem processMessageCall_mono {fuel fuel' : Nat} {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} {r : MessageResult}
    (h : processMessageCall fuel ctx w tr msg = .ok r) (hle : fuel ≤ fuel') :
    processMessageCall fuel' ctx w tr msg = .ok r := by
  unfold processMessageCall processMessageCallWith at *
  dsimp only at *
  split at h
  · exact h
  · rename_i m heq
    cases hrun : run fuel m with
    | error e => rw [hrun] at h; cases h
    | ok r0 =>
      rw [hrun] at h
      rw [run_mono hrun hle]
      exact h

theorem result_eq {fuel n : Nat} {ctx : Context} {w : World} {tr : TransientStorage}
    {msg : Message} {r r' : MessageResult}
    (hn : ∀ fuel, n ≤ fuel → processMessageCall fuel ctx w tr msg = .ok r')
    (h : processMessageCall fuel ctx w tr msg = .ok r) : r = r' := by
  have h1 := processMessageCall_mono h (Nat.le_max_left fuel n)
  rw [hn _ (Nat.le_max_right fuel n)] at h1
  cases h1; rfl

/-! ## Accounts of the deployment worlds -/

theorem account_incrementNonce (w : World) (a b : Address) :
    (incrementNonce w a).account b =
      if b = a then { w.account a with nonce := (w.account a).nonce + 1 } else w.account b :=
  account_modifyState w a _ b (by simp [Account.isEmpty])

theorem account_setCode (w : World) (a : Address) (out : ByteArray) (hs : out.size ≠ 0)
    (b : Address) :
    (setCode w a out).account b = if b = a then { w.account a with code := out } else w.account b :=
  account_modifyState w a _ b (by simp [Account.isEmpty, hs])

theorem account_sstore (w : World) (a : Address) (k v : Word) (b : Address) :
    (w.sstore a k v).account b =
      if b = a then { w.account a with storage := (w.account a).storage.set k v }
      else w.account b := by
  split
  · subst_vars; exact World.account_modify_self _ _ _
  · exact World.account_modify_ne _ _ ‹_›

theorem storage_empty_of_deployable {w : World} {a : Address} (hd : accountDeployable w a = true) :
    (w.account a).storage = ∅ := by
  simp only [accountDeployable, Bool.and_eq_true, decide_eq_true_eq] at hd
  exact Std.ExtTreeMap.isEmpty_iff.mp hd.2

/-- The asset's account after its creation; every other account unchanged. -/
theorem account_assetWorld (crypto : Crypto) (chainId : Nat) (w : World) (self b : Address) :
    (assetWorld crypto chainId w self).account b =
      if b = self then
        { nonce := (w.account self).nonce + 1, balance := (w.account self).balance,
          code := SolmateAsset.runtimeCodeWith (Asset.immutables crypto chainId self),
          storage := (((w.account self).storage.set 0#256 Asset.nameSlot).set 1#256
            Asset.symbolSlot) }
      else w.account b := by
  simp only [assetWorld]
  rw [account_setCode _ _ _ (by rw [size_runtimeCodeWith]; decide)]
  by_cases hb : b = self
  · subst hb; simp [account_sstore, account_incrementNonce]
  · simp [hb, account_sstore, account_incrementNonce]

/-- The vault's account after its creation; every other account unchanged. -/
theorem account_vaultWorld (crypto : Crypto) (chainId : Nat) (w : World) (self asset b : Address)
    (dec : Word) :
    (vaultWorld crypto chainId w self asset dec).account b =
      if b = self then
        { nonce := (w.account self).nonce + 1, balance := (w.account self).balance,
          code := SolmateVault.runtimeCodeWith (Vault.immutables crypto chainId self asset dec),
          storage := (((((w.account self).storage.set 6#256 0#256).set 7#256 0#256).set 0#256
            Vault.nameSlot).set 1#256 Vault.symbolSlot) }
      else w.account b := by
  simp only [vaultWorld]
  rw [account_setCode _ _ _ (by rw [size_vaultRuntimeCodeWith]; decide)]
  by_cases hb : b = self
  · subst hb; simp [account_sstore, account_incrementNonce]
  · simp [hb, account_sstore, account_incrementNonce]

/-! ## The ledgers after deployment -/

theorem tokenView_wf_of_zero {crypto : Crypto} {w : World} {token : Address}
    (h : ∀ k, k ≠ 0#256 → k ≠ 1#256 → w.sload token k = 0#256)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [0#256, 1#256]) :
    (tokenView crypto w token).WF := by
  have hb : ∀ a, w.sload token (ERC20.balanceSlot crypto ERC20.Layout.solmate a) = 0#256 := by
    intro a
    have hne := hk _ ⟨a, 3#256, by simp, rfl⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hne
    exact h _ hne.1 hne.2
  have hs : w.sload token 2#256 = 0#256 := h _ (by decide) (by decide)
  have hz : (tokenView crypto w token).balanceOf = 0 := by
    ext a
    simp [tokenView, toToken, ERC20.view, hb]
  refine ⟨?_, ?_⟩
  · rw [hz]
    simp [total, tokenView, toToken, ERC20.view, ERC20.Layout.solmate, hs]
  · simp [tokenView, toToken, ERC20.view, ERC20.Layout.solmate, hs, MAX]

/-! ## Deployment transactions -/

/-- **A creation message** running `init` at `new`: no value, not static, at depth 0, at least
`minGas` and fewer than `2⁶⁴` gas, hash `crypto`, before Prague or without EIP-7702
authorizations. (The new account must also be deployable; that is a property of the world.) -/
structure CreationMsg (cr : Crypto) (ctx : Context) (msg : Message) (init : ByteArray)
    (new : Address) (minGas : Nat) : Prop where
  hcrypto : ctx.crypto = cr
  hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []
  htarget : msg.target = none
  hcode : msg.code = init
  hvalue : msg.value = 0
  hdepth : msg.depth = 0
  hstatic : msg.isStatic = false
  hnew : msg.currentTarget = new
  hgas : minGas ≤ msg.gas
  hgas' : msg.gas < 2 ^ 64

variable {crypto : Crypto} {asset vault : Address}

/-- **The two creations**: the asset's creation and then the vault's both succeed, in
`assetWorld` and then `vaultWorld` (the vault's decimals are the asset's 18). -/
theorem create_worlds {ctx₁ ctx₂ : Context} {w₀ : World} {tr₁ tr₂ : TransientStorage}
    {msg₁ msg₂ : Message} {fuel₁ fuel₂ : Nat} {r₁ r₂ : MessageResult}
    (h₁ : CreationMsg crypto ctx₁ msg₁ (SolmateAsset.creationCode ++ SolmateAsset.constructorArgs)
      asset 1000000)
    (hr₁ : processMessageCall fuel₁ ctx₁ w₀ tr₁ msg₁ = .ok r₁)
    (h₂ : CreationMsg crypto ctx₂ msg₂
      (SolmateVault.creationCode ++ SolmateVault.constructorArgsFor asset) vault 2000000)
    (hr₂ : processMessageCall fuel₂ ctx₂ r₁.world tr₂ msg₂ = .ok r₂)
    (hda : accountDeployable w₀ asset = true) (hdv : accountDeployable w₀ vault = true)
    (hne : vault ≠ asset) (hpa : ∀ fork, Precompile.isPrecompile fork asset = false) :
    r₁.success = true ∧ r₂.success = true ∧
      r₁.world = assetWorld crypto ctx₁.block.chainId w₀ asset ∧
      r₂.world = vaultWorld crypto ctx₂.block.chainId r₁.world vault asset 18#256 := by
  obtain ⟨r, ⟨n, hn⟩, hs, hw⟩ := asset_create h₁.hdeleg h₁.htarget h₁.hcode h₁.hvalue h₁.hdepth
    h₁.hstatic (h₁.hnew ▸ hda) h₁.hgas h₁.hgas'
  obtain rfl := result_eq hn hr₁
  rw [h₁.hnew, h₁.hcrypto] at hw
  have hacc₁ : ∀ b, r₁.world.account b = if b = asset then _ else w₀.account b := fun b => by
    rw [hw]; exact account_assetWorld _ _ _ _ _
  have hcodeA : r₁.world.code asset =
      SolmateAsset.runtimeCodeWith (Asset.immutables crypto ctx₁.block.chainId asset) := by
    simp only [World.code, hacc₁, ↓reduceIte]
  have hdv₁ : accountDeployable r₁.world vault = true := by
    simp only [accountDeployable, hacc₁, hne, ↓reduceIte]; exact hdv
  obtain ⟨r', ⟨n', hn'⟩, hs', hw'⟩ := vault_create h₂.hdeleg h₂.htarget h₂.hcode
    h₂.hvalue h₂.hdepth h₂.hstatic (h₂.hnew ▸ hdv₁) hcodeA (hpa _) h₂.hgas h₂.hgas'
  obtain rfl := result_eq hn' hr₂
  rw [h₂.hnew, h₂.hcrypto] at hw'
  have hdec : (Asset.immutables crypto ctx₁.block.chainId asset).decimals &&& 255#256 = 18#256 := by
    simp only [Asset.immutables]; decide
  rw [hdec] at hw'
  exact ⟨hs, hs', hw, hw'⟩

/-- **Deployment yields the starting invariant.** From a world in which `asset` and `vault` are
distinct deployable addresses (no code, nonce 0, empty storage) and not precompiles, the
creation of the Solmate asset at `asset` (canonical arguments), then of the Solmate vault over
it at `vault`, both succeed, and the resulting world is `Deployed` with well-formed ledgers. -/
theorem deployed_inv_of_create {ctx₁ ctx₂ : Context} {w₀ : World} {tr₁ tr₂ : TransientStorage}
    {msg₁ msg₂ : Message} {fuel₁ fuel₂ : Nat} {r₁ r₂ : MessageResult}
    (h₁ : CreationMsg crypto ctx₁ msg₁ (SolmateAsset.creationCode ++ SolmateAsset.constructorArgs)
      asset 1000000)
    (hr₁ : processMessageCall fuel₁ ctx₁ w₀ tr₁ msg₁ = .ok r₁)
    (h₂ : CreationMsg crypto ctx₂ msg₂
      (SolmateVault.creationCode ++ SolmateVault.constructorArgsFor asset) vault 2000000)
    (hr₂ : processMessageCall fuel₂ ctx₂ r₁.world tr₂ msg₂ = .ok r₂)
    (hda : accountDeployable w₀ asset = true) (hdv : accountDeployable w₀ vault = true)
    (hne : vault ≠ asset)
    (hpa : ∀ fork, Precompile.isPrecompile fork asset = false)
    (hpv : ∀ fork, Precompile.isPrecompile fork vault = false)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [0#256, 1#256]) :
    r₁.success = true ∧ r₂.success = true ∧ Deployed r₂.world vault asset ∧
      Solmate.Inv (abs crypto r₂.world vault asset) := by
  obtain ⟨hs, hs', hw, hw'⟩ := create_worlds h₁ hr₁ h₂ hr₂ hda hdv hne hpa
  have hacc₁ : ∀ b, r₁.world.account b = if b = asset then _ else w₀.account b := fun b => by
    rw [hw]; exact account_assetWorld _ _ _ _ _
  have hacc₂ : ∀ b, r₂.world.account b = if b = vault then _ else r₁.world.account b := fun b => by
    rw [hw']; exact account_vaultWorld _ _ _ _ _ _ _
  refine ⟨hs, hs', ⟨⟨Vault.immutables crypto ctx₂.block.chainId vault asset 18#256, rfl, ?_⟩,
    ⟨Asset.immutables crypto ctx₁.block.chainId asset, ?_⟩, hpv, hpa⟩, ?_, ?_⟩
  · simp only [World.code, hacc₂, ↓reduceIte]
  · simp only [World.code, hacc₂, hne.symm, hacc₁, ↓reduceIte]
  · -- the asset's ledger
    apply tokenView_wf_of_zero _ hk
    intro k hk0 hk1
    simp only [World.sload, hacc₂, hne.symm, ↓reduceIte, hacc₁, storage_empty_of_deployable hda,
      Storage.get_set, hk0, hk1, Storage.get_empty]
    rfl
  · -- the vault's ledger
    apply tokenView_wf_of_zero _ hk
    intro k hk0 hk1
    simp only [World.sload, hacc₂, ↓reduceIte, hacc₁, hne, storage_empty_of_deployable hdv,
      Storage.get_set, hk0, hk1, Storage.get_empty]
    split <;> (try split) <;> rfl

/-- **The deployed code is `runtimeCodeFor`** of `Deploy.lean`, for a `Crypto` that hashes the
two constants the constructors push as literals (`ConstHashes`). -/
theorem code_of_create {ctx₁ ctx₂ : Context} {w₀ : World} {tr₁ tr₂ : TransientStorage}
    {msg₁ msg₂ : Message} {fuel₁ fuel₂ : Nat} {r₁ r₂ : MessageResult}
    (h₁ : CreationMsg crypto ctx₁ msg₁ (SolmateAsset.creationCode ++ SolmateAsset.constructorArgs)
      asset 1000000)
    (hr₁ : processMessageCall fuel₁ ctx₁ w₀ tr₁ msg₁ = .ok r₁)
    (h₂ : CreationMsg crypto ctx₂ msg₂
      (SolmateVault.creationCode ++ SolmateVault.constructorArgsFor asset) vault 2000000)
    (hr₂ : processMessageCall fuel₂ ctx₂ r₁.world tr₂ msg₂ = .ok r₂)
    (hda : accountDeployable w₀ asset = true) (hdv : accountDeployable w₀ vault = true)
    (hne : vault ≠ asset) (hpa : ∀ fork, Precompile.isPrecompile fork asset = false)
    (hc : ConstHashes crypto) :
    r₂.world.code asset = SolmateAsset.runtimeCodeFor crypto.keccak256 ctx₁.block.chainId asset ∧
      r₂.world.code vault =
        SolmateVault.runtimeCodeFor crypto.keccak256 ctx₂.block.chainId asset vault := by
  obtain ⟨-, -, hw, hw'⟩ := create_worlds h₁ hr₁ h₂ hr₂ hda hdv hne hpa
  have hacc₁ : ∀ b, r₁.world.account b = if b = asset then _ else w₀.account b := fun b => by
    rw [hw]; exact account_assetWorld _ _ _ _ _
  have hacc₂ : ∀ b, r₂.world.account b = if b = vault then _ else r₁.world.account b := fun b => by
    rw [hw']; exact account_vaultWorld _ _ _ _ _ _ _
  refine ⟨?_, ?_⟩
  · simp only [World.code, hacc₂, hne.symm, hacc₁, ↓reduceIte, SolmateAsset.runtimeCodeFor,
      asset_immutables_eq hc]
  · simp only [World.code, hacc₂, ↓reduceIte, SolmateVault.runtimeCodeFor,
      vault_immutables_eq hc]

/-! ## Deployment followed by any trace -/

/-- **The Solmate deployment**: `w` is the world after creating the asset at `asset` from `w₀`
(canonical arguments), then the vault over it at `vault` (`CreationMsg`: no value, depth 0,
enough gas, hash `crypto`, …), each a terminated top-level message. -/
def Deploys (crypto : Crypto) (w₀ : World) (asset vault : Address) (w : World) : Prop :=
  ∃ (ctx₁ ctx₂ : Context) (tr₁ tr₂ : TransientStorage) (msg₁ msg₂ : Message) (fuel₁ fuel₂ : Nat)
    (r₁ r₂ : MessageResult),
    CreationMsg crypto ctx₁ msg₁ (SolmateAsset.creationCode ++ SolmateAsset.constructorArgs)
      asset 1000000 ∧
    processMessageCall fuel₁ ctx₁ w₀ tr₁ msg₁ = .ok r₁ ∧
    CreationMsg crypto ctx₂ msg₂
      (SolmateVault.creationCode ++ SolmateVault.constructorArgsFor asset) vault 2000000 ∧
    processMessageCall fuel₂ ctx₂ r₁.world tr₂ msg₂ = .ok r₂ ∧ r₂.world = w

/-- The addresses are fresh, distinct and not precompiles. -/
structure FreshPair (w₀ : World) (a v : Address) : Prop where
  hasset : accountDeployable w₀ a = true
  hvault : accountDeployable w₀ v = true
  hne : v ≠ a
  hpa : ∀ fork, Precompile.isPrecompile fork a = false
  hpv : ∀ fork, Precompile.isPrecompile fork v = false

theorem keccakAvoids_sub {crypto : Crypto} {S : ByteArray → Prop} {l l' : List Word}
    (h : KeccakAvoids crypto S l) (hl : ∀ x ∈ l', x ∈ l) : KeccakAvoids crypto S l' :=
  fun x hx hm => h x hx (hl _ hm)

/-- **Deployment yields the starting invariant** (`deployed_inv_of_create` for `Deploys`). -/
theorem deployed_inv_of_deploys {w₀ w : World} (hD : Deploys crypto w₀ asset vault w)
    (hF : FreshPair w₀ asset vault)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [0#256, 1#256]) :
    Deployed w vault asset ∧ Solmate.Inv (abs crypto w vault asset) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h₁, hr₁, h₂, hr₂, rfl⟩ := hD
  obtain ⟨-, -, h⟩ := deployed_inv_of_create h₁ hr₁ h₂ hr₂ hF.hasset hF.hvault hF.hne
    hF.hpa hF.hpv hk
  exact h

variable {Act : List Address} {K : Invariants.VCall → Prop}

/-- **The lifting theorem, anchored**: after the deployment and any trace of modelled calls
(`Invariants.lift`), the world is deployed, its ledgers are well formed, and `abs` agrees with
the model's execution from the deployed state. No starting invariant is assumed. -/
theorem lift_anchored {minGas : Nat} (hs : Invariants.SlotsOk crypto vault Act)
    (hR : Invariants.RefinesFor crypto vault asset minGas Act K)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [0#256, 1#256])
    {w₀ w₁ w : World} {cs : List Invariants.VCall} (hD : Deploys crypto w₀ asset vault w₁)
    (hF : FreshPair w₀ asset vault) (htr : Invariants.Trace crypto vault asset minGas w₁ cs w)
    (hact : ∀ c ∈ cs, ∀ a ∈ c.actors, a ∈ Act) (hK : ∀ c ∈ cs, K c) :
    Deployed w vault asset ∧ Solmate.Inv (abs crypto w vault asset) ∧
      AgreeOn (Invariants.ActorPairs Act) (abs crypto w vault asset)
        (Solmate.exec (abs crypto w₁ vault asset) (cs.map Invariants.VCall.op)) := by
  obtain ⟨hdep, hinv⟩ := deployed_inv_of_deploys hD hF hk
  exact Invariants.lift hs hR hdep hinv htr hact hK

/-- **The lifting theorem for arbitrary transactions at any gas, anchored**
(`LowGas.lift_nested_anyGas` from the deployed world). -/
theorem lift_nested_anyGas_anchored
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [0#256, 1#256, 2#256, 6#256, 7#256])
    (hs : Invariants.SlotsOk crypto vault Act) {w₀ w₁ w : World}
    (hD : Deploys crypto w₀ asset vault w₁) (hF : FreshPair w₀ asset vault)
    (htr : LowGas.TxTraceAnyGas crypto vault asset Act K w₁ w) :
    Deployed w vault asset ∧ Solmate.Inv (abs crypto w vault asset) ∧
      ∃ cs : List Invariants.VCall, (∀ c ∈ cs, Nested.Admitted Act K c) ∧
        AgreeOn (Invariants.ActorPairs Act) (abs crypto w vault asset)
          (Solmate.exec (abs crypto w₁ vault asset) (cs.map Invariants.VCall.op)) := by
  obtain ⟨hdep, hinv⟩ := deployed_inv_of_deploys hD hF
    (keccakAvoids_sub hk (by simp))
  exact LowGas.lift_nested_anyGas (keccakAvoids_sub hk (by simp)) hs hdep hinv htr

/-- **`totalSupply` = Σ `balanceOf` after deployment and any transactions at any gas**, for
the shares and for the asset, read from storage. -/
theorem supply_eq_sum_anchored
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [0#256, 1#256, 2#256, 6#256, 7#256])
    (hs : Invariants.SlotsOk crypto vault Act) {w₀ w₁ w : World}
    (hD : Deploys crypto w₀ asset vault w₁) (hF : FreshPair w₀ asset vault)
    (htr : LowGas.TxTraceAnyGas crypto vault asset Act K w₁ w) :
    (w.sload vault 2#256).toNat =
        ∑ a : Address, (w.sload vault (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat ∧
      (w.sload asset 2#256).toNat =
        ∑ a : Address, (w.sload asset (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat := by
  obtain ⟨hdep, hinv⟩ := deployed_inv_of_deploys hD hF
    (keccakAvoids_sub hk (by simp))
  exact LowGas.supply_eq_sum_nested_anyGas (keccakAvoids_sub hk (by simp)) hs hdep hinv htr

/-- **Solvency after deployment and any transactions at any gas**: `Σₐ ⌊shares[a]·T/S⌋ ≤ T`,
read from storage. -/
theorem solvent_anchored
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [0#256, 1#256, 2#256, 6#256, 7#256])
    (hs : Invariants.SlotsOk crypto vault Act) {w₀ w₁ w : World}
    (hD : Deploys crypto w₀ asset vault w₁) (hF : FreshPair w₀ asset vault)
    (htr : LowGas.TxTraceAnyGas crypto vault asset Act K w₁ w) :
    ∑ a : Address, Invariants.sharesAt crypto w vault a * Invariants.assetsAt crypto w vault asset /
        Invariants.supplyAt w vault ≤ Invariants.assetsAt crypto w vault asset := by
  obtain ⟨hdep, hinv⟩ := deployed_inv_of_deploys hD hF
    (keccakAvoids_sub hk (by simp))
  exact LowGas.solvent_nested_anyGas (keccakAvoids_sub hk (by simp)) hs hdep hinv htr

end Verified.Solmate.Constructor
