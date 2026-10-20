import Examples.Solmate.ERC4626.Invariants.System
import Defi.ERC4626.Price
import Defi.ERC4626.Inflation
import Examples.Solmate.ERC4626.Withdraw
import Examples.Solmate.ERC4626.Deposit

/-!
# The model's invariants hold for the deployed bytecode

The lifting theorem (`Defi/Trace/Lift.lean`) instantiated with the concrete system of
`Invariants/System.lean` and the per-call refinement theorems: along any trace of modelled
top-level calls, supply = Σ balances, solvency, no dilution, price monotonicity, and the
donation attack, on storage (`*_deployed`). See `docs/erc4626/details.md` §3.
-/

section

namespace Examples.Solmate.ERC4626.Invariants
open Examples.Solmate.ERC20 Defi.ERC4626 Defi.Trace
open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open Defi.Math Defi.ERC20 Defi.ERC4626.Solmate Defi.Trace.Lift

variable {crypto : Crypto} {vault asset : Address} {minGas : Nat} {Act : List Address}
  {K : VCall → Prop}

/-! ## Traces -/

/-- **Concrete traces**: modelled calls `cs`, in order, interleaved with environment steps. -/
def Trace (crypto : Crypto) (vault asset : Address) (minGas : Nat) :
    World → List VCall → World → Prop :=
  (system crypto vault asset minGas [] (fun _ => True)).Reach

theorem Trace.nil (w : World) : Trace crypto vault asset minGas w [] w := .refl w

theorem Trace.cons {w w' w'' : World} {c : VCall} {cs : List VCall}
    (h : CallStep crypto vault asset minGas w c w') (t : Trace crypto vault asset minGas w' cs w'') :
    Trace crypto vault asset minGas w (c :: cs) w'' := System.Reach.call h t

theorem Trace.env {w w' w'' : World} {cs : List VCall} (h : EnvStep vault asset w w')
    (t : Trace crypto vault asset minGas w' cs w'') : Trace crypto vault asset minGas w cs w'' :=
  System.Reach.env h t

theorem Trace.reach {w w' : World} {cs : List VCall} (h : Trace crypto vault asset minGas w cs w') :
    (system crypto vault asset minGas Act K).Reach w cs w' :=
  System.Reach.mono (σ := system crypto vault asset minGas [] (fun _ => True))
    (σ' := system crypto vault asset minGas Act K)
    (fun _ _ _ h => h) (fun _ _ h => h) h

theorem Trace.split {w w' : World} {cs₁ cs₂ : List VCall}
    (h : Trace crypto vault asset minGas w (cs₁ ++ cs₂) w') :
    ∃ v, Trace crypto vault asset minGas w cs₁ v ∧ Trace crypto vault asset minGas v cs₂ w' :=
  System.Reach.split h

/-! ## Refinement hypotheses -/

/-- Every call kind admitted by `K` refines its model operation. -/
def RefinesFor (crypto : Crypto) (vault asset : Address) (minGas : Nat) (Act : List Address)
    (K : VCall → Prop) : Prop :=
  ∀ c, K c → OpRefinesAt crypto vault asset minGas Act c

theorem refinesFor_proven (hmin : 100000 ≤ minGas) :
    RefinesFor crypto vault asset minGas Act VCall.Proven :=
  fun c hc => opRefines_proven hmin c hc

/-- The refinement obligations of the four ERC-4626 entry points (discharged by `pending_of`). -/
structure Pending (crypto : Crypto) (vault asset : Address) (minGas : Nat) (Act : List Address) :
    Prop where
  deposit : ∀ c a r, OpRefinesAt crypto vault asset minGas Act (.deposit c a r)
  mint : ∀ c n r, OpRefinesAt crypto vault asset minGas Act (.mint c n r)
  withdraw : ∀ c a r o, OpRefinesAt crypto vault asset minGas Act (.withdraw c a r o)
  redeem : ∀ c n r o, OpRefinesAt crypto vault asset minGas Act (.redeem c n r o)

/-- Every modelled call except the four ERC-4626 entry points. -/
def VCall.NotEntry : VCall → Prop
  | .deposit .. | .mint .. | .withdraw .. | .redeem .. => False
  | .transfer .. | .transferFrom .. | .approve .. | .assetTransfer .. | .assetTransferFrom ..
  | .assetApprove .. | .assetMint .. | .assetBurn .. => True

theorem VCall.Proven.notEntry {c : VCall} (h : c.Proven) : c.NotEntry := by
  cases c <;> first | exact h.elim | trivial

/-- **Every call but the four entry points refines its operation.** -/
theorem opRefines_notEntry (hmin : 100000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256]) (c : VCall) (hc : c.NotEntry) :
    OpRefinesAt crypto vault asset minGas Act c := by
  cases c with
  | assetApprove c sp v => exact opRefines_assetApprove hmin c sp v
  | assetMint c d v => exact opRefines_assetMint hmin hk c d v
  | assetBurn c s v => exact opRefines_assetBurn hmin hk c s v
  | transfer c d v => exact opRefines_transfer hmin c d v
  | transferFrom c s d v => exact opRefines_transferFrom hmin c s d v
  | approve c sp v => exact opRefines_approve hmin c sp v
  | assetTransfer c d v => exact opRefines_assetTransfer hmin c d v
  | assetTransferFrom c s d v => exact opRefines_assetTransferFrom hmin c s d v
  | deposit => exact hc.elim
  | mint => exact hc.elim
  | withdraw => exact hc.elim
  | redeem => exact hc.elim

/-- Every call but the four entry points, under the hash hypothesis that no balance slot is the
`totalSupply` slot (the asset's `mint`/`burn` write it). -/
theorem refinesFor_now (hmin : 100000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256]) :
    RefinesFor crypto vault asset minGas Act VCall.NotEntry :=
  fun c hc => opRefines_notEntry hmin hk c hc

/-- Every call kind, given the entry-point obligations. -/
theorem refinesFor_all (hmin : 100000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256])
    (hp : Pending crypto vault asset minGas Act) :
    RefinesFor crypto vault asset minGas Act (fun _ => True) := by
  intro c _
  cases c with
  | deposit c a r => exact hp.deposit c a r
  | mint c n r => exact hp.mint c n r
  | withdraw c a r o => exact hp.withdraw c a r o
  | redeem c n r o => exact hp.redeem c n r o
  | _ => exact opRefines_notEntry hmin hk _ trivial

theorem RefinesFor.mono {K' : VCall → Prop} (h : RefinesFor crypto vault asset minGas Act K)
    (hK : ∀ c, K' c → K c) : RefinesFor crypto vault asset minGas Act K' :=
  fun c hc => h c (hK c hc)

/-! ## The lifting theorem on bytecode -/

theorem exec_system (s : State Address) (cs : List VCall) :
    Lift.exec (system crypto vault asset minGas Act K).step s cs =
      Solmate.exec s (cs.map VCall.op) := by
  rw [exec_eq]
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih => exact ih _

/-- **The lifting theorem.** Along every trace of admitted calls with actors in `Act`, under
`SlotsOk`, from a deployed world with well-formed ledgers: the final world is deployed, its
ledgers are well formed, and `abs` agrees (up to non-actor allowances) with `Solmate.exec`. -/
theorem lift (hs : SlotsOk crypto vault Act) (hR : RefinesFor crypto vault asset minGas Act K)
    {w₀ w : World} {cs : List VCall} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) (htr : Trace crypto vault asset minGas w₀ cs w)
    (hact : ∀ c ∈ cs, ∀ a ∈ c.actors, a ∈ Act) (hK : ∀ c ∈ cs, K c) :
    Deployed w vault asset ∧ Solmate.Inv (abs crypto w vault asset) ∧
      AgreeOn (ActorPairs Act) (abs crypto w vault asset)
        (Solmate.exec (abs crypto w₀ vault asset) (cs.map VCall.op)) := by
  obtain ⟨h1, h2, h3⟩ := (refinement (K := K) hs hR).lift (σ := system crypto vault asset minGas Act K)
    htr.reach (fun c hc => ⟨hact c hc, hK c hc⟩) hdep ⟨hinv, rfl⟩
  exact ⟨h1, h2.1, exec_system (K := K) (minGas := minGas) _ cs ▸ h3⟩

/-- **Invariants transfer to the bytecode.** A model invariant preserved by every successful
step and insensitive to non-actor allowances, holding initially, holds after every trace. -/
theorem invariant (hs : SlotsOk crypto vault Act) (hR : RefinesFor crypto vault asset minGas Act K)
    {I : State Address → Prop} (hI : ∀ s op s', Solmate.Inv s → I s → step s op = some s' → I s')
    (hIa : ∀ s t, AgreeOn (ActorPairs Act) s t → I s → I t)
    {w₀ w : World} {cs : List VCall} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) (htr : Trace crypto vault asset minGas w₀ cs w)
    (hact : ∀ c ∈ cs, ∀ a ∈ c.actors, a ∈ Act) (hK : ∀ c ∈ cs, K c)
    (hI₀ : I (abs crypto w₀ vault asset)) : I (abs crypto w vault asset) := by
  obtain ⟨-, -, ha⟩ := lift hs hR hdep hinv htr hact hK
  have := (exec_induction (step := step) (Inv := Solmate.Inv) (fun _ _ _ hi h => Inv_step hi h) hI hinv hI₀
    (cs.map VCall.op)).2
  rw [← exec_eq] at this
  exact hIa _ _ ha.symm this

/-! ## Headline corollaries -/

/-- The vault's share supply, read from storage (slot 2). -/
noncomputable def supplyAt (w : World) (vault : Address) : ℕ := (w.sload vault 2#256).toNat

/-- The vault's total assets, read from storage: its balance slot in the asset. -/
noncomputable def assetsAt (crypto : Crypto) (w : World) (vault asset : Address) : ℕ :=
  (w.sload asset (ERC20.balanceSlot crypto ERC20.Layout.solmate vault)).toNat

/-- The share balance of `a`, read from storage. -/
noncomputable def sharesAt (crypto : Crypto) (w : World) (vault a : Address) : ℕ :=
  (w.sload vault (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat

theorem abs_totalSupply' (w : World) :
    (abs crypto w vault asset).totalSupply = supplyAt w vault := rfl

theorem abs_totalAssets' (w : World) :
    (abs crypto w vault asset).totalAssets = assetsAt crypto w vault asset :=
  abs_totalAssets crypto w vault asset

theorem abs_sharesOf (w : World) (a : Address) :
    (abs crypto w vault asset).shares.balanceOf a = sharesAt crypto w vault a :=
  tokenView_balanceOf crypto w vault a

theorem supply_eq_sum_of_wf {w : World} {token : Address} (h : (tokenView crypto w token).WF) :
    (w.sload token 2#256).toNat =
      ∑ a : Address, (w.sload token (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat := by
  rw [← tokenView_totalSupply, ← h.1, total, Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp only [tokenView_balanceOf]

/-- **INV-SUPPLY on bytecode.** In every world reached by a trace, the share token's
`totalSupply` slot is the sum of all its balance slots, and likewise for the asset. -/
theorem supply_eq_sum (hs : SlotsOk crypto vault Act) (hR : RefinesFor crypto vault asset minGas Act K)
    {w₀ w : World} {cs : List VCall} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) (htr : Trace crypto vault asset minGas w₀ cs w)
    (hact : ∀ c ∈ cs, ∀ a ∈ c.actors, a ∈ Act) (hK : ∀ c ∈ cs, K c) :
    (w.sload vault 2#256).toNat =
        ∑ a : Address, (w.sload vault (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat ∧
      (w.sload asset 2#256).toNat =
        ∑ a : Address, (w.sload asset (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat := by
  obtain ⟨-, hi, -⟩ := lift hs hR hdep hinv htr hact hK
  exact ⟨supply_eq_sum_of_wf hi.2, supply_eq_sum_of_wf hi.1⟩

/-- `supply_eq_sum` for every call but the four entry points (`refinesFor_now`). -/
theorem supply_eq_sum_now (hmin : 100000 ≤ minGas) (hs : SlotsOk crypto vault Act)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256])
    {w₀ w : World} {cs : List VCall} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) (htr : Trace crypto vault asset minGas w₀ cs w)
    (hact : ∀ c ∈ cs, ∀ a ∈ c.actors, a ∈ Act) (hK : ∀ c ∈ cs, c.NotEntry) :
    (w.sload vault 2#256).toNat =
        ∑ a : Address, (w.sload vault (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat ∧
      (w.sload asset 2#256).toNat =
        ∑ a : Address, (w.sload asset (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat :=
  supply_eq_sum hs (refinesFor_now hmin hk) hdep hinv htr hact hK

/-- **I-SOLVENT on bytecode.** After any trace, `Σₐ ⌊shares[a]·T/S⌋ ≤ T` (`T` the vault's
asset balance, `S` its share supply, read from storage). -/
theorem solvent (hs : SlotsOk crypto vault Act) (hR : RefinesFor crypto vault asset minGas Act K)
    {w₀ w : World} {cs : List VCall} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) (htr : Trace crypto vault asset minGas w₀ cs w)
    (hact : ∀ c ∈ cs, ∀ a ∈ c.actors, a ∈ Act) (hK : ∀ c ∈ cs, K c) :
    ∑ a : Address, sharesAt crypto w vault a * assetsAt crypto w vault asset / supplyAt w vault ≤
      assetsAt crypto w vault asset := by
  obtain ⟨-, hi, -⟩ := lift hs hR hdep hinv htr hact hK
  have := Solmate.solvent _ hi
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp)] at this
  simpa only [abs_sharesOf, abs_totalAssets', abs_totalSupply'] using this

/-- `solvent` for every call but the four entry points (`refinesFor_now`). -/
theorem solvent_now (hmin : 100000 ≤ minGas) (hs : SlotsOk crypto vault Act)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256])
    {w₀ w : World} {cs : List VCall} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) (htr : Trace crypto vault asset minGas w₀ cs w)
    (hact : ∀ c ∈ cs, ∀ a ∈ c.actors, a ∈ Act) (hK : ∀ c ∈ cs, c.NotEntry) :
    ∑ a : Address, sharesAt crypto w vault a * assetsAt crypto w vault asset / supplyAt w vault ≤
      assetsAt crypto w vault asset :=
  solvent hs (refinesFor_now hmin hk) hdep hinv htr hact hK

/-- **E-PRICE on bytecode (one call).** Inside any trace, a user call (`UserOp`) executed from
a world `v` in which the vault has shares, ending in `v'`, never lowers assets-per-share:
`T(v)·S(v') ≤ T(v')·S(v)`. -/
theorem no_dilution (hs : SlotsOk crypto vault Act) (hR : RefinesFor crypto vault asset minGas Act K)
    {w₀ w : World} {cs₁ cs₂ : List VCall} {c : VCall} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : Trace crypto vault asset minGas w₀ (cs₁ ++ c :: cs₂) w)
    (hact : ∀ d ∈ cs₁ ++ c :: cs₂, ∀ a ∈ d.actors, a ∈ Act) (hK : ∀ d ∈ cs₁ ++ c :: cs₂, K d)
    (hu : UserOp vault c.op) :
    ∃ v v', CallStep crypto vault asset minGas v c v' ∧
      (supplyAt v vault ≠ 0 →
        assetsAt crypto v vault asset * supplyAt v' vault ≤
          assetsAt crypto v' vault asset * supplyAt v vault) := by
  obtain ⟨v, v', hc, ha, ha', hi⟩ := (refinement (K := K) hs hR).lift_step
    (σ := system crypto vault asset minGas Act K) htr.reach
    (fun c' hc => ⟨hact c' hc, hK c' hc⟩) hdep ⟨hinv, rfl⟩
  refine ⟨v, v', hc, fun hS => ?_⟩
  set s := Lift.exec (system crypto vault asset minGas Act K).step (abs crypto w₀ vault asset) cs₁
  have ha₁ : AgreeOn (ActorPairs Act) (abs crypto v vault asset) s := ha
  have ha₂ : AgreeOn (ActorPairs Act) (abs crypto v' vault asset)
      (Lift.stepD step s c.op) := ha'
  rw [← abs_totalSupply', ← abs_totalSupply', ← abs_totalAssets', ← abs_totalAssets',
    ha₁.totalSupply, ha₂.totalSupply, ha₁.totalAssets, ha₂.totalAssets]
  rw [← abs_totalSupply', ha₁.totalSupply] at hS
  exact price_mono_stepD hi.1 (hi.2 ▸ hu) hS

/-- **E-PRICE on bytecode (whole trace).** Along a trace of user calls during which the vault
is never empty (every world on the trace at a call boundary has shares), the share price
`T/S` read from storage never decreases. -/
theorem price_mono (hs : SlotsOk crypto vault Act) (hR : RefinesFor crypto vault asset minGas Act K)
    {w₀ w : World} {cs : List VCall} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) (htr : Trace crypto vault asset minGas w₀ cs w)
    (hact : ∀ c ∈ cs, ∀ a ∈ c.actors, a ∈ Act) (hK : ∀ c ∈ cs, K c)
    (hu : ∀ c ∈ cs, UserOp vault c.op)
    (hS : ∀ k v, Trace crypto vault asset minGas w₀ (cs.take k) v →
      Trace crypto vault asset minGas v (cs.drop k) w → supplyAt v vault ≠ 0) :
    (assetsAt crypto w₀ vault asset : ℚ) / supplyAt w₀ vault ≤
      (assetsAt crypto w vault asset : ℚ) / supplyAt w vault := by
  have hmodel := price_exec_mono (s := abs crypto w₀ vault asset) hinv
    (ops := cs.map VCall.op) (fun op hop => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hop
      exact hu c hc) (fun k hk => ?_)
  · obtain ⟨-, -, ha⟩ := lift hs hR hdep hinv htr hact hK
    rw [exec_eq] at ha
    have hp := ha.price
    unfold State.price at hp hmodel
    rw [abs_totalAssets', abs_totalSupply'] at hp hmodel
    rw [hp]; exact hmodel
  · have hk' : k ≤ cs.length := by simpa using hk
    rw [← List.take_append_drop k cs] at htr
    obtain ⟨v, h₁, h₂⟩ := Trace.split htr
    have hv := hS k v h₁ h₂
    obtain ⟨-, -, ha⟩ := lift hs hR hdep hinv h₁ (fun c hc => hact c (List.mem_of_mem_take hc))
      (fun c hc => hK c (List.mem_of_mem_take hc))
    rw [exec_eq, List.map_take] at ha
    rw [← ha.totalSupply, abs_totalSupply']
    exact hv

/-- `no_dilution` for every call but the four entry points (`refinesFor_now`). -/
theorem no_dilution_now (hmin : 100000 ≤ minGas) (hs : SlotsOk crypto vault Act)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256])
    {w₀ w : World} {cs₁ cs₂ : List VCall} {c : VCall} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : Trace crypto vault asset minGas w₀ (cs₁ ++ c :: cs₂) w)
    (hact : ∀ d ∈ cs₁ ++ c :: cs₂, ∀ a ∈ d.actors, a ∈ Act)
    (hK : ∀ d ∈ cs₁ ++ c :: cs₂, d.NotEntry) (hu : UserOp vault c.op) :
    ∃ v v', CallStep crypto vault asset minGas v c v' ∧
      (supplyAt v vault ≠ 0 →
        assetsAt crypto v vault asset * supplyAt v' vault ≤
          assetsAt crypto v' vault asset * supplyAt v vault) :=
  no_dilution hs (refinesFor_now hmin hk) hdep hinv htr hact hK hu

/-- `price_mono` for every call but the four entry points (`refinesFor_now`). -/
theorem price_mono_now (hmin : 100000 ≤ minGas) (hs : SlotsOk crypto vault Act)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256])
    {w₀ w : World} {cs : List VCall} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) (htr : Trace crypto vault asset minGas w₀ cs w)
    (hact : ∀ c ∈ cs, ∀ a ∈ c.actors, a ∈ Act) (hK : ∀ c ∈ cs, c.NotEntry)
    (hu : ∀ c ∈ cs, UserOp vault c.op)
    (hS : ∀ k v, Trace crypto vault asset minGas w₀ (cs.take k) v →
      Trace crypto vault asset minGas v (cs.drop k) w → supplyAt v vault ≠ 0) :
    (assetsAt crypto w₀ vault asset : ℚ) / supplyAt w₀ vault ≤
      (assetsAt crypto w vault asset : ℚ) / supplyAt w vault :=
  price_mono hs (refinesFor_now hmin hk) hdep hinv htr hact hK hu hS

/-! ## The donation attack on bytecode -/

/-- The calls admitted for the attack: `VCall.Proven` and `deposit`. -/
def VCall.ProvenOrDeposit (c : VCall) : Prop :=
  c.Proven ∨ ∃ c' a r, c = .deposit c' a r

/-- **The donation (first-depositor) attack on the bytecode.** From an empty vault, the trace
attacker `deposit(1)`, `asset.transfer(vault, D)`, victim `deposit(a, r)` (funded: `h₁`, `h₂`)
ends with: if `a ≤ D`, the attacker holds the only share and `r` none; if `D < a ≤ 2D + 1`,
the victim's call reverted or `r` got one share worth `⌊(a + D + 1)/2⌋`. Takes the `deposit`
refinement as a hypothesis. -/
theorem donation_attack (hmin : 100000 ≤ minGas)
    (hdepR : ∀ c a r, OpRefinesAt crypto vault asset minGas Act (.deposit c a r))
    (hs : SlotsOk crypto vault Act) {att v r : Address} (hatt : att ∈ Act) (hv : v ∈ Act)
    (hr : r ∈ Act) (hattv : att ≠ vault) (hvv : v ≠ vault)
    {w₀ w : World} (hdep : Deployed w₀ vault asset) (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (hS : supplyAt w₀ vault = 0) (hT : assetsAt crypto w₀ vault asset = 0)
    {D a : Word} {s₁ s₂ : State Address} {n : ℕ}
    (h₁ : Solmate.deposit (abs crypto w₀ vault asset) att 1 att = some (s₁, n))
    (h₂ : step s₁ (.assetTransfer att vault D.toNat) = some s₂)
    (htr : Trace crypto vault asset minGas w₀
      [.deposit att 1#256 att, .assetTransfer att vault D, .deposit v a r] w) :
    (a.toNat ≤ D.toNat →
      supplyAt w vault = 1 ∧ assetsAt crypto w vault asset = D.toNat + 1 ∧
        sharesAt crypto w vault att = 1 ∧ (r ≠ att → sharesAt crypto w vault r = 0)) ∧
    (D.toNat < a.toNat → a.toNat ≤ 2 * D.toNat + 1 →
      (supplyAt w vault = 1 ∧ assetsAt crypto w vault asset = D.toNat + 1) ∨
      (supplyAt w vault = 2 ∧ assetsAt crypto w vault asset = a.toNat + D.toNat + 1 ∧
        (r ≠ att → sharesAt crypto w vault r = 1) ∧
        (abs crypto w vault asset).convertToAssets 1 = some ((a.toNat + D.toNat + 1) / 2))) := by
  have hR : RefinesFor crypto vault asset minGas Act VCall.ProvenOrDeposit := by
    rintro c (hc | ⟨c', a', r', rfl⟩)
    · exact opRefines_proven hmin c hc
    · exact hdepR c' a' r'
  obtain ⟨-, -, hag⟩ := lift hs hR hdep hinv htr
    (by simp [VCall.actors, hatt, hv, hr, hs.vault_mem])
    (by simp [VCall.ProvenOrDeposit, VCall.Proven])
  set s₀ := abs crypto w₀ vault asset
  have hself₀ : s₀.self = vault := rfl
  have e₁ : step s₀ (VCall.deposit att 1#256 att).op = some s₁ := by
    show Option.map Prod.fst (Solmate.deposit s₀ att (1#256).toNat att) = _
    rw [show (1#256 : Word).toNat = 1 from rfl, h₁]; rfl
  have hself₁ : s₁.self = vault := (self_step e₁).trans hself₀
  have hi₁ : Solmate.Inv s₁ := Inv_step hinv e₁
  have hi₂ : Solmate.Inv s₂ := Inv_step hi₁ h₂
  have hself₂ : s₂.self = vault := (self_step h₂).trans hself₁
  obtain ⟨-, hS₂, hT₂, hb₂⟩ := solmate_attack_setup (s₀ := s₀) hinv
    (by rw [abs_totalSupply']; exact hS) (by rw [abs_totalAssets']; exact hT)
    (by rw [hself₀]; exact hattv) h₁ (by rw [hself₁]; exact h₂)
  have hexec : Solmate.exec s₀ (List.map VCall.op
      [.deposit att 1#256 att, .assetTransfer att vault D, .deposit v a r]) =
      (step s₂ (.deposit v a.toNat r)).getD s₂ := by
    simp only [List.map_cons, List.map_nil, Solmate.exec]
    rw [e₁]
    simp only [Option.getD_some, VCall.op]
    rw [h₂]
    rfl
  rw [hexec] at hag
  have hr₂ : r ≠ att → s₂.shares.balanceOf r = 0 := by
    intro hra
    have h := Defi.ERC20.add_le_total (f := s₂.shares.balanceOf) hra
    rw [hi₂.2.1, hb₂] at h
    change _ + 1 ≤ s₂.totalSupply at h
    omega
  have hread : ∀ x, sharesAt crypto w vault x =
      ((step s₂ (.deposit v a.toNat r)).getD s₂).shares.balanceOf x := fun x => by
    rw [← abs_sharesOf, hag.shares.balanceOf]
  have hSw : supplyAt w vault = ((step s₂ (.deposit v a.toNat r)).getD s₂).totalSupply := by
    rw [← abs_totalSupply', hag.totalSupply]
  have hTw : assetsAt crypto w vault asset =
      ((step s₂ (.deposit v a.toNat r)).getD s₂).totalAssets := by
    rw [← abs_totalAssets', hag.totalAssets]
  constructor
  · intro ha
    obtain ⟨-, hnone⟩ := solmate_attack_victim_reverts (v := v) (r := r) hi₂ hS₂ hT₂ ha
    have : step s₂ (.deposit v a.toNat r) = none := by
      show Option.map Prod.fst _ = none; rw [hnone]; rfl
    rw [this, Option.getD_none] at hread hSw hTw
    exact ⟨hSw.trans hS₂, hTw.trans hT₂, (hread att).trans hb₂,
      fun hra => (hread r).trans (hr₂ hra)⟩
  · intro ha₁ ha₂
    cases e : Solmate.deposit s₂ v a.toNat r with
    | none =>
      have : step s₂ (.deposit v a.toNat r) = none := by
        show Option.map Prod.fst _ = none; rw [e]; rfl
      rw [this, Option.getD_none] at hSw hTw
      exact .inl ⟨hSw.trans hS₂, hTw.trans hT₂⟩
    | some p =>
      obtain ⟨s₃, m⟩ := p
      have : step s₂ (.deposit v a.toNat r) = some s₃ := by
        show Option.map Prod.fst _ = _; rw [e]; rfl
      rw [this, Option.getD_some] at hread hSw hTw hag
      obtain ⟨hm, hS₃, hT₃, hconv, -, -⟩ :=
        solmate_attack_victim_one_share hi₂ hS₂ hT₂ ha₁ ha₂ (by rw [hself₂]; exact hvv) e
      subst hm
      obtain ⟨-, -, -, -, -, -, -, hb, -⟩ := deposit_eq_some e
      refine .inr ⟨hSw.trans hS₃, hTw.trans hT₃, fun hra => ?_, ?_⟩
      · rw [hread r, hb, Token.add_single_apply, hr₂ hra]; simp
      · rw [hag.convertToAssets]; exact hconv

/-- In the successful-victim case of `donation_attack`, a top-level `convertToAssets(1)` call
returns `⌊(a + D + 1)/2⌋` and changes nothing. -/
theorem donation_attack_view {w : World} {ctx : Context} {tr : TransientStorage}
    {caller : Address} {gas : Nat} {wa : AddressSet} {wk : StorageKeySet} {x : ℕ}
    (hdep : Deployed w vault asset) (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hgas : 60000 ≤ gas) (hgas' : gas < 2 ^ 64)
    (hconv : (abs ctx.crypto w vault asset).convertToAssets 1 = some x) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller (Abi.encodeCall 0x07a2d13a [1#256]) gas wa wk) =
          .ok res ∧ res.world = w ∧ ViewResult res (some x) := by
  have h := convertToAssets_call (tr := tr) (caller := caller) (wa := wa) (wk := wk) hdep hdeleg
    hgas hgas' 1#256
  rw [show (1#256 : Word).toNat = 1 from rfl, hconv] at h
  exact h

end Examples.Solmate.ERC4626.Invariants

end

section

/-!
## `withdraw` / `redeem`: the `Pending` obligations

From `withdraw_call` / `redeem_call`. `hk`: no balance slot is the `totalSupply` slot or the
`beforeWithdraw` counter (both are written); `SlotsOk` gives the rest of `Out.OutSlots`.
-/

namespace Examples.Solmate.ERC4626.Invariants
open Examples.Solmate.ERC20 Defi.ERC4626 Defi.Trace
open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open Defi.Math Defi.ERC20 Defi.ERC4626.Solmate Defi.Trace.Lift
open Examples.Solmate.ERC4626.Out

variable {crypto : Crypto} {vault asset : Address} {minGas : Nat} {Act : List Address}

theorem outSlots_of (hs : SlotsOk crypto vault Act)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256]) {c r o : Address}
    (hc : c ∈ Act) (hr : r ∈ Act) (ho : o ∈ Act) : OutSlots crypto vault c o r where
  rows := hk
  ownerOk := hs.bal o ho
  owner7 := (hs.balFixed o ho).2
  allowOk := fun _ => hs.allow o ho c hc
  allow67 := fun _ => hs.allowFixed o ho c hc
  vaultOk := hs.bal vault hs.vault_mem
  receiverOk := hs.bal r hr

theorem outAllowances_of (hs : SlotsOk crypto vault Act) {c o : Address} (hc : c ∈ Act)
    (ho : o ∈ Act) {a b : Address} (h : ActorPairs Act a b) : OutAllowances crypto c o a b := by
  obtain ⟨ha, hb⟩ := h
  refine ⟨?_, (hs.allowFixed a ha b hb).1,
    (ERC20.balanceSlot_ne_allowanceSlot (hs.allow a ha b hb) o).symm, (hs.allow a ha b hb).2.2⟩
  rcases hs.allowP ha hb ho hc with h | h
  · exact .inr (.inl h)
  · exact .inr (.inr h)

theorem transferAllowances_of (hs : SlotsOk crypto vault Act) {r : Address} {a b : Address}
    (h : ActorPairs Act a b) : TransferAllowances crypto vault r a b :=
  ⟨(ERC20.balanceSlot_ne_allowanceSlot (hs.allow a h.1 b h.2) _).symm,
    (ERC20.balanceSlot_ne_allowanceSlot (hs.allow a h.1 b h.2) _).symm⟩

theorem agree_of_refinesOn (hs : SlotsOk crypto vault Act) {c r o : Address} (hc : c ∈ Act)
    (ho : o ∈ Act) {w' : World} {s' : State Address}
    (h : RefinesOn (OutAllowances crypto c o) (TransferAllowances crypto vault r) crypto w' vault
      asset s') :
    AgreeOn (ActorPairs Act) (abs crypto w' vault asset) s' :=
  agree_of_reps h.self h.shares h.asset (fun _ _ hp => outAllowances_of hs hc ho hp)
    (fun _ _ hp => transferAllowances_of hs hp) h.afterDeposit h.beforeWithdraw

set_option maxHeartbeats 1000000 in
/-- **`vault.withdraw`** refines `Op.withdraw`. -/
theorem opRefines_withdraw (hmin : 200000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256]) (caller : Address)
    (assets : Word) (receiver owner : Address) :
    OpRefinesAt crypto vault asset minGas Act (.withdraw caller assets receiver owner) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, hg', -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, Bool.false_eq_true,
    ite_false] at hn
  have hc : caller ∈ Act := hact caller (by simp [VCall.actors])
  have hr : receiver ∈ Act := hact receiver (by simp [VCall.actors])
  have ho : owner ∈ Act := hact owner (by simp [VCall.actors])
  obtain ⟨n', hn'⟩ := withdraw_call (tr := tr) (wa := wa) (wk := wk) hdep hdeleg (by omega) hg'
    (outSlots_of hs hk hc hr ho) hinv assets
  obtain ⟨res, hrun, hres⟩ := hn' (max n n') (le_max_right _ _)
  obtain rfl := terminates_unique hn (le_max_left _ _) hrun
  unfold OutResult at hres
  split at hres
  · rename_i s' v hW
    obtain ⟨-, -, hR, hC⟩ := hres
    refine ⟨hdep.of_code (hC vault) (hC asset), callRefines_some ?_ (agree_of_refinesOn hs hc ho hR)⟩
    show Option.map Prod.fst (Solmate.withdraw _ _ _ _ _) = _
    rw [hW]; rfl
  · rename_i hW
    obtain ⟨-, -, hwld⟩ := hres
    refine ⟨hwld ▸ hdep, callRefines_none ?_ hwld⟩
    show Option.map Prod.fst (Solmate.withdraw _ _ _ _ _) = _
    rw [hW]; rfl

set_option maxHeartbeats 1000000 in
/-- **`vault.redeem`** refines `Op.redeem`. -/
theorem opRefines_redeem (hmin : 200000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256]) (caller : Address)
    (shares : Word) (receiver owner : Address) :
    OpRefinesAt crypto vault asset minGas Act (.redeem caller shares receiver owner) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, hg', -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, Bool.false_eq_true,
    ite_false] at hn
  have hc : caller ∈ Act := hact caller (by simp [VCall.actors])
  have hr : receiver ∈ Act := hact receiver (by simp [VCall.actors])
  have ho : owner ∈ Act := hact owner (by simp [VCall.actors])
  obtain ⟨n', hn'⟩ := redeem_call (tr := tr) (wa := wa) (wk := wk) hdep hdeleg (by omega) hg'
    (outSlots_of hs hk hc hr ho) hinv shares
  obtain ⟨res, hrun, hres⟩ := hn' (max n n') (le_max_right _ _)
  obtain rfl := terminates_unique hn (le_max_left _ _) hrun
  unfold OutResult at hres
  split at hres
  · rename_i s' v hW
    obtain ⟨-, -, hR, hC⟩ := hres
    refine ⟨hdep.of_code (hC vault) (hC asset), callRefines_some ?_ (agree_of_refinesOn hs hc ho hR)⟩
    show Option.map Prod.fst (Solmate.redeem _ _ _ _ _) = _
    rw [hW]; rfl
  · rename_i hW
    obtain ⟨-, -, hwld⟩ := hres
    refine ⟨hwld ▸ hdep, callRefines_none ?_ hwld⟩
    show Option.map Prod.fst (Solmate.redeem _ _ _ _ _) = _
    rw [hW]; rfl

end Examples.Solmate.ERC4626.Invariants

end

section

/-!
## `deposit` / `mint`: the `Pending` obligations

From `deposit_call` / `mint_call`. `hk`: no balance slot is slot 2 or 7 (written) or counter 6
(the receiver's balance write must not touch it); `SlotsOk` gives the per-actor slots.
-/

namespace Examples.Solmate.ERC4626.Invariants
open Examples.Solmate.ERC20 Defi.ERC4626 Defi.Trace
open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open Defi.Math Defi.ERC20 Defi.ERC4626.Solmate Defi.Trace.Lift

variable {crypto : Crypto} {vault asset : Address} {minGas : Nat} {Act : List Address}

theorem depositAllowances_of (hs : SlotsOk crypto vault Act) {r : Address} {a b : Address}
    (h : ActorPairs Act a b) : DepositAllowances crypto r a b :=
  ⟨⟨(hs.allow a h.1 b h.2).2.2, hs.balP h.1 h.2 r⟩, (hs.allowFixed a h.1 b h.2).2⟩

theorem transferFromAllowances_of (hs : SlotsOk crypto vault Act) {c : Address} (hc : c ∈ Act)
    {a b : Address} (h : ActorPairs Act a b) : TransferFromAllowances crypto vault c vault a b :=
  ⟨⟨hs.balP h.1 h.2 c, hs.balP h.1 h.2 vault⟩, hs.allowP h.1 h.2 hc hs.vault_mem⟩

theorem agree_of_entry (hs : SlotsOk crypto vault Act) {c r : Address} (hc : c ∈ Act)
    {w' : World} {s' : State Address}
    (h : Out.RefinesOn (DepositAllowances crypto r) (TransferFromAllowances crypto vault c vault)
      crypto w' vault asset s') :
    AgreeOn (ActorPairs Act) (abs crypto w' vault asset) s' :=
  agree_of_reps h.self h.shares h.asset (fun _ _ hp => depositAllowances_of hs hp)
    (fun _ _ hp => transferFromAllowances_of hs hc hp) h.afterDeposit h.beforeWithdraw

set_option maxHeartbeats 1000000 in
/-- **`vault.deposit`** refines `Op.deposit`. -/
theorem opRefines_deposit (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256]) (caller : Address)
    (assets : Word) (receiver : Address) :
    OpRefinesAt crypto vault asset minGas Act (.deposit caller assets receiver) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, hg', -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, Bool.false_eq_true,
    ite_false] at hn
  have hc : caller ∈ Act := hact caller (by simp [VCall.actors])
  have hr : receiver ∈ Act := hact receiver (by simp [VCall.actors])
  obtain ⟨n', hn'⟩ := deposit_call (tr := tr) (wa := wa) (wk := wk) hdep hdeleg (by omega) hg'
    hk (hs.bal caller hc) (hs.bal vault hs.vault_mem) (hs.bal receiver hr)
    (hs.allow caller hc vault hs.vault_mem) hinv assets
  obtain ⟨res, hrun, hres⟩ := hn' (max n n') (le_max_right _ _)
  obtain rfl := terminates_unique hn (le_max_left _ _) hrun
  unfold EntryResult at hres
  split at hres
  · rename_i s' v hW
    obtain ⟨-, -, hwld, hR⟩ := hres
    refine ⟨hdep.of_code (by rw [hwld]; exact code_depositWorld ..)
      (by rw [hwld]; exact code_depositWorld ..), callRefines_some ?_ (agree_of_entry hs hc hR)⟩
    show Option.map Prod.fst (Solmate.deposit _ _ _ _) = _
    rw [hW]; rfl
  · rename_i hW
    obtain ⟨-, -, hwld⟩ := hres
    refine ⟨hwld ▸ hdep, callRefines_none ?_ hwld⟩
    show Option.map Prod.fst (Solmate.deposit _ _ _ _) = _
    rw [hW]; rfl

set_option maxHeartbeats 1000000 in
/-- **`vault.mint`** refines `Op.mint`. -/
theorem opRefines_mint (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256]) (caller : Address)
    (shares : Word) (receiver : Address) :
    OpRefinesAt crypto vault asset minGas Act (.mint caller shares receiver) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, hg', -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, Bool.false_eq_true,
    ite_false] at hn
  have hc : caller ∈ Act := hact caller (by simp [VCall.actors])
  have hr : receiver ∈ Act := hact receiver (by simp [VCall.actors])
  obtain ⟨n', hn'⟩ := mint_call (tr := tr) (wa := wa) (wk := wk) hdep hdeleg (by omega) hg'
    hk (hs.bal caller hc) (hs.bal vault hs.vault_mem) (hs.bal receiver hr)
    (hs.allow caller hc vault hs.vault_mem) hinv shares
  obtain ⟨res, hrun, hres⟩ := hn' (max n n') (le_max_right _ _)
  obtain rfl := terminates_unique hn (le_max_left _ _) hrun
  unfold EntryResult at hres
  split at hres
  · rename_i s' v hW
    obtain ⟨-, -, hwld, hR⟩ := hres
    refine ⟨hdep.of_code (by rw [hwld]; exact code_depositWorld ..)
      (by rw [hwld]; exact code_depositWorld ..), callRefines_some ?_ (agree_of_entry hs hc hR)⟩
    show Option.map Prod.fst (Solmate.mint _ _ _ _) = _
    rw [hW]; rfl
  · rename_i hW
    obtain ⟨-, -, hwld⟩ := hres
    refine ⟨hwld ▸ hdep, callRefines_none ?_ hwld⟩
    show Option.map Prod.fst (Solmate.mint _ _ _ _) = _
    rw [hW]; rfl

/-- All four entry-point obligations, under the fixed-slot hypothesis `[2, 6, 7]`. -/
theorem pending_of (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256]) :
    Pending crypto vault asset minGas Act where
  deposit c a r := opRefines_deposit hmin hk c a r
  mint c n r := opRefines_mint hmin hk c n r
  withdraw c a r o := opRefines_withdraw (by omega) (KeccakAvoids.sub hk (by simp)) c a r o
  redeem c n r o := opRefines_redeem (by omega) (KeccakAvoids.sub hk (by simp)) c n r o

/-- **Every call kind refines its operation** under `SlotsOk` and the fixed-slot hypothesis. -/
theorem refinesFor_all_of (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256]) :
    RefinesFor crypto vault asset minGas Act (fun _ => True) :=
  refinesFor_all (by omega) (KeccakAvoids.sub hk (by simp)) (pending_of hmin hk)

end Examples.Solmate.ERC4626.Invariants

end

section

/-!
## The headline theorems, with every call kind proved

`refinesFor_all_of` instantiates the generic theorems above. Hypotheses: `hmin` (gas per call),
`hk`/`hs` (Keccak freshness of the fixed slots and the actors' slots; global injectivity is
never assumed), `hdep`/`hinv`, `htr`. See `docs/erc4626/README.md` (Hypotheses and exclusions).
-/

namespace Examples.Solmate.ERC4626.Invariants
open Examples.Solmate.ERC20 Defi.ERC4626 Defi.Trace
open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open Defi.Math Defi.ERC20 Defi.ERC4626.Solmate Defi.Trace.Lift

variable {crypto : Crypto} {vault asset : Address} {minGas : Nat} {Act : List Address}

/-- **Share and asset supply equal the sum of balances** after any trace of modelled calls. -/
theorem supply_eq_sum_deployed (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} {cs : List VCall}
    (hdep : Deployed w₀ vault asset) (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : Trace crypto vault asset minGas w₀ cs w) (hact : ∀ c ∈ cs, ∀ a ∈ c.actors, a ∈ Act) :
    (w.sload vault 2#256).toNat =
        ∑ a : Address, (w.sload vault (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat ∧
      (w.sload asset 2#256).toNat =
        ∑ a : Address, (w.sload asset (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat :=
  supply_eq_sum hs (refinesFor_all_of hmin hk) hdep hinv htr hact (fun _ _ => trivial)

/-- **Solvency**: the vault's asset balance covers every holder's shares converted at the
current price (rounding down), after any trace of modelled calls. -/
theorem solvent_deployed (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} {cs : List VCall}
    (hdep : Deployed w₀ vault asset) (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : Trace crypto vault asset minGas w₀ cs w) (hact : ∀ c ∈ cs, ∀ a ∈ c.actors, a ∈ Act) :
    ∑ a : Address, sharesAt crypto w vault a * assetsAt crypto w vault asset / supplyAt w vault ≤
      assetsAt crypto w vault asset :=
  solvent hs (refinesFor_all_of hmin hk) hdep hinv htr hact (fun _ _ => trivial)

/-- **No dilution**: inside any trace, a user operation (deposit, mint, withdraw, redeem)
starting with shares outstanding never lowers the assets-per-share price `T / S`. -/
theorem no_dilution_deployed (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} {cs₁ cs₂ : List VCall} {c : VCall}
    (hdep : Deployed w₀ vault asset) (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : Trace crypto vault asset minGas w₀ (cs₁ ++ c :: cs₂) w)
    (hact : ∀ d ∈ cs₁ ++ c :: cs₂, ∀ a ∈ d.actors, a ∈ Act) (hu : UserOp vault c.op) :
    ∃ v v', CallStep crypto vault asset minGas v c v' ∧
      (supplyAt v vault ≠ 0 →
        assetsAt crypto v vault asset * supplyAt v' vault ≤
          assetsAt crypto v' vault asset * supplyAt v vault) :=
  no_dilution hs (refinesFor_all_of hmin hk) hdep hinv htr hact (fun _ _ => trivial) hu

/-- **Price monotonicity**: along a trace of user operations that never empties the vault,
the assets-per-share price never decreases. -/
theorem price_mono_deployed (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} {cs : List VCall}
    (hdep : Deployed w₀ vault asset) (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : Trace crypto vault asset minGas w₀ cs w) (hact : ∀ c ∈ cs, ∀ a ∈ c.actors, a ∈ Act)
    (hu : ∀ c ∈ cs, UserOp vault c.op)
    (hS : ∀ k v, Trace crypto vault asset minGas w₀ (cs.take k) v →
      Trace crypto vault asset minGas v (cs.drop k) w → supplyAt v vault ≠ 0) :
    (assetsAt crypto w₀ vault asset : ℚ) / supplyAt w₀ vault ≤
      (assetsAt crypto w vault asset : ℚ) / supplyAt w vault :=
  price_mono hs (refinesFor_all_of hmin hk) hdep hinv htr hact (fun _ _ => trivial) hu hS

/-- **The donation attack on the deployed bytecode**: `donation_attack` with the `deposit`
refinement discharged. -/
theorem donation_attack_deployed (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {att v r : Address} (hatt : att ∈ Act) (hv : v ∈ Act)
    (hr : r ∈ Act) (hattv : att ≠ vault) (hvv : v ≠ vault)
    {w₀ w : World} (hdep : Deployed w₀ vault asset) (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (hS : supplyAt w₀ vault = 0) (hT : assetsAt crypto w₀ vault asset = 0)
    {D a : Word} {s₁ s₂ : State Address} {n : ℕ}
    (h₁ : Solmate.deposit (abs crypto w₀ vault asset) att 1 att = some (s₁, n))
    (h₂ : step s₁ (.assetTransfer att vault D.toNat) = some s₂)
    (htr : Trace crypto vault asset minGas w₀
      [.deposit att 1#256 att, .assetTransfer att vault D, .deposit v a r] w) :
    (a.toNat ≤ D.toNat →
      supplyAt w vault = 1 ∧ assetsAt crypto w vault asset = D.toNat + 1 ∧
        sharesAt crypto w vault att = 1 ∧ (r ≠ att → sharesAt crypto w vault r = 0)) ∧
    (D.toNat < a.toNat → a.toNat ≤ 2 * D.toNat + 1 →
      (supplyAt w vault = 1 ∧ assetsAt crypto w vault asset = D.toNat + 1) ∨
      (supplyAt w vault = 2 ∧ assetsAt crypto w vault asset = a.toNat + D.toNat + 1 ∧
        (r ≠ att → sharesAt crypto w vault r = 1) ∧
        (abs crypto w vault asset).convertToAssets 1 = some ((a.toNat + D.toNat + 1) / 2))) :=
  donation_attack (by omega) (fun c a r => opRefines_deposit hmin hk c a r) hs hatt hv hr hattv
    hvv hdep hinv hS hT h₁ h₂ htr

end Examples.Solmate.ERC4626.Invariants

end
