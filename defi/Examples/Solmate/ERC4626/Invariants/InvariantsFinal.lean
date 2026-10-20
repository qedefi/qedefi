import Examples.Solmate.ERC4626.Invariants.InvariantsDepositMint

/-!
# The headline theorems, with every call kind proved

`Invariants.lean` states each headline property for any refinement hypothesis
`RefinesFor … K`. `refinesFor_all_of` discharges that hypothesis for **every** modelled call
(the four ERC-4626 entry points, the vault's share-token functions and views, and the asset's
transfers, approvals, mints and burns, including donations to the vault). This file
instantiates it, so the theorems below are about the deployed bytecode with no pending
refinement obligations.

The remaining hypotheses, all explicit:

* `hmin`: every modelled call in the trace carries at least 250 000 gas (and below 2⁶⁴, in
  `Trace`); calls carry no ETH; no EIP-7702 authorizations (or a fork before Prague).
* `hk`, `hs`: Keccak freshness. No address's share-balance slot is one of the fixed slots
  2, 6, 7, and the balance/allowance slots of the finitely many actors are fresh (`SlotsOk`).
  Global Keccak injectivity is false (pigeonhole) and is never assumed.
* `hdep`, `hinv`: the vault and the asset hold the compiled Solmate `MockERC4626` /
  `MockERC20` runtime code (any immutables), and the initial ledgers are well formed.
* `htr`: the trace consists of top-level modelled calls by arbitrary callers (success or
  revert) interleaved with arbitrary steps that leave the vault's and asset's storage and code
  unchanged. Nested calls into the vault from other contracts are covered at frame level for
  the entry points and views, not yet by the trace (see `INVARIANTS.md`).
-/

namespace EvmLeanSpecs.Refinement.Invariants

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Vault EvmLeanSpecs.Vault.Solmate EvmLeanSpecs.Refinement.Lift

variable {crypto : Crypto} {vault asset : Address} {minGas : Nat} {Act : List Address}

/-- **Share and asset supply equal the sum of balances**, on the deployed bytecode, after any
trace of modelled calls. -/
theorem supply_eq_sum_deployed (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} {cs : List VCall}
    (hdep : Deployed w₀ vault asset) (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : Trace crypto vault asset minGas w₀ cs w) (hact : ∀ c ∈ cs, ∀ a ∈ c.actors, a ∈ Act) :
    (w.sload vault 2#256).toNat =
        ∑ a : Address, (w.sload vault (Erc20.balanceSlot crypto Erc20.Layout.solmate a)).toNat ∧
      (w.sload asset 2#256).toNat =
        ∑ a : Address, (w.sload asset (Erc20.balanceSlot crypto Erc20.Layout.solmate a)).toNat :=
  supply_eq_sum hs (refinesFor_all_of hmin hk) hdep hinv htr hact (fun _ _ => trivial)

/-- **Solvency**: the vault's asset balance covers every holder's shares converted at the
current price (rounding down), on the deployed bytecode, after any trace of modelled calls. -/
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

/-- **The first-depositor donation attack, executed on the deployed bytecode**: attacker
`deposit(1)`, donation of `D` assets, victim `deposit(a)`. If `a ≤ D` the victim's receiver
gets no shares and the attacker holds the only share; if `D < a ≤ 2D + 1` either the victim's
call reverted or the receiver got exactly one share worth `⌊(a + D + 1)/2⌋`. -/
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

end EvmLeanSpecs.Refinement.Invariants
