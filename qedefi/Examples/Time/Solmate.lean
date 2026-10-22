import Examples.Solmate.ERC4626.Nested.Invariants
import QEDefi.Trace.Time

/-!
# The Solmate vault across blocks

The Solmate ERC-4626 vault is time-independent, so its multi-block theorems are instances of
the single-sequence ones at no cost: a multi-block trace (`BlockTrace` of `BlockTxStep`: in
each block, covered transactions executed **in that block's environment**, and environment
steps) is in particular a `TxTrace`, whatever the block environments are
(`txTrace_of_blockTrace`). The headline theorems `lift_nested`, `invariant_nested`,
`supply_eq_sum_nested`, `solvent_nested` and `price_mono_nested` therefore hold for any
sequence of blocks — no monotonicity of timestamps or numbers is needed, and nothing about
time is enumerated. Their statements are unchanged; the `_multiBlock` corollaries below only
replace the trace hypothesis.
-/

namespace Examples.Time.Solmate
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Solidity QEDefi.ERC4626 QEDefi.Trace
open QEDefi.Trace.Lift QEDefi.Trace.Time Examples.Solmate.ERC4626 Examples.Solmate.ERC4626.Nested
open Examples.Solmate.ERC4626.Invariants Examples.Solmate.ERC20 QEDefi.ERC4626.Solmate
open EvmLogic.Program.Nested (TopOk)

variable {crypto : Crypto} {vault asset : Address} {Act : List Address} {K : VCall → Prop}
  {minGas : Nat}

/-- **One step inside block `b`**: a covered top-level call executed in `b`'s environment
(`ctx.block = b`), or an environment step. -/
inductive BlockTxStep (crypto : Crypto) (vault asset : Address) (minGas : Nat)
    (Act : List Address) (K : VCall → Prop) (b : BlockEnv) : World → World → Prop
  /-- A covered top-level message call in block `b`. -/
  | call {w : World} {ctx : Context} {tr : TransientStorage} {msg : Message} {fuel : Nat}
      {r : MessageResult} : ctx.block = b → ctx.crypto = crypto →
      (ctx.fork < .prague ∨ ctx.tx.authorizations = []) → TopOk (Prot vault asset) w msg →
      msg.gas < 2 ^ 64 → TxOk vault asset minGas Act K ctx w tr msg →
      processMessageCall fuel ctx w tr msg = .ok r →
      BlockTxStep crypto vault asset minGas Act K b w r.world
  /-- Any transition keeping the storage and code of the vault and the asset. -/
  | env {w w' : World} : EnvStep vault asset w w' →
      BlockTxStep crypto vault asset minGas Act K b w w'

theorem BlockTxStep.txStep {b : BlockEnv} {w w' : World}
    (h : BlockTxStep crypto vault asset minGas Act K b w w') :
    TxStep crypto vault asset minGas Act K w w' := by
  cases h with
  | call _ hcr hdeleg hmsg hgas hok hr => exact .call hcr hdeleg hmsg hgas hok hr
  | env he => exact .env he

/-- **A multi-block trace is a transaction trace**, for any block environments. -/
theorem txTrace_of_blockTrace {bs : List BlockEnv} {w₀ w : World}
    (h : BlockTrace (BlockTxStep crypto vault asset minGas Act K) bs w₀ w) :
    TxTrace crypto vault asset minGas Act K w₀ w :=
  BlockTrace.induction_on (R := TxTrace crypto vault asset minGas Act K)
    (fun _ => Relation.ReflTransGen.refl) (fun _ _ _ _ hr hs => hr.tail hs.txStep) h

/-- **The lifting theorem across blocks** (`lift_nested`, for any sequence of blocks). -/
theorem lift_multiBlock (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {bs : List BlockEnv} {w₀ w : World}
    (hdep : Deployed w₀ vault asset) (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : BlockTrace (BlockTxStep crypto vault asset minGas Act K) bs w₀ w) :
    Deployed w vault asset ∧ Solmate.Inv (abs crypto w vault asset) ∧
      ∃ cs : List VCall, (∀ c ∈ cs, Admitted Act K c) ∧
        AgreeOn (ActorPairs Act) (abs crypto w vault asset)
          (Solmate.exec (abs crypto w₀ vault asset) (cs.map VCall.op)) :=
  lift_nested hmin hk hs hdep hinv (txTrace_of_blockTrace htr)

/-- **Invariants transfer across blocks** (`invariant_nested`, for any sequence of blocks). -/
theorem invariant_multiBlock (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {I : State Address → Prop}
    (hI : ∀ s op s', Solmate.Inv s → I s → step s op = some s' → I s')
    (hIa : ∀ s t, AgreeOn (ActorPairs Act) s t → I s → I t) {bs : List BlockEnv}
    {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : BlockTrace (BlockTxStep crypto vault asset minGas Act K) bs w₀ w)
    (hI₀ : I (abs crypto w₀ vault asset)) : I (abs crypto w vault asset) :=
  invariant_nested hmin hk hs hI hIa hdep hinv (txTrace_of_blockTrace htr) hI₀

/-- **`totalSupply` = Σ `balanceOf` across blocks**, for the shares and for the asset. -/
theorem supply_eq_sum_multiBlock (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {bs : List BlockEnv} {w₀ w : World}
    (hdep : Deployed w₀ vault asset) (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : BlockTrace (BlockTxStep crypto vault asset minGas Act K) bs w₀ w) :
    (w.sload vault 2#256).toNat =
        ∑ a : Address, (w.sload vault (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat ∧
      (w.sload asset 2#256).toNat =
        ∑ a : Address, (w.sload asset (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat :=
  supply_eq_sum_nested hmin hk hs hdep hinv (txTrace_of_blockTrace htr)

/-- **Solvency across blocks**: `Σₐ ⌊shares[a]·T/S⌋ ≤ T`, read from storage. -/
theorem solvent_multiBlock (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {bs : List BlockEnv} {w₀ w : World}
    (hdep : Deployed w₀ vault asset) (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : BlockTrace (BlockTxStep crypto vault asset minGas Act K) bs w₀ w) :
    ∑ a : Address, sharesAt crypto w vault a * assetsAt crypto w vault asset / supplyAt w vault ≤
      assetsAt crypto w vault asset :=
  solvent_nested hmin hk hs hdep hinv (txTrace_of_blockTrace htr)

/-- **Price monotonicity across blocks** (`price_mono_nested`, for any sequence of blocks). -/
theorem price_mono_multiBlock (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {bs : List BlockEnv} {w₀ w : World}
    (hdep : Deployed w₀ vault asset) (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : BlockTrace (BlockTxStep crypto vault asset minGas Act (fun c => UserOp vault c.op))
      bs w₀ w) :
    ∃ cs : List VCall, (∀ c ∈ cs, (∀ a ∈ c.actors, a ∈ Act) ∧ UserOp vault c.op) ∧
      ((∀ k ≤ cs.length,
          (Solmate.exec (abs crypto w₀ vault asset) ((cs.take k).map VCall.op)).totalSupply ≠ 0) →
        (assetsAt crypto w₀ vault asset : ℚ) / supplyAt w₀ vault ≤
          (assetsAt crypto w vault asset : ℚ) / supplyAt w vault) :=
  price_mono_nested hmin hk hs hdep hinv (txTrace_of_blockTrace htr)

end Examples.Time.Solmate
