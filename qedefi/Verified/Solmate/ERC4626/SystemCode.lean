import Verified.Solmate.ERC4626.Blocks
import EvmLogic.Chain.SystemSafe

/-!
# The vault's system calls are covered by the canonical system code

`Verified.Solmate.ERC4626.Blocks` asks, for each system call a chain runs, that the vault and
asset frames it reaches be covered (`SysCovered`), at the world the call runs in. A system
contract holding its canonical code, or no code, reaches no frame but its own
(`EvmLogic.Chain.reaches_systemMessage`: the canonical codes contain no call or creation), so
`SysCovered` holds as soon as the system contract is neither the vault nor the asset
(`sysCovered_of_code`). The canonical code is a block invariant
(`EvmLogic.Chain.SystemCodeIn`, `blockPreserves_systemCodeIn`), so along a chain starting where
the system contracts hold it, only the transactions need coverage: `TxCoveredChain` (a chain of
valid blocks whose transactions are covered) is a `CoveredChain` (`TxCoveredChain.coveredChain`),
and the headline theorems of `Blocks` hold of it (`lift_txCoveredChain`,
`solvent_txCoveredChain`).
-/

namespace Verified.Solmate.ERC4626.Nested
open Verified.Solmate.ERC20 QEDefi.ERC4626 QEDefi.Trace
open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open Verified.Solmate.Contracts
open QEDefi.Math QEDefi.ERC20 QEDefi.ERC4626.Solmate QEDefi.Trace.Lift
open Verified.Solmate.ERC4626.Invariants
open EvmLean.Block (ChainHead stateTransition systemAddress)
open EvmLogic.Chain (systemContracts systemCode SystemCodeIn TxRun BodyRun CheckedCall txsOf
  Applies blockPreserves_systemCodeIn systemCodeIn_systemCall reaches_systemMessage)

variable {crypto : Crypto} {vault asset : Address} {Act : List Address} {K : VCall → Prop}

/-! ## System calls -/

/-- **A system call to a system contract holding its canonical code, or no code, is covered**
when the system contract is neither the vault nor the asset: it starts no frame at any other
account (`reaches_systemMessage`), so no vault or asset frame (`VaultStart`). -/
theorem sysCovered_of_code {fork : Fork} {env : BlockEnv} {world : World} {target : Address}
    {data : ByteArray} (ht : target ∈ systemContracts) (hv : ¬ Prot vault asset target)
    (hcode : world.code target = systemCode target ∨ (world.code target).size = 0) :
    SysCovered vault asset Act K crypto fork env world target data :=
  fun _ hm hs _ => absurd ((reaches_systemMessage ht hcode hm).2 ▸ hs.prot) hv

theorem sysCovered_of_systemCodeIn {fork : Fork} {env : BlockEnv} {world : World}
    {target : Address} {data : ByteArray} (ht : target ∈ systemContracts)
    (hv : ¬ Prot vault asset target) (hw : SystemCodeIn world) :
    SysCovered vault asset Act K crypto fork env world target data :=
  sysCovered_of_code ht hv (.inl (hw target ht))

/-- No system contract is the canonical vault or its asset. -/
theorem not_prot_systemContracts :
    ∀ a ∈ systemContracts, ¬ Prot SolmateVault.address SolmateVault.deployment.asset a := by
  intro a ha
  simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> (unfold Prot; decide)

/-! ## Blocks -/

/-- **The system calls of a block body are covered** when the system contracts hold their
canonical code at its start and none is the vault or the asset: only the transactions need
coverage (`htx`). The code is kept by every step of the body (`blockPreserves_systemCodeIn`),
so it holds at the world of each system call. -/
theorem bodyCovered_of_systemCodeIn (hP : ∀ a ∈ systemContracts, ¬ Prot vault asset a)
    {fuel : Nat} {fork : Fork} {env : BlockEnv} {txs : List (Transaction × Option Address)}
    {ws : List Withdrawal} {world w₁ w₂ w₃ w₄ : World}
    (hrun : BodyRun fuel crypto fork env txs ws world w₁ w₂ w₃ w₄) (hc : SystemCodeIn world)
    (htx : TxsCovered vault asset Act K fuel crypto fork env 0 0 txs w₂) :
    BodyCovered vault asset Act K fuel crypto fork env txs ws world w₁ w₂ w₃ := by
  obtain ⟨⟨r₁, h₁⟩, hh, ht, -⟩ := hrun
  have S := (blockPreserves_systemCodeIn fuel crypto fork env).steps
  have c₁ : SystemCodeIn w₁ := systemCodeIn_systemCall hc h₁
  have c₂ : SystemCodeIn w₂ := by
    split at hh
    · obtain ⟨r, hr⟩ := hh; exact systemCodeIn_systemCall c₁ hr
    · rw [hh]; exact c₁
  have tr : ∀ w₁ w₂ w₃ : World, (SystemCodeIn w₁ → SystemCodeIn w₂) →
      (SystemCodeIn w₂ → SystemCodeIn w₃) → SystemCodeIn w₁ → SystemCodeIn w₃ :=
    fun _ _ _ e₁ e₂ hw => e₂ (e₁ hw)
  have c₃ : SystemCodeIn w₃ := ht.rel S (fun _ => id) tr c₂
  have cw : SystemCodeIn (EvmLean.Block.applyWithdrawals w₃ ws) :=
    EvmLogic.Chain.applyWithdrawals_rel S (fun _ => id) tr ws w₃ c₃
  refine ⟨sysCovered_of_systemCodeIn EvmLogic.Chain.mem_systemContracts_beaconRoots
      (hP _ EvmLogic.Chain.mem_systemContracts_beaconRoots) hc,
    fun _ => sysCovered_of_systemCodeIn EvmLogic.Chain.mem_systemContracts_historyStorage
      (hP _ EvmLogic.Chain.mem_systemContracts_historyStorage) c₁, htx,
    fun _ => ⟨sysCovered_of_systemCodeIn EvmLogic.Chain.mem_systemContracts_withdrawalRequest
      (hP _ EvmLogic.Chain.mem_systemContracts_withdrawalRequest) cw, fun w hw => ?_⟩⟩
  obtain ⟨-, r, hr, -⟩ := hw
  exact sysCovered_of_systemCodeIn EvmLogic.Chain.mem_systemContracts_consolidationRequest
    (hP _ EvmLogic.Chain.mem_systemContracts_consolidationRequest)
    (systemCodeIn_systemCall cw hr)

/-- **The transactions of a block are covered**: `TxsCovered` for the body run of `block` on top
of `head`. -/
def BlockTxsCovered (vault asset : Address) (Act : List Address) (K : VCall → Prop)
    (fuel : Nat) (crypto : Crypto) (fork : Fork) (chainId : Nat) (head : ChainHead)
    (block : Block) (hints : List (Option Address)) : Prop :=
  ∀ w₁ w₂ w₃ w₄, BodyRun fuel crypto fork (envOf chainId head block) (txsOf block hints)
      block.withdrawals head.world w₁ w₂ w₃ w₄ →
    TxsCovered vault asset Act K fuel crypto fork (envOf chainId head block) 0 0
      (txsOf block hints) w₂

/-- **A block whose transactions are covered is covered**, when the system contracts hold their
canonical code at its start and none is the vault or the asset. -/
theorem blockCovered_of_systemCodeIn (hP : ∀ a ∈ systemContracts, ¬ Prot vault asset a)
    {fuel : Nat} {fork : Fork} {chainId : Nat} {head : ChainHead} {block : Block}
    {hints : List (Option Address)} (hc : SystemCodeIn head.world)
    (htx : BlockTxsCovered vault asset Act K fuel crypto fork chainId head block hints) :
    BlockCovered vault asset Act K fuel crypto fork chainId head block hints :=
  fun _ _ _ _ hrun => bodyCovered_of_systemCodeIn hP hrun hc (htx _ _ _ _ hrun)

/-! ## Chains -/

/-- **A chain of valid blocks whose transactions are covered** (`CoveredChain` without the
system-call coverage). -/
inductive TxCoveredChain (crypto : Crypto) (vault asset : Address) (Act : List Address)
    (K : VCall → Prop) (chainId : Nat) :
    ChainHead → List (Nat × Fork × BlockEnv) → ChainHead → Prop
  /-- No block. -/
  | nil (head : ChainHead) : TxCoveredChain crypto vault asset Act K chainId head [] head
  /-- A valid block whose transactions are covered, then the rest of the chain. -/
  | cons {fuel : Nat} {fork : Fork} {head head₁ head₂ : ChainHead} {block : Block}
      {hints : List (Option Address)} {rs : Array Receipt}
      {bs : List (Nat × Fork × BlockEnv)} :
      stateTransition fuel crypto fork chainId head block hints = .ok (head₁, rs) →
      BlockTxsCovered vault asset Act K fuel crypto fork chainId head block hints →
      TxCoveredChain crypto vault asset Act K chainId head₁ bs head₂ →
      TxCoveredChain crypto vault asset Act K chainId head
        ((fuel, fork, envOf chainId head block) :: bs) head₂

/-- **A chain whose transactions are covered is a covered chain**, when it starts in a world
where the system contracts hold their canonical code and none is the vault or the asset. -/
theorem TxCoveredChain.coveredChain (hP : ∀ a ∈ systemContracts, ¬ Prot vault asset a)
    {chainId : Nat} {head head' : ChainHead} {bs : List (Nat × Fork × BlockEnv)}
    (h : TxCoveredChain crypto vault asset Act K chainId head bs head')
    (hc : SystemCodeIn head.world) :
    CoveredChain crypto vault asset Act K chainId head bs head' := by
  induction h with
  | nil => exact .nil _
  | cons hst hcov _ ih =>
    exact .cons hst (blockCovered_of_systemCodeIn hP hc hcov)
      (ih (EvmLogic.Chain.stateTransition_preserves (blockPreserves_systemCodeIn _ _ _ _) hc hst))

/-- **The lifting theorem along a chain of valid blocks whose transactions are covered**
(`lift_coveredChain`), from a head where the system contracts hold their canonical code (as on
mainnet from Prague on), when neither `SYSTEM_ADDRESS` nor any system contract is the vault or
the asset (`not_prot_systemAddress`, `not_prot_systemContracts` for the canonical
deployment). -/
theorem lift_txCoveredChain
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) (hP : ¬ Prot vault asset systemAddress)
    (hPs : ∀ a ∈ systemContracts, ¬ Prot vault asset a) {chainId : Nat}
    {head head' : ChainHead} {bs : List (Nat × Fork × BlockEnv)}
    (hdep : Deployed head.world vault asset)
    (hinv : Solmate.Inv (abs crypto head.world vault asset)) (hc : SystemCodeIn head.world)
    (h : TxCoveredChain crypto vault asset Act K chainId head bs head') :
    Deployed head'.world vault asset ∧ Solmate.Inv (abs crypto head'.world vault asset) ∧
      ∃ cs : List VCall, (∀ c ∈ cs, Admitted Act K c) ∧
        AgreeOn (ActorPairs Act) (abs crypto head'.world vault asset)
          (Solmate.exec (abs crypto head.world vault asset) (cs.map VCall.op)) :=
  lift_coveredChain hk hs hP hdep hinv (h.coveredChain hPs hc)

/-- **Solvency along a chain of valid blocks whose transactions are covered**, from a head where
the system contracts hold their canonical code. -/
theorem solvent_txCoveredChain
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) (hP : ¬ Prot vault asset systemAddress)
    (hPs : ∀ a ∈ systemContracts, ¬ Prot vault asset a) {chainId : Nat}
    {head head' : ChainHead} {bs : List (Nat × Fork × BlockEnv)}
    (hdep : Deployed head.world vault asset)
    (hinv : Solmate.Inv (abs crypto head.world vault asset)) (hc : SystemCodeIn head.world)
    (h : TxCoveredChain crypto vault asset Act K chainId head bs head') :
    ∑ a : Address, sharesAt crypto head'.world vault a * assetsAt crypto head'.world vault asset /
        supplyAt head'.world vault ≤ assetsAt crypto head'.world vault asset :=
  solvent_coveredChain hk hs hP hdep hinv (h.coveredChain hPs hc)

end Verified.Solmate.ERC4626.Nested
