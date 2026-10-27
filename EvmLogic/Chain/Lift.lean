import EvmLogic.Chain.Body

/-!
# Lifting world properties to blocks and chains

A block changes the world only by system calls, transactions and balance credits
(`applyBody_bodyRun`). So a world property kept by each of the three is kept by every valid block
(`stateTransition_preserves`) and by every chain of valid blocks (`Applies.preserves`). The
transaction obligation is taken as a hypothesis on `Tx.process`, to be discharged by the
transaction layer; the credit obligation holds of any property of the storage and code of
accounts holding code (`good_creditBalance`), and the system-call obligation of any `GoodOk`
property of protected contracts other than `SYSTEM_ADDRESS`, given the frame summaries of the
protected frames a system call reaches (`systemCall_good`); `blockPreserves_good` assembles them.

The same holds of any reflexive and transitive relation between worlds (`stateTransition_rel`),
e.g. "the balance of `a` does not decrease" or "the storage of `p` only changes through
transactions".

`Applies crypto chainId head bs head'`: `head'` is reached from `head` by `Block.stateTransition`
on a sequence of blocks, `bs` recording each block's fuel, fork and block environment. The
environments form a `BlockChain` (`Applies.blockChain`), so the time lemmas of
`EvmLogic.Program.Time` apply to them.
-/

namespace EvmLogic.Chain
open EvmLean EvmLean.Interpreter EvmLean.Block EvmLogic.Program EvmLogic.Program.Nested

/-! ## Relations -/

/-- A relation between worlds containing the three kinds of world transitions of a block in
environment `env`: system calls to the system contracts, transactions and balance credits. -/
structure BlockSteps (fuel : Nat) (crypto : Crypto) (fork : Fork) (env : BlockEnv)
    (R : World → World → Prop) : Prop where
  /-- A system call to a system contract, with any calldata. -/
  sys : ∀ w target data w' res, target ∈ systemContracts →
    systemCall fuel crypto fork env w target data = .ok (w', res) → R w w'
  /-- A transaction, with any gas and blob gas available. -/
  tx : ∀ gasAvailable blobGasAvailable w tx hint (r : Tx.TxOutput),
    Tx.process fuel crypto fork env gasAvailable blobGasAvailable w tx hint = .ok r → R w r.world
  /-- A balance credit (a withdrawal). -/
  credit : ∀ w a amount, R w (Tx.creditBalance w a amount)

section Rel
variable {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv} {R : World → World → Prop}

theorem TxRun.rel (S : BlockSteps fuel crypto fork env R) (hrefl : ∀ w, R w w)
    (htrans : ∀ w₁ w₂ w₃, R w₁ w₂ → R w₂ w₃ → R w₁ w₃)
    {g bg : Nat} {txs : List (Transaction × Option Address)} {w w' : World}
    (h : TxRun fuel crypto fork env g bg txs w w') : R w w' := by
  induction h with
  | nil => exact hrefl _
  | cons hp _ ih => exact htrans _ _ _ (S.tx _ _ _ _ _ _ hp) ih

theorem applyWithdrawals_rel (S : BlockSteps fuel crypto fork env R) (hrefl : ∀ w, R w w)
    (htrans : ∀ w₁ w₂ w₃, R w₁ w₂ → R w₂ w₃ → R w₁ w₃) (ws : List Withdrawal) :
    ∀ w, R w (applyWithdrawals w ws) := by
  induction ws with
  | nil => exact hrefl
  | cons wd ws ih =>
    intro w
    rw [applyWithdrawals_cons]
    exact htrans _ _ _ (S.credit _ _ _) (ih _)

theorem mem_systemContracts_beaconRoots : beaconRootsAddress ∈ systemContracts := by
  simp [systemContracts]
theorem mem_systemContracts_historyStorage : historyStorageAddress ∈ systemContracts := by
  simp [systemContracts]
theorem mem_systemContracts_withdrawalRequest : withdrawalRequestAddress ∈ systemContracts := by
  simp [systemContracts]
theorem mem_systemContracts_consolidationRequest :
    consolidationRequestAddress ∈ systemContracts := by
  simp [systemContracts]

theorem BodyRun.rel (S : BlockSteps fuel crypto fork env R) (hrefl : ∀ w, R w w)
    (htrans : ∀ w₁ w₂ w₃, R w₁ w₂ → R w₂ w₃ → R w₁ w₃)
    {txs : List (Transaction × Option Address)} {ws : List Withdrawal}
    {world w₁ w₂ w₃ w₄ : World} (h : BodyRun fuel crypto fork env txs ws world w₁ w₂ w₃ w₄) :
    R world w₄ := by
  obtain ⟨⟨r₁, h₁⟩, hh, ht, hp⟩ := h
  have e₁ : R world w₁ := S.sys _ _ _ _ _ mem_systemContracts_beaconRoots h₁
  have e₂ : R w₁ w₂ := by
    split at hh
    · obtain ⟨r, hr⟩ := hh; exact S.sys _ _ _ _ _ mem_systemContracts_historyStorage hr
    · rw [hh]; exact hrefl _
  have e₃ : R w₂ w₃ := ht.rel S hrefl htrans
  have e₄ : R w₃ w₄ := by
    have ew := applyWithdrawals_rel S hrefl htrans ws w₃
    split at hp
    · obtain ⟨w, ⟨-, r, hr, -⟩, ⟨-, r', hr', -⟩⟩ := hp
      exact htrans _ _ _ ew (htrans _ _ _
        (S.sys _ _ _ _ _ mem_systemContracts_withdrawalRequest hr)
        (S.sys _ _ _ _ _ mem_systemContracts_consolidationRequest hr'))
    · rw [hp]; exact ew
  exact htrans _ _ _ e₁ (htrans _ _ _ e₂ (htrans _ _ _ e₃ e₄))

/-- **A relation containing the block's world transitions relates the worlds before and after
a block body.** -/
theorem applyBody_rel (S : BlockSteps fuel crypto fork env R) (hrefl : ∀ w, R w w)
    (htrans : ∀ w₁ w₂ w₃, R w₁ w₂ → R w₂ w₃ → R w₁ w₃) {world : World}
    {txs : List (Transaction × Option Address)} {ws : List Withdrawal} {out : BodyOutput}
    (h : applyBody fuel crypto fork env world txs ws = .ok out) : R world out.world := by
  obtain ⟨_, _, _, hr⟩ := applyBody_bodyRun h
  exact hr.rel S hrefl htrans

end Rel

/-- **A relation containing the world transitions of a valid block relates the worlds of the
old and the new head.** -/
theorem stateTransition_rel {fuel : Nat} {crypto : Crypto} {fork : Fork} {chainId : Nat}
    {R : World → World → Prop} {head head' : ChainHead} {block : Block}
    {hints : List (Option Address)} {rs : Array Receipt}
    (S : BlockSteps fuel crypto fork (envOf chainId head block) R) (hrefl : ∀ w, R w w)
    (htrans : ∀ w₁ w₂ w₃, R w₁ w₂ → R w₂ w₃ → R w₁ w₃)
    (h : stateTransition fuel crypto fork chainId head block hints = .ok (head', rs)) :
    R head.world head'.world := by
  obtain ⟨out, hb, hw⟩ := stateTransition_applyBody h
  rw [hw]; exact applyBody_rel S hrefl htrans hb

/-! ## Invariants -/

/-- A world property kept by the three kinds of world transitions of a block in environment
`env` (`BlockSteps` of `I w → I w'`). -/
structure BlockPreserves (fuel : Nat) (crypto : Crypto) (fork : Fork) (env : BlockEnv)
    (I : World → Prop) : Prop where
  /-- System calls to the system contracts keep `I`. -/
  sys : ∀ w target data w' res, target ∈ systemContracts → I w →
    systemCall fuel crypto fork env w target data = .ok (w', res) → I w'
  /-- Successful transactions keep `I` (the transaction layer's obligation). -/
  tx : ∀ gasAvailable blobGasAvailable w tx hint (r : Tx.TxOutput), I w →
    Tx.process fuel crypto fork env gasAvailable blobGasAvailable w tx hint = .ok r → I r.world
  /-- Balance credits keep `I`. -/
  credit : ∀ w a amount, I w → I (Tx.creditBalance w a amount)

theorem BlockPreserves.steps {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {I : World → Prop} (h : BlockPreserves fuel crypto fork env I) :
    BlockSteps fuel crypto fork env (fun w w' => I w → I w') :=
  ⟨fun _ _ _ _ _ ht hs hw => h.sys _ _ _ _ _ ht hw hs,
   fun _ _ _ _ _ _ hp hw => h.tx _ _ _ _ _ _ hw hp,
   fun _ _ _ hw => h.credit _ _ _ hw⟩

/-- **Invariants of block bodies.** -/
theorem applyBody_preserves {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {I : World → Prop} (hI : BlockPreserves fuel crypto fork env I) {world : World}
    {txs : List (Transaction × Option Address)} {ws : List Withdrawal} {out : BodyOutput}
    (hw : I world) (h : applyBody fuel crypto fork env world txs ws = .ok out) : I out.world :=
  applyBody_rel hI.steps (fun _ => id) (fun _ _ _ h₁ h₂ hw => h₂ (h₁ hw)) h hw

/-- **Invariants of valid blocks**: a world property kept by system calls, transactions and
balance credits in the block's environment holds after the block if it held before. -/
theorem stateTransition_preserves {fuel : Nat} {crypto : Crypto} {fork : Fork} {chainId : Nat}
    {I : World → Prop} {head head' : ChainHead} {block : Block}
    {hints : List (Option Address)} {rs : Array Receipt}
    (hI : BlockPreserves fuel crypto fork (envOf chainId head block) I) (hw : I head.world)
    (h : stateTransition fuel crypto fork chainId head block hints = .ok (head', rs)) :
    I head'.world :=
  stateTransition_rel hI.steps (fun _ => id) (fun _ _ _ h₁ h₂ hw => h₂ (h₁ hw)) h hw

/-! ## Chains of valid blocks -/

/-- **A chain of valid blocks.** `Applies crypto chainId head bs head'`: `head'` is reached from
`head` by `Block.stateTransition` on a sequence of blocks; `bs` records, block by block, the
fuel, the fork and the block environment (`envOf`) the block was executed in. -/
inductive Applies (crypto : Crypto) (chainId : Nat) :
    ChainHead → List (Nat × Fork × BlockEnv) → ChainHead → Prop
  /-- No block. -/
  | nil (head : ChainHead) : Applies crypto chainId head [] head
  /-- A valid block, then the rest of the chain from its head. -/
  | cons {fuel : Nat} {fork : Fork} {head head₁ head₂ : ChainHead} {block : Block}
      {hints : List (Option Address)} {rs : Array Receipt} {bs : List (Nat × Fork × BlockEnv)} :
      stateTransition fuel crypto fork chainId head block hints = .ok (head₁, rs) →
      Applies crypto chainId head₁ bs head₂ →
      Applies crypto chainId head ((fuel, fork, envOf chainId head block) :: bs) head₂

namespace Applies

variable {crypto : Crypto} {chainId : Nat}

/-- **A relation containing every block's world transitions relates the first and last
worlds of a chain.** -/
theorem rel {R : World → World → Prop} (hrefl : ∀ w, R w w)
    (htrans : ∀ w₁ w₂ w₃, R w₁ w₂ → R w₂ w₃ → R w₁ w₃) {head head' : ChainHead}
    {bs : List (Nat × Fork × BlockEnv)} (h : Applies crypto chainId head bs head')
    (hR : ∀ b ∈ bs, BlockSteps b.1 crypto b.2.1 b.2.2 R) : R head.world head'.world := by
  induction h with
  | nil => exact hrefl _
  | cons hst _ ih =>
    exact htrans _ _ _
      (stateTransition_rel (hR _ (List.mem_cons_self ..)) hrefl htrans hst)
      (ih fun b hb => hR b (List.mem_cons_of_mem _ hb))

/-- **Invariants of chains**: a world property kept by system calls, transactions and balance
credits in every block's environment and fork holds at the end of a chain of valid blocks if
it held at its start. -/
theorem preserves {I : World → Prop} {head head' : ChainHead}
    {bs : List (Nat × Fork × BlockEnv)} (h : Applies crypto chainId head bs head')
    (hI : ∀ b ∈ bs, BlockPreserves b.1 crypto b.2.1 b.2.2 I) (hw : I head.world) :
    I head'.world :=
  h.rel (R := fun w w' => I w → I w') (fun _ => id) (fun _ _ _ h₁ h₂ hw => h₂ (h₁ hw))
    (fun b hb => (hI b hb).steps) hw

/-- **The block environments of a chain of valid blocks form a `BlockChain`**: same chain id,
numbers counting up, strictly increasing timestamps, ancestor hashes shifted by each parent's
hash. -/
theorem blockChain {head head' : ChainHead} {bs : List (Nat × Fork × BlockEnv)}
    (h : Applies crypto chainId head bs head') : BlockChain (bs.map fun b => b.2.2) := by
  induction h with
  | nil => trivial
  | cons h₁ htl ih =>
    cases htl with
    | nil => trivial
    | cons h₂ _ => exact ⟨nextBlock_stateTransition h₁ h₂, ih⟩

/-- Chains compose. -/
theorem append {head₁ head₂ head₃ : ChainHead} {bs bs' : List (Nat × Fork × BlockEnv)}
    (h₁ : Applies crypto chainId head₁ bs head₂) (h₂ : Applies crypto chainId head₂ bs' head₃) :
    Applies crypto chainId head₁ (bs ++ bs') head₃ := by
  induction h₁ with
  | nil => exact h₂
  | cons hst _ ih => exact .cons hst (ih h₂)

end Applies

/-! ## Protected contracts -/

/-- **The block obligations of a `GoodOk` property** (storage and code of protected accounts
holding code, the nested-call simulation's predicates): credits keep it with no hypothesis;
system calls keep it when `SYSTEM_ADDRESS` is not protected and the dangerous frames a system
call reaches end `Good` (`hsum`, as in `processMessageCall_good`; vacuous when no protected
frame is reached, e.g. when the system contracts call no protected account); transactions are
the transaction layer's obligation (`htx`). -/
theorem blockPreserves_good {P : Address → Prop} {Good : World → Prop} (S : GoodOk P Good)
    (hsys : ¬ P systemAddress) {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    (hsum : ∀ world target data, target ∈ systemContracts → Good world →
      ∀ m, Reaches (systemContext crypto fork env) world ∅ (systemMessage world target data) m →
        DangerStart P Good systemTransactionGas m → (∀ f ∈ m.parents, ¬ Danger P f) →
        Halts m (fun mf o => Good (frameResult mf o).2.1))
    (htx : ∀ gasAvailable blobGasAvailable w tx hint (r : Tx.TxOutput), Good w →
      Tx.process fuel crypto fork env gasAvailable blobGasAvailable w tx hint = .ok r →
      Good r.world) :
    BlockPreserves fuel crypto fork env Good :=
  ⟨fun w _ _ _ _ ht hw hs => systemCall_good S hsys hw (hsum w _ _ ht hw) hs, htx,
   fun _ _ _ hw => good_creditBalance S hw _ _⟩

end EvmLogic.Chain
