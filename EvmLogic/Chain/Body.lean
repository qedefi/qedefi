import EvmLogic.Chain.SystemCall
import EvmLogic.Program.Time

/-!
# Decomposing a block

A successful block body (`Block.applyBody`) is, world by world (`BodyRun`):

1. the EIP-4788 beacon-roots system call (every fork);
2. from Prague, the EIP-2935 history-storage system call with the parent hash;
3. the transactions, in order, each through `Tx.process` with the block gas and blob gas still
   available (`TxRun`, which exposes every intermediate world and the gas used so far);
4. the withdrawals (`applyWithdrawals`, balance credits);
5. from Prague, the EIP-7002 and EIP-7251 request dequeues, as checked system calls (the target
   holds code and the call succeeds); the EIP-6110 deposit requests are parsed from the logs and
   do not change the world.

`applyBody_bodyRun` proves the decomposition; `stateTransition_applyBody` says that a valid block
(`Block.stateTransition`) runs its body in `envOf chainId head block` from the head's world, and
its new head's world is the body's.
-/

namespace EvmLogic.Chain
open EvmLean EvmLean.Interpreter EvmLean.Block EvmLogic.Program

/-! ## `Except` plumbing -/

private theorem ok_of_bind {ε α β : Type} {e : Except ε β} {k : β → Except ε α} {x : α}
    (h : (e >>= k) = .ok x) : ∃ a, e = .ok a ∧ k a = .ok x := by
  cases e with
  | error => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem ok_of_mapError {ε ε' β : Type} {f : ε → ε'} {e : Except ε β} {a : β}
    (h : e.mapError f = .ok a) : e = .ok a := by
  cases e with
  | error => cases h
  | ok a => cases h; rfl

private theorem ok_of_ite_throw {ε α β : Type} {c : Prop} [Decidable c] {e : ε}
    {jp : β → Except ε α} {B : Except ε α} {x : α}
    (h : (if c then (throw e >>= jp) else B : Except ε α) = .ok x) : ¬c ∧ B = .ok x := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte] at h; cases h
  · simp only [hc, ↓reduceIte] at h; exact ⟨hc, h⟩

private theorem ok_of_ite_ite_throw {ε α β : Type} {c d : Prop} [Decidable c] [Decidable d]
    {e : ε} {jp : β → Except ε α} {B : Except ε α} {x : α}
    (h : (if c then (if d then (throw e >>= jp) else B) else B : Except ε α) = .ok x) :
    B = .ok x := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte] at h; exact (ok_of_ite_throw h).2
  · simp only [hc, ↓reduceIte] at h; exact h

/-! ## The transaction loop -/

/-- **The transaction loop, transaction by transaction.** `TxRun … g bg txs w w'`: from world
`w`, with block gas `g` and blob gas `bg` already used, the transactions `txs` (with their
sender hints) are processed in order by `Tx.process`, each with the block gas and blob gas
still available, ending in world `w'`. -/
inductive TxRun (fuel : Nat) (crypto : Crypto) (fork : Fork) (env : BlockEnv) :
    Nat → Nat → List (Transaction × Option Address) → World → World → Prop
  /-- No transaction left. -/
  | nil {g bg : Nat} {w : World} : TxRun fuel crypto fork env g bg [] w w
  /-- Process `tx`, then the rest from its world, with its gas and blob gas counted. -/
  | cons {g bg : Nat} {tx : Transaction} {hint : Option Address}
      {rest : List (Transaction × Option Address)} {w w' : World} {r : Tx.TxOutput} :
      Tx.process fuel crypto fork env (env.gasLimit - g) ((Tx.blobParams fork).maxGasPerBlock - bg)
        w tx hint = .ok r →
      TxRun fuel crypto fork env (g + r.gasUsed) (bg + r.blobGasUsed) rest r.world w' →
      TxRun fuel crypto fork env g bg ((tx, hint) :: rest) w w'

/-- `applyTxs` runs its transactions as `TxRun` describes. -/
theorem applyTxs_txRun {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv} :
    ∀ (txs : List (Transaction × Option Address)) (i : Nat) (out out' : BodyOutput),
      applyTxs fuel crypto fork env i txs out = .ok out' →
      TxRun fuel crypto fork env out.gasUsed out.blobGasUsed txs out.world out'.world
  | [], i, out, out', h => by
    simp only [applyTxs, Except.ok.injEq] at h
    subst h; exact .nil
  | (tx, hint) :: rest, i, out, out', h => by
    simp only [applyTxs] at h
    cases hp : Tx.process fuel crypto fork env (env.gasLimit - out.gasUsed)
        ((Tx.blobParams fork).maxGasPerBlock - out.blobGasUsed) out.world tx hint with
    | error e =>
      rw [hp] at h
      cases e <;> cases h
    | ok r =>
      rw [hp] at h
      exact .cons hp (applyTxs_txRun rest _ _ _ h)

/-! ## The body -/

/-- A checked system call (`checkedSystemCall`): the target holds code and the system call
succeeds. -/
def CheckedCall (fuel : Nat) (crypto : Crypto) (fork : Fork) (env : BlockEnv) (w : World)
    (target : Address) (data : ByteArray) (w' : World) : Prop :=
  (w.code target).size ≠ 0 ∧
    ∃ res, systemCall fuel crypto fork env w target data = .ok (w', res) ∧ res.success = true

/-- **The worlds of a block body.** From `world`: the beacon-roots call gives `w₁`; from Prague
the history-storage call gives `w₂` (before Prague `w₂ = w₁`); the transactions give `w₃`;
the withdrawals, then from Prague the two request dequeues, give `w₄`. -/
structure BodyRun (fuel : Nat) (crypto : Crypto) (fork : Fork) (env : BlockEnv)
    (txs : List (Transaction × Option Address)) (ws : List Withdrawal)
    (world w₁ w₂ w₃ w₄ : World) : Prop where
  /-- EIP-4788: the beacon-roots system call with the parent beacon block root. -/
  beacon : ∃ res, systemCall fuel crypto fork env world beaconRootsAddress
    (Bytes.ofWord env.parentBeaconBlockRoot) = .ok (w₁, res)
  /-- EIP-2935 (Prague): the history-storage system call with the parent hash. -/
  history : if fork ≥ .prague then
      ∃ res, systemCall fuel crypto fork env w₁ historyStorageAddress
        (Bytes.ofWord (env.blockHashes[0]?.getD 0)) = .ok (w₂, res)
    else w₂ = w₁
  /-- The transactions, in order. -/
  txs : TxRun fuel crypto fork env 0 0 txs w₂ w₃
  /-- Withdrawals, then (Prague) the EIP-7002 and EIP-7251 dequeues. -/
  post : if fork ≥ .prague then
      ∃ w, CheckedCall fuel crypto fork env (applyWithdrawals w₃ ws) withdrawalRequestAddress
          .empty w ∧
        CheckedCall fuel crypto fork env w consolidationRequestAddress .empty w₄
    else w₄ = applyWithdrawals w₃ ws

theorem checkedCall_of_ok {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {w : World} {target : Address} {data : ByteArray} {p : World × ByteArray}
    (h : checkedSystemCall fuel crypto fork env w target data = .ok p) :
    CheckedCall fuel crypto fork env w target data p.1 := by
  obtain ⟨hc, res, hs, hr, -⟩ := checkedSystemCall_ok (w' := p.1) (out := p.2) h
  exact ⟨hc, res, hs, hr⟩

/-- **Decomposition of a block body**: a successful `applyBody` is a `BodyRun` ending in its
output world. -/
theorem applyBody_bodyRun {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {world : World} {txs : List (Transaction × Option Address)} {ws : List Withdrawal}
    {out : BodyOutput} (h : applyBody fuel crypto fork env world txs ws = .ok out) :
    ∃ w₁ w₂ w₃, BodyRun fuel crypto fork env txs ws world w₁ w₂ w₃ out.world := by
  unfold applyBody at h
  obtain ⟨w₁, hb, h⟩ := ok_of_bind h
  have hb' := beaconRootsCall_ok (ok_of_mapError hb)
  dsimp only at h
  by_cases hf : fork ≥ .prague
  · simp only [hf, ↓reduceIte] at h
    obtain ⟨p, hp, h⟩ := ok_of_bind h
    obtain ⟨w₂, hw₂, h⟩ := ok_of_bind h
    cases hw₂
    obtain ⟨o, ht, h⟩ := ok_of_bind h
    have hrun := applyTxs_txRun txs 0 { world := p.1 } o ht
    obtain ⟨q, hq, h⟩ := ok_of_bind h
    unfold generalPurposeRequests at hq
    obtain ⟨d, -, hq⟩ := ok_of_bind hq
    obtain ⟨p₁, h₁, hq⟩ := ok_of_bind hq
    obtain ⟨p₂, h₂, hq⟩ := ok_of_bind hq
    cases hq
    cases h
    refine ⟨w₁, p.1, o.world, hb', ?_, hrun, ?_⟩
    · simp only [hf, ↓reduceIte]
      exact ⟨p.2, ok_of_mapError hp⟩
    · simp only [hf, ↓reduceIte]
      exact ⟨p₁.1, checkedCall_of_ok h₁, checkedCall_of_ok h₂⟩
  · simp only [hf, ↓reduceIte] at h
    obtain ⟨w₂, hw₂, h⟩ := ok_of_bind h
    cases hw₂
    obtain ⟨o, ht, h⟩ := ok_of_bind h
    have hrun := applyTxs_txRun txs 0 { world := w₁ } o ht
    cases h
    refine ⟨w₁, w₁, o.world, hb', ?_, hrun, ?_⟩ <;> simp only [hf, ↓reduceIte]

/-! ## Valid blocks -/

/-- The transactions of `block` with their sender hints, as `stateTransition` passes them. -/
def txsOf (block : Block) (hints : List (Option Address)) :
    List (Transaction × Option Address) :=
  block.transactions.zipIdx.map fun (tx, i) => (tx, (hints[i]?).join)

/-- **A valid block runs its body** in `envOf chainId head block`, from the head's world, and
the new head's world is the body's output world. -/
theorem stateTransition_applyBody {fuel : Nat} {crypto : Crypto} {fork : Fork} {chainId : Nat}
    {head head' : ChainHead} {block : Block} {hints : List (Option Address)}
    {rs : Array Receipt}
    (h : stateTransition fuel crypto fork chainId head block hints = .ok (head', rs)) :
    ∃ out, applyBody fuel crypto fork (envOf chainId head block) head.world (txsOf block hints)
      block.withdrawals = .ok out ∧ head'.world = out.world := by
  unfold stateTransition at h
  dsimp only at h
  replace h := ok_of_ite_ite_throw h
  obtain ⟨-, h⟩ := ok_of_ite_throw h
  obtain ⟨u, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_ite_throw h
  obtain ⟨out, hb, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_ite_throw h
  obtain ⟨-, h⟩ := ok_of_ite_throw h
  obtain ⟨-, h⟩ := ok_of_ite_throw h
  obtain ⟨-, h⟩ := ok_of_ite_throw h
  obtain ⟨-, h⟩ := ok_of_ite_throw h
  obtain ⟨-, h⟩ := ok_of_ite_throw h
  obtain ⟨-, h⟩ := ok_of_ite_throw h
  obtain ⟨-, h⟩ := ok_of_ite_throw h
  cases h
  exact ⟨out, hb, rfl⟩

/-- **Decomposition of a valid block**: system calls, transactions, withdrawals and requests
from the head's world to the new head's world. -/
theorem stateTransition_bodyRun {fuel : Nat} {crypto : Crypto} {fork : Fork} {chainId : Nat}
    {head head' : ChainHead} {block : Block} {hints : List (Option Address)}
    {rs : Array Receipt}
    (h : stateTransition fuel crypto fork chainId head block hints = .ok (head', rs)) :
    ∃ w₁ w₂ w₃, BodyRun fuel crypto fork (envOf chainId head block) (txsOf block hints)
      block.withdrawals head.world w₁ w₂ w₃ head'.world := by
  obtain ⟨out, hb, hw⟩ := stateTransition_applyBody h
  rw [hw]; exact applyBody_bodyRun hb

end EvmLogic.Chain
