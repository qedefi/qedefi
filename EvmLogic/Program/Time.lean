import EvmLean.Block

/-!
# Block environments across blocks

What consensus guarantees between the block environments (`BlockEnv`) of consecutive blocks,
as the hypotheses of multi-block theorems (`QEDefi.Trace.Time`): timestamps strictly
increase, numbers increase by one, the chain id is fixed and the ancestor hashes shift by the
parent's hash (`NextBlock`). Everything else (coinbase, gas limit, base fee, `PREVRANDAO`,
blob gas, the beacon root) is unconstrained, so theorems hold for arbitrary values of them.

`nextBlock_stateTransition` checks these hypotheses against the semantics: the environments
in which `Block.stateTransition` executes two consecutive valid blocks are `NextBlock`
(`validate_header` in `cancun/fork.py` enforces the timestamp and number). `BlockChain`
extends `NextBlock` to lists; its consequences (`BlockChain.timestamp_lt`,
`BlockChain.number_eq`) are all multi-block proofs need about time.
-/

namespace EvmLogic.Program
open EvmLean EvmLean.Block

/-- **Consecutive block environments** `b` (parent) and `b'` (child), as consensus guarantees
them: same chain id, number `+1`, strictly larger timestamp, ancestor hashes shifted by the
parent's hash. -/
structure NextBlock (b b' : BlockEnv) : Prop where
  /-- The chain id does not change. -/
  chainId : b'.chainId = b.chainId
  /-- Block numbers increase by one. -/
  number : b'.number = b.number + 1
  /-- Timestamps strictly increase. -/
  timestamp : b.timestamp < b'.timestamp
  /-- `BLOCKHASH` of the child sees the parent's hash, then the parent's ancestors. -/
  hashes : ∃ h, b'.blockHashes = (h :: b.blockHashes).take 256

/-- A chain of block environments, each the child of the previous one. -/
def BlockChain : List BlockEnv → Prop
  | b :: b' :: bs => NextBlock b b' ∧ BlockChain (b' :: bs)
  | _ => True

namespace BlockChain

theorem tail {b : BlockEnv} {bs : List BlockEnv} (h : BlockChain (b :: bs)) : BlockChain bs := by
  cases bs with
  | nil => trivial
  | cons b' bs => exact h.2

/-- Timestamps strictly increase along a chain. -/
theorem timestamp_lt : ∀ {bs : List BlockEnv}, BlockChain bs →
    bs.Pairwise fun b b' => b.timestamp < b'.timestamp
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | b :: b' :: bs, h => by
    have ih := timestamp_lt h.2
    refine List.Pairwise.cons ?_ ih
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact h.1.timestamp
    · exact Nat.lt_trans h.1.timestamp ((List.pairwise_cons.1 ih).1 c hc)

/-- Timestamps do not decrease along a chain. -/
theorem timestamp_le {bs : List BlockEnv} (h : BlockChain bs) :
    bs.Pairwise fun b b' => b.timestamp ≤ b'.timestamp :=
  (timestamp_lt h).imp Nat.le_of_lt

/-- Block numbers count up along a chain. -/
theorem number_eq : ∀ {bs : List BlockEnv}, BlockChain bs →
    ∀ (i : Nat) (hi : i < bs.length), bs[i].number = (bs[0]'(by omega)).number + i
  | [], _, i, hi => absurd hi (by simp)
  | [_], _, i, hi => by
    have : i = 0 := by simp at hi; omega
    subst this; rfl
  | b :: b' :: bs, h, i, hi => by
    cases i with
    | zero => rfl
    | succ i =>
      have := number_eq h.2 i (by simp at hi ⊢; omega)
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at this ⊢
      rw [this, h.1.number]; omega

/-- The chain id is the same along a chain. -/
theorem chainId_eq : ∀ {bs : List BlockEnv}, BlockChain bs → ∀ b ∈ bs, ∀ b' ∈ bs,
    b.chainId = b'.chainId
  | [], _ => by simp
  | [_], _ => by simp
  | b :: b' :: bs, h => by
    have ih := chainId_eq h.2
    have hb : ∀ c ∈ b' :: bs, c.chainId = b.chainId := fun c hc =>
      (ih c hc b' (List.mem_cons_self ..)).trans h.1.chainId
    intro c hc d hd
    simp only [List.mem_cons] at hc hd
    rcases hc with rfl | hc <;> rcases hd with rfl | hd
    · rfl
    · exact (hb d (by simp_all)).symm
    · exact hb c (by simp_all)
    · exact ih c (by simp_all) d (by simp_all)

end BlockChain

/-! ## Agreement with block validation -/

/-- The environment in which `Block.stateTransition` executes `block` on top of `head`. -/
def envOf (chainId : Nat) (head : ChainHead) (block : Block) : BlockEnv :=
  blockEnv chainId block.header head.ancestorHashes

private theorem ok_of_ite {ε α : Type} {c : Prop} [Decidable c] {A B : Except ε α} {x : α}
    (h : (if c then A else B) = .ok x) : A = .ok x ∨ B = .ok x := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte] at h; exact .inl h
  · simp only [hc, ↓reduceIte] at h; exact .inr h

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
  rcases ok_of_ite h with h | h
  · exact (ok_of_ite_throw h).2
  · exact h

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

/-- A valid header has a larger timestamp than its parent and the next number. -/
theorem validateHeader_ok {keccak256 : ByteArray → Word} {fork : Fork} {parent : Header}
    {parentHash : Word} {h : Header}
    (hv : validateHeader keccak256 fork parent parentHash h = .ok ()) :
    parent.timestamp < h.timestamp ∧ h.number = parent.number + 1 := by
  unfold validateHeader at hv
  dsimp only at hv
  obtain ⟨-, hv⟩ := ok_of_ite_throw hv
  obtain ⟨-, hv⟩ := ok_of_ite_throw hv
  obtain ⟨-, hv⟩ := ok_of_ite_throw hv
  obtain ⟨-, hv⟩ := ok_of_ite_throw hv
  obtain ⟨-, hv⟩ := ok_of_ite_throw hv
  obtain ⟨-, hv⟩ := ok_of_ite_throw hv
  obtain ⟨h₁, hv⟩ := ok_of_ite_throw hv
  obtain ⟨h₂, -⟩ := ok_of_ite_throw hv
  exact ⟨by omega, by omega⟩

/-- **What a valid block leaves behind**: the new head is the block's header and hash, its
ancestor hashes are the old ones shifted by its hash, and the header passed
`validateHeader` against the old head. -/
theorem stateTransition_head {fuel : Nat} {crypto : Crypto} {fork : Fork} {chainId : Nat}
    {head head' : ChainHead} {block : Block} {hints : List (Option Address)}
    {rs : Array Receipt}
    (h : stateTransition fuel crypto fork chainId head block hints = .ok (head', rs)) :
    head'.header = block.header ∧ head'.hash = headerHash crypto.keccak256 block.header ∧
      head'.ancestorHashes = (head'.hash :: head.ancestorHashes).take 256 ∧
      validateHeader crypto.keccak256 fork head.header head.hash block.header = .ok () := by
  unfold stateTransition at h
  dsimp only at h
  replace h := ok_of_ite_ite_throw h
  obtain ⟨-, h⟩ := ok_of_ite_throw h
  obtain ⟨u, hv, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_ite_throw h
  obtain ⟨out, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_ite_throw h
  obtain ⟨-, h⟩ := ok_of_ite_throw h
  obtain ⟨-, h⟩ := ok_of_ite_throw h
  obtain ⟨-, h⟩ := ok_of_ite_throw h
  obtain ⟨-, h⟩ := ok_of_ite_throw h
  obtain ⟨-, h⟩ := ok_of_ite_throw h
  obtain ⟨-, h⟩ := ok_of_ite_throw h
  obtain ⟨-, h⟩ := ok_of_ite_throw h
  cases h
  exact ⟨rfl, rfl, rfl, ok_of_mapError hv⟩

/-- **The hypotheses are sound**: the environments of two consecutive valid blocks (as
`Block.stateTransition` executes them, on any forks) are `NextBlock`. -/
theorem nextBlock_stateTransition {fuel₁ fuel₂ : Nat} {crypto : Crypto} {fork₁ fork₂ : Fork}
    {chainId : Nat} {head₀ head₁ head₂ : ChainHead} {blk₁ blk₂ : Block}
    {hints₁ hints₂ : List (Option Address)} {rs₁ rs₂ : Array Receipt}
    (h₁ : stateTransition fuel₁ crypto fork₁ chainId head₀ blk₁ hints₁ = .ok (head₁, rs₁))
    (h₂ : stateTransition fuel₂ crypto fork₂ chainId head₁ blk₂ hints₂ = .ok (head₂, rs₂)) :
    NextBlock (envOf chainId head₀ blk₁) (envOf chainId head₁ blk₂) := by
  obtain ⟨hh, -, ha, -⟩ := stateTransition_head h₁
  obtain ⟨-, -, -, hv⟩ := stateTransition_head h₂
  obtain ⟨hts, hnum⟩ := validateHeader_ok hv
  rw [hh] at hts hnum
  refine ⟨rfl, hnum, hts, ⟨head₁.hash, ?_⟩⟩
  simp only [envOf, blockEnv, ha, List.take_take, Nat.min_self, List.take_succ_cons]
  rfl

end EvmLogic.Program
