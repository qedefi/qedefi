import Verified.Safe.Contracts.MiniSafe
import EvmLogic.Tactic.OwnStep
import EvmLogic.Solidity.Memory
import QEDefi.Actor.Derive

/-!
# MiniSafe's signature loop on bytecode

The loop of `checkSignatures` (pc `604`, `0x025c`): with fewer than `threshold` owners among the
signers `T`, it never exits normally. Each iteration recovers a signer with the `ecrecover`
precompile, requires it to exceed the previous one and to be an owner, so after `i` iterations
`i` distinct owners whose signature `ecrecover` produced have been counted. A recovered owner is
in `T` (`Signers`, a hypothesis in the style of `SigUnforgeable`: the digest is a MiniSafe
digest of this Safe on this chain). So `i ≤ cnt (O ∩ T) last ≤ |O ∩ T| < threshold`, and the
loop condition `i < threshold` never fails: every path reverts.

`loop` states this as `Own`: from the loop head, every own path of the frame ends it, with no
`SSTORE` and only `ecrecover` calls.
-/

namespace Verified.Safe.MiniSafe

open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested
open Verified.Safe.Contracts

/-! ## The frame and its safety conditions -/

/-- The constants of a MiniSafe frame (standard precompiles). -/
abbrev fix (msg : Message) (ctx : Context) : Fix :=
  ⟨msg, ctx, PrecompileImpl.standard ctx, MiniSafe.runtimeCode⟩

/-- A MiniSafe frame writes only the nonce (slot `1`). -/
abbrev S : Machine → Prop := Own.SstoreOk (· = 1)

/-- A MiniSafe frame calls only `ecrecover` (precompile `1`). -/
def C : Machine → CallRequest → Prop := fun _ req => req.msg.currentTarget = 1

/-- The storage slot of `isOwner[a]` (mapping at slot `2`). -/
def ownerSlot (crypto : Crypto) (a : Address) : Word :=
  crypto.keccak256 (Bytes.ofWord (Word.ofAddress a) ++ Bytes.ofWord 2)

/-- The 192 bytes a MiniSafe at `ms` on chain `chainId` hashes into a transaction digest
(`getTransactionHash`): they start with the chain id and the Safe. -/
def Encoded (chainId : Nat) (ms : Address) (x : ByteArray) : Prop :=
  x.size = 192 ∧ x.extract 0 64 = Bytes.ofWord (ofNat chainId) ++ Bytes.ofWord (Word.ofAddress ms)

/-- **The signers** (in the style of `SigUnforgeable`): every owner that `ecrecover` recovers
from a digest of this MiniSafe is in `T`. Owners outside `T` signed no transaction of this Safe
on this chain. -/
def Signers (crypto : Crypto) (chainId : Nat) (ms : Address) (O T : Finset Address) : Prop :=
  ∀ x v r s a, Encoded chainId ms x → ecrecoverAddress? crypto (crypto.keccak256 x) v r s = some a →
    a ∈ O → a ∈ T

/-- The counted owners up to the address word `x`. -/
def cnt (OT : Finset Address) (x : Word) : Nat :=
  (OT.filter fun a => (Word.ofAddress a).toNat ≤ x.toNat).card

/-! ## Counting -/

theorem card_le (s : Finset Address) : s.card ≤ 2 ^ 160 := by
  have h := Finset.card_le_card_of_injOn (s := s) (t := Finset.range (2 ^ 160))
    (fun a : Address => a.toNat) (fun a _ => by simpa using a.isLt)
    (fun a _ b _ h => BitVec.eq_of_toNat_eq h)
  simpa using h

theorem cnt_le (OT : Finset Address) (x : Word) : cnt OT x ≤ OT.card :=
  Finset.card_filter_le _ _

theorem cnt_lt {OT : Finset Address} {a : Address} {x y : Word} (ha : a ∈ OT)
    (hx : x.toNat < (Word.ofAddress a).toNat) (hy : (Word.ofAddress a).toNat ≤ y.toNat) :
    cnt OT x < cnt OT y := by
  unfold cnt
  apply Finset.card_lt_card
  refine ⟨fun b hb => ?_, fun h => ?_⟩
  · simp only [Finset.mem_filter] at hb ⊢
    exact ⟨hb.1, by omega⟩
  · have := h (Finset.mem_filter.2 ⟨ha, hy⟩)
    simp only [Finset.mem_filter] at this
    omega

/-! ## Words -/

theorem ofBool_ne_zero {b : Bool} : Word.ofBool b ≠ 0 ↔ b = true := by
  cases b <;> decide

theorem iszero_ne_zero {x : Word} : Word.iszero x ≠ 0 ↔ x = 0 := by
  unfold Word.iszero; rw [ofBool_ne_zero, beq_iff_eq]

theorem iszero_eq_zero {x : Word} : Word.iszero x = 0 ↔ x ≠ 0 := by
  rw [← not_iff_not, not_not, ← ne_eq, iszero_ne_zero]

theorem lt_ne_zero {x y : Word} : Word.lt x y ≠ 0 ↔ x.toNat < y.toNat := by
  unfold Word.lt; rw [ofBool_ne_zero]; simp [BitVec.ult]

theorem gt_ne_zero {x y : Word} : Word.gt x y ≠ 0 ↔ y.toNat < x.toNat := by
  unfold Word.gt; rw [ofBool_ne_zero]; simp [BitVec.ult]

theorem and_mask_of_lt {x : Word} (h : x.toNat < 2 ^ 160) :
    (x &&& 1461501637330902918203684832716283019655932542975#256) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1461501637330902918203684832716283019655932542975#256).toNat =
    2 ^ 160 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]

theorem mask_and_of_lt {x : Word} (h : x.toNat < 2 ^ 160) :
    (1461501637330902918203684832716283019655932542975#256 &&& x) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1461501637330902918203684832716283019655932542975#256).toNat =
    2 ^ 160 - 1 from rfl, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]

theorem toNat_ofAddress_lt (a : Address) : (Word.ofAddress a).toNat < 2 ^ 160 := by
  simp only [Word.ofAddress, BitVec.toNat_setWidth]; have := a.isLt; omega

/-- The address mask `2¹⁶⁰ - 1` keeps an address. -/
theorem mask_and_ofAddress (a : Address) :
    (1461501637330902918203684832716283019655932542975#256 &&& Word.ofAddress a) =
      Word.ofAddress a :=
  mask_and_of_lt (toNat_ofAddress_lt a)

/-! ## Memory and `ecrecover` -/

theorem read_128 (m : Memory) (off : Nat) : m.read off 128 =
    m.read off 32 ++ (m.read (off + 32) 32 ++ (m.read (off + 64) 32 ++ m.read (off + 96) 32)) := by
  rw [show (128 : Nat) = 32 + 96 from rfl, Memory.read_add, show (96 : Nat) = 32 + 64 from rfl,
    Memory.read_add, show (64 : Nat) = 32 + 32 from rfl, Memory.read_add, Nat.add_assoc]

/-- `ecrecover` on four words, as the standard precompile at `1`. -/
theorem run_ecrecover (ctx : Context) (h v r s : Word) (g : Nat) :
    (PrecompileImpl.standard ctx).run (Word.toAddress 1#256)
        (Bytes.ofWord h ++ (Bytes.ofWord v ++ (Bytes.ofWord r ++ Bytes.ofWord s))) g =
      if 3000 ≤ g then (⟨true, g - 3000, ecrecoverOutput ctx.crypto h v r s⟩ : Precompile.Result)
      else Precompile.fail := by
  show Precompile.run ctx.crypto ctx.fork 1 _ g = _
  rw [run_one]
  split
  · rw [ecrecover_words _ _ _ _ _ (by assumption)]; rfl
  · rename_i hg
    unfold Precompile.ecrecover
    simp [Nat.lt_of_not_le hg]

/-! ## The loop -/

/-- What the loop relies on: the threshold `t` (above the number of owners among the signers),
the owners' slots, the signers, the digest being a MiniSafe digest, and `ecrecover` being the
precompile. -/
structure LoopCtx (msg : Message) (ctx : Context) (w : World) (O T : Finset Address) (thr : Nat)
    (t hash : Word) : Prop where
  thr_lt : thr < 2 ^ 256
  t_eq : t = BitVec.ofNat 256 thr
  card : (O ∩ T).card < thr
  owner : ∀ a, w.sload msg.currentTarget (ownerSlot ctx.crypto a) ≠ 0 → a ∈ O
  signers : Signers ctx.crypto ctx.block.chainId msg.currentTarget O T
  digest : ∃ x, Encoded ctx.block.chainId msg.currentTarget x ∧ hash = ctx.crypto.keccak256 x
  deleg : ctx.fork < .prague ∨ delegatedAddress? (w.code 1) = none

variable {msg : Message} {ctx : Context} {w : World} {O T : Finset Address} {thr : Nat}
  {t hash len off : Word}

set_option maxHeartbeats 4000000 in
/-- **The loop never exits normally.** -/
theorem loop (hL : LoopCtx msg ctx w O T thr t hash) :
    ∀ n (m : Machine) (M : Memory) (i last : Word) (p : Nat) (rest : List Word),
      Fr (fix msg ctx) m 604 (i :: last :: t :: len :: off :: hash :: rest) M w →
      M.loadWord 64 = BitVec.ofNat 256 p → 128 ≤ p → p ≤ 352 + 32 * i.toNat →
      i.toNat ≤ cnt (O ∩ T) last → last.toNat < 2 ^ 160 →
      (O ∩ T).card - cnt (O ∩ T) last = n → Own S C m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro m M i last p rest hF hfp hp1 hp2 hi hlast hn
  have hp3 : p < 2 ^ 200 := by
    have := cnt_le (O ∩ T) last
    have := card_le (O ∩ T)
    omega
  own_explore [604] using [hfp, Memory.loadWord_storeWord_of_disjoint, BitVec.ofNat_add_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  · -- `ecrecover` is a precompile.
    show Precompile.isPrecompile ctx.fork (Word.toAddress 1#256) = true
    exact isPrecompile_one _
  · exact hL.deleg
  · intro req h
    show req.msg.currentTarget = 1
    rw [h]; rfl
  · -- The back edge: one more owner among the signers.
    obtain ⟨g, hsucc, rfl⟩ := hres (iszero_eq_zero.1 (iszero_ne_zero.1 hc703))
    simp only [Nat.reducePow] at hp3
    have e1 : (BitVec.ofNat 256 (p + 32)).toNat = p + 32 := by
      simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
    have e2 : BitVec.ofNat 256 (160 + p) - BitVec.ofNat 256 (p + 32) = 128#256 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow]; omega
    have e3 : BitVec.ofNat 256 (p + 32) - 32#256 = BitVec.ofNat 256 p := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow]; omega
    simp (disch := omega) only [e1, e2, e3, BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_eq_of_lt,
      readBytes_bytes, read_128, Memory.read_64, Memory.read_expand,
      Memory.read_storeWord_of_disjoint, Memory.read_storeWord] at hsucc hc750 hc783 hF
    rw [run_ecrecover] at hsucc hc750 hc783 hF
    by_cases hg : 3000 ≤ g
    swap
    · simp [hg, Precompile.fail] at hsucc
    simp only [hg, ↓reduceIte, returnMemory_ecrecoverOutput] at hc750 hc783 hF
    obtain ⟨x, hx, hxh⟩ := hL.digest
    split at hc750
    · -- A signer `a` was recovered.
      rename_i a hrec
      simp only [hrec] at hc783 hF
      simp (disch := omega) only [e3, BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_eq_of_lt,
        Memory.loadWord_expand, Memory.loadWord_storeWord, Memory.loadWord_storeWord_of_disjoint,
        mask_and_ofAddress, and_mask_of_lt (toNat_ofAddress_lt a)] at hc750 hc783 hF
      rw [mask_and_of_lt hlast, iszero_eq_zero, gt_ne_zero] at hc750
      -- `a` is an owner (its slot is set) and a signer.
      have hO : a ∈ O := hL.owner a fun h0 => hc783 (by
        have h0' : w.sload msg.currentTarget (ctx.crypto.keccak256
            (Bytes.ofWord (Word.ofAddress a) ++ Bytes.ofWord 2#256)) = 0 := h0
        rw [h0']; rfl)
      have hT : a ∈ T := hL.signers x _ _ _ a hx (hxh ▸ hrec) hO
      have hOT : a ∈ O ∩ T := Finset.mem_inter.2 ⟨hO, hT⟩
      have hcnt := cnt_lt hOT hc750 (Nat.le_refl _)
      have hle := cnt_le (O ∩ T) (Word.ofAddress a)
      have hi1 : (i + 1#256).toNat = i.toNat + 1 := by
        have := card_le (O ∩ T)
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
        omega
      refine ih _ (by omega) m _ (i + 1#256) (Word.ofAddress a) (p + 32) rest hF ?_ (by omega)
        (by omega) (by omega) (toNat_ofAddress_lt a) rfl
      simp (disch := omega) only [Memory.loadWord_expand, Memory.loadWord_storeWord,
        Memory.loadWord_storeWord_of_disjoint]
    · -- No signer: `cur = 0`, which is not above `last`.
      exfalso
      simp (disch := omega) only [e3, BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_eq_of_lt,
        Memory.loadWord_expand, Memory.loadWord_storeWord,
        Memory.loadWord_storeWord_of_disjoint, BitVec.and_zero] at hc750
      rw [iszero_eq_zero, gt_ne_zero] at hc750
      simp at hc750
  · -- `cur > last` failed, yet its value was used as true.
    exact absurd (iszero_ne_zero.1 hc750) hc783
  · -- The loop exits only if `i ≥ threshold`, but `i ≤ |O ∩ T| < threshold`.
    exfalso
    rw [iszero_ne_zero, ← not_ne_iff, lt_ne_zero, hL.t_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hL.thr_lt] at hc612
    have := cnt_le (O ∩ T) last
    have := hL.card
    omega

end Verified.Safe.MiniSafe
