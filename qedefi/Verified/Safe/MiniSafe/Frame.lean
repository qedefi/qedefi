import Verified.Safe.MiniSafe.Loop

/-!
# MiniSafe frames on bytecode: every path ends the frame safely

`frame`: from the start of any frame running MiniSafe's code, every path of the frame by its own
instructions ends it (`Own S C`), writes storage only at the nonce (slot `1`) and calls only the
`ecrecover` precompile, provided fewer than `threshold` owners are signers. So the final `CALL`
of `execTransaction` is never reached. The signature loop is `Verified.Safe.MiniSafe.loop`;
`hashFn` is the transaction digest (`getTransactionHash`), which is a MiniSafe digest.
-/

namespace Verified.Safe.MiniSafe

open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested
open Verified.Safe.Contracts

variable {msg : Message} {ctx : Context} {w : World}

/-- A MiniSafe digest of the Safe at `msg.currentTarget` on this chain. -/
def Digest (msg : Message) (ctx : Context) (h : Word) : Prop :=
  ∃ x, Encoded ctx.block.chainId msg.currentTarget x ∧ h = ctx.crypto.keccak256 x

theorem extract_read_192 (m : Memory) (off : Nat) :
    (m.read off 192).extract 0 64 = m.read off 64 := by
  rw [show (192 : Nat) = 64 + 128 from rfl, Memory.read_add]
  have h : (m.read off 64).size = 64 := Memory.size_read _ _ _
  rw [ByteArray.extract_append_eq_left h.symm]

set_option maxHeartbeats 4000000 in
/-- **The transaction digest** (`getTransactionHash`, pc `249`): it returns a MiniSafe digest,
with the free memory pointer at `0x160`. -/
theorem hashFn {m : Machine} {M : Memory} {nonce L dataOff value dst ret : Word}
    {rest : List Word}
    (hF : Fr (fix msg ctx) m 249 (nonce :: L :: dataOff :: value :: dst :: ret :: rest) M w)
    (hM : M.loadWord 64 = 128#256) (hL : L.toNat < 2 ^ 64)
    (k : ∀ m' M' h, Fr (fix msg ctx) m' ret.toNat (h :: rest) M' w →
      M'.loadWord 64 = 352#256 → Digest msg ctx h → Own S C m') :
    Own S C m := by
  own_explore using [hM, Memory.loadWord_storeWord_of_disjoint, Own.loadWord_copyIn_readBytes,
    Memory.read_storeWord_of_disjoint]
  refine k m _ _ hF ?_ ⟨_, ⟨size_readBytes _ _ _, ?_⟩, rfl⟩
  · simp (disch := own_disch) only [Memory.loadWord_expand, Memory.loadWord_storeWord]
  · simp (disch := own_disch) only [readBytes_bytes, extract_read_192, Memory.read_64,
      Memory.read_expand, Memory.read_storeWord, Memory.read_storeWord_of_disjoint,
      mask_and_ofAddress]

theorem len_bound {L : Word} (h : (L.gt 18446744073709551615#256).iszero ≠ 0) : L.toNat < 2 ^ 64 := by
  rw [iszero_ne_zero, ← not_ne_iff, gt_ne_zero] at h
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
  omega

/-- What a MiniSafe frame relies on, about its entry world `w` (the Safe is `msg.currentTarget`):
the threshold `thr` exceeds the number of owners among the signers `T`, the owner slots, the
signers, and `ecrecover` being the precompile. -/
structure FrameCtx (msg : Message) (ctx : Context) (w : World) (O T : Finset Address) (thr : Nat) :
    Prop where
  thr_lt : thr < 2 ^ 256
  threshold : w.sload msg.currentTarget 0 = BitVec.ofNat 256 thr
  card : (O ∩ T).card < thr
  owner : ∀ a, w.sload msg.currentTarget (ownerSlot ctx.crypto a) ≠ 0 → a ∈ O
  slot_ne : ∀ a, ownerSlot ctx.crypto a ≠ 1
  signers : Signers ctx.crypto ctx.block.chainId msg.currentTarget O T
  deleg : ctx.fork < .prague ∨ delegatedAddress? (w.code 1) = none

set_option maxHeartbeats 10000000 in
/-- **A MiniSafe frame ends safely**: from its start (pc `0`, empty stack and memory), every own
path ends the frame, writes only the nonce and calls only `ecrecover`. -/
theorem frame {O T : Finset Address} {thr : Nat} (hC : FrameCtx msg ctx w O T thr) {m : Machine}
    (hF : Fr (fix msg ctx) m 0 [] {} w) : Own S C m := by
  own_explore [249]
  all_goals
    refine hashFn hF (by simp only [Memory.loadWord_storeWord])
      (len_bound (by assumption)) fun m M h hF hM hD => ?_
    try simp only [BitVec.reduceToNat] at hF
    own_explore [604] using [hM, Memory.loadWord_storeWord_of_disjoint]
  -- The signature loop, from `execTransaction`, after the nonce is incremented.
  obtain ⟨x, hx, hh⟩ := hD
  refine loop (w := w.sstore msg.currentTarget 1#256 _) (thr := thr) (hash := h)
    ⟨hC.thr_lt, ?_, hC.card, fun a ha => hC.owner a ?_, hC.signers, ⟨x, hx, hh⟩, ?_⟩ _ m M
    0#256 0#256 352 _ hF hM (by omega) (by simp) (by simp) (by simp) rfl
  · rw [World.sload_sstore_ne_key _ _ _ (by decide)]; exact hC.threshold
  · rwa [World.sload_sstore_ne_key (k := 1#256) _ _ _ (hC.slot_ne a)] at ha
  · rw [World.code_sstore]; exact hC.deleg

end Verified.Safe.MiniSafe
