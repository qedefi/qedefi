import Verified.WeirdERC20.AMPL.Spec.PermitMem

/-!
# AMPL's `name()` copy loop, at any gas

`DOMAIN_SEPARATOR()` hashes `name()`, which solc 0.7 copies from storage into memory. A long
name (32 bytes or more) is copied by the loop at pc `1911`. It stores the word at slot
`keccak256(51) + i` at memory `dst + 32 i`, until `dst + 32 i` reaches the end `e`.

`loop_low`: from the loop head with `k` words left, at any gas, the frame fails or reaches the
loop's exit (pc `1931`) with the memory `loopMem` (the `k` words stored). The gas and the
access lists are left unknown. `read_loopMem`: those words read back as `Str.wordsFrom`.
-/

set_option linter.unusedSimpArgs false

namespace Verified.WeirdERC20.AMPL.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Verified.WeirdERC20.AMPL.Contracts Verified.Solady.Spec.AnyGas

set_option maxHeartbeats 0 in
/-- **One iteration of the copy loop at any gas**: the word at slot `p` stored at `dst`, then
back to the head while `e > dst + 32`, else to the exit. -/
theorem loop_step {H : Machine → Outcome → Prop} {Q : Machine → Prop} (hF : FailH H)
    (m : Machine) (dst p e : Word) (rest : List Word)
    (hc : m.frame.code = AMPL.runtimeCode) (hj : JumpTable m.frame.jumpDests AMPL.runtimeCode)
    (hpc : m.frame.pc = 1911) (hs : m.frame.stack = dst :: p :: e :: rest)
    (kc : ∀ (g : Nat) (sb : Substate), sb.logs = m.frame.sub.logs → Word.gt e (32#256 + dst) ≠ 0 →
      WP { m with frame := { m.frame with
        pc := 1911
        stack := (32#256 + dst) :: (1#256 + p) :: e :: rest
        memory := (m.frame.memory.expand dst.toNat 32).storeWord dst.toNat
          (m.world.sload m.frame.msg.currentTarget p)
        gasLeft := g
        sub := sb } } Q H)
    (kx : ∀ (g : Nat) (sb : Substate), sb.logs = m.frame.sub.logs → Word.gt e (32#256 + dst) = 0 →
      WP { m with frame := { m.frame with
        pc := 1931
        stack := (32#256 + dst) :: (1#256 + p) :: e :: rest
        memory := (m.frame.memory.expand dst.toNat 32).storeWord dst.toNat
          (m.world.sload m.frame.msg.currentTarget p)
        gasLeft := g
        sub := sb } } Q H) :
    WP m Q H := by
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hc hpc hs
  refine pwp_jumpdest hF (by pcode_fact) fun _ => ?_
  dsimp only
  hwp_steps stop_at [1911, 1931] []
  all_goals first | exact kc _ _ rfl ‹_› | exact kx _ _ rfl ‹_›

/-- **The copy loop at any gas**: `k + 1` words left (`e` within the last). -/
theorem loop_low {H : Machine → Outcome → Prop} {Q : Machine → Prop} (hF : FailH H) :
    ∀ (k : Nat) (m : Machine) (dst p e : Word) (rest : List Word),
      m.frame.code = AMPL.runtimeCode → JumpTable m.frame.jumpDests AMPL.runtimeCode →
      m.frame.pc = 1911 → m.frame.stack = dst :: p :: e :: rest →
      dst.toNat + 32 * (k + 1) < 2 ^ 256 → dst.toNat + 32 * k < e.toNat →
      e.toNat ≤ dst.toNat + 32 * (k + 1) →
      (∀ (g : Nat) (sb : Substate), sb.logs = m.frame.sub.logs → WP { m with frame := { m.frame with
        pc := 1931
        stack := (BitVec.ofNat 256 (32 * (k + 1)) + dst) :: (BitVec.ofNat 256 (k + 1) + p) :: e ::
          rest
        memory := loopMem (m.world.sload m.frame.msg.currentTarget) m.frame.memory dst p (k + 1)
        gasLeft := g
        sub := sb } } Q H) →
      WP m Q H := by
  intro k
  induction k with
  | zero =>
    intro m dst p e rest hc hj hpc hs hb hlo hhi hk
    have hd32 := toNat_32_add (dst := dst) (by omega)
    refine loop_step hF m dst p e rest hc hj hpc hs
      (fun _ _ _ h => absurd (Str.gt_eq_zero (by rw [hd32]; omega)) h) fun g sb hsb _ => ?_
    have := hk g sb hsb
    rw [loopMem_succ, loopMem_zero] at this
    exact this
  | succ k ih =>
    intro m dst p e rest hc hj hpc hs hb hlo hhi hk
    have hd32 := toNat_32_add (dst := dst) (by omega)
    refine loop_step hF m dst p e rest hc hj hpc hs (fun g sb hsb _ => ?_)
      fun _ _ _ h => by
        rw [Str.gt_eq_one (a := e) (b := 32#256 + dst) (by rw [hd32]; omega)] at h
        exact absurd h (by decide)
    refine ih _ (32#256 + dst) (1#256 + p) e rest hc hj rfl rfl (by omega) (by omega)
      (by omega) fun g' sb' hsb' => ?_
    have h1 : BitVec.ofNat 256 (32 * (k + 1)) + (32#256 + dst) =
        BitVec.ofNat 256 (32 * (k + 1 + 1)) + dst := by
      rw [show 32 * (k + 1 + 1) = 32 * (k + 1) + 32 by ring, BitVec.ofNat_add, BitVec.add_assoc]
    have h2 : BitVec.ofNat 256 (k + 1) + (1#256 + p) = BitVec.ofNat 256 (k + 1 + 1) + p := by
      rw [BitVec.ofNat_add (k + 1) 1, BitVec.add_assoc]
    have := hk g' sb' (hsb'.trans hsb)
    rw [loopMem_succ] at this
    dsimp only
    rw [h1, h2]
    exact this

end Verified.WeirdERC20.AMPL.Spec.Malformed
