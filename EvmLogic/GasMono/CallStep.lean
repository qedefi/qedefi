import EvmLogic.GasMono.Bump

/-!
# Gas monotonicity: the `CALL` step

`exec_bump` (`EvmLogic.Program.Nested.Gas`) covers every instruction except the ones reading the gas. This
file covers the `CALL` family from a machine related to a low-gas machine `m` by

  `withTop b (bump d x ps m)`: `d` more frame gas, and the requested gas on top of the stack
  replaced by `b` with `a ≤ b ≤ a + d` (`a` the low request),

which is the relation after a `GAS` (`exec_gas_bump`: the high run pushes `d` more) and, with
`b = a`, the plain bump. `execCall_mono`: if the low instruction succeeds, so does the high
one, with

* the same action up to the child's gas: `.next` for both (depth limit, insufficient balance:
  the call is not made and the forwarded gas is refunded), or `.call req` and
  `.call (req.withGas c')` with `req.msg.gas ≤ c'` (EIP-150's all-but-1/64 is monotone);
* a bumped caller afterwards (`BumpOf`): the high caller keeps at least the low caller's gas,
  because the extra forwarded gas `c' - c` is at most `d` (`mcg_mono`).
-/

namespace EvmLogic.GasMono
open EvmLean EvmLogic.Program

open EvmLean.Interpreter EvmLogic.Program.Nested

/-- `m''` is `m'` with more frame gas, message gas `x` and parents `ps`. -/
def BumpOf (x : Nat) (ps : List Frame) (m' m'' : Machine) : Prop :=
  m'.frame.gasLeft ≤ m''.frame.gasLeft ∧
    m'' = bump (m''.frame.gasLeft - m'.frame.gasLeft) x ps m'

/-- How the actions and machines of a low and a high `CALL*` correspond. -/
def CallRel (x : Nat) (ps : List Frame) : Action → Action → Machine → Machine → Prop
  | .next, .next, m', m'' => BumpOf x ps m' m''
  | .call req, .call req', m', m'' => req.msg.gas ≤ req'.msg.gas ∧
      req' = req.withGas req'.msg.gas ∧ BumpOf x ps m' m''
  | .next, .stop _, _, _ | .next, .revert _, _, _ | .next, .call _, _, _
  | .next, .create _, _, _ => False
  | .call _, .next, _, _ | .call _, .stop _, _, _ | .call _, .revert _, _, _
  | .call _, .create _, _, _ => False
  | .stop _, _, _, _ | .revert _, _, _, _ | .create _, _, _, _ => False

/-- `BumpOf` as a bump. -/
theorem BumpOf.eq {x : Nat} {ps : List Frame} {m' m'' : Machine} (h : BumpOf x ps m' m'') :
    ∃ d', m'' = bump d' x ps m' := ⟨_, h.2⟩

/-- **The arithmetic of a monotone call**: with `a ≤ b ≤ a + d` requested and `d` more gas
left, the high call is affordable, forwards at least as much, and leaves the caller at least as
much (before and after a refund of the forwarded gas). -/
theorem mcg_mono {v a b L d M E : Nat} (hab : a ≤ b) (hbd : b ≤ a + d)
    (hle : (Gas.messageCallGas v a L M E).cost + M ≤ L) :
    (Gas.messageCallGas v b (L + d) M E).cost + M ≤ L + d ∧
    (Gas.messageCallGas v a L M E).subCall ≤ (Gas.messageCallGas v b (L + d) M E).subCall ∧
    L - ((Gas.messageCallGas v a L M E).cost + M) ≤
      L + d - ((Gas.messageCallGas v b (L + d) M E).cost + M) ∧
    L + d - ((Gas.messageCallGas v b (L + d) M E).cost + M) =
      L - ((Gas.messageCallGas v a L M E).cost + M) +
        (L + d - ((Gas.messageCallGas v b (L + d) M E).cost + M) -
          (L - ((Gas.messageCallGas v a L M E).cost + M))) ∧
    L - ((Gas.messageCallGas v a L M E).cost + M) + (Gas.messageCallGas v a L M E).subCall ≤
      L + d - ((Gas.messageCallGas v b (L + d) M E).cost + M) +
        (Gas.messageCallGas v b (L + d) M E).subCall ∧
    L + d - ((Gas.messageCallGas v b (L + d) M E).cost + M) +
        (Gas.messageCallGas v b (L + d) M E).subCall =
      L - ((Gas.messageCallGas v a L M E).cost + M) + (Gas.messageCallGas v a L M E).subCall +
        (L + d - ((Gas.messageCallGas v b (L + d) M E).cost + M) +
            (Gas.messageCallGas v b (L + d) M E).subCall -
          (L - ((Gas.messageCallGas v a L M E).cost + M) +
            (Gas.messageCallGas v a L M E).subCall)) := by
  unfold Gas.messageCallGas Gas.maxMessageCallGas at *
  by_cases h1 : L < E + M
  · simp only [h1, ↓reduceIte] at hle; omega
  · have h2 : ¬ L + d < E + M := by omega
    simp only [h1, h2, ↓reduceIte] at hle ⊢
    omega

@[simp] theorem twp_accessDelegation {m : Machine} (a : Address)
    {Q : Bool × Address × ByteArray × Nat → Machine → Prop} :
    Twp (accessDelegation a) Q m ↔
      ((m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code a) = none) ∧
        Q (false, a, m.world.code a, 0) m) ∨
      (∃ d, ¬ m.ctx.fork < .prague ∧ delegatedAddress? (m.world.code a) = some d ∧
        Q (true, d, delegateCode m.precompiles.isPrecompile m.world d,
            Gas.accessCost (m.frame.sub.accessedAddresses.contains d))
          { m with frame := { m.frame with sub := m.frame.sub.warmAddr d } }) := by
  unfold accessDelegation
  by_cases hf : m.ctx.fork < .prague
  · simp [hf]
  · cases hd : delegatedAddress? (m.world.code a) with
    | none => simp [hf, hd]
    | some d => simp [hf, hd]

/-- Close a goal of the `CALL` relation: introduce, split conjunctions, pick the disjunct whose
side conditions are hypotheses, and finish the arithmetic with `mcg_mono`. -/
syntax "callrel_solve" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| callrel_solve) => `(tactic| first
      | with_reducible_and_instances assumption
      | (intro h; first
          | (obtain ⟨_, _, _, _, _, _⟩ := mcg_mono (d := d) hab hbd h; callrel_solve)
          | callrel_solve)
      | (apply And.intro <;> callrel_solve)
      | (apply Or.inl; apply And.intro; with_reducible_and_instances assumption; callrel_solve)
      | (apply Or.inr; apply And.intro; with_reducible_and_instances assumption; callrel_solve)
      | (apply Or.inr; callrel_solve)
      | (apply Or.inl; callrel_solve)
      | (apply Exists.intro; callrel_solve)
      | with_reducible_and_instances rfl)

set_option maxHeartbeats 4000000 in
/-- `STATICCALL` from the related high machine. -/
theorem execCall_staticcall_mono (m : Machine) (b : Word) (d x : Nat) (ps : List Frame)
    (a : Word) (s : List Word) (hs : m.frame.stack = a :: s) (hab : a.toNat ≤ b.toNat)
    (hbd : b.toNat ≤ a.toNat + d) :
    Wp (execCall .staticcall) (fun act m' => Twp (execCall .staticcall)
      (fun act' m'' => CallRel x ps act act' m' m'') (withTop b (bump d x ps m))) m := by
  simp [execCall, withTop, bump, hs, memoryExpansion, expandMemory, readMemory,
    setReturnData, genericCall]
  intro x1 xs h1 x2 xs2 h2 x3 xs3 h3 x4 xs4 h4 x5 xs5 h5
  subst h1 h2 h3 h4 h5
  simp only [CallRel, BumpOf, bump, CallRequest.withGas, Machine.mk.injEq, Frame.mk.injEq,
    Message.mk.injEq, CallRequest.mk.injEq, true_and, and_true]
  callrel_solve

set_option maxHeartbeats 4000000 in
/-- `CALL` from the related high machine. -/
theorem execCall_call_mono (m : Machine) (b : Word) (d x : Nat) (ps : List Frame)
    (a : Word) (s : List Word) (hs : m.frame.stack = a :: s) (hab : a.toNat ≤ b.toNat)
    (hbd : b.toNat ≤ a.toNat + d) :
    Wp (execCall .call) (fun act m' => Twp (execCall .call)
      (fun act' m'' => CallRel x ps act act' m' m'') (withTop b (bump d x ps m))) m := by
  simp (config := { maxSteps := 2000000 }) [execCall, withTop, bump, hs, memoryExpansion,
    expandMemory, readMemory, setReturnData, genericCall]
  intro x1 xs h1 x2 xs2 h2 x3 xs3 h3 x4 xs4 h4 x5 xs5 h5 x6 xs6 h6
  subst h1 h2 h3 h4 h5 h6
  simp only [CallRel, BumpOf, bump, CallRequest.withGas, Machine.mk.injEq, Frame.mk.injEq,
    Message.mk.injEq, CallRequest.mk.injEq, true_and, and_true]
  refine ⟨fun hcond hc hst => ?_, fun dl hfork hdl hc hst => ?_⟩
  · have hm := mcg_mono (d := d) hab hbd hc
    have h1 := hm.1
    have h2 := hm.2.1
    have h3 := hm.2.2.1
    have h4 := hm.2.2.2.1
    have h5 := hm.2.2.2.2.1
    have h6 := hm.2.2.2.2.2
    exact ⟨fun hbal hlen => .inl ⟨hcond, h1, hst, .inl ⟨hbal, hlen, h5, h6⟩⟩,
      fun hbal => ⟨fun hdep hlen => .inl ⟨hcond, h1, hst, .inr ⟨hbal, .inl ⟨hdep, hlen, h5, h6⟩⟩⟩,
        fun hdep => .inl ⟨hcond, h1, hst, .inr ⟨hbal, .inr ⟨hdep, h2, h3, h4⟩⟩⟩⟩⟩
  · have hm := mcg_mono (d := d) hab hbd hc
    have h1 := hm.1
    have h2 := hm.2.1
    have h3 := hm.2.2.1
    have h4 := hm.2.2.2.1
    have h5 := hm.2.2.2.2.1
    have h6 := hm.2.2.2.2.2
    refine ⟨fun hbal hlen => .inr ⟨hfork, dl, hdl, h1, hst, .inl ⟨hbal, hlen, h5, h6, rfl⟩⟩,
      fun hbal => ⟨fun hdep hlen => .inr ⟨hfork, dl, hdl, h1, hst, .inr ⟨hbal, .inl ⟨hdep, hlen, h5, h6, rfl⟩⟩⟩,
        fun hdep => .inr ⟨hfork, dl, hdl, h1, hst, .inr ⟨hbal, .inr ⟨hdep, ?_⟩⟩⟩⟩⟩
    repeat' apply And.intro
    all_goals first | rfl | assumption

end EvmLogic.GasMono
