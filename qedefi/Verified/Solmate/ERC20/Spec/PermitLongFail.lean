import Verified.Solmate.ERC20.Spec.PermitLongDs
import Verified.Solady.Spec.AnyGasTactic

/-!
# Solmate's `permit` with a name too long to copy

The copy loop of `0x0a66` costs at least one gas per word (its `JUMPDEST` alone does), so a
frame whose gas is below the number of words still to copy cannot finish it: it fails, whatever
its gas (`plCopy_fails`). Off the deployment chain with a `name` of more than `2⁶⁴` words, every
frame of `permit` (it has less than `2⁶⁴` gas) fails this way.

`plany_steps`: the any-gas calculus of `Verified.Solady.Spec.AnyGas` (every instruction is
taken, or the frame ends with an exceptional halt, which the postcondition admits) over the
asset's patched code, keeping every hypothesis the rules provide (the gas bounds included, so
that the gas left is known to decrease) and leaving the gas as a closed difference.
-/

namespace Verified.Solmate.ERC20.Spec.PermitLongAny
open EvmLean Lean Meta Elab Tactic EvmLean.Interpreter EvmLogic.Program
open Verified.Solady.Spec.AnyGas

/-- One any-gas step of the main goal over literal or patched code. -/
def planyStep (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :
    TacticM (Option (List MVarId)) := withMainContext do
  let g ← getMainGoal
  let some m ← wpGoalMachine? g | return none
  let fr ← whnfR (mkApp (mkConst ``Machine.frame) m)
  let code ← whnfR (mkApp (mkConst ``Frame.code) fr)
  let pcE ← whnfR (mkApp (mkConst ``Frame.pc) fr)
  let some pc ← (evalNat (← instantiateMVars pcE)).run | return none
  let some (bytes, pinfo) ← codeInfo? code | return none
  let some b := bytes[pc]? | return none
  let hb ← Term.exprToSyntax (← pcodeFact code pinfo pc b)
  let bn := b.toNat
  let norm : TacticM Unit := do
    try evalTactic (← `(tactic| apwp_norm [$extra,*])) catch _ => pure ()
  let keep (k : Nat) : TacticM Unit := do
    for _ in [0:k] do
      evalTactic (← `(tactic| intro))
  let run (t : TSyntax `tactic) (k : Nat) : TacticM (Option (List MVarId)) := do
    if ← EvmLogic.Tactic.PrefixStep.attempt (do evalTactic t; keep k; norm) then return some (← getGoals) else return none
  if bn = 0xfd then
    if ← EvmLogic.Tactic.PrefixStep.attempt (evalTactic (← `(tactic| exact pwp_revert ‹_› $hb rfl))) then
      return some [] else return none
  if bn = 0xfe then
    if ← EvmLogic.Tactic.PrefixStep.attempt (evalTactic (← `(tactic| exact pwp_invalid ‹_› $hb))) then
      return some [] else return none
  if 0x5f ≤ bn ∧ bn ≤ 0x7f then
    let n := bn - 0x5f
    let some hvE ← ppushFact? code pinfo bytes pc n | return none
    let hv ← Term.exprToSyntax hvE
    let nS := Syntax.mkNumLit (toString n)
    return ← run (← `(tactic| refine pwp_push $nS (by decide) ‹_› $hb $hv ?_)) 2
  if 0x80 ≤ bn ∧ bn < 0x90 then
    let nS := Syntax.mkNumLit (toString (bn - 0x80))
    return ← run (← `(tactic| refine pwp_dup ⟨$nS, by decide⟩ ‹_› $hb rfl ?_)) 2
  if 0x90 ≤ bn ∧ bn < 0xa0 then
    let nS := Syntax.mkNumLit (toString (bn - 0x90))
    return ← run (← `(tactic| refine pwp_swap ⟨$nS, by decide⟩ ‹_› $hb rfl rfl ?_)) 1
  if bn = 0x57 then
    let ok ← EvmLogic.Tactic.PrefixStep.attempt do
      evalTactic (← `(tactic| refine pwp_jumpi ‹_› $hb rfl ?_ ?_))
      let gs ← getGoals
      let mut out : List MVarId := []
      for (gi, k) in gs.zip [1, 2] do
        setGoals [gi]
        evalTactic (← `(tactic| intro hc))
        keep k
        evalTactic (← `(tactic| (revert hc; intro hc)))
        EvmLogic.Tactic.PrefixStep.closeBranch extra
        if (← getGoals).isEmpty then continue
        norm
        out := out ++ (← getGoals)
      setGoals out
    if ok then return some (← getGoals) else return none
  match Verified.Solady.Spec.AnyGasTactic.ruleFor bn with
  | none => return none
  | some r =>
    let lS := mkIdent r.lemma
    let t ← if r.stk then `(tactic| refine $lS ‹_› $hb rfl ?_)
      else `(tactic| refine $lS ‹_› $hb ?_)
    run t r.intros

/-- Step every goal until each stops (at most `fuel` steps), or reaches a pc in `stops`. -/
def planySteps (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) (fuel : Nat)
    (stops : List Nat := []) : TacticM Unit := do
  let mut todo ← getGoals
  let mut stopped : List MVarId := []
  for _ in [0:fuel] do
    match todo with
    | [] => break
    | g :: rest =>
      if !stops.isEmpty then
        if let some pc ← Verified.Solady.Spec.AnyGasTactic.goalPc? g then
          if stops.contains pc then
            stopped := stopped ++ [g]; todo := rest; continue
      setGoals [g]
      match ← planyStep extra with
      | none => stopped := stopped ++ [g]; todo := rest
      | some new => todo := new ++ rest
  setGoals (stopped ++ todo)

/-- `plany_steps n stop_at [q₁, …] [h₁, …]`: at most `n` any-gas steps per call over
literal or patched code, stopping at the pcs `qᵢ` (after at least one step). -/
syntax "plany_steps" (ppSpace num)? (" stop_at " "[" num,* "]")?
  (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| plany_steps $[$n]? $[stop_at [$stops,*]]? $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    let stops := ((stops.map (·.getElems)).getD #[]).toList.map (·.getNat)
    planySteps extra ((n.map (·.getNat)).getD 100000) stops

end Verified.Solmate.ERC20.Spec.PermitLongAny

namespace Verified.Solmate.ERC20.Spec
open QEDefi.ERC4626 Verified.Solmate.ERC20.Permit
open Verified.Solmate.ERC20.Spec.PermitLongGas Verified.Solady.Spec.AnyGas

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts

set_option maxHeartbeats 0 in
/-- One word of the copy loop at any gas: back at the head with the next word, strictly less
gas, or a failure. -/
theorem plCopy_any {ia : SolmateAsset.Immutables} {H : Machine → Outcome → Prop}
    (hH : FailH H) {d Lw S : Word} {L k : Nat} {tl : List Word} (m : Machine)
    (hc : m.frame.code = SolmateAsset.runtimeCodeWith ia)
    (hj : JumpTable m.frame.jumpDests (SolmateAsset.runtimeCodeWith ia))
    (hpc : m.frame.pc = 2770) (hs : m.frame.stack = plStk d Lw S tl k)
    (hLw : Lw.toNat = L) (hk : 32 * k < L) (hL2 : L < 2 ^ 255) :
    WP m (fun m' => m'.frame.code = SolmateAsset.runtimeCodeWith ia ∧
      m'.frame.jumpDests = m.frame.jumpDests ∧ m'.frame.pc = 2770 ∧
      m'.frame.stack = plStk d Lw S tl (k + 1) ∧ m'.frame.gasLeft < m.frame.gasLeft) H := by
  have hagree := assetJumpDestsAgree ia
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only [plStk] at *
  subst hc hpc hs
  have hlt : Word.lt (BitVec.ofNat 256 (32 * k)) Lw = 1#256 :=
    (Word.lt_eq_one_iff _ _).2 (by rw [hLw, Str.toNat_ofNat_of_lt (by omega)]; omega)
  have hptr' : d + BitVec.ofNat 256 k + 1#256 = d + BitVec.ofNat 256 (k + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hi' : 32#256 + BitVec.ofNat 256 (32 * k) = BitVec.ofNat 256 (32 * (k + 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  plany_steps 1 [hlt, hptr', hi']
  plany_steps 30 stop_at [2770] [hlt, hptr', hi']
  apply WP.ret
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  dsimp only
  simp only [Gas.jumpdest] at *
  omega


/-- **The copy loop cannot finish on less gas than words to copy**: from its head after `k` of
`n` words, with gas below `n - k - 1`, the frame fails (any postcondition `H` that admits
failures). -/
theorem plCopy_fails {ia : SolmateAsset.Immutables} {H : Machine → Outcome → Prop}
    (hH : FailH H) {Q : Machine → Prop} {d Lw S : Word} {L n k : Nat} {tl : List Word}
    (m : Machine) (hc : m.frame.code = SolmateAsset.runtimeCodeWith ia)
    (hj : JumpTable m.frame.jumpDests (SolmateAsset.runtimeCodeWith ia))
    (hpc : m.frame.pc = 2770) (hs : m.frame.stack = plStk d Lw S tl k)
    (hLw : Lw.toNat = L) (hn : n = (L + 31) / 32) (hL2 : L < 2 ^ 255)
    (hgas : m.frame.gasLeft + k + 1 < n) : WP m Q H := by
  refine WP.loop_nat (fun j m' => ∃ k, j = n - k ∧ m'.frame.code = SolmateAsset.runtimeCodeWith ia ∧
      JumpTable m'.frame.jumpDests (SolmateAsset.runtimeCodeWith ia) ∧ m'.frame.pc = 2770 ∧
      m'.frame.stack = plStk d Lw S tl k ∧ m'.frame.gasLeft + k + 1 < n)
    ⟨k, rfl, hc, hj, hpc, hs, hgas⟩ ?_
  rintro j m' ⟨k, rfl, hc', hj', hpc', hs', hg'⟩
  refine (plCopy_any hH m' hc' hj' hpc' hs' hLw (by omega) hL2).mono_left ?_
  rintro m'' ⟨h1, h2, h3, h4, h5⟩
  exact .inl ⟨n - (k + 1), by omega, k + 1, rfl, h1, h2 ▸ hj', h3, h4, by omega⟩


set_option maxHeartbeats 0 in
/-- **`DOMAIN_SEPARATOR()` off the deployment chain with a name of more words than the frame
has gas**: the frame fails in the copy loop. -/
theorem pl_ds_huge {ia : SolmateAsset.Immutables} {H : Machine → Outcome → Prop} (hH : FailH H)
    {Q : Machine → Prop} (m : Machine) {r : Word} {rest : List Word}
    (hc : m.frame.code = SolmateAsset.runtimeCodeWith ia)
    (hj : JumpTable m.frame.jumpDests (SolmateAsset.runtimeCodeWith ia))
    (hpc : m.frame.pc = 1060) (hs : m.frame.stack = r :: rest) (hlen : rest.length ≤ 1000)
    (hfmp : m.frame.memory.loadWord 64 = 128#256) (hsize : m.frame.memory.size = 96)
    (hne : ofNat m.ctx.block.chainId ≠ ia.initialChainId)
    (hodd : m.world.sload m.frame.msg.currentTarget 0#256 &&& 1#256 = 1#256)
    (hg : 10000 ≤ m.frame.gasLeft)
    (hbig : m.frame.gasLeft + 1 <
      ((Word.shr 1#256 (m.world.sload m.frame.msg.currentTarget 0#256)).toNat + 31) / 32) :
    WP m Q H := by
  have hagree := assetJumpDestsAgree ia
  generalize hLdef : (Word.shr 1#256 (m.world.sload m.frame.msg.currentTarget 0#256)).toNat = L
    at hbig
  have hL2 : L < 2 ^ 255 := by
    rw [← hLdef, Str.shr_one]; simp only [BitVec.toNat_ofNat]
    have := (m.world.sload m.frame.msg.currentTarget 0#256).isLt; omega
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hpc hs hc
  have hne' : Word.eq (ofNat m_ctx.block.chainId) ia.initialChainId = 0#256 := eq_of_ne hne
  generalize hS : m_world.sload m_msg.currentTarget 0#256 = S at hodd hLdef ⊢
  have hlt : Word.lt (Word.shr 1#256 S) 32#256 = 0#256 :=
    (Word.lt_eq_zero_iff _ _).2 (by rw [hLdef]; show 32 ≤ L; omega)
  pwp_run_to 2770 [hne', readBytes_asset_chainId, hfmp, hsize, hS, hodd, hlt, permit_norm]
  have h0 : BitVec.ofNat 256 0 = (0 : Word) := rfl
  refine plCopy_fails (k := 0) (d := m_ctx.crypto.keccak256 (Bytes.ofWord 0#256))
    (Lw := Word.shr 1#256 S) (S := S)
    (tl := 1913#256 :: 63076024560530113402979550242307453568063438748328787417531900361828837441551#256
      :: 0#256 :: 1108#256 :: 0#256 :: r :: rest) hH _ rfl hj rfl ?_ hLdef rfl hL2 ?_
  · simp only [plStk, Nat.mul_zero, h0, add_zero]
  · dsimp only; omega

end Verified.Solmate.ERC20.Spec
