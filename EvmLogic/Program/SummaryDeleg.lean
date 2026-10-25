import EvmLogic.Program.Summary
import EvmLogic.Program.Delegation

/-!
# Top-level glue for any transaction, EIP-7702 authorizations included

`processMessageCall_eq_run` and `processMessageCall_of_halts` assume
`ctx.fork < .prague ∨ ctx.tx.authorizations = []`, under which `processMessageCall` runs the
message as given in the world as given. In general it first applies the authorizations
(`applyTopLevelDelegation`): the run starts in the delegated world with the delegated message,
and the authorizations' refund is added to the result. The `_7702` versions state that.
-/

namespace EvmLogic.Program
open EvmLean EvmLean.Interpreter

/-- The delegated world, message and authorization refund of a top-level message call. -/
abbrev delegated (ctx : Context) (w : World) (msg : Message) : World × Message × Int :=
  applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg

/-- Add the authorizations' refund to a message result. -/
def addRefund (refund : Int) (r : MessageResult) : MessageResult :=
  { r with refundCounter := r.refundCounter + refund }

/-- An account holding real code (not empty, no designator) keeps it through the
authorizations. -/
theorem delegated_code {ctx : Context} {w : World} {msg : Message} {a : Address}
    (hsize : (w.code a).size ≠ 0) (hdel : delegatedAddress? (w.code a) = none) :
    (delegated ctx w msg).1.code a = w.code a := by
  have he := (applyTopLevelDelegation_frame ctx (PrecompileImpl.standard ctx).isPrecompile w
    msg).1.account_eq hsize hdel
  show ((delegated ctx w msg).1.account a).code = (w.account a).code
  rw [he]

/-- **`processMessageCall` is `run` from the machine `initMachine` sets up in the delegated
world**, plus the authorizations' refund, for any transaction. -/
theorem processMessageCall_eq_run_7702 {ctx : Context} {w : World} {tr : TransientStorage}
    {msg : Message} {m : Machine}
    (hinit : initMachine (PrecompileImpl.standard ctx) ctx (delegated ctx w msg).1 tr
      (delegated ctx w msg).2.1 = .inr m) (fuel : Nat) :
    processMessageCall fuel ctx w tr msg =
      (run fuel m).map (addRefund (delegated ctx w msg).2.2) := by
  unfold processMessageCall processMessageCallWith
  unfold delegated at hinit ⊢
  generalize applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg = d
    at hinit ⊢
  obtain ⟨w', msg', refund⟩ := d
  dsimp only at hinit ⊢
  rw [hinit]
  rfl

/-- **Top-level glue, for any transaction.** A frame summary of the machine started in the
delegated world gives the result of `processMessageCall` for all large enough fuel: a call to a
non-precompile `a` running `a`'s code (`msg.code = w.code a`), which holds no designator after the
authorizations, at depth zero, with no value. -/
theorem processMessageCall_of_halts_7702 {ctx : Context} {w : World} {tr : TransientStorage}
    {msg : Message} {a : Address} {H : Machine → Outcome → Prop}
    (hcode : msg.code = w.code a)
    (hdel : delegatedAddress? ((delegated ctx w msg).1.code a) = none)
    (htarget : msg.target = some a) (hca : msg.codeAddress = some a)
    (hpre : Precompile.isPrecompile ctx.fork a = false)
    (hval : msg.value = 0) (hdepth : msg.depth = 0)
    (h : Halts (startMachine ctx (delegated ctx w msg).1 tr (delegated ctx w msg).2.1) H) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ mf o, H mf o ∧
      SameFrame (startMachine ctx (delegated ctx w msg).1 tr (delegated ctx w msg).2.1) mf ∧
      processMessageCall fuel ctx w tr msg = .ok (addRefund (delegated ctx w msg).2.2
        (topLevelResult msg.target (frameResult mf o).2.1 (frameResult mf o).2.2
          (frameResult mf o).1)) := by
  obtain ⟨-, -, -, htarget', hdepth', -, -, hval', -, -, hc⟩ :=
    applyTopLevelDelegation_frame ctx (PrecompileImpl.standard ctx).isPrecompile w msg
  have hca' := ((hc a hcode hca).1 hdel).2
  obtain ⟨n, mf, o, hH, hs, hrun⟩ := h.run rfl
  refine ⟨n, fun fuel hle => ⟨mf, o, hH, hs, ?_⟩⟩
  rw [processMessageCall_eq_run_7702 (initMachine_call (pre := PrecompileImpl.standard ctx)
    (htarget'.trans htarget) hca' hpre (hval'.trans hval) (hdepth'.trans hdepth)) fuel]
  change Except.map _ (run fuel (startMachine ctx (delegated ctx w msg).1 tr
    (delegated ctx w msg).2.1)) = _
  rw [hrun fuel hle]
  have ht : (startMachine ctx (delegated ctx w msg).1 tr (delegated ctx w msg).2.1).frame.msg.target
      = msg.target := htarget'
  rw [ht]
  rfl

end EvmLogic.Program
