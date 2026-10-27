import EvmLogic.Program.Nested.Run
import EvmLogic.Program.Delegation

/-!
# The nested-call simulation for any transaction, EIP-7702 authorizations included

`processMessageCall_good` assumes `ctx.fork < .prague ∨ ctx.tx.authorizations = []`. That
hypothesis is not needed: an authorization only rewrites the code and nonce of an account that
holds empty code or a delegation designator (`EvmLogic.Program.Delegation`), and a protected
account of a `GoodOk` world holds real code. So the delegated world is `Good`
(`GoodOk.deleg_world`), and a `TopOk` message stays `TopOk` in it (`TopOk.delegate`): a call to a protected account
still runs that account's own code, which no authorization can replace.

`processMessageCall_good_7702` is `processMessageCall_good` without the hypothesis.
-/

namespace EvmLogic.Program.Nested
open EvmLean EvmLean.Interpreter EvmLogic.Program

variable {P : Address → Prop} {Good : World → Prop}

/-- The frame of the authorizations keeps every protected account that holds real code. -/
theorem _root_.EvmLogic.Program.DelegFrame.keepP {w w' : World} (h : DelegFrame w w')
    (hcode : ∀ p, P p → (w.code p).size ≠ 0)
    (hdel : ∀ p, P p → delegatedAddress? (w.code p) = none) : KeepP P w w' :=
  fun p hp => h.keep (hcode p hp) (hdel p hp)

/-- A `GoodOk` invariant survives the frame of the authorizations. -/
theorem GoodOk.delegFrame (S : GoodOk P Good) {w w' : World} (hw : Good w) (h : DelegFrame w w') :
    Good w' :=
  S.keep _ _ hw (h.keepP (S.code w hw) (S.deleg w hw))

/-- **A `GoodOk` invariant holds of the delegated world.** -/
theorem GoodOk.deleg_world (S : GoodOk P Good) (ctx : Context) (isPre : Address → Bool)
    {w : World} (msg : Message) (hw : Good w) :
    Good (applyTopLevelDelegation ctx isPre w msg).1 :=
  S.delegFrame hw (applyTopLevelDelegation_frame ctx isPre w msg).1

/-- **A `TopOk` message stays `TopOk` after top-level delegation**, when the protected accounts
of the delegated world hold no designator (which a `Good` world guarantees). A call to a
protected account runs the delegated world's code of that account. -/
theorem TopOk.delegate {ctx : Context} {isPre : Address → Bool} {w : World} {msg : Message}
    (hmsg : TopOk P w msg)
    (hdel : ∀ p, P p →
      delegatedAddress? ((applyTopLevelDelegation ctx isPre w msg).1.code p) = none) :
    TopOk P (applyTopLevelDelegation ctx isPre w msg).1
      (applyTopLevelDelegation ctx isPre w msg).2.1 := by
  obtain ⟨-, hcur, hcaller, htarget, hdepth, -, -, -, -, -, hcode⟩ :=
    applyTopLevelDelegation_frame ctx isPre w msg
  refine ⟨hdepth.trans hmsg.depth, hcaller ▸ hmsg.caller, ?_, fun hp ht => ?_⟩
  · rw [htarget, hcur]; exact hmsg.target
  · rw [hcur] at hp ht ⊢
    rw [htarget] at ht
    obtain ⟨hc, hca⟩ := hmsg.code hp ht
    exact (hcode _ hc hca).1 (hdel _ hp)

/-- **The simulation, for a top-level message call of any transaction.** `processMessageCall_good`
without `ctx.fork < .prague ∨ ctx.tx.authorizations = []`: from a `Good` world, a `TopOk` message
with at most `G` gas, in any fork and with any EIP-7702 authorizations, ends in a `Good` world,
provided every dangerous frame reached with no dangerous parent ends in a `Good` world (`hsum`). -/
theorem processMessageCall_good_7702 (S : GoodOk P Good) {G fuel : Nat} {ctx : Context}
    {w : World} {tr : TransientStorage} {msg : Message} {r : MessageResult} (hw : Good w)
    (hmsg : TopOk P w msg) (hG : msg.gas ≤ G)
    (hsum : ∀ m, Reaches ctx w tr msg m → DangerStart P Good G m →
      (∀ f ∈ m.parents, ¬ Danger P f) → Halts m (fun mf o => Good (frameResult mf o).2.1))
    (hr : processMessageCall fuel ctx w tr msg = .ok r) : Good r.world := by
  have hw' := S.deleg_world ctx (PrecompileImpl.standard ctx).isPrecompile msg hw
  have hmsg' := hmsg.delegate (ctx := ctx) (isPre := (PrecompileImpl.standard ctx).isPrecompile)
    (fun p hp => S.deleg _ hw' p hp)
  have hgas := (applyTopLevelDelegation_frame ctx (PrecompileImpl.standard ctx).isPrecompile w
    msg).2.2.2.2.2.2.1
  have hst : ∀ m₀, initMachine (PrecompileImpl.standard ctx) ctx
      (applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg).1 tr
      (applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg).2.1 =
        .inr m₀ → StartsAt ctx w tr msg m₀ := fun _ h => h
  unfold processMessageCall processMessageCallWith at hr
  generalize applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg = d
    at hw' hmsg' hgas hst hr
  obtain ⟨w', msg', refund⟩ := d
  dsimp only at hw' hmsg' hgas hst hr
  rcases initMachine_out (ctx := ctx) (tr := tr) S hw' hmsg' (hgas ▸ hG) with
    ⟨r', hi, hg⟩ | ⟨m₀, hi, hm⟩ <;> rw [hi] at hr <;> dsimp only at hr
  · cases hr; exact hg
  · have hst := hst m₀ hi
    cases hrun : run fuel m₀ with
    | error e => rw [hrun] at hr; cases hr
    | ok r' =>
      rw [hrun] at hr
      cases hr
      show Good r'.world
      rcases hm with hm | ⟨hm, hp⟩
      · exact run_good S (fun n m hn hd hs => hsum m ⟨m₀, n, hst, hn⟩ hd hs) fuel 0 m₀ r' rfl hm
          hrun
      · exact run_good_top hp (hsum m₀ ⟨m₀, 0, hst, rfl⟩ hm (by rw [hp]; simp)) hrun

end EvmLogic.Program.Nested
