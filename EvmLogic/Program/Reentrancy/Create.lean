import EvmLogic.Program.Reentrancy.Havoc
import EvmLogic.Program.Create

/-!
# Creations of arbitrary init code: the havoc rules for `CREATE` and `CREATE2`

`WP.create_havoc`/`WP.create2_havoc` are the counterparts of `WP.call_havoc` for a factory:
the init code is arbitrary (a factory's `CREATE2` of a pair contract, or attacker-supplied code),
so it is never explored. If the world at the instruction satisfies the call-site invariant `Good`
(a `GoodOk` predicate on protected storage and code) and the protected code `Covers` frames with
the child's gas (the init code may call back into protected contracts), the creator continues
from **every** return of the child whose world is `Good`, with the address or `0` pushed
(`resumeAfter_create_stack`).

The new account is never protected: a protected account holds code (`GoodOk.code`) and the new
address has none (`accountDeployable`), so the child frame is not dangerous and `halts_inv`
applies to it directly.
-/

namespace EvmLogic.Program.Reentrancy
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested

variable {P : Address → Prop} {Good : World → Prop}

/-- A free address (EIP-7610) is not protected. -/
theorem not_protected_of_deployable (S : GoodOk P Good) {w : World} {a : Address} (hw : Good w)
    (h : accountDeployable w a = true) : ¬ P a := by
  intro hp
  have hc := S.code w hw a hp
  simp only [accountDeployable, Bool.and_eq_true, decide_eq_true_eq] at h
  exact hc h.1.2

/-- The world of the creator after its nonce increment is `Good`. -/
theorem good_incrementNonce (S : GoodOk P Good) {w : World} (hw : Good w) (a : Address) :
    Good (incrementNonce w a) :=
  S.keep _ _ hw fun p hp => keep_incrementNonce (S.code w hw p hp)

/-- The world in which the init code starts is `Good`: two nonce increments and a value
transfer change no storage or code. -/
theorem good_createChild_world (S : GoodOk P Good) {m : Machine} (hw : Good m.world) (b : Bool)
    (value off size salt : Word) (rest : List Word) :
    Good (createChild m b value off size salt rest).world :=
  S.transferValue (good_incrementNonce S (good_incrementNonce S hw _) _) _

/-- The init-code frame satisfies the invariant of `halts_inv`. -/
theorem inv_createChild (S : GoodOk P Good) {m : Machine} {b : Bool}
    {value off size salt : Word} {rest : List Word} (hw : Good m.world)
    (hfree : accountDeployable m.world (newAddress m b off size salt) = true)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx) :
    Inv P Good (createChild m b value off size salt rest) := by
  have hnp := not_protected_of_deployable S hw hfree
  exact ⟨good_createChild_world S hw b value off size salt rest,
    ⟨good_incrementNonce S hw _, fun hd => hnp hd.1, fun _ => hnp⟩, hstd⟩

variable {m : Machine} {value off size salt : Word} {rest : List Word}

/-- **Rely–guarantee at a `CREATE` of arbitrary init code.** In a world satisfying the call-site
invariant `Good`, with `Covers` for the child's gas (`createGas`, all but 1/64 of what is left
after the charge), the creator continues from every return whose world is `Good`. The other
outcomes of the instruction are `step_create_soft`, `step_create_collision` and the halts
`step_create_oog`/`_initcode`/`_static`. -/
theorem WP.create_havoc (S : GoodOk P Good) {G : Nat} (hcov : Covers P Good G)
    {Q : Machine → Prop} {H : Machine → Outcome → Prop}
    (hcode : m.frame.code[m.frame.pc]? = some 0xf0)
    (hstk : m.frame.stack = value :: off :: size :: rest)
    (hgas : createCharge m false off size ≤ m.frame.gasLeft)
    (hsize : size.toNat ≤ Gas.maxInitCodeSize m.ctx.fork)
    (hstatic : m.frame.msg.isStatic = false)
    (hbal : value.toNat ≤ (m.world.balance m.frame.msg.currentTarget).toNat)
    (hnonce : (m.world.account m.frame.msg.currentTarget).nonce ≠ Gas.maxNonce)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hfree : accountDeployable m.world (newAddress m false off size 0) = true)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx) (hI : Good m.world)
    (hG : createGas m false off size ≤ G)
    (k : ∀ mf o, SameFrame (createChild m false value off size 0 rest) mf →
      Good (frameResult mf o).2.1 →
      WP (resumeAfter (creatorFrame m false off size 0 rest) m.parents mf o) Q H) :
    WP m Q H :=
  WP.havoc S hcov (step_create hcode hstk hgas hsize hstatic hbal hnonce hdepth hfree) rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hG (.inl (inv_createChild S hI hfree hstd)) k

/-- **Rely–guarantee at a `CREATE2` of arbitrary init code** (`WP.create_havoc` for `CREATE2`:
the address depends on the salt and the init-code hash). -/
theorem WP.create2_havoc (S : GoodOk P Good) {G : Nat} (hcov : Covers P Good G)
    {Q : Machine → Prop} {H : Machine → Outcome → Prop}
    (hcode : m.frame.code[m.frame.pc]? = some 0xf5)
    (hstk : m.frame.stack = value :: off :: size :: salt :: rest)
    (hgas : createCharge m true off size ≤ m.frame.gasLeft)
    (hsize : size.toNat ≤ Gas.maxInitCodeSize m.ctx.fork)
    (hstatic : m.frame.msg.isStatic = false)
    (hbal : value.toNat ≤ (m.world.balance m.frame.msg.currentTarget).toNat)
    (hnonce : (m.world.account m.frame.msg.currentTarget).nonce ≠ Gas.maxNonce)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hfree : accountDeployable m.world (newAddress m true off size salt) = true)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx) (hI : Good m.world)
    (hG : createGas m true off size ≤ G)
    (k : ∀ mf o, SameFrame (createChild m true value off size salt rest) mf →
      Good (frameResult mf o).2.1 →
      WP (resumeAfter (creatorFrame m true off size salt rest) m.parents mf o) Q H) :
    WP m Q H :=
  WP.havoc S hcov (step_create2 hcode hstk hgas hsize hstatic hbal hnonce hdepth hfree) rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hG (.inl (inv_createChild S hI hfree hstd)) k

end EvmLogic.Program.Reentrancy
