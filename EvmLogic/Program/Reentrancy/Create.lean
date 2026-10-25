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


/-! ## Any outcome of the instruction -/

/-- `step_create`/`step_create2` for either opcode (`createByte b`, `createRest b salt rest`). -/
theorem step_createChild {b : Bool} (hcode : m.frame.code[m.frame.pc]? = some (createByte b))
    (hstk : m.frame.stack = value :: off :: size :: createRest b salt rest)
    (hgas : createCharge m b off size ≤ m.frame.gasLeft)
    (hsize : size.toNat ≤ Gas.maxInitCodeSize m.ctx.fork)
    (hstatic : m.frame.msg.isStatic = false)
    (hbal : value.toNat ≤ (m.world.balance m.frame.msg.currentTarget).toNat)
    (hnonce : (m.world.account m.frame.msg.currentTarget).nonce ≠ Gas.maxNonce)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hfree : accountDeployable m.world (newAddress m b off size salt) = true) :
    step m = .running (createChild m b value off size salt rest) := by
  cases b
  · have he : newAddress m false off size salt = newAddress m false off size 0 := by
      simp only [newAddress, Bool.false_eq_true, ite_false]
    have hc : createChild m false value off size salt rest =
        createChild m false value off size 0 rest := by
      simp only [createChild, creatorFrame, createMsg, he]
    rw [hc]
    simp only [createRest_false] at hstk
    rw [he] at hfree
    exact step_create hcode hstk hgas hsize hstatic hbal hnonce hdepth hfree
  · exact step_create2 hcode hstk hgas hsize hstatic hbal hnonce hdepth hfree

/-- **Rely–guarantee at a `CREATE`/`CREATE2` of arbitrary init code, whatever happens.** In a
world satisfying the call-site invariant `Good`, with `Covers` for the creator's gas, the
instruction either ends the frame exceptionally (out of gas, EIP-3860, static frame: `hfail`), or
the creator continues at the next instruction with one word (the new address or `0`) pushed on
`rest`, in a `Good` world: after a soft failure (balance, nonce, depth), an address collision
(only the creator's nonce changed), or any return of the init code. No gas, balance, nonce,
depth or freshness hypothesis. `hlen` (the stack had room for the pushed word) holds of every
reachable machine: the instruction popped at least three of at most 1024 words. -/
theorem WP.create_havoc_any (S : GoodOk P Good) {b : Bool} (hcov : Covers P Good m.frame.gasLeft)
    {Q : Machine → Prop} {H : Machine → Outcome → Prop}
    (hcode : m.frame.code[m.frame.pc]? = some (createByte b))
    (hstk : m.frame.stack = value :: off :: size :: createRest b salt rest)
    (hlen : rest.length < 1024)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx) (hI : Good m.world)
    (hfail : ∀ e, H m (.halt e))
    (k : ∀ m', SameFrame m m' → m'.frame.pc = m.frame.pc + 1 →
      (∃ x, m'.frame.stack = x :: rest) → Good m'.world → WP m' Q H) :
    WP m Q H := by
  by_cases hg : createCharge m b off size ≤ m.frame.gasLeft
  · by_cases hs : size.toNat ≤ Gas.maxInitCodeSize m.ctx.fork
    · cases hst : m.frame.msg.isStatic
      · by_cases hsoft : (m.world.balance m.frame.msg.currentTarget).toNat < value.toNat ∨
            (m.world.account m.frame.msg.currentTarget).nonce = Gas.maxNonce ∨
            Gas.stackDepthLimit < m.frame.msg.depth + 1
        · exact WP.of_step (step_create_soft hcode hstk hlen hg hs hst hsoft)
            (sameFrame_createSoftFail ..)
            (k _ (sameFrame_createSoftFail ..) rfl ⟨0, rfl⟩ hI)
        · have hbal : value.toNat ≤ (m.world.balance m.frame.msg.currentTarget).toNat :=
            Nat.le_of_not_lt fun h => hsoft (.inl h)
          have hnonce : (m.world.account m.frame.msg.currentTarget).nonce ≠ Gas.maxNonce :=
            fun h => hsoft (.inr (.inl h))
          have hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit :=
            Nat.le_of_not_lt fun h => hsoft (.inr (.inr h))
          cases hfree : accountDeployable m.world (newAddress m b off size salt)
          · exact WP.of_step
              (step_create_collision hcode hstk hlen hg hs hst hbal hnonce hdepth hfree)
              (sameFrame_createCollision ..)
              (k _ (sameFrame_createCollision ..) rfl ⟨0, rfl⟩ (good_incrementNonce S hI _))
          · have hG : createGas m b off size ≤ m.frame.gasLeft :=
              Nat.le_trans (createGas_le m b off size) (Nat.sub_le _ _)
            refine WP.havoc S (hcov.mono hG)
              (step_createChild hcode hstk hg hs hst hbal hnonce hdepth hfree) rfl
              ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (Nat.le_refl _)
              (.inl (inv_createChild S hI hfree hstd)) fun mf o hsf hgood => ?_
            have hk : mf.frame.kind = .create := hsf.kind
            have hsame : SameFrame m (resumeAfter (creatorFrame m b off size salt rest)
                m.parents mf o) :=
              by
                refine SameFrame.trans ?_ (sameFrame_resume _ _)
                exact ⟨hsf.ctx, hsf.precompiles, hsf.originalWorld, rfl, rfl, rfl, rfl, rfl, rfl⟩
            obtain ⟨hpc, hstk'⟩ := resumeAfter_create_stack (p := creatorFrame m b off size salt rest)
              (ps := m.parents) (o := o) hk
            refine k _ hsame hpc ?_ hgood
            rcases hstk' with h | h
            · exact ⟨_, h⟩
            · exact ⟨_, h⟩
      · exact WP.halt_of_step (step_create_static hcode hstk hg hs hst) (.refl m) (hfail _)
    · exact WP.halt_of_step (step_create_initcode hcode hstk hg (Nat.lt_of_not_le hs)) (.refl m)
        (hfail _)
  · exact WP.halt_of_step (step_create_oog hcode hstk (Nat.lt_of_not_le hg)) (.refl m) (hfail _)
end EvmLogic.Program.Reentrancy
