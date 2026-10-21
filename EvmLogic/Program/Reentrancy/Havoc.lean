import EvmLogic.Program.Reentrancy.Halts

/-!
# Untrusted calls in the frame-local logic: havoc, stipend, static, frozen

Rules for a protected frame that calls code it does not trust, each one symbolic step with no
exploration of the callee:

* `WP.havoc`, `WP.call_havoc` (**rely–guarantee at an untrusted call site**): if the world at the
  call satisfies the *call-site invariant* `Good` (a predicate on protected storage and code) and
  every dangerous frame keeps `Good` (`Covers`, the guarantee of the protected code, proved once
  per contract, possibly by induction on gas with `covers_of_lt`), then the caller continues from
  **every** return in which the world satisfies `Good`, with arbitrary success flag and return
  data. Callbacks into the protected contracts, at any depth, are covered by `Covers`.
* `WP.call_stipend` (**the stipend lemma**): a callee given at most 2300 gas, whatever its code,
  returns the world it started with (`halts_low`). No invariant, no summaries.
* `WP.staticcall_havoc`: a `STATICCALL`ed callee keeps any `Good` without summaries.
* `Frozen`, `goodOk_frozen`, `covers_frozen` (**guards**): with `Good := Frozen P w` (protected
  storage and code exactly as in `w`), `Covers` says that a callback never changes protected
  storage, e.g. because a reentrancy lock is held and every function that writes checks it; the
  untrusted call is then atomic.
* `processMessageCall_covers`: the any-transaction theorem from `Covers` for all gas.
-/

namespace EvmLogic.Program.Reentrancy
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested

variable {P : Address → Prop} {Good : World → Prop}

/-! ## The havoc rule -/

/-- **The havoc rule.** If `step m` pushes a child `mc` (caller `p`) that is either an arbitrary
non-dangerous frame satisfying `Inv` or a dangerous frame start, and `Covers` holds for its gas,
then `m` continues from every return to `p` whose world is `Good`. -/
theorem WP.havoc (S : GoodOk P Good) {G : Nat} (hcov : Covers P Good G) {m mc : Machine}
    {p : Frame} {Q : Machine → Prop} {H : Machine → Outcome → Prop}
    (hstep : step m = .running mc) (hpar : mc.parents = p :: m.parents)
    (hp : SameFrame m { mc with frame := p, parents := m.parents })
    (hg : mc.frame.gasLeft ≤ G) (hchild : Inv P Good mc ∨ DangerStart P Good G mc)
    (k : ∀ mf o, SameFrame mc mf → Good (frameResult mf o).2.1 →
      WP (resumeAfter p m.parents mf o) Q H) : WP m Q H :=
  WP.call hstep hpar hp (hchild.elim (halts_inv S hcov _ hg) (hcov _)) k

/-! ## `CALL` -/

section Call

variable {m : Machine} {gas toW value inOff inSize outOff outSize : Word} {rest : List Word}

/-- The child machine pushed by `CALL` with any value (`step_call`). -/
abbrev callChild (m : Machine) (gas toW value inOff inSize outOff outSize : Word)
    (rest : List Word) : Machine :=
  { m with
    world := transferValue m.world
      (childMsg m m.frame.msg.currentTarget (Word.toAddress toW) (Word.toAddress toW) value
        (callGas m gas value (Word.toAddress toW) (createCost m.world value (Word.toAddress toW))
          (transferCost value) inOff inSize outOff outSize).subCall true false
        inOff inSize outOff outSize)
    frame := Frame.init
      (childMsg m m.frame.msg.currentTarget (Word.toAddress toW) (Word.toAddress toW) value
        (callGas m gas value (Word.toAddress toW) (createCost m.world value (Word.toAddress toW))
          (transferCost value) inOff inSize outOff outSize).subCall true false
        inOff inSize outOff outSize)
      (.call outOff.toNat outSize.toNat) (m.world, m.transient)
    parents := callerFrame m rest (callCost m gas value (Word.toAddress toW)
      (createCost m.world value (Word.toAddress toW)) (transferCost value) inOff inSize outOff
      outSize) (Word.toAddress toW) inOff inSize outOff outSize :: m.parents }

/-- The suspended caller frame of a `CALL` with any value. -/
abbrev callCaller (m : Machine) (gas toW value inOff inSize outOff outSize : Word)
    (rest : List Word) : Frame :=
  callerFrame m rest (callCost m gas value (Word.toAddress toW)
    (createCost m.world value (Word.toAddress toW)) (transferCost value) inOff inSize outOff
    outSize) (Word.toAddress toW) inOff inSize outOff outSize

/-- `step_call` with the abbreviations. -/
theorem step_callChild (hcode : m.frame.code[m.frame.pc]? = some 0xf1)
    (hstk : m.frame.stack = gas :: toW :: value :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas value (Word.toAddress toW) (createCost m.world value (Word.toAddress toW))
      (transferCost value) inOff inSize outOff outSize ≤ m.frame.gasLeft)
    (hstatic : m.frame.msg.isStatic = false ∨ value = 0)
    (hbal : value.toNat ≤ (m.world.balance m.frame.msg.currentTarget).toNat)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = false) :
    step m = .running (callChild m gas toW value inOff inSize outOff outSize rest) :=
  step_call hcode hstk hdel hgas hstatic hbal hdepth hpre

/-- **Rely–guarantee at an untrusted `CALL`.** At a `CALL` to an unprotected account (any code,
any value) in a world satisfying the call-site invariant `Good`, with `Covers` for the child's
gas, the caller continues from every return whose world is `Good`. -/
theorem WP.call_havoc (S : GoodOk P Good) {G : Nat} (hcov : Covers P Good G)
    {Q : Machine → Prop} {H : Machine → Outcome → Prop}
    (hcode : m.frame.code[m.frame.pc]? = some 0xf1)
    (hstk : m.frame.stack = gas :: toW :: value :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas value (Word.toAddress toW) (createCost m.world value (Word.toAddress toW))
      (transferCost value) inOff inSize outOff outSize ≤ m.frame.gasLeft)
    (hstatic : m.frame.msg.isStatic = false ∨ value = 0)
    (hbal : value.toNat ≤ (m.world.balance m.frame.msg.currentTarget).toNat)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = false)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hto : ¬ P (Word.toAddress toW)) (hI : Good m.world)
    (hG : (callChild m gas toW value inOff inSize outOff outSize rest).frame.gasLeft ≤ G)
    (k : ∀ mf o, SameFrame (callChild m gas toW value inOff inSize outOff outSize rest) mf →
      Good (frameResult mf o).2.1 →
      WP (resumeAfter (callCaller m gas toW value inOff inSize outOff outSize rest) m.parents mf o)
        Q H) :
    WP m Q H :=
  WP.havoc S hcov (step_callChild hcode hstk hdel hgas hstatic hbal hdepth hpre) rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hG
    (.inl ⟨S.transferValue hI _, ⟨hI, fun hd => hto hd.1, fun hk => by cases hk⟩, hstd⟩) k

/-- **The stipend rule.** At a `CALL` (any target, any code) whose child gets at most
`Gas.callStipend` gas, the caller continues from every return in which the callee's final world
is the world it started with: a successful return sees exactly the world after the value transfer,
a failed one the world before the call. -/
theorem WP.call_stipend {Q : Machine → Prop} {H : Machine → Outcome → Prop}
    (hcode : m.frame.code[m.frame.pc]? = some 0xf1)
    (hstk : m.frame.stack = gas :: toW :: value :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas value (Word.toAddress toW) (createCost m.world value (Word.toAddress toW))
      (transferCost value) inOff inSize outOff outSize ≤ m.frame.gasLeft)
    (hstatic : m.frame.msg.isStatic = false ∨ value = 0)
    (hbal : value.toNat ≤ (m.world.balance m.frame.msg.currentTarget).toNat)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = false)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hlow : (callChild m gas toW value inOff inSize outOff outSize rest).frame.gasLeft ≤
      Gas.callStipend)
    (k : ∀ mf o, SameFrame (callChild m gas toW value inOff inSize outOff outSize rest) mf →
      mf.world = (callChild m gas toW value inOff inSize outOff outSize rest).world →
      WP (resumeAfter (callCaller m gas toW value inOff inSize outOff outSize rest) m.parents mf o)
        Q H) :
    WP m Q H :=
  WP.call (step_callChild hcode hstk hdel hgas hstatic hbal hdepth hpre) rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (halts_low _ hlow hstd) k

end Call

/-! ## `STATICCALL` -/

section Staticcall

variable {m : Machine} {gas toW inOff inSize outOff outSize : Word} {rest : List Word}

/-- The child machine pushed by `STATICCALL` (`step_staticcall`). -/
abbrev staticChild (m : Machine) (gas toW inOff inSize outOff outSize : Word) (rest : List Word) :
    Machine :=
  { m with
    frame := Frame.init
      (childMsg m m.frame.msg.currentTarget (Word.toAddress toW) (Word.toAddress toW) 0
        (callGas m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize).subCall true true
        inOff inSize outOff outSize)
      (.call outOff.toNat outSize.toNat) (m.world, m.transient)
    parents := callerFrame m rest (callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff
      outSize) (Word.toAddress toW) inOff inSize outOff outSize :: m.parents }

/-- The suspended caller frame of a `STATICCALL`. -/
abbrev staticCaller (m : Machine) (gas toW inOff inSize outOff outSize : Word) (rest : List Word) :
    Frame :=
  callerFrame m rest (callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize)
    (Word.toAddress toW) inOff inSize outOff outSize

/-- **An untrusted `STATICCALL` keeps any `Good`**, with no frame summaries: the callee and all
its descendants are static. -/
theorem WP.staticcall_havoc (S : GoodOk P Good) {Q : Machine → Prop}
    {H : Machine → Outcome → Prop}
    (hcode : m.frame.code[m.frame.pc]? = some 0xfa)
    (hstk : m.frame.stack = gas :: toW :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize ≤ m.frame.gasLeft)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = false)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx) (hI : Good m.world)
    (k : ∀ mf o, SameFrame (staticChild m gas toW inOff inSize outOff outSize rest) mf →
      Good (frameResult mf o).2.1 →
      WP (resumeAfter (staticCaller m gas toW inOff inSize outOff outSize rest) m.parents mf o)
        Q H) :
    WP m Q H := by
  refine WP.call (step_staticcall hcode hstk hdel hgas hdepth hpre) rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (halts_static S _ ?_ ?_) k
  · rfl
  · refine ⟨hI, ⟨hI, ?_, fun hk => by cases hk⟩, hstd⟩
    intro hd; simp [Danger, Frame.init, childMsg] at hd

end Staticcall

/-! ## Frozen protected storage (reentrancy guards) -/

/-- Protected storage and code exactly as in `w₀`. -/
def Frozen (P : Address → Prop) (w₀ w : World) : Prop := KeepP P w₀ w

/-- `Frozen` is a simulation predicate when the protected accounts hold code that is no EIP-7702
delegation. -/
theorem goodOk_frozen {w₀ : World} (hcode : ∀ p, P p → (w₀.code p).size ≠ 0)
    (hdel : ∀ p, P p → delegatedAddress? (w₀.code p) = none) : GoodOk P (Frozen P w₀) where
  keep _ _ h hk := h.trans hk
  code w h p hp := by rw [(h p hp).code]; exact hcode p hp
  deleg w h p hp := by rw [(h p hp).code]; exact hdel p hp

/-- **`Covers` for a frozen state**: it suffices that every dangerous frame started in a world
agreeing with `w₀` on protected storage either fails (its snapshot is restored) or succeeds
without changing protected storage, e.g. because a reentrancy lock recorded in `w₀` is held and
every function that writes checks it first. -/
theorem covers_frozen {w₀ : World} {G : Nat}
    (h : ∀ m, DangerStart P (Frozen P w₀) G m →
      Halts m (fun mf o => ∀ out, o = .success out → Frozen P w₀ mf.world)) :
    Covers P (Frozen P w₀) G := by
  intro m hd
  obtain ⟨ko, ks, hfr⟩ := hd.fresh
  refine (h m hd).mono fun mf o hsf hpost => ?_
  have hk : mf.frame.kind = .call ko ks := by rw [hsf.kind, hfr]; rfl
  cases o with
  | success out => rw [frameResult_success_call hk]; exact hpost out rfl
  | revert out => rw [frameResult_revert, hsf.snapshot]; exact hd.snapshot
  | halt e => rw [frameResult_halt, hsf.snapshot]; exact hd.snapshot

/-- **An untrusted `CALL` under a held guard is atomic.** If `Covers` holds for the frozen state of
the world at the call (callbacks change no protected storage), the caller continues from every
return in which protected storage and code are exactly as at the call. -/
theorem WP.call_frozen {m : Machine} {gas toW value inOff inSize outOff outSize : Word}
    {rest : List Word} {G : Nat} {Q : Machine → Prop} {H : Machine → Outcome → Prop}
    (hcodeP : ∀ p, P p → (m.world.code p).size ≠ 0)
    (hdelP : ∀ p, P p → delegatedAddress? (m.world.code p) = none)
    (hcov : Covers P (Frozen P m.world) G)
    (hcode : m.frame.code[m.frame.pc]? = some 0xf1)
    (hstk : m.frame.stack = gas :: toW :: value :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas value (Word.toAddress toW) (createCost m.world value (Word.toAddress toW))
      (transferCost value) inOff inSize outOff outSize ≤ m.frame.gasLeft)
    (hstatic : m.frame.msg.isStatic = false ∨ value = 0)
    (hbal : value.toNat ≤ (m.world.balance m.frame.msg.currentTarget).toNat)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = false)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hto : ¬ P (Word.toAddress toW))
    (hG : (callChild m gas toW value inOff inSize outOff outSize rest).frame.gasLeft ≤ G)
    (k : ∀ mf o, SameFrame (callChild m gas toW value inOff inSize outOff outSize rest) mf →
      KeepP P m.world (frameResult mf o).2.1 →
      WP (resumeAfter (callCaller m gas toW value inOff inSize outOff outSize rest) m.parents mf o)
        Q H) :
    WP m Q H :=
  WP.call_havoc (goodOk_frozen hcodeP hdelP) hcov hcode hstk hdel hgas hstatic hbal hdepth hpre
    hstd hto (keepP_refl _) hG k

/-! ## Any transaction -/

/-- **Any top-level message call keeps `Good`** when the protected code `Covers` it for its gas:
dangerous frames may now be reached with dangerous ancestors (callbacks), unlike in
`processMessageCall_good`'s summaries, which this instantiates. -/
theorem processMessageCall_covers (S : GoodOk P Good) {fuel : Nat} {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} {r : MessageResult} (hw : Good w)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hmsg : TopOk P w msg)
    (hcov : Covers P Good msg.gas)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) : Good r.world :=
  processMessageCall_good S hw hdeleg hmsg (Nat.le_refl _) (fun m _ hd _ => hcov m hd) hr

end EvmLogic.Program.Reentrancy
