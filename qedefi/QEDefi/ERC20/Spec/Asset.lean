import QEDefi.ERC20.Spec.Invariant

/-!
# Laws on bytecode

Consequences of `ERC20Spec` and a law of the model, at the level of `processMessageCall`, for
top-level calls to the token (any transaction type), for a set of actors containing the sender
and the accounts the calldata names:

* `Asset.post`: the token's state after a top-level call with well-formed calldata is its state
  before, the model's state after an ERC-20 call by the sender naming actors, or the model's
  state after an entry point the sender can call;
* `Asset.debit_call`, `Asset.debit`: with `DebitAuth`, a call not sent by `o` lowers `o`'s
  balance only if it is a `transferFrom` from `o` (`debit` also needs `OpsDebitAuth`: the
  laws are about ERC-20 calls only, and an entry point such as an admin burn may lower any
  balance);
* `Asset.trace_wf`: with `WFInvariant`, the model invariant holds after any sequence of
  top-level calls to the token (`Trace`), the rest of the world changing arbitrarily between
  them.
-/

namespace QEDefi.ERC20.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Solidity
open QEDefi.ERC20.Spec.TopLevel QEDefi.ERC20.Spec.Invariant

variable {σ E : Type}

namespace Asset

/-- **The model states a call by `caller` can lead to from `s`**, naming only actors: `s`
itself, the state after an ERC-20 call, or after an entry point `caller` can call (value
zero). -/
def Post (M : TokenModel σ Address E) (ops : Address → ByteArray → ℕ → Option E)
    (opAddrs : E → List Address) (Act : Finset Address) (caller : Address) (s s' : σ) : Prop :=
  s' = s ∨
  (∃ (c : Call Address) (ret : RetData), (∀ x ∈ c.addrs, x ∈ Act) ∧ M.call s caller c = .ok s' ret) ∨
  (∃ d e, ops caller d 0 = some e ∧ (∀ x ∈ opAddrs e, x ∈ Act) ∧ M.op s e = some s')

/-- **An entry point not called by `o` never lowers `o`'s balance** (in states satisfying the
invariant). Not a consequence of `DebitAuth`, which is about ERC-20 calls only. -/
def OpsDebitAuth (M : TokenModel σ Address E) (ops : Address → ByteArray → ℕ → Option E)
    (o : Address) : Prop :=
  ∀ caller d v e s s', caller ≠ o → ops caller d v = some e → M.wf s → M.op s e = some s' →
    M.balanceOf s o ≤ M.balanceOf s' o

variable {code : ByteArray} {abs : TokenAbs σ} {M : TokenModel σ Address E} {g₀ : Nat}
  {sel : List Nat} {ops : Address → ByteArray → ℕ → Option E} {opAddrs : E → List Address}
  {perm : Option ((Machine → Nat) × (Machine → ℕ → Address))} {Act : Finset Address} {ctx : Context} {w : World}
  {tr : TransientStorage} {msg : Message} {a : Address}

theorem wellFormed_congr {m₁ m₂ : Message} (hd : m₂.data = m₁.data) (hc : m₂.caller = m₁.caller)
    (hv : m₂.value = m₁.value) (h : WellFormed sel ops opAddrs perm Act m₁) :
    WellFormed sel ops opAddrs perm Act m₂ := by
  unfold WellFormed; rw [hd, hc, hv]; exact h

/-- **The token's state after a top-level call** with well-formed calldata naming actors, sent
by an actor (for a token with `permit`, with `ecrecover` running the precompile): one the model allows from its state before (`Post`), and the token keeps its
code. -/
theorem post (hspec : ERC20Spec code abs M g₀ sel ops opAddrs)
    (hpermit : ∀ gp r, perm = some (gp, r) → PermitSpec code abs M gp r) (h : Msg code ctx w msg a)
    (hcaller : msg.caller ∈ Act) (hsound : abs.Sound ctx.crypto Act)
    (hwf : M.wf (abs.read ctx.crypto Act w a))
    (hwfd : WellFormed sel ops opAddrs perm Act msg)
    (hecr : perm.isSome → EcrecoverPlain (start ctx w tr msg)) :
    Ends ctx w tr msg fun r =>
      Post M ops opAddrs Act msg.caller (abs.read ctx.crypto Act w a)
        (abs.read ctx.crypto Act r.world a) ∧ r.world.code a = code := by
  obtain ⟨-, hct, hcl, -, -, hval, -, hdata⟩ := h.dmsg_facts
  have hs := h.start_ok tr hcaller hsound hwf (M := M)
  have hwfd' : WellFormed sel ops opAddrs perm Act (start ctx w tr msg).frame.msg :=
    wellFormed_congr hdata hcl (hval.trans h.value.symm) hwfd
  refine h.ends (explained_of_spec hspec hpermit hs hwfd' hecr) fun mf o hsf hx => ?_
  have hpre := h.pre_start abs Act tr
  have hcl' : (start ctx w tr msg).frame.msg.caller = msg.caller := hcl
  have hct' : (start ctx w tr msg).frame.msg.currentTarget = a := hct
  have hv0 : (start ctx w tr msg).frame.msg.value.toNat = 0 := by
    show (dmsg ctx w msg).value.toNat = 0; rw [hval]; rfl
  have hworld : (start ctx w tr msg).world = world ctx w msg := rfl
  -- a failed frame rolls back
  have hfail : Fails o → Post M ops opAddrs Act msg.caller (abs.read ctx.crypto Act w a)
      (abs.read ctx.crypto Act (Msg.result ctx w msg mf o).world a) ∧
      (Msg.result ctx w msg mf o).world.code a = code := fun hf => by
    rw [(Msg.result_fail hsf hf).1.2.1]
    exact ⟨.inl (h.read abs ctx.crypto Act), h.worldCode⟩
  -- a successful frame hands over its world
  have hsucc : ∀ out, o = .success out →
      (Msg.result ctx w msg mf o).world = mf.world := fun out ho => by
    subst ho; exact (Msg.result_success hsf).2.2.1
  rcases hx with hf | ⟨hw, -⟩ | ⟨c, hc, hm⟩ | ⟨d, e, he, hea, hm⟩
  · exact hfail hf
  · cases o with
    | success out =>
      rw [hsucc out rfl, hw, hworld]
      exact ⟨.inl (h.read abs ctx.crypto Act), h.worldCode⟩
    | revert out => exact hfail trivial
    | halt e => exact hfail trivial
  · rw [hpre, hcl'] at hm
    revert hm
    cases hres : M.call (abs.read ctx.crypto Act w a) msg.caller c with
    | ok s' ret =>
      rintro ⟨ho, hread, hkeep, -⟩
      rw [hsucc _ ho]
      rw [hct'] at hread hkeep
      exact ⟨.inr (.inl ⟨c, ret, hc, by rw [hres]; exact congrArg (fun x => Result.ok x ret) hread.symm⟩),
        hkeep.code.trans h.worldCode⟩
    | halt k =>
      cases k with
      | revert => rintro ⟨out, ho⟩; subst ho; exact hfail trivial
      | invalid => rintro ⟨e, ho⟩; subst ho; exact hfail trivial
  · rw [hcl', hv0] at he
    unfold OpMatches at hm
    rw [hpre] at hm
    revert hm
    cases hres : M.op (abs.read ctx.crypto Act w a) e with
    | some s' =>
      rintro ⟨⟨out, ho⟩, hread, hkeep, -⟩
      rw [hsucc _ ho]
      rw [hct'] at hread hkeep
      exact ⟨.inr (.inr ⟨d, e, he, hea, by rw [hres]; exact congrArg some hread.symm⟩),
        hkeep.code.trans h.worldCode⟩
    | none => exact hfail

/-! ## `DebitAuth` on bytecode -/

/-- **Only `transferFrom` from `o` lowers `o`'s balance**, for a top-level ERC-20 call: a call
encoding `c`, not sent by `o`, after which `o`'s balance (as the actors see it) is lower, is a
`transferFrom` from `o`. -/
theorem debit_call {c : Call Address} (hc : CallSpec code abs M g₀ c) (hD : M.DebitAuth)
    (h : Msg code ctx w msg a) (hcaller : msg.caller ∈ Act) (haddrs : ∀ x ∈ c.addrs, x ∈ Act)
    (hsound : abs.Sound ctx.crypto Act) (hwf : M.wf (abs.read ctx.crypto Act w a))
    (he : c.Encodes msg.data) {o : Address} (ho : o ≠ msg.caller) {fuel : Nat}
    {r : MessageResult} (hr : processMessageCall fuel ctx w tr msg = .ok r)
    (hlow : M.balanceOf (abs.read ctx.crypto Act r.world a) o <
      M.balanceOf (abs.read ctx.crypto Act w a) o) :
    ∃ dst v, c = .transferFrom o dst v := by
  rcases call_read hc h hcaller haddrs hsound hwf he hr with ⟨ret, -, hok⟩ | ⟨-, hst, -⟩
  · exact hD _ _ _ _ _ o hok ho hlow
  · rw [hst] at hlow; exact absurd hlow (lt_irrefl _)

/-- **Only `transferFrom` from `o` lowers `o`'s balance**, for any top-level call with
well-formed calldata naming actors: if a call not sent by `o` lowers `o`'s balance (as the
actors see it), the token's new state is the model's state after a `transferFrom` from `o` by
the sender. Needs `OpsDebitAuth`: entry points other than the ERC-20 calls are not covered by
`DebitAuth`. -/
theorem debit (hspec : ERC20Spec code abs M g₀ sel ops opAddrs)
    (hpermit : ∀ gp r, perm = some (gp, r) → PermitSpec code abs M gp r) (hD : M.DebitAuth)
    {o : Address} (hops : OpsDebitAuth M ops o) (h : Msg code ctx w msg a)
    (hcaller : msg.caller ∈ Act) (hsound : abs.Sound ctx.crypto Act)
    (hwf : M.wf (abs.read ctx.crypto Act w a)) (hwfd : WellFormed sel ops opAddrs perm Act msg)
    (hecr : perm.isSome → EcrecoverPlain (start ctx w tr msg)) (ho : o ≠ msg.caller) {fuel : Nat} {r : MessageResult}
    (hr : processMessageCall fuel ctx w tr msg = .ok r)
    (hlow : M.balanceOf (abs.read ctx.crypto Act r.world a) o <
      M.balanceOf (abs.read ctx.crypto Act w a) o) :
    ∃ dst v ret, M.call (abs.read ctx.crypto Act w a) msg.caller (.transferFrom o dst v) =
      .ok (abs.read ctx.crypto Act r.world a) ret := by
  rcases ((post (tr := tr) hspec hpermit h hcaller hsound hwf hwfd hecr).2 fuel r hr).1 with
    he | ⟨c, ret, -, hok⟩ | ⟨d, e, hde, -, hop⟩
  · rw [he] at hlow; exact absurd hlow (lt_irrefl _)
  · obtain ⟨dst, v, rfl⟩ := hD _ _ _ _ _ o hok ho hlow
    exact ⟨dst, v, ret, hok⟩
  · exact absurd (hops _ _ _ _ _ _ (Ne.symm ho) hde hwf hop) (not_le.2 hlow)

/-! ## `WFInvariant` on bytecode -/

/-- **A sequence of top-level calls to the token**, from `w₀`, for the actors `Act`: each a
call to the token at `a` (`Msg`) with `crypto`, sent by an actor with well-formed calldata
naming actors (for a token with `permit`, with `ecrecover` running the precompile,
`EcrecoverPlain`); between them, anything that leaves the token's account as it is (the other
accounts arbitrary). -/
inductive Trace (code : ByteArray) (sel : List Nat) (ops : Address → ByteArray → ℕ → Option E)
    (opAddrs : E → List Address) (perm : Option ((Machine → Nat) × (Machine → ℕ → Address))) (crypto : Crypto)
    (Act : Finset Address) (a : Address) : World → World → Prop where
  | refl (w : World) : Trace code sel ops opAddrs perm crypto Act a w w
  | env {w₀ w w' : World} : Trace code sel ops opAddrs perm crypto Act a w₀ w →
      w'.account a = w.account a → Trace code sel ops opAddrs perm crypto Act a w₀ w'
  | call {w₀ w : World} {fuel : Nat} {ctx : Context} {tr : TransientStorage} {msg : Message}
      {r : MessageResult} : Trace code sel ops opAddrs perm crypto Act a w₀ w →
      Msg code ctx w msg a → ctx.crypto = crypto → msg.caller ∈ Act →
      WellFormed sel ops opAddrs perm Act msg → (perm.isSome → EcrecoverPlain (start ctx w tr msg)) →
      processMessageCall fuel ctx w tr msg = .ok r →
      Trace code sel ops opAddrs perm crypto Act a w₀ r.world

/-- **The model invariant holds after any sequence of top-level calls to the token**, the rest
of the world changing arbitrarily between them, when it held before. -/
theorem trace_wf (hspec : ERC20Spec code abs M g₀ sel ops opAddrs)
    (hpermit : ∀ gp r, perm = some (gp, r) → PermitSpec code abs M gp r) (hW : M.WFInvariant)
    {crypto : Crypto} (hsound : abs.Sound crypto Act) {w₀ w : World} (hcode : w₀.code a = code)
    (hwf : M.wf (abs.read crypto Act w₀ a))
    (h : Trace code sel ops opAddrs perm crypto Act a w₀ w) :
    w.code a = code ∧ M.wf (abs.read crypto Act w a) := by
  induction h with
  | refl => exact ⟨hcode, hwf⟩
  | @env w1 w2 _ hacc ih =>
    refine ⟨?_, ?_⟩
    · show (w2.account a).code = code
      rw [hacc]; exact ih.1
    · rw [abs.read_congr crypto Act w1 w2 a (fun k _ => by simp only [World.sload, hacc])
        (by simp only [World.balance, hacc])]
      exact ih.2
  | call _ hm hc hcaller hwfd hecr hr ih =>
    subst hc
    obtain ⟨hpost, hcode'⟩ := (post hspec hpermit hm hcaller hsound ih.2 hwfd hecr).2 _ _ hr
    refine ⟨hcode', ?_⟩
    rcases hpost with he | ⟨c, ret, -, hok⟩ | ⟨d, e, -, -, hop⟩
    · rw [he]; exact ih.2
    · exact hW.1 _ _ _ _ _ ih.2 hok
    · exact hW.2 _ _ _ ih.2 hop

end Asset

end QEDefi.ERC20.Spec
