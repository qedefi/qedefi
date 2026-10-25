import QEDefi.ERC20.Spec.TopLevel
import QEDefi.ERC20.VariantProps
import EvmLogic.Program.Reentrancy.Deleg
import EvmLogic.Tx.Guard

/-!
# The model invariant across transactions, nested calls included

For a token proved to be the model `M` on its bytecode, `M.wf (abs.read crypto w a)` (with the
token's code at `a`) holds after every successful transaction (`process_inv`, any type, EIP-7702
authorizations included) and every sequence of them (`txSteps_inv`), when it held before. The
token may be called at any depth during the transaction, by any contract, with any calldata and
value: every frame running the token's code is a `Start` frame whose end the spec explains
(`AllFrames`), and no other code can write the token's storage. This is the ether-aware
nested-call simulation of `EvmLogic.Program.Reentrancy` (`processMessageCall_good_v_7702`) with
the token's code as the only protected code; its frame summaries (`CoversV`) are derived once
here from the spec (`coversV`).

What this needs beyond `ERC20Spec` and `M.WFInvariant`:

* **`AllFrames`**: every frame of the token's code, whatever its calldata, is explained by a
  model action (fails, an ERC-20 call, nothing changed, another entry point). Nested calls carry
  arbitrary calldata, so the four exact obligations of `ERC20Spec` do not cover them;
  `MalformedSpec` (in `ERC20Spec.Complete`) does (`allFrames_of_malformed`). `AllFrames` also
  admits `permit` as an explanation, which `MalformedSpec` does not: a token with `permit`
  proves `AllFrames` from its `PermitSpec` and the rest (see the report on `MalformedSpec`).
* **`EtherFree`**: the invariant does not depend on the token's ether balance (others can send
  it ether without running its code: `SELFDESTRUCT`, the coinbase reward). Immediate when `abs`
  does not read the balance (`etherFree_of_read`).
* **`BigCalldata`**: frames of the token's code with at least `2⁶⁴` bytes of calldata (outside
  `Start`) keep the invariant. Such a frame needs a caller that paid for `2⁶⁴` bytes of memory
  (more than `2¹⁰⁰` gas), but the simulation does not track memory against gas, so this is a
  hypothesis.
* the hash hypotheses `abs.Sound crypto`, and the token's code is real code (not empty, no
  EIP-7702 designator), which the transaction-level statement needs anyway.

The crypto is fixed along a sequence of transactions (`TxSteps` admitting only transactions
with that crypto): `abs.read` depends on it, and `EvmLogic.Tx.Steps` lets every transaction use
a different one.

`variant_conserved`: for a `Sane` variant with a stored supply that does not rebase,
`total bal + total frozen = supply` after any sequence of transactions.
-/

namespace QEDefi.ERC20.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
  EvmLogic.Program.Reentrancy EvmLogic.Tx

variable {σ E : Type}

namespace Invariant

/-! ## The invariant and its hypotheses -/

/-- **The token's invariant in world `w`**: `a` holds the token's code and its model state
satisfies the model's invariant. -/
def Inv (code : ByteArray) (abs : TokenAbs σ) (M : TokenModel σ Address E) (crypto : Crypto)
    (a : Address) (w : World) : Prop :=
  w.code a = code ∧ M.wf (abs.read crypto w a)

/-- **The invariant does not depend on the token's ether balance**: a world with the same
footprint storage satisfies it too. -/
def EtherFree (abs : TokenAbs σ) (M : TokenModel σ Address E) : Prop :=
  ∀ crypto (w w' : World) t, (∀ k, abs.footprint crypto k → w'.sload t k = w.sload t k) →
    M.wf (abs.read crypto w t) → M.wf (abs.read crypto w' t)

/-- `EtherFree` when the abstraction does not read the token's ether balance. -/
theorem etherFree_of_read {abs : TokenAbs σ} {M : TokenModel σ Address E}
    (h : ∀ crypto (w w' : World) t, (∀ k, abs.footprint crypto k → w'.sload t k = w.sload t k) →
      abs.read crypto w' t = abs.read crypto w t) : EtherFree abs M :=
  fun crypto w w' t hk hw => by rw [h crypto w w' t hk]; exact hw

/-- **The end `(mf, o)` of the frame `m` is explained by a model action of its caller**: it
failed, or it is an ERC-20 call (any, `permit` included), or it changed nothing, or it is an
entry point the decoder accepts. `MalformedSpec` without its restriction to non-`permit`
calls. -/
def Explained (abs : TokenAbs σ) (M : TokenModel σ Address E)
    (ops : Address → ByteArray → ℕ → Option E) (m mf : Machine) (o : Outcome) : Prop :=
  Fails o ∨
  (∃ c, Matches abs m mf o (M.events (pre abs m) m.frame.msg.caller c)
    (M.call (pre abs m) m.frame.msg.caller c)) ∨
  (mf.world = m.world ∧ mf.transient = m.transient ∧ mf.frame.sub.logs = m.frame.sub.logs) ∨
  (∃ d e s', ops m.frame.msg.caller d m.frame.msg.value.toNat = some e ∧
    M.op (pre abs m) e = some s' ∧
    abs.read m.ctx.crypto mf.world m.frame.msg.currentTarget = s' ∧
    FrameKeeps abs m.ctx.crypto m.frame.msg.currentTarget m.world mf.world)

/-- **Every frame of the token's code is explained** by a model action. -/
def AllFrames (code : ByteArray) (abs : TokenAbs σ) (M : TokenModel σ Address E)
    (ops : Address → ByteArray → ℕ → Option E) : Prop :=
  ∀ m, Start code abs M m → Halts m (Explained abs M ops m)

/-- `MalformedSpec` (part of `ERC20Spec.Complete`) gives `AllFrames`. -/
theorem allFrames_of_malformed {code : ByteArray} {abs : TokenAbs σ} {M : TokenModel σ Address E}
    {ops : Address → ByteArray → ℕ → Option E} (h : MalformedSpec code abs M ops) :
    AllFrames code abs M ops := fun m hs =>
  (h m hs).mono fun _ _ _ hx => by
    rcases hx with hx | ⟨c, -, hc⟩ | hx | hx
    · exact .inl hx
    · exact .inr (.inl ⟨c, hc⟩)
    · exact .inr (.inr (.inl hx))
    · exact .inr (.inr (.inr hx))

/-- The protected account of the simulation: the token. -/
abbrev Prot (a : Address) : Address → Prop := fun p => p = a

/-- The context of the transactions: the crypto `abs` is read with. -/
abbrev Ctx (crypto : Crypto) : Context → Prop := fun ctx => ctx.crypto = crypto

/-- **Frames with huge calldata keep the invariant**: a dangerous frame of the simulation
started at the token with at least `2⁶⁴` bytes of calldata (out of `Start`'s reach) ends with the
invariant. See the module docstring. -/
def BigCalldata (code : ByteArray) (abs : TokenAbs σ) (M : TokenModel σ Address E)
    (crypto : Crypto) (a : Address) : Prop :=
  ∀ G m, DStartV (Prot a) (Inv code abs M crypto a) (Ctx crypto) G m →
    2 ^ 64 ≤ m.frame.msg.data.size →
    Halts m (fun mf o => Inv code abs M crypto a (frameResult mf o).2.1)

/-! ## Closure of the invariant -/

variable {code : ByteArray} {abs : TokenAbs σ} {M : TokenModel σ Address E} {crypto : Crypto}
  {a : Address}

/-- The invariant depends only on the token's storage and code. -/
theorem Inv.keep (hE : EtherFree abs M) {w w' : World} (hw : Inv code abs M crypto a w)
    (h : Keep a w w') : Inv code abs M crypto a w' :=
  ⟨h.code.trans hw.1, hE crypto w w' a (fun k _ => h.sload k) hw.2⟩

/-- **The invariant is closed under everything other code can do** (`GoodOps`), for real code. -/
theorem goodOps (hE : EtherFree abs M) (hreal : code.size ≠ 0)
    (hdel : delegatedAddress? code = none) :
    GoodOps (Prot a) (Inv code abs M crypto a) where
  code w hw p hp := by subst hp; rw [hw.1]; exact hreal
  deleg w hw p hp := by subst hp; rw [hw.1]; exact hdel
  sstore w b k v hw hb := hw.keep hE (keep_sstore fun e => hb e.symm)
  nonce w b hw := hw.keep hE (keep_incrementNonce (by rw [hw.1]; exact hreal))
  move w src dst v hw _ _ := hw.keep hE (keep_moveEther (by rw [hw.1]; exact hreal))
  burn w b hw _ := hw.keep hE (keep_setAccountBalance (by rw [hw.1]; exact hreal))
  setCode w b c hw hb := hw.keep hE (keep_setCode fun e => hb e.symm)

/-! ## Frames of the token -/

/-- **A frame of the token's code keeps the invariant**: from `Start`, the world it hands back
(the frame's world on success, its snapshot on failure) satisfies `Inv`. -/
theorem frame_inv {ops : Address → ByteArray → ℕ → Option E} (hX : AllFrames code abs M ops)
    (hW : M.WFInvariant) (hE : EtherFree abs M) (hreal : code.size ≠ 0) {m : Machine}
    (hs : Start code abs M m) (hk : ∃ o s, m.frame.kind = .call o s)
    (hsnap : m.frame.snapshot.1.code m.frame.msg.currentTarget = code) :
    Halts m (fun mf o =>
      Inv code abs M m.ctx.crypto m.frame.msg.currentTarget (frameResult mf o).2.1) := by
  obtain ⟨ko, ks, hk⟩ := hk
  set t := m.frame.msg.currentTarget
  have hsnapInv : Inv code abs M m.ctx.crypto t m.frame.snapshot.1 := ⟨hsnap, hs.wf⟩
  have hkeep0 : Keep t m.frame.snapshot.1 m.world := by
    rw [hs.launched]; exact keep_transferValue (by rw [hsnap]; exact hreal)
  have hmInv : Inv code abs M m.ctx.crypto t m.world := hsnapInv.keep hE hkeep0
  refine (hX m hs).mono fun mf o hsf hx => ?_
  have hkf : mf.frame.kind = .call ko ks := hsf.kind.trans hk
  have hsn : mf.frame.snapshot = m.frame.snapshot := hsf.snapshot
  match o with
  | .revert out => rw [frameResult_revert, hsn]; exact hsnapInv
  | .halt e => rw [frameResult_halt, hsn]; exact hsnapInv
  | .success out =>
    rw [frameResult_success_call hkf]
    show Inv code abs M m.ctx.crypto t mf.world
    rcases hx with hx | ⟨c, hc⟩ | ⟨hw, -⟩ | ⟨d, e, s', -, hop, hread, hfk⟩
    · exact hx.elim
    · revert hc
      cases hres : M.call (pre abs m) m.frame.msg.caller c with
      | ok s' ret =>
        rintro ⟨-, hread, hfk, -⟩
        exact ⟨hfk.code.trans hmInv.1, hread ▸ hW.1 _ _ _ _ _ hs.wf hres⟩
      | halt h =>
        cases h with
        | revert => rintro ⟨_, ho⟩; cases ho
        | invalid => rintro ⟨_, ho⟩; cases ho
    · rw [hw]; exact hmInv
    · exact ⟨hfk.code.trans hmInv.1, hread ▸ hW.2 _ _ _ hs.wf hop⟩

/-- **The frame summaries of the simulation, from the spec**: every dangerous frame at the
token (a frame running the token's code, started by a value-moving call from a world satisfying
`Inv`) ends in a world satisfying `Inv`. -/
theorem coversV {ops : Address → ByteArray → ℕ → Option E} (hX : AllFrames code abs M ops)
    (hW : M.WFInvariant) (hE : EtherFree abs M) (hB : BigCalldata code abs M crypto a)
    (hsound : abs.Sound crypto) (hreal : code.size ≠ 0) (G : Nat) :
    CoversV (Prot a) (Inv code abs M crypto a) (Ctx crypto) G := by
  intro m hd
  by_cases hbig : 2 ^ 64 ≤ m.frame.msg.data.size
  · exact hB G m hd hbig
  have ht : m.frame.msg.currentTarget = a := hd.danger.1
  have hsnap : m.frame.snapshot.1.code a = code := hd.snapshot.1
  have hwcode : m.world.code a = code := ((hd.keep a rfl).code).trans hsnap
  obtain ⟨ko, ks, hfr⟩ := hd.fresh
  have hfresh : Fresh code m := by
    have := fresh_init m m.frame.msg _ _ hfr
    rw [hd.code, ht, hwcode] at this
    exact this
  have hstart : Start code abs M m :=
    { fresh := hfresh
      launched := hd.world_eq
      value := .inl hd.transfers
      size := by omega
      sound := by rw [hd.context]; exact hsound
      wf := by
        show M.wf (abs.read m.ctx.crypto m.frame.snapshot.1 m.frame.msg.currentTarget)
        rw [hd.context, ht]; exact hd.snapshot.2 }
  have h := frame_inv hX hW hE hreal hstart ⟨ko, ks, by rw [hfr]; rfl⟩ (by rw [ht]; exact hsnap)
  rw [hd.context, ht] at h
  exact h

/-! ## Message calls and transactions -/

/-- **A top-level message call keeps the invariant**, whatever it calls (the token or anything
calling it, at any depth), with any calldata, for any transaction type: a message from an
unprotected caller (`TopOk`) that moves its value, in the context of `crypto`. -/
theorem processMessageCall_inv {ops : Address → ByteArray → ℕ → Option E}
    (hX : AllFrames code abs M ops) (hW : M.WFInvariant) (hE : EtherFree abs M)
    (hB : BigCalldata code abs M crypto a) (hsound : abs.Sound crypto) (hreal : code.size ≠ 0)
    (hdel : delegatedAddress? code = none) {fuel : Nat} {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} {r : MessageResult}
    (hw : Inv code abs M crypto a w) (hmsg : TopOk (Prot a) w msg)
    (hv : msg.shouldTransferValue = true) (hC : ctx.crypto = crypto)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) : Inv code abs M crypto a r.world :=
  processMessageCall_good_v_7702 (C := Ctx crypto) (goodOps hE hreal hdel) hw hmsg hv hC
    (coversV hX hW hE hB hsound hreal msg.gas) hr

/-- **A successful transaction keeps the invariant**: any type, recipient, calldata, value and
authorizations, any fork and block, with the crypto `abs` is read with. -/
theorem process_inv {ops : Address → ByteArray → ℕ → Option E} (hX : AllFrames code abs M ops)
    (hW : M.WFInvariant) (hE : EtherFree abs M) (hB : BigCalldata code abs M crypto a)
    (hsound : abs.Sound crypto) (hreal : code.size ≠ 0) (hdel : delegatedAddress? code = none)
    {fuel : Nat} {fork : Fork} {env : BlockEnv} {gasAvail blobAvail : Nat} {w : World}
    {tx : Transaction} {hint : Option Address} {out : EvmLean.Tx.TxOutput}
    (hw : Inv code abs M crypto a w)
    (h : EvmLean.Tx.process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    Inv code abs M crypto a out.world := by
  refine process_keeps (P := Prot a) (fun w hw p hp => ?_) (fun ctx w₁ msg r hw₁ htop hr => ?_)
    (fun w w' hw hk => hw.keep hE (hk a rfl)) hw h
  · subst hp; rw [hw.1]; exact realCode_of_deleg hreal hdel
  · exact processMessageCall_inv hX hW hE hB hsound hreal hdel hw₁ htop.top htop.transfers
      htop.ctxCrypto hr

/-- The transactions of a chain using `crypto`. -/
def WithCrypto (crypto : Crypto) (i : Input) (_ : World) (_ : EvmLean.Tx.TxOutput) : Prop :=
  i.crypto = crypto

/-- **The invariant holds after any sequence of successful transactions** using `crypto`. -/
theorem txSteps_inv {ops : Address → ByteArray → ℕ → Option E} (hX : AllFrames code abs M ops)
    (hW : M.WFInvariant) (hE : EtherFree abs M) (hB : BigCalldata code abs M crypto a)
    (hsound : abs.Sound crypto) (hreal : code.size ≠ 0) (hdel : delegatedAddress? code = none)
    {w w' : World} (hw : Inv code abs M crypto a w) (h : TxSteps (WithCrypto crypto) w w') :
    Inv code abs M crypto a w' :=
  h.keeps (fun i v out hv hr hc => by
    unfold WithCrypto at hc; subst hc
    exact process_inv hX hW hE hB hsound hreal hdel hv hr) hw

/-! ## Variants: the supply is the sum of the balances -/

/-- **Every `Sane` variant's invariant is an invariant of its model.** -/
theorem variant_wfInvariant {A : Type} [DecidableEq A] [Zero A] {V : Variant A}
    (hV : V.Sane) (ev : VState A → A → Call A → List (Event A)) :
    (V.model ev).WFInvariant := by
  refine ⟨fun s caller c s' r hw h => ?_, fun s e s' hw h => V.WF_stepOp hV hw h⟩
  simp only [Variant.model_call, Variant.call] at h
  revert h
  cases hs : V.step s caller c with
  | some s1 => intro h; cases h; exact V.WF_step hV hw hs
  | none =>
    unfold Variant.failWith
    cases V.failKind s caller c with
    | revert => intro h; cases h
    | invalid => intro h; cases h
    | returnFalse => intro h; cases h; exact hw

/-- **The supply is the sum of the balances and frozen balances, after any sequence of
transactions**, for a token proved to be a `Sane` variant with a stored supply that does not
rebase (OpenZeppelin, Solady, … as variants), under the hypotheses of `txSteps_inv`. -/
theorem variant_conserved {V : Variant Address} (hV : V.Sane) (hr : V.rebasing = false)
    (hsup : V.supply = .stored) {ev : VState Address → Address → Call Address → List (Event Address)}
    {abs : TokenAbs (VState Address)} {ops : Address → ByteArray → ℕ → Option (Variant.Op Address)}
    (hX : AllFrames code abs (V.model ev) ops) (hE : EtherFree abs (V.model ev))
    (hB : BigCalldata code abs (V.model ev) crypto a) (hsound : abs.Sound crypto)
    (hreal : code.size ≠ 0) (hdel : delegatedAddress? code = none) {w w' : World}
    (hw : Inv code abs (V.model ev) crypto a w) (h : TxSteps (WithCrypto crypto) w w') :
    total (abs.read crypto w' a).bal + total (abs.read crypto w' a).frozen =
      (abs.read crypto w' a).supply := by
  have hi := txSteps_inv hX (variant_wfInvariant hV ev) hE hB hsound hreal hdel hw h
  have := hi.2
  simp only [Variant.model_wf, Variant.WF, hr, hsup, Bool.false_eq_true, ↓reduceIte,
    reduceCtorEq] at this
  exact this.1

end Invariant

end QEDefi.ERC20.Spec
