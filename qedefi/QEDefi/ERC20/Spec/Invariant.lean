import QEDefi.ERC20.Spec.TopLevel
import QEDefi.ERC20.VariantProps
import EvmLogic.Program.Reentrancy.Deleg
import EvmLogic.Tx.Guard
import QEDefi.Solvency.Tx

/-!
# The model invariant across transactions, nested calls included

For a token proved to be the model `M` on its bytecode, the token's invariant as a finite set of
actors `Act` sees it, `M.wf (abs.read crypto Act w a)` (with the token's code at `a`), holds
after every successful transaction (`process_inv`, any type, EIP-7702 authorizations included)
and every sequence of them (`txSteps_inv`), when it held before, provided the actors contain
every account the transactions involve at the token. The token may be called at any depth
during a transaction, by any contract: every frame running the token's code is a `Start` frame
the spec explains, and no other code can write the token's storage. This is the ether-aware
nested-call simulation of `EvmLogic.Program.Reentrancy`, with the token's code as the only
protected code, restricted to the frames a message call actually reaches (`halts_inv_reach`,
`processMessageCall_good_reach`: the actors' hypothesis is about the execution, so the frame
summaries are only needed for reached frames); its frame summaries are derived once here from
the spec (`frame_inv`).

What this needs beyond `ERC20Spec` and `M.WFInvariant`, as hypotheses:

* **`Touch`** (`FramesTouch`, `TxTouch`): every frame of the token's code that a transaction
  reaches has an actor as caller and well-formed calldata naming only actors (`WellFormed`: an
  ERC-20 call, a view, the fallback, an entry point of `ops`, or a `permit` for a token with
  one), and calldata shorter than `2⁶⁴` bytes; for a token with `permit`, the account `0x01`
  holds no EIP-7702 designator in the frame's world (`EcrecoverPlain`: nobody holds its key),
  and before Osaka the transaction's gas is below `2⁶⁴` (from Osaka the protocol caps it at
  `2²⁴`; a nested frame has at most the top-level message's gas). The spec is exact only for
  actors' calls (`Start.caller`, `Call.addrs`), and the invariant is about the actors' view: a
  transfer to an account outside the actors changes the actors' sum but not the supply. The
  size bound holds on any real chain (a caller pays for its calldata in memory: `2⁶⁴` bytes cost
  more than `2¹⁰⁰` gas) but the simulation does not track memory against gas.
* **`EtherFree`**: the invariant does not depend on the token's ether balance (others can send
  it ether without running its code: `SELFDESTRUCT`, the coinbase reward). Immediate when `abs`
  does not read the balance (`etherFree_of_read`).
* the hash hypotheses `abs.Sound crypto Act`, and the token's code is real code (not empty, no
  EIP-7702 designator).
* all ether below `2²⁵⁶` before the first transaction (`TokGood`; true on any real chain, and
  kept by every transaction: `QEDefi.Solvency.process_keeps_ether_7702`). `Start` needs it: a
  frame with value starts from a snapshot where the token's balance plus the value does not wrap.
  A token frame the simulation reaches is never a call with value from the token to itself
  (its caller is not the token: the token's own calls are inside the spec's summaries).

The crypto is fixed along a sequence of transactions: `abs.read` depends on it, and
`EvmLogic.Tx.Steps` lets every transaction use a different one.

`variant_conserved`: for a `Sane` variant with a stored supply that does not rebase,
`total bal + total frozen = supply` over the actors after any such sequence of transactions;
the hypothesis that it holds before says that the actors hold every token.
-/

namespace QEDefi.ERC20.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
  EvmLogic.Program.Reentrancy EvmLogic.Tx EvmLogic.Solidity
open QEDefi.Solvency (supply add_le_sum supply_sstore supply_incrementNonce supply_moveEther
  supply_setAccountBalance_zero supply_setCode supply_prefixWorld process_keeps_ether_7702
  processMessageCall_supply_le_7702)

variable {σ E : Type}

namespace Invariant

/-! ## The simulation, restricted to reached frames -/

section Reach

variable {P : Address → Prop} {Good : World → Prop} {C : Context → Prop}

/-- `halts_resume` that also says the resumed machine is reached from `m`. -/
theorem halts_resume_reach {m mc : Machine} {p : Frame} {Hc H : Machine → Outcome → Prop}
    (hstep : step m = .running mc) (hpar : mc.parents = p :: m.parents)
    (hp : SameFrame m { mc with frame := p, parents := m.parents })
    (hpre : PrecompilesOk mc.precompiles) (hcallee : Halts mc Hc)
    (k : ∀ mf o j, stepN j m = .running (resumeAfter p m.parents mf o) → SameFrame mc mf →
      Hc mf o → (resumeAfter p m.parents mf o).frame.gasLeft ≤ p.gasLeft + mc.frame.gasLeft →
      Halts (resumeAfter p m.parents mf o) H) : Halts m H := by
  obtain ⟨n, mf, o, hH, hs, hn⟩ := hcallee.resume hpar
  have hsame : SameFrame m (resumeAfter p m.parents mf o) := by
    refine SameFrame.trans ?_ (sameFrame_resume _ _)
    exact ⟨hs.ctx.trans hp.ctx, hs.precompiles.trans hp.precompiles,
      hs.originalWorld.trans hp.originalWorld, rfl, hp.msg, hp.code, hp.jumpDests, hp.kind,
      hp.snapshot⟩
  have hg := stepN_gas hpre n
  rw [hn] at hg
  simp only [resultGas, gasSum, resumeAfter, resume_gasLeft, resume_parents, hpar,
    List.map_cons, List.sum_cons] at hg
  have hrun : stepN (n + 1) m = .running (resumeAfter p m.parents mf o) := by
    rw [show n + 1 = 1 + n by omega, stepN_add_of_running (by rw [stepN_one, hstep]), hn]
  refine Halts.of_steps ⟨n + 1, hrun, hsame⟩ (k mf o (n + 1) hrun hs hH ?_)
  simp only [resumeAfter, resume_gasLeft]; omega

/-- **`halts_inv_v` for the frames reached from `m₀`**: the frame summaries (`hcov`) are only
needed for dangerous frames reached from `m₀`. -/
theorem halts_inv_reach (S : GoodOps P Good) {G : Nat} {m₀ : Machine}
    (hcov : ∀ j m, stepN j m₀ = .running m → DStartV P Good C G m →
      Halts m (fun mf o => Good (frameResult mf o).2.1)) :
    ∀ j m, stepN j m₀ = .running m → C m.ctx → m.frame.gasLeft ≤ G → Inv P Good m →
      Halts m (fun mf o => Good (frameResult mf o).2.1) := by
  suffices ∀ n j m, stepN j m₀ = .running m → m.frame.gasLeft = n → C m.ctx → n ≤ G →
      Inv P Good m → Halts m (fun mf o => Good (frameResult mf o).2.1) from
    fun j m hj hC hg h => this _ j m hj rfl hC hg h
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro j m hj hn hC hG h
    have ih' : ∀ j' m'', stepN j' m₀ = .running m'' → m''.frame.gasLeft < m.frame.gasLeft →
        m''.ctx = m.ctx → Inv P Good m'' →
        Halts m'' (fun mf o => Good (frameResult mf o).2.1) :=
      fun j' m'' hj' hlt hc hi => ih _ (hn ▸ hlt) j' m'' hj' rfl (hc ▸ hC) (by omega) hi
    have hnext : ∀ m', step m = .running m' → stepN (j + 1) m₀ = .running m' := fun m' hs => by
      rw [stepN_add_of_running hj 1, stepN_one, hs]
    rcases step_value m with ⟨m', o, he, hf, hws⟩ | ⟨m', he, hf, hs, hws⟩ |
      ⟨m', req, he, hf, hc, hs, hws, ht, hv⟩ | ⟨m', msg, he, hf, hc, hs, hst, ht⟩
    · exact Halts.of_step he hf.same
        (S.frameResult (h.frame.of_same hf.same.msg hf.same.snapshot hf.same.kind)
          (S.step h.world h.frame.safe hws) o)
    · refine Halts.of_steps (Steps.of_step he hf.same)
        (ih' (j + 1) m' (hnext m' he) hs hf.same.ctx ?_)
      exact ⟨S.step h.world h.frame.safe hws,
        h.frame.of_same hf.same.msg hf.same.snapshot hf.same.kind,
        by rw [hf.same.precompiles, hf.same.ctx]; exact h.pre⟩
    · have hw' := S.step h.world h.frame.safe hws
      have hfr' := h.frame.of_same hf.same.msg hf.same.snapshot hf.same.kind
      have hpre' : m'.precompiles = PrecompileImpl.standard m'.ctx := by
        rw [hf.same.precompiles, hf.same.ctx]; exact h.pre
      rcases launchCall_cases m' req with ⟨r, w, t, hl, hw, hr⟩ | hl <;> rw [hl] at he
      · have hr' := hr (by rw [hpre']; exact precompilesOk_standard _)
        have hsf : SameFrame m (resume { m' with world := w, transient := t } r) :=
          (hf.same.trans (show SameFrame m' { m' with world := w, transient := t } from
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)).trans (sameFrame_resume _ _)
        refine Halts.of_steps (Steps.of_step he hsf) (ih' (j + 1) _ (hnext _ he) ?_ hsf.ctx ?_)
        · simp only [resume_gasLeft]; omega
        · refine ⟨?_, hfr'.of_same rfl rfl rfl, hpre'⟩
          rcases hw with rfl | rfl
          · exact transfer_of_ok S h hw' ht
          · exact hw'
      · have hpar : (pushCall m' req).parents = m'.frame :: m.parents := by
          simp only [pushCall, hf.same.parents]
        have hcallee : Halts (pushCall m' req) (fun mf o => Good (frameResult mf o).2.1) := by
          rcases child_cases_v (G := G) S h hf hc hw' ht hv (by omega) hC with hd | hi
          · exact hcov (j + 1) _ (hnext _ he) hd
          · exact ih' (j + 1) _ (hnext _ he) (by rw [pushCall_gasLeft]; omega) hf.same.ctx hi
        refine halts_resume_reach he hpar ⟨hf.same.ctx, hf.same.precompiles,
          hf.same.originalWorld, rfl, hf.same.msg, hf.same.code, hf.same.jumpDests, hf.same.kind,
          hf.same.snapshot⟩
          (by simp only [pushCall]; rw [hpre']; exact precompilesOk_standard _) hcallee ?_
        intro mf o j' hj' hsf hgood hgas
        refine ih' (j + j') _ (by rw [stepN_add_of_running hj, hj'])
          ?_ (hsf.ctx.trans hf.same.ctx) (Inv.of_resume hfr' hgood ?_)
        · rw [pushCall_gasLeft] at hgas; omega
        · rw [hsf.precompiles, hsf.ctx]; exact hpre'
    · obtain ⟨hcaller, hbal, hw0⟩ := ht
      have hnp : ¬ P m.frame.msg.currentTarget := fun hp => h.frame.safe ⟨hp, hst⟩
      have hw' : Good m'.world := by rw [hw0]; exact S.nonce _ _ h.world
      have hfr' := h.frame.of_same hf.same.msg hf.same.snapshot hf.same.kind
      have hpre' : m'.precompiles = PrecompileImpl.standard m'.ctx := by
        rw [hf.same.precompiles, hf.same.ctx]; exact h.pre
      have hnpc : ¬ P msg.currentTarget := fun hp => S.code _ hw' _ hp hc.code
      have hpar : (launchCreate m' msg).parents = m'.frame :: m.parents := by
        simp only [launchCreate, hf.same.parents]
      have hcallee : Halts (launchCreate m' msg) (fun mf o => Good (frameResult mf o).2.1) := by
        refine ih' (j + 1) _ (hnext _ he) (by rw [launchCreate_gasLeft]; omega) hf.same.ctx
          ⟨?_, ⟨hw', ?_, ?_⟩, ?_⟩
        · simp only [launchCreate, beginCreate]
          refine S.transfer (S.nonce _ _ hw') fun _ _ => ⟨?_, .inl (hcaller ▸ hnp)⟩
          rw [balance_incrementNonce, hw0, balance_incrementNonce, hcaller]
          rw [hcaller] at hbal; exact hbal
        · exact fun hd => hnpc hd.1
        · exact fun _ => hnpc
        · simp only [launchCreate]; exact hpre'
      refine halts_resume_reach he hpar ⟨hf.same.ctx, hf.same.precompiles,
        hf.same.originalWorld, rfl, hf.same.msg, hf.same.code, hf.same.jumpDests, hf.same.kind,
        hf.same.snapshot⟩
        (by simp only [launchCreate]; rw [hpre']; exact precompilesOk_standard _) hcallee ?_
      intro mf o j' hj' hsf hgood hgas
      refine ih' (j + j') _ (by rw [stepN_add_of_running hj, hj'])
        ?_ (hsf.ctx.trans hf.same.ctx) (Inv.of_resume hfr' hgood ?_)
      · rw [launchCreate_gasLeft] at hgas; omega
      · rw [hsf.precompiles, hsf.ctx]; exact hpre'

/-- **`processMessageCall_good_v_7702` for the frames the message call reaches**: the frame
summaries are only needed for the dangerous frames it reaches (`Reaches`). -/
theorem processMessageCall_good_reach (S : GoodOps P Good) {fuel : Nat} {ctx : Context}
    {w : World} {tr : TransientStorage} {msg : Message} {r : MessageResult} (hw : Good w)
    (hmsg : TopOk P w msg) (hv : msg.shouldTransferValue = true) (hC : C ctx)
    (hcov : ∀ m, Reaches ctx w tr msg m → DStartV P Good C msg.gas m →
      Halts m (fun mf o => Good (frameResult mf o).2.1))
    (hr : processMessageCall fuel ctx w tr msg = .ok r) : Good r.world := by
  have hw' := S.deleg_world ctx (PrecompileImpl.standard ctx).isPrecompile msg hw
  have hmsg' := hmsg.delegate (ctx := ctx) (isPre := (PrecompileImpl.standard ctx).isPrecompile)
    (fun p hp => S.deleg _ hw' p hp)
  have hF := applyTopLevelDelegation_frame ctx (PrecompileImpl.standard ctx).isPrecompile w msg
  have hgas := hF.2.2.2.2.2.2.1
  have hv' := hF.2.2.2.2.2.2.2.2.1.trans hv
  have hst : ∀ m₀, initMachine (PrecompileImpl.standard ctx) ctx
      (applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg).1 tr
      (applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg).2.1 =
        .inr m₀ → StartsAt ctx w tr msg m₀ := fun _ h => h
  unfold processMessageCall processMessageCallWith at hr
  generalize applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg = d
    at hw' hmsg' hgas hv' hr hst
  obtain ⟨w', msg', refund⟩ := d
  dsimp only at hw' hmsg' hgas hv' hr hst
  rcases initMachine_out_e (ctx := ctx) (tr := tr) S hw' hmsg' with
    ⟨r', hi, hg⟩ | ⟨m₀, hi, hpar, hg0, hm⟩ <;> rw [hi] at hr <;> dsimp only at hr
  · cases hr; exact hg
  · have hst := hst m₀ hi
    have hH : Halts m₀ (fun mf o => Good (frameResult mf o).2.1) := by
      rcases hm with hm | hm
      · exact halts_inv_reach (C := C) (G := msg'.gas) S
          (fun j m hj hd => hcov m ⟨m₀, j, hst, hj⟩ (hgas ▸ hd)) 0 m₀ rfl
          (by rw [(initMachine_msg hi).2]; exact hC) (by rw [hg0]) hm
      · have hd0 : DStartV P Good C msg'.gas m₀ := ⟨hm, by rw [(initMachine_msg hi).1]; exact hv',
          by rw [(initMachine_msg hi).2]; exact hC⟩
        exact hcov m₀ ⟨m₀, 0, hst, rfl⟩ (hgas ▸ hd0)
    obtain ⟨n, mf, o, hgood, hsf, hrun⟩ := hH.run hpar
    cases hrun' : run fuel m₀ with
    | error e => rw [hrun'] at hr; cases hr
    | ok r' =>
      rw [hrun'] at hr
      cases hr
      have h1 := run_mono hrun' (Nat.le_max_left fuel n)
      rw [hrun (max fuel n) (Nat.le_max_right fuel n)] at h1
      cases h1
      show Good (topLevelResult _ _ _ _).world
      unfold topLevelResult; split <;> exact hgood

end Reach

/-! ## The invariant and its hypotheses -/

/-- **The token's invariant in world `w`**, for the actors `Act`: `a` holds the token's code and
its model state, as the actors see it, satisfies the model's invariant. -/
def TokInv (code : ByteArray) (abs : TokenAbs σ) (M : TokenModel σ Address E) (crypto : Crypto)
    (Act : Finset Address) (a : Address) (w : World) : Prop :=
  w.code a = code ∧ M.wf (abs.read crypto Act w a)

/-- **The invariant does not depend on the token's ether balance**: a world with the same
footprint storage satisfies it too. -/
def EtherFree (abs : TokenAbs σ) (M : TokenModel σ Address E) : Prop :=
  ∀ crypto Act (w w' : World) t,
    (∀ k, abs.footprint crypto Act k → w'.sload t k = w.sload t k) →
    M.wf (abs.read crypto Act w t) → M.wf (abs.read crypto Act w' t)

/-- `EtherFree` when the abstraction does not read the token's ether balance. -/
theorem etherFree_of_read {abs : TokenAbs σ} {M : TokenModel σ Address E}
    (h : ∀ crypto Act (w w' : World) t,
      (∀ k, abs.footprint crypto Act k → w'.sload t k = w.sload t k) →
      abs.read crypto Act w' t = abs.read crypto Act w t) : EtherFree abs M :=
  fun crypto Act w w' t hk hw => by rw [h crypto Act w w' t hk]; exact hw

/-- **Calldata the spec covers, naming only actors**: an ERC-20 call or a view whose accounts
are actors, an unknown selector or short calldata (the fallback), an entry point whose accounts
are actors, or (for a token with `permit`, `perm = some _`) a `permit` for two actors. -/
def WellFormed (sel : List Nat) (ops : Address → ByteArray → ℕ → Option E)
    (opAddrs : E → List Address) (perm : Option ((Machine → Nat) × (Machine → ℕ → Address))) (Act : Finset Address)
    (msg : Message) : Prop :=
  (∃ c : Call Address, c.Encodes msg.data ∧ ∀ x ∈ c.addrs, x ∈ Act) ∨
  (∃ v : View, v.Encodes msg.data ∧ ∀ x ∈ v.addrs, x ∈ Act) ∨
  (msg.data.size < 4 ∨ Abi.selectorOf msg.data ∉ sel) ∨
  (∃ e, ops msg.caller msg.data msg.value.toNat = some e ∧ ∀ x ∈ opAddrs e, x ∈ Act) ∨
  (perm.isSome ∧ ∃ (o sp : Address) (v dl pv pr ps : Word), o ∈ Act ∧ sp ∈ Act ∧
    Args msg.data 0xd505accf [Word.ofAddress o, Word.ofAddress sp, v, dl, pv, pr, ps])

/-- **The end `(mf, o)` of the frame `m` is explained by a model action of an actor naming only
actors**: it failed, or changed nothing, or it is an ERC-20 call, or an entry point. -/
def Explained (abs : TokenAbs σ) (M : TokenModel σ Address E)
    (ops : Address → ByteArray → ℕ → Option E) (opAddrs : E → List Address) (Act : Finset Address) (m mf : Machine) (o : Outcome) : Prop :=
  Fails o ∨
  (mf.world = m.world ∧ mf.transient = m.transient ∧ mf.frame.sub.logs = m.frame.sub.logs) ∨
  (∃ c : Call Address, (∀ x ∈ c.addrs, x ∈ Act) ∧
    Matches abs Act m mf o (M.events (pre abs Act m) m.frame.msg.caller c)
      (M.call (pre abs Act m) m.frame.msg.caller c)) ∨
  (∃ d e, ops m.frame.msg.caller d m.frame.msg.value.toNat = some e ∧
    (∀ x ∈ opAddrs e, x ∈ Act) ∧ OpMatches abs M Act e m mf o)

variable {code : ByteArray} {abs : TokenAbs σ} {M : TokenModel σ Address E} {crypto : Crypto}
  {Act : Finset Address} {a : Address} {g₀ : Nat} {sel : List Nat}
  {ops : Address → ByteArray → ℕ → Option E} {opAddrs : E → List Address}
  {perm : Option ((Machine → Nat) × (Machine → ℕ → Address))}

/-- **The spec explains every frame with well-formed calldata naming actors.** -/
theorem explained_of_spec (hspec : ERC20Spec code abs M g₀ sel ops opAddrs)
    (hpermit : ∀ gp r, perm = some (gp, r) → PermitSpec code abs M gp r) {m : Machine}
    (hs : Start code abs M Act m) (hwf : WellFormed sel ops opAddrs perm Act m.frame.msg)
    (hecr : perm.isSome → EcrecoverPlain m ∧ m.frame.gasLeft < 2 ^ 64) :
    Halts m (Explained abs M ops opAddrs Act m) := by
  rcases hwf with ⟨c, he, hc⟩ | ⟨v, he, hv⟩ | hd | ⟨e, he, hea⟩ | ⟨hrec, o, sp, v, dl, pv, pr, ps,
    ho, hsp, hargs⟩
  · exact (hspec.calls c Act m hs he hc).mono fun _ _ _ h => h.elim
      (fun hm => .inr (.inr (.inl ⟨c, hc, hm⟩))) (fun hf => .inl hf.1)
  · exact (hspec.views v Act m hs he hv).mono fun _ _ _ h => h.elim
      (fun ⟨_, _, _, hw, ht, _, hl⟩ => .inr (.inl ⟨hw, ht, hl⟩)) (fun hf => .inl hf.1)
  · exact (hspec.fallback Act m hs hd).mono fun _ _ _ h => h.elim
      (fun hm => .inr (.inr (.inl ⟨_, by simp [Call.addrs], hm⟩))) (fun hf => .inl hf.1)
  · exact (hspec.ops Act m e hs he hea).mono fun _ _ _ h => h.elim
      (fun hm => .inr (.inr (.inr ⟨_, e, he, hea, hm⟩))) (fun hf => .inl hf.1)
  · obtain ⟨⟨gp, r⟩, hr⟩ := Option.isSome_iff_exists.1 hrec
    exact (hpermit gp r hr Act m o sp v dl pv pr ps hs ho hsp (hecr hrec).1 (hecr hrec).2 hargs).mono fun _ _ _ h => h.elim
      (fun hm => .inr (.inr (.inl ⟨_, by simp [Call.addrs, ho, hsp], hm⟩)))
      (fun hf => .inl hf.1)

/-! ## Closure of the invariant -/

/-- The invariant depends only on the token's storage and code. -/
theorem TokInv.keep (hE : EtherFree abs M) {w w' : World} (hw : TokInv code abs M crypto Act a w)
    (h : Keep a w w') : TokInv code abs M crypto Act a w' :=
  ⟨h.code.trans hw.1, hE crypto Act w w' a (fun k _ => h.sload k) hw.2⟩

/-- The protected account of the simulation: the token. -/
abbrev Prot (a : Address) : Address → Prop := fun p => p = a

/-- The context of the transactions: the crypto `abs` is read with. -/
abbrev Ctx (crypto : Crypto) : Context → Prop := fun ctx => ctx.crypto = crypto

/-- **The invariant of the simulation**: the token's invariant, and all ether below `2²⁵⁶`
(which bounds the token's balance plus any value sent to it). -/
def TokGood (code : ByteArray) (abs : TokenAbs σ) (M : TokenModel σ Address E) (crypto : Crypto)
    (Act : Finset Address) (a : Address) (w : World) : Prop :=
  TokInv code abs M crypto Act a w ∧ supply w < 2 ^ 256

/-- **The invariant is closed under everything other code can do** (`GoodOps`), for real code. -/
theorem goodOps (hE : EtherFree abs M) (hreal : code.size ≠ 0)
    (hdel : delegatedAddress? code = none) :
    GoodOps (Prot a) (TokGood code abs M crypto Act a) where
  code w hw p hp := by subst hp; rw [hw.1.1]; exact hreal
  deleg w hw p hp := by subst hp; rw [hw.1.1]; exact hdel
  sstore w b k v hw hb :=
    ⟨hw.1.keep hE (keep_sstore fun e => hb e.symm), by rw [supply_sstore]; exact hw.2⟩
  nonce w b hw := ⟨hw.1.keep hE (keep_incrementNonce (by rw [hw.1.1]; exact hreal)),
    by rw [supply_incrementNonce]; exact hw.2⟩
  move w src dst v hw hv _ := ⟨hw.1.keep hE (keep_moveEther (by rw [hw.1.1]; exact hreal)),
    by rw [supply_moveEther hv hw.2]; exact hw.2⟩
  burn w b hw _ := ⟨hw.1.keep hE (keep_setAccountBalance (by rw [hw.1.1]; exact hreal)),
    lt_of_le_of_lt (supply_setAccountBalance_zero w b) hw.2⟩
  setCode w b c hw hb :=
    ⟨hw.1.keep hE (keep_setCode fun e => hb e.symm), by rw [supply_setCode]; exact hw.2⟩

/-! ## Frames of the token -/

/-- A successful frame of the token changes no balance (`FrameKeeps`), so it keeps all ether. -/
theorem supply_frameKeeps {crypto : Crypto} {t : Address} {w w' : World}
    (h : FrameKeeps abs crypto Act t w w') : supply w' = supply w := by
  unfold supply
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : b = t
  · subst hb; rw [h.balance]
  · simp only [World.balance, h.others b hb]

/-- **An explained frame of the token's code keeps the invariant**: from `Start`, with all ether
below `2²⁵⁶` in its snapshot and its world, the world it hands back (the frame's world on
success, its snapshot on failure) satisfies `TokGood`. -/
theorem frame_inv (hW : M.WFInvariant) (hE : EtherFree abs M) (hreal : code.size ≠ 0)
    {m : Machine} (hs : Start code abs M Act m) (hX : Halts m (Explained abs M ops opAddrs Act m))
    (hk : ∃ o s, m.frame.kind = .call o s)
    (hsnap : m.frame.snapshot.1.code m.frame.msg.currentTarget = code)
    (hsupS : supply m.frame.snapshot.1 < 2 ^ 256) (hsupW : supply m.world < 2 ^ 256) :
    Halts m (fun mf o =>
      TokGood code abs M m.ctx.crypto Act m.frame.msg.currentTarget (frameResult mf o).2.1) := by
  obtain ⟨ko, ks, hk⟩ := hk
  set t := m.frame.msg.currentTarget
  have hsnapInv : TokInv code abs M m.ctx.crypto Act t m.frame.snapshot.1 := ⟨hsnap, hs.wf⟩
  have hkeep0 : Keep t m.frame.snapshot.1 m.world := by
    rw [hs.launched]; exact keep_transferValue (by rw [hsnap]; exact hreal)
  have hmInv : TokInv code abs M m.ctx.crypto Act t m.world := hsnapInv.keep hE hkeep0
  refine hX.mono fun mf o hsf hx => ?_
  have hkf : mf.frame.kind = .call ko ks := hsf.kind.trans hk
  have hsn : mf.frame.snapshot = m.frame.snapshot := hsf.snapshot
  match o with
  | .revert out => rw [frameResult_revert, hsn]; exact ⟨hsnapInv, hsupS⟩
  | .halt e => rw [frameResult_halt, hsn]; exact ⟨hsnapInv, hsupS⟩
  | .success out =>
    rw [frameResult_success_call hkf]
    show TokGood code abs M m.ctx.crypto Act t mf.world
    rcases hx with hx | ⟨hw, -⟩ | ⟨c, -, hc⟩ | ⟨-, e, -, -, hop⟩
    · exact hx.elim
    · rw [hw]; exact ⟨hmInv, hsupW⟩
    · revert hc
      cases hres : M.call (pre abs Act m) m.frame.msg.caller c with
      | ok s' ret =>
        rintro ⟨-, hread, hfk, -⟩
        exact ⟨⟨hfk.code.trans hmInv.1, hread ▸ hW.1 _ _ _ _ _ hs.wf hres⟩,
          by rw [supply_frameKeeps hfk]; exact hsupW⟩
      | halt h =>
        cases h with
        | revert => rintro ⟨_, ho⟩; cases ho
        | invalid => rintro ⟨_, ho⟩; cases ho
    · revert hop
      unfold OpMatches
      cases hres : M.op (pre abs Act m) e with
      | some s' =>
        rintro ⟨-, hread, hfk, -⟩
        exact ⟨⟨hfk.code.trans hmInv.1, hread ▸ hW.2 _ _ _ hs.wf hres⟩,
          by rw [supply_frameKeeps hfk]; exact hsupW⟩
      | none => intro hf; exact hf.elim

/-! ## Message calls and transactions -/

/-- **Every token frame a message call reaches touches only actors**: it has an actor as
caller, well-formed calldata naming only actors, shorter than `2⁶⁴` bytes, and, for a token
with `permit`, `ecrecover` runs the precompile in its world (`EcrecoverPlain`). -/
def FramesTouch (code : ByteArray) (abs : TokenAbs σ) (M : TokenModel σ Address E)
    (sel : List Nat) (ops : Address → ByteArray → ℕ → Option E) (opAddrs : E → List Address)
    (perm : Option ((Machine → Nat) × (Machine → ℕ → Address))) (crypto : Crypto) (Act : Finset Address) (a : Address)
    (ctx : Context) (w : World) (tr : TransientStorage) (msg : Message) : Prop :=
  ∀ m, Reaches ctx w tr msg m →
    DStartV (Prot a) (TokGood code abs M crypto Act a) (Ctx crypto) msg.gas m →
    m.frame.msg.data.size < 2 ^ 64 ∧ m.frame.msg.caller ∈ Act ∧
      WellFormed sel ops opAddrs perm Act m.frame.msg ∧ (perm.isSome → EcrecoverPlain m)

/-- **A top-level message call keeps the invariant**, whatever it calls (the token or anything
calling it, at any depth), for any transaction type: a message from an unprotected caller
(`TopOk`) that moves its value, in the context of `crypto`, all of whose token frames touch
only actors, with less than `2⁶⁴` gas for a token with `permit` (its frames then have less),
from a world satisfying `TokGood` (the invariant, all ether below `2²⁵⁶`). -/
theorem processMessageCall_inv (hspec : ERC20Spec code abs M g₀ sel ops opAddrs)
    (hpermit : ∀ gp r, perm = some (gp, r) → PermitSpec code abs M gp r) (hW : M.WFInvariant)
    (hE : EtherFree abs M) (hsound : abs.Sound crypto Act) (hreal : code.size ≠ 0)
    (hdel : delegatedAddress? code = none) {fuel : Nat} {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} {r : MessageResult}
    (hw : TokGood code abs M crypto Act a w) (hmsg : TopOk (Prot a) w msg)
    (hv : msg.shouldTransferValue = true) (hC : ctx.crypto = crypto)
    (htouch : FramesTouch code abs M sel ops opAddrs perm crypto Act a ctx w tr msg)
    (hgas : perm.isSome → msg.gas < 2 ^ 64)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    TokGood code abs M crypto Act a r.world := by
  refine processMessageCall_good_reach (C := Ctx crypto) (goodOps hE hreal hdel) hw hmsg hv hC
    (fun m hreach hd => ?_) hr
  obtain ⟨hsize, hcaller, hwfd, hecr⟩ := htouch m hreach hd
  have ht : m.frame.msg.currentTarget = a := hd.danger.1
  have hsnap : m.frame.snapshot.1.code a = code := hd.snapshot.1.1
  have hwcode : m.world.code a = code := ((hd.keep a rfl).code).trans hsnap
  obtain ⟨ko, ks, hfr⟩ := hd.fresh
  have hfresh : Fresh code m := by
    have := fresh_init m m.frame.msg _ _ hfr
    rw [hd.code, ht, hwcode] at this
    exact this
  have hstart : Start code abs M Act m :=
    { fresh := hfresh
      launched := hd.world_eq
      value := by
        by_cases hv0 : m.frame.msg.value = 0
        · exact .inl hv0
        · refine .inr ⟨hd.transfers, fun he => hd.caller (he.trans ht), ?_⟩
          have haff := hd.afford hd.transfers hv0
          have hle := add_le_sum (fun b => (m.frame.snapshot.1.balance b).toNat)
            (a := a) (b := m.frame.msg.caller) (fun e => hd.caller e.symm)
          have hs := hd.snapshot.2
          unfold supply at hs
          rw [ht]
          omega
      precompiles := hd.pre
      size := hsize
      caller := hcaller
      sound := by rw [hd.context]; exact hsound
      wf := by
        show M.wf (abs.read m.ctx.crypto Act m.frame.snapshot.1 m.frame.msg.currentTarget)
        rw [hd.context, ht]; exact hd.snapshot.1.2
      hasCode := by rw [ht, hwcode]; exact hreal }
  have hsupW : supply m.world < 2 ^ 256 := by
    rw [hd.world_eq]
    unfold transferValue
    split
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rw [supply_moveEther (hd.afford hc.1 hc.2) hd.snapshot.2]; exact hd.snapshot.2
    · exact hd.snapshot.2
  have h := frame_inv hW hE hreal hstart (explained_of_spec hspec hpermit hstart hwfd
    fun hp => ⟨hecr hp, by have := hd.gas; have := hgas hp; rw [hfr]; show m.frame.msg.gas < _; omega⟩)
    ⟨ko, ks, by rw [hfr]; rfl⟩ (by rw [ht]; exact hsnap) hd.snapshot.2 hsupW
  rw [hd.context, ht] at h
  exact h

/-- **Every token frame a transaction reaches touches only actors** (`FramesTouch` for the
transaction's top-level message call), the transaction uses `crypto`, and, for a token with
`permit`, before Osaka its gas is below `2⁶⁴` (`PermitSpec` needs frames below `2⁶⁴` gas; from
Osaka the protocol caps a transaction's gas at `2²⁴`). -/
def TxTouch (code : ByteArray) (abs : TokenAbs σ) (M : TokenModel σ Address E) (sel : List Nat)
    (ops : Address → ByteArray → ℕ → Option E) (opAddrs : E → List Address)
    (perm : Option ((Machine → Nat) × (Machine → ℕ → Address))) (crypto : Crypto) (Act : Finset Address) (a : Address)
    (i : Input) (w : World) (_ : EvmLean.Tx.TxOutput) : Prop :=
  i.crypto = crypto ∧ (perm.isSome → i.fork < .osaka → i.tx.gas < 2 ^ 64) ∧
  ∀ (intr : EvmLean.Tx.IntrinsicGas) (c : EvmLean.Tx.Checked),
    EvmLean.Tx.validate i.fork i.tx = .ok intr →
    EvmLean.Tx.check i.crypto i.fork i.env i.gasAvail i.blobAvail w i.tx i.hint = .ok c →
    let w₁ := prefixWorld w c.sender
      (BitVec.ofNat 256 ((w.account c.sender).balance.toNat - upfrontFee i.fork i.env i.tx c))
    FramesTouch code abs M sel ops opAddrs perm crypto Act a (txContext i.crypto i.fork i.env i.tx c)
      w₁ ∅ (EvmLean.Tx.prepareMessage i.crypto i.fork i.env w₁ i.tx c.sender
        (w.account c.sender).nonce (i.tx.gas - intr.regular))

/-- **A successful transaction keeps the invariant**: any type, recipient, calldata, value and
authorizations, any fork and block, with the crypto `abs` is read with, all of whose token
frames touch only actors; all ether stays below `2²⁵⁶`. -/
theorem process_inv (hspec : ERC20Spec code abs M g₀ sel ops opAddrs)
    (hpermit : ∀ gp r, perm = some (gp, r) → PermitSpec code abs M gp r) (hW : M.WFInvariant)
    (hE : EtherFree abs M) (hsound : abs.Sound crypto Act) (hreal : code.size ≠ 0)
    (hdel : delegatedAddress? code = none) {i : Input} {w : World} {out : EvmLean.Tx.TxOutput}
    (hw : TokGood code abs M crypto Act a w) (h : i.run w = .ok out)
    (htouch : TxTouch code abs M sel ops opAddrs perm crypto Act a i w out) :
    TokGood code abs M crypto Act a out.world := by
  obtain ⟨hcr, htg, htouch⟩ := htouch
  -- all ether does not grow
  have hsupOut := (process_keeps_ether_7702 (P := fun _ => False)
    (Inv := fun w => supply w < 2 ^ 256) (fun _ _ _ h => h.elim) (fun _ h => h)
    (fun _ _ _ _ hw₁ hm hr => lt_of_le_of_lt
      (processMessageCall_supply_le_7702 hw₁ hm.top.depth hm.top.target hm.transfers hr) hw₁)
    (fun _ _ _ _ h => h) hw.2 h).2
  obtain ⟨intr, c, r, gu, hv, hc, hr, -, hout, -, -⟩ := process_ok h
  have hP : ∀ p, Prot a p → RealCode (w.code p) := fun p hp => by
    subst hp; rw [hw.1.1]; exact realCode_of_deleg hreal hdel
  have hfee : upfrontFee i.fork i.env i.tx c ≤ (w.account c.sender).balance.toNat := by
    have := (check_ok hc).2.2.2.1; omega
  have hs1 := supply_prefixWorld hfee
  set w₁ := prefixWorld w c.sender
    (BitVec.ofNat 256 ((w.account c.sender).balance.toNat - upfrontFee i.fork i.env i.tx c))
  have hw₁ : TokGood code abs M crypto Act a w₁ :=
    ⟨hw.1.keep hE (keep_prefixWorld _ _ _ a), by have := hw.2; omega⟩
  have htop := topOk_prepareMessage hP hc
    (BitVec.ofNat 256 ((w.account c.sender).balance.toNat - upfrontFee i.fork i.env i.tx c))
    (w.account c.sender).nonce (i.tx.gas - intr.regular)
  have hrw := processMessageCall_inv hspec hpermit hW hE hsound hreal hdel hw₁ htop
    (prepareMessage_shouldTransferValue ..) (by rw [txContext_crypto, hcr]) (htouch intr c hv hc)
    (fun hp => by
      rw [prepareMessage_gas]
      by_cases ho : i.fork < .osaka
      · have := htg hp ho; omega
      · have h24 := (validate_ok hv).2.2.2 (show Fork.osaka.toNat ≤ i.fork.toNat from
          Nat.not_lt.mp ho)
        simp only [EvmLean.Tx.txMaxGasLimit] at h24; omega) hr
  obtain ⟨hd, hs⟩ := processMessageCall_realCode hr
    (by rw [hw₁.1.1]; exact realCode_of_deleg hreal hdel)
  refine ⟨?_, lt_of_le_of_lt hsupOut hw.2⟩
  rw [hout]
  exact hrw.1.keep hE (keep_suffixWorld hs hd _ _ _ _)

/-- **The invariant holds after any sequence of successful transactions** using `crypto`, all
of whose token frames touch only actors, from a world with all ether below `2²⁵⁶`. -/
theorem txSteps_inv (hspec : ERC20Spec code abs M g₀ sel ops opAddrs)
    (hpermit : ∀ gp r, perm = some (gp, r) → PermitSpec code abs M gp r) (hW : M.WFInvariant)
    (hE : EtherFree abs M) (hsound : abs.Sound crypto Act) (hreal : code.size ≠ 0)
    (hdel : delegatedAddress? code = none) {w w' : World}
    (hw : TokGood code abs M crypto Act a w)
    (h : TxSteps (TxTouch code abs M sel ops opAddrs perm crypto Act a) w w') :
    TokGood code abs M crypto Act a w' :=
  h.keeps (fun _ _ _ hv hr ht => process_inv hspec hpermit hW hE hsound hreal hdel hv hr ht) hw

/-! ## Variants: the supply is the sum of the actors' balances -/

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

/-- **The supply is the sum of the actors' balances and frozen balances, after any sequence of
transactions**, for a token proved to be a `Sane` variant with a stored supply that does not
rebase (OpenZeppelin, Solady, … as variants), when it was before (the actors hold every token)
with all ether below `2²⁵⁶`, and every token frame of the transactions touches only actors
(`TxTouch`). -/
theorem variant_conserved {V : Variant Address} (hV : V.Sane) (hr : V.rebasing = false)
    (hsup : V.supply = .stored) {ev : VState Address → Address → Call Address → List (Event Address)}
    {abs : TokenAbs (VState Address)} {ops : Address → ByteArray → ℕ → Option (Variant.Op Address)}
    {opAddrs : Variant.Op Address → List Address}
    (hspec : ERC20Spec code abs (V.model ev) g₀ sel ops opAddrs)
    (hpermit : ∀ gp r, perm = some (gp, r) → PermitSpec code abs (V.model ev) gp r)
    (hE : EtherFree abs (V.model ev)) (hsound : abs.Sound crypto Act) (hreal : code.size ≠ 0)
    (hdel : delegatedAddress? code = none) {w w' : World}
    (hw : TokGood code abs (V.model ev) crypto Act a w)
    (h : TxSteps (TxTouch code abs (V.model ev) sel ops opAddrs perm crypto Act a) w w') :
    total (abs.read crypto Act w' a).bal + total (abs.read crypto Act w' a).frozen =
      (abs.read crypto Act w' a).supply := by
  have hi := txSteps_inv hspec hpermit (variant_wfInvariant hV ev) hE hsound hreal hdel hw h
  have := hi.1.2
  simp only [Variant.model_wf, Variant.WF, hr, hsup, Bool.false_eq_true, ↓reduceIte,
    reduceCtorEq] at this
  exact this.1

end Invariant

end QEDefi.ERC20.Spec
