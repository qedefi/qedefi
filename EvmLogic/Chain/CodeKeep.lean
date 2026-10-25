import EvmLogic.Chain.SystemCode
import EvmLogic.AbsInt.Code
import EvmLogic.Tx.Lift

/-!
# Real code never changes

An account holding real code (not empty, not an EIP-7702 designator, `Tx.RealCode`) keeps exactly
that code through a top-level message call (`processMessageCall_code`): no instruction changes
code (`AbsInt.exec_code`), code is deposited only by a finished creation at an account without
code in the starting world (`Tx.DelInv`, EIP-684/EIP-7610), a revert restores a snapshot taken
during the call, and an EIP-7702 authorization cannot have an account with real code as its
authority (`Tx.applyTopLevelDelegation_code`). `Tx.processMessageCall_realCode` only says such an
account still holds *some* code; here the code is the same.

Lifted to transactions (`process_code`, through `Tx.process_keeps`), system calls
(`systemCall_code`) and balance credits, the canonical code of the system contracts is a block
invariant (`SystemCodeIn`, `blockPreserves_systemCodeIn` in `EvmLogic.Chain.SystemSafe`).
-/

namespace EvmLogic.Chain
open EvmLean EvmLean.Interpreter EvmLean.Block EvmLogic.Program EvmLogic.Program.Nested

/-! ## The invariant -/

/-- Every account holding code in `w₀` holds the same code in `w`. -/
def CodeSame (w₀ w : World) : Prop := ∀ a, (w₀.code a).size ≠ 0 → w.code a = w₀.code a

theorem CodeSame.refl (w : World) : CodeSame w w := fun _ _ => rfl

theorem CodeSame.congr {w₀ w w' : World} (h : CodeSame w₀ w) (hc : AbsInt.SameCode w w') :
    CodeSame w₀ w' := fun a ha => (hc a).trans (h a ha)

theorem CodeSame.setCode {w₀ w : World} (h : CodeSame w₀ w) {b : Address} (hb : Tx.Fresh w₀ b)
    (c : ByteArray) : CodeSame w₀ (Interpreter.setCode w b c) := fun a ha => by
  by_cases hab : b = a
  · subst hab; exact absurd hb ha
  · rw [Tx.code_setCode_ne w c hab]; exact h a ha

/-- The code part of the invariant of a machine started from `w₀`: the current world and every
rollback snapshot keep the code of `w₀`. Carried together with `Tx.DelInv`, which says that a
creation frame creates an account without code in `w₀`. -/
structure CodeInv (w₀ : World) (m : Machine) : Prop where
  world : CodeSame w₀ m.world
  snapshots : ∀ f ∈ m.frame :: m.parents, CodeSame w₀ f.snapshot.1

/-! ## One step -/

theorem frameResult_codeSame {w₀ : World} {m : Machine} (h : CodeInv w₀ m)
    (hcr : m.frame.kind = .create → Tx.Fresh w₀ m.frame.msg.currentTarget) (o : Outcome) :
    CodeSame w₀ (frameResult m o).2.1 := by
  rcases frameResult_world m o with he | ⟨hk, out, he⟩ | he <;> rw [he]
  · exact h.world
  · exact h.world.setCode (hcr hk) out
  · exact h.snapshots _ List.mem_cons_self

theorem finishFrame_codeInv {w₀ : World} {m : Machine} (h : CodeInv w₀ m)
    (hcr : m.frame.kind = .create → Tx.Fresh w₀ m.frame.msg.currentTarget) (o : Outcome) :
    (∀ m', finishFrame m o = .running m' → CodeInv w₀ m') ∧
    (∀ r, finishFrame m o = .done r → CodeSame w₀ r.world) := by
  have hw := frameResult_codeSame h hcr o
  rw [finishFrame_eq]
  cases hp : m.parents with
  | nil =>
    refine ⟨fun _ h' => (by cases h'), fun r h' => ?_⟩
    cases h'
    unfold topLevelResult
    split <;> exact hw
  | cons p ps =>
    refine ⟨fun m' h' => ?_, fun _ h' => (by cases h')⟩
    cases h'
    have hpar : ∀ f ∈ p :: ps, CodeSame w₀ f.snapshot.1 := fun f hf =>
      h.snapshots f (List.mem_cons_of_mem _ (hp ▸ hf))
    refine ⟨hw, fun f hf => ?_⟩
    rcases List.mem_cons.1 hf with rfl | hf
    · exact hpar p List.mem_cons_self
    · exact hpar f (List.mem_cons_of_mem _ hf)

theorem CodeInv.instr {w₀ : World} {m m₁ : Machine} (h : CodeInv w₀ m) (hf : SameFrame m m₁)
    (hc : AbsInt.SameCode m.world m₁.world) : CodeInv w₀ m₁ := by
  refine ⟨h.world.congr hc, ?_⟩
  rw [hf.parents]
  intro f hf'
  rcases List.mem_cons.1 hf' with rfl | hf'
  · rw [hf.snapshot]; exact h.snapshots _ List.mem_cons_self
  · exact h.snapshots f (List.mem_cons_of_mem _ hf')

theorem launchCall_codeInv {w₀ : World} {m : Machine} (h : CodeInv w₀ m) (req : CallRequest) :
    CodeInv w₀ (launchCall m req) := by
  unfold launchCall
  dsimp only
  split
  · unfold runPrecompile
    dsimp only
    have hs : ∀ (M : Machine) (r : ChildResult), M.frame = m.frame → M.parents = m.parents →
        ∀ f ∈ (resume M r).frame :: (resume M r).parents, CodeSame w₀ f.snapshot.1 := by
      intro M r hfr hpa f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · show CodeSame w₀ M.frame.snapshot.1
        rw [hfr]; exact h.snapshots _ List.mem_cons_self
      · rw [show (resume M r).parents = M.parents from rfl, hpa] at hf
        exact h.snapshots f (List.mem_cons_of_mem _ hf)
    split
    · exact ⟨h.world.congr (AbsInt.code_transferValue _ _), hs _ _ rfl rfl⟩
    · exact ⟨h.world, hs _ _ rfl rfl⟩
  · refine ⟨h.world.congr (AbsInt.code_transferValue _ _), ?_⟩
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact h.world
    · exact h.snapshots f hf

theorem launchCreate_codeInv {w₀ : World} {m : Machine} (h : CodeInv w₀ m) (msg : Message) :
    CodeInv w₀ (launchCreate m msg) := by
  unfold launchCreate beginCreate
  dsimp only
  refine ⟨h.world.congr ((AbsInt.code_incrementNonce _ _).trans
    (AbsInt.code_transferValue _ _)), ?_⟩
  intro f hf
  rcases List.mem_cons.1 hf with rfl | hf
  · exact h.world
  · exact h.snapshots f hf

/-- **One step keeps the code invariant**, and a finished message keeps the code of `w₀`. -/
theorem step_codeInv {w₀ : World} {m : Machine} (hd : Tx.DelInv w₀ m) (h : CodeInv w₀ m) :
    (∀ m', step m = .running m' → CodeInv w₀ m') ∧
    (∀ r, step m = .done r → CodeSame w₀ r.world) := by
  unfold step
  by_cases hpc : m.frame.pc < m.frame.code.size
  · simp only [hpc, ↓reduceDIte]
    cases he : (exec (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc])).run m with
    | error e => exact finishFrame_codeInv h hd.frame.create _
    | ok p =>
      obtain ⟨a, m₁⟩ := p
      have hf := ((exec_frame _ m).of_run he).1.same
      have h₁ : CodeInv w₀ m₁ := h.instr hf ((AbsInt.exec_code _ m).of_run he)
      have hcr : m₁.frame.kind = .create → Tx.Fresh w₀ m₁.frame.msg.currentTarget := by
        rw [hf.kind, hf.msg]; exact hd.frame.create
      cases a with
      | next => exact ⟨fun _ h' => by cases h'; exact h₁, fun _ h' => by cases h'⟩
      | stop out => exact finishFrame_codeInv h₁ hcr _
      | revert out => exact finishFrame_codeInv h₁ hcr _
      | call req =>
        exact ⟨fun _ h' => by cases h'; exact launchCall_codeInv h₁ req, fun _ h' => by cases h'⟩
      | create msg =>
        exact ⟨fun _ h' => by cases h'; exact launchCreate_codeInv h₁ msg,
          fun _ h' => by cases h'⟩
  · simp only [hpc, ↓reduceDIte]
    exact finishFrame_codeInv h hd.frame.create _

theorem run_codeSame {w₀ : World} : ∀ (fuel : Nat) (m : Machine) (r : MessageResult),
    Tx.DelInv w₀ m → CodeInv w₀ m → run fuel m = .ok r → CodeSame w₀ r.world
  | 0, _, _, _, _, h => by cases h
  | fuel + 1, m, r, hd, hm, h => by
    simp only [run] at h
    split at h
    · rename_i r' he
      cases h
      exact (step_codeInv hd hm).2 _ he
    · rename_i m' he
      exact run_codeSame fuel m' r ((Tx.step_del hd).1 _ he) ((step_codeInv hd hm).1 _ he) h

/-! ## A top-level message call -/

theorem initMachine_codeSame {pre : PrecompileImpl} {ctx : Context} {w₀ : World}
    {tr : TransientStorage} {msg : Message} :
    (∀ r, initMachine pre ctx w₀ tr msg = .inl r → CodeSame w₀ r.world) ∧
    (∀ m₀, initMachine pre ctx w₀ tr msg = .inr m₀ → CodeInv w₀ m₀) := by
  have hone : ∀ f ∈ [Frame.init msg (.call 0 0) (w₀, tr)], CodeSame w₀ f.snapshot.1 :=
    fun f hf => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf; exact CodeSame.refl w₀
  unfold initMachine
  dsimp only
  split
  · exact ⟨fun _ h => by cases h; exact CodeSame.refl _, fun _ h => by cases h⟩
  split
  · exact ⟨fun _ h => by cases h; exact CodeSame.refl _, fun _ h => by cases h⟩
  split
  · split
    · exact ⟨fun _ h => by cases h; exact CodeSame.refl _, fun _ h => by cases h⟩
    · refine ⟨fun _ h => (by cases h), fun m₀ h => ?_⟩
      cases h
      refine ⟨(CodeSame.refl w₀).congr ((AbsInt.code_incrementNonce _ _).trans
        (AbsInt.code_transferValue _ _)), fun f hf => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf; exact CodeSame.refl w₀
  · split
    · refine ⟨fun r h => ?_, fun _ h => (by cases h)⟩
      cases h
      unfold runPrecompile
      dsimp only
      split
      · unfold topLevelResult
        split <;> exact (CodeSame.refl w₀).congr (AbsInt.code_transferValue _ _)
      · unfold topLevelResult
        split <;> exact CodeSame.refl w₀
    · refine ⟨fun _ h => (by cases h), fun m₀ h => ?_⟩
      cases h
      exact ⟨(CodeSame.refl w₀).congr (AbsInt.code_transferValue _ _), hone⟩

/-- **A top-level message call keeps the code of every account holding code** in the world
after the transaction's EIP-7702 delegations. -/
theorem processMessageCall_codeSame {fuel : Nat} {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} {r : MessageResult}
    (h : processMessageCall fuel ctx w tr msg = .ok r) :
    CodeSame (applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg).1
      r.world := by
  unfold processMessageCall processMessageCallWith at h
  generalize applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg = d
    at h ⊢
  obtain ⟨w₀, msg', refund⟩ := d
  dsimp only at h ⊢
  have hi := initMachine_codeSame (pre := PrecompileImpl.standard ctx) (ctx := ctx) (w₀ := w₀)
    (tr := tr) (msg := msg')
  have hdi := Tx.initMachine_del (pre := PrecompileImpl.standard ctx) (ctx := ctx) (w₀ := w₀)
    (tr := tr) (msg := msg')
  cases hm : initMachine (PrecompileImpl.standard ctx) ctx w₀ tr msg' with
  | inl r' =>
    rw [hm] at h; cases h
    exact hi.1 r' hm
  | inr m₀ =>
    rw [hm] at h
    dsimp only at h
    cases hrun : run fuel m₀ with
    | error e => rw [hrun] at h; cases h
    | ok r' =>
      rw [hrun] at h; cases h
      exact run_codeSame fuel m₀ r' (hdi.2 m₀ hm) (hi.2 m₀ hm) hrun

/-- **A top-level message call never changes real code**: an account whose code is not empty and
not an EIP-7702 designator holds the same code afterwards, with or without EIP-7702
authorizations. -/
theorem processMessageCall_code {fuel : Nat} {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} {r : MessageResult}
    (h : processMessageCall fuel ctx w tr msg = .ok r) {a : Address}
    (ha : Tx.RealCode (w.code a)) : r.world.code a = w.code a := by
  have hc := Tx.applyTopLevelDelegation_code (ctx := ctx)
    (isPre := (PrecompileImpl.standard ctx).isPrecompile) (msg := msg) ha
  rw [← hc]
  exact processMessageCall_codeSame h a (by rw [hc]; exact ha.1)

/-! ## Transactions, system calls, credits -/

/-- An account holding the real code `c`. -/
def HoldsCode (a : Address) (c : ByteArray) (w : World) : Prop := w.code a = c

/-- **A transaction never changes real code**: a successful `Tx.process` leaves an account
holding real code with the same code. -/
theorem process_code {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {gasAvail blobAvail : Nat} {w : World} {tx : Transaction} {hint : Option Address}
    {out : Tx.TxOutput} {a : Address} (ha : Tx.RealCode (w.code a))
    (h : Tx.process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    out.world.code a = w.code a := by
  have hk : ∀ w', HoldsCode a (w.code a) w' → Tx.RealCode (w'.code a) := fun w' hw' => by
    unfold HoldsCode at hw'; rw [hw']; exact ha
  exact Tx.process_keeps (P := (· = a)) (Inv := HoldsCode a (w.code a))
    (fun w' hw' p hp => hp ▸ hk w' hw')
    (fun _ w₁ _ _ hw₁ _ hr => (processMessageCall_code hr (hk w₁ hw₁)).trans hw₁)
    (fun _ _ hw' hkeep => (hkeep a rfl).2.trans hw') rfl h

/-- **A system call never changes real code** (to any target). -/
theorem systemCall_code {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {world : World} {target : Address} {data : ByteArray} {w' : World} {res : MessageResult}
    (h : systemCall fuel crypto fork env world target data = .ok (w', res)) {a : Address}
    (ha : Tx.RealCode (world.code a)) : w'.code a = world.code a := by
  obtain ⟨hr, rfl⟩ := systemCall_ok.1 h
  have hc := processMessageCall_code hr ha
  rw [← hc]
  exact ((eraseEmpty_destroyTouchedEmpty _ _).keep (by rw [hc]; exact ha.1)).2

/-- A balance credit never changes code. -/
theorem creditBalance_code (w : World) (b : Address) (amount : Nat) (a : Address) :
    (Tx.creditBalance w b amount).code a = w.code a :=
  code_creditBalance w b amount a

end EvmLogic.Chain
