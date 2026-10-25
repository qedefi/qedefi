import EvmLogic.Tx.Delete
import EvmLogic.Program.Nested.Run

/-!
# A transaction never deletes an account that is never created in it

`SELFDESTRUCT` schedules an account for deletion only if the account is in `createdAccounts`
(EIP-6780), and an account enters `createdAccounts` only when a creation frame starts at it. So
if no creation frame of a message call is ever at an account of `X` (`CreateIdle`), no account of
`X` is in the call's `accountsToDelete` (`processMessageCall_not_deleted`).

The guard simulations (`EvmLogic.Program.Nested.Guard`, `…Sandbox`) prove `CreateIdle` of every
reached machine for their idle principals (`GuardTxInv.createIdle`, `SandCommon.createIdle`):
an idle account has a nonzero nonce, so it is never deployable. With this file, an idle
principal survives the suffix of its transaction (which erases `accountsToDelete`) with its
nonce, so it is still idle in the next one.
-/

namespace EvmLogic.Tx
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested

variable {X : Address → Prop}

/-- No creation frame of the machine is at an account of `X`. -/
def CreateIdle (X : Address → Prop) (m : Machine) : Prop :=
  ∀ f ∈ m.frame :: m.parents, f.kind = .create → ¬ X f.msg.currentTarget

/-- No account of `X` was created in the transaction or is scheduled for deletion by a frame of
the machine. -/
def NoDel (X : Address → Prop) (m : Machine) : Prop :=
  ∀ x, X x → x ∉ m.createdAccounts ∧ ∀ f ∈ m.frame :: m.parents, x ∉ f.sub.accountsToDelete

theorem frameResult_sub (m : Machine) (o : Outcome) :
    (Program.frameResult m o).1.sub = m.frame.sub := by
  cases o with
  | success out =>
    cases hk : m.frame.kind with
    | call a b => simp [Program.frameResult, hk]
    | create =>
      cases hdc : depositCode m.ctx.fork m.frame.gasLeft out <;>
        simp [Program.frameResult, hk, hdc]
  | revert out => rfl
  | halt e => rfl

theorem not_mem_init_del {x : Address} {msg : Message} {kind : FrameKind}
    {snap : World × TransientStorage} : x ∉ (Frame.init msg kind snap).sub.accountsToDelete := by
  simp [Frame.init]

theorem noDel_instr {m m' : Machine} (h : NoDel X m) (hf : InstrFrame m m')
    (hd : DelPost m .next m') : NoDel X m' := fun x hx => by
  refine ⟨by rw [hf.created]; exact (h x hx).1, fun f hf' => ?_⟩
  rcases List.mem_cons.1 hf' with rfl | hp
  · intro hm
    rcases hd.2 x hm with hm | hm
    · exact (h x hx).2 _ List.mem_cons_self hm
    · exact (h x hx).1 hm
  · rw [hf.same.parents] at hp
    exact (h x hx).2 f (List.mem_cons_of_mem _ hp)

/-- A resumed frame schedules for deletion only what it or its child scheduled. -/
theorem not_mem_resume_del {M : Machine} {r : ChildResult} {x : Address}
    (hp : x ∉ M.frame.sub.accountsToDelete) (hr : x ∉ r.sub.accountsToDelete) :
    x ∉ (resume M r).frame.sub.accountsToDelete := by
  intro ha
  simp only [resume] at ha
  split at ha
  · rcases mem_union ha with ha | ha
    · exact hp ha
    · exact hr ha
  · split at ha
    · exact hp ha
    · exact hp ha

theorem noDel_finish {m : Machine} (h : NoDel X m) (o : Outcome) :
    (∀ m', finishFrame m o = .running m' → NoDel X m') ∧
    (∀ r, finishFrame m o = .done r → ∀ x, X x → x ∉ r.accountsToDelete) := by
  have hsub := frameResult_sub m o
  rw [finishFrame_eq]
  cases hp : m.parents with
  | nil =>
    refine ⟨fun _ h' => (by cases h'), fun r h' x hx => ?_⟩
    cases h'
    unfold topLevelResult
    split
    · show x ∉ (Program.frameResult m o).1.sub.accountsToDelete
      rw [hsub]; exact (h x hx).2 _ List.mem_cons_self
    · simp
  | cons p ps =>
    refine ⟨fun m' h' => ?_, fun _ h' => (by cases h')⟩
    cases h'
    intro x hx
    have hps : ∀ f ∈ p :: ps, x ∉ f.sub.accountsToDelete := fun f hf =>
      (h x hx).2 f (by rw [hp]; exact List.mem_cons_of_mem _ hf)
    refine ⟨(h x hx).1, fun f hf => ?_⟩
    rcases List.mem_cons.1 hf with rfl | hf
    · unfold resumeAfter
      exact not_mem_resume_del (hps p List.mem_cons_self)
        (by rw [hsub]; exact (h x hx).2 _ List.mem_cons_self)
    · unfold resumeAfter at hf
      rw [(sameFrame_resume _ _).parents] at hf
      exact hps f (List.mem_cons_of_mem _ hf)

theorem noDel_launchCall {m : Machine} (h : NoDel X m) (req : CallRequest) :
    NoDel X (launchCall m req) := by
  intro x hx
  unfold launchCall
  dsimp only
  split
  · unfold runPrecompile
    dsimp only
    have hr : x ∉ (Substate.ofMessage req.msg).accountsToDelete := by
      simp [Substate.ofMessage]
    split
    · exact ⟨(h x hx).1, fun f hf => by
        rcases List.mem_cons.1 hf with rfl | hf
        · exact not_mem_resume_del ((h x hx).2 _ List.mem_cons_self) hr
        · exact (h x hx).2 f (List.mem_cons_of_mem _ (by simpa [resume] using hf))⟩
    · exact ⟨(h x hx).1, fun f hf => by
        rcases List.mem_cons.1 hf with rfl | hf
        · exact not_mem_resume_del ((h x hx).2 _ List.mem_cons_self) hr
        · exact (h x hx).2 f (List.mem_cons_of_mem _ (by simpa [resume] using hf))⟩
  · refine ⟨(h x hx).1, fun f hf => ?_⟩
    rcases List.mem_cons.1 hf with rfl | hf
    · exact not_mem_init_del
    · exact (h x hx).2 f hf

theorem noDel_launchCreate {m : Machine} (h : NoDel X m) {msg : Message}
    (hc : ¬ X msg.currentTarget) : NoDel X (launchCreate m msg) := by
  intro x hx
  refine ⟨fun ha => ?_, fun f hf => ?_⟩
  · simp only [launchCreate, beginCreate] at ha
    rcases Std.ExtTreeSet.mem_insert.1 ha with ha | ha
    · exact hc (by rw [Std.LawfulEqCmp.eq_of_compare ha]; exact hx)
    · exact (h x hx).1 ha
  · rcases List.mem_cons.1 hf with rfl | hf
    · exact not_mem_init_del
    · exact (h x hx).2 f hf

/-- **One step keeps `NoDel`** when the next machine starts no creation at an account of `X`,
and a finished message schedules no account of `X` for deletion. -/
theorem noDel_step {m : Machine} (h : NoDel X m) :
    (∀ m', step m = .running m' → CreateIdle X m' → NoDel X m') ∧
    (∀ r, step m = .done r → ∀ x, X x → x ∉ r.accountsToDelete) := by
  rcases step_cases_del m with ⟨m', o, he, hf, hd⟩ | ⟨m', he, hf, hd⟩ | ⟨m', req, he, hf, hd⟩ |
    ⟨m', msg, he, hf, hd, -⟩
  · rw [he]
    have := noDel_finish (noDel_instr h hf hd) o
    exact ⟨fun m'' h' _ => this.1 m'' h', this.2⟩
  · rw [he]
    exact ⟨fun _ h' _ => by cases h'; exact noDel_instr h hf hd, fun _ h' => by cases h'⟩
  · rw [he]
    exact ⟨fun _ h' _ => by cases h'; exact noDel_launchCall (noDel_instr h hf hd) req,
      fun _ h' => by cases h'⟩
  · rw [he]
    refine ⟨fun _ h' hc => ?_, fun _ h' => by cases h'⟩
    cases h'
    exact noDel_launchCreate (noDel_instr h hf hd)
      (hc _ List.mem_cons_self (by simp [launchCreate, Frame.init]))

theorem run_noDel {m₀ : Machine} (hc : ∀ n m, stepN n m₀ = .running m → CreateIdle X m) :
    ∀ (fuel n : Nat) {m : Machine} {r : MessageResult}, stepN n m₀ = .running m → NoDel X m →
      run fuel m = .ok r → ∀ x, X x → x ∉ r.accountsToDelete
  | 0, _, _, _, _, _, hr => by cases hr
  | fuel + 1, n, m, r, hn, h, hr => by
    simp only [run] at hr
    cases hs : step m with
    | done r' => rw [hs] at hr; cases hr; exact (noDel_step h).2 _ hs
    | running m' =>
      rw [hs] at hr
      have hn' : stepN (n + 1) m₀ = .running m' := by
        rw [stepN_add_of_running hn 1, stepN_one, hs]
      exact run_noDel hc fuel (n + 1) hn' ((noDel_step h).1 m' hs (hc _ _ hn')) hr

/-- **A top-level message call deletes no account of `X`** when no creation frame of it is at an
account of `X`. -/
theorem processMessageCall_not_deleted {fuel : Nat} {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} {r : MessageResult}
    (hc : ∀ m, Reaches ctx w tr msg m → CreateIdle X m)
    (h : processMessageCall fuel ctx w tr msg = .ok r) : ∀ x, X x → x ∉ r.accountsToDelete := by
  have hst : ∀ m₀, initMachine (PrecompileImpl.standard ctx) ctx
      (applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg).1 tr
      (applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg).2.1 =
        .inr m₀ → StartsAt ctx w tr msg m₀ := fun _ h => h
  unfold processMessageCall processMessageCallWith at h
  generalize applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg = d
    at h hst
  obtain ⟨w₀, msg', refund⟩ := d
  dsimp only at h hst
  cases hm : initMachine (PrecompileImpl.standard ctx) ctx w₀ tr msg' with
  | inl r' =>
    rw [hm] at h; cases h
    intro x _ hx
    unfold initMachine at hm
    dsimp only at hm
    split at hm
    · cases hm; simp [failureResult] at hx
    split at hm
    · cases hm; simp [failureResult] at hx
    split at hm
    · split at hm
      · cases hm; simp [failureResult] at hx
      · cases hm
    · split at hm
      · cases hm
        unfold runPrecompile at hx
        dsimp only at hx
        split at hx <;> unfold topLevelResult at hx <;> split at hx <;>
          simp [Substate.ofMessage] at hx
      · cases hm
  | inr m₀ =>
    rw [hm] at h
    dsimp only at h
    cases hrun : run fuel m₀ with
    | error e => rw [hrun] at h; cases h
    | ok r' =>
      rw [hrun] at h; cases h
      have hs := hst m₀ hm
      have hc' : ∀ n m, stepN n m₀ = .running m → CreateIdle X m :=
        fun n m hn => hc m ⟨m₀, n, hs, hn⟩
      have h0 : NoDel X m₀ := by
        have hc0 := hc' 0 m₀ rfl
        intro x hx
        unfold initMachine at hm
        dsimp only at hm
        split at hm
        · cases hm
        split at hm
        · cases hm
        split at hm
        · split at hm
          · cases hm
          · cases hm
            refine ⟨fun ha => ?_, fun f hf => ?_⟩
            · simp only [beginCreate] at ha
              rcases Std.ExtTreeSet.mem_insert.1 ha with ha | ha
              · exact hc0 _ List.mem_cons_self rfl (by
                  show X msg'.currentTarget
                  rw [Std.LawfulEqCmp.eq_of_compare ha]; exact hx)
              · simp at ha
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
              subst hf; exact not_mem_init_del
        · split at hm
          · cases hm
          · cases hm
            refine ⟨fun ha => by simp at ha, fun f hf => ?_⟩
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
            subst hf; exact not_mem_init_del
      exact run_noDel hc' fuel 0 rfl h0 hrun (r := r')

end EvmLogic.Tx
