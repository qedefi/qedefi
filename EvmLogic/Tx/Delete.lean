import EvmLogic.Tx.Exec
import EvmLogic.Program.Nested.Step

/-!
# Which accounts a transaction may delete

`SELFDESTRUCT` schedules its account for deletion only if the account was created in the same
transaction (EIP-6780): `execSelfdestruct` inserts into `accountsToDelete` only members of
`createdAccounts`, and an account is created only where no code is (`accountDeployable`). Code
is never removed during a message: every update goes through `modifyState` (which erases only
empty, hence codeless, accounts), code is set only at the end of a creation, and a revert restores
a snapshot taken earlier in the same run.

`processMessageCall_del`: if a top-level message call ends with `r`, every account of
`r.accountsToDelete` held no code in the world the machine started from (after the EIP-7702
delegations of the transaction), and every account holding code there still holds code in
`r.world`. `processMessageCall_not_mem_accountsToDelete`: an account holding code that is not an
EIP-7702 designator before the message is never deleted.
-/

namespace EvmLogic.Tx
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested

/-! ## Sets of addresses -/

theorem mem_union {s t : AddressSet} {a : Address} (h : a ∈ s ∪ t) : a ∈ s ∨ a ∈ t :=
  Std.ExtTreeSet.mem_union_iff.1 h

/-! ## The invariant -/

/-- Every account holding code in `w₀` holds code in `w`. -/
def CodeKept (w₀ w : World) : Prop := ∀ a, (w₀.code a).size ≠ 0 → (w.code a).size ≠ 0

/-- `a` holds no code in `w₀`. -/
def Fresh (w₀ : World) (a : Address) : Prop := (w₀.code a).size = 0

theorem CodeKept.refl (w : World) : CodeKept w w := fun _ h => h

theorem CodeKept.fresh {w₀ w : World} {a : Address} (h : CodeKept w₀ w)
    (ha : (w.code a).size = 0) : Fresh w₀ a :=
  Classical.byContradiction fun hn => h a hn ha

theorem CodeKept.transferValue {w₀ w : World} (h : CodeKept w₀ w) (msg : Message) :
    CodeKept w₀ (transferValue w msg) := fun a ha => by rw [code_transferValue]; exact h a ha

theorem CodeKept.incrementNonce {w₀ w : World} (h : CodeKept w₀ w) (b : Address) :
    CodeKept w₀ (incrementNonce w b) := fun a ha => by rw [code_incrementNonce]; exact h a ha

theorem code_setCode_ne (w : World) {b a : Address} (c : ByteArray) (hab : b ≠ a) :
    (setCode w b c).code a = w.code a := by
  unfold Interpreter.setCode World.code modifyState
  dsimp only
  split <;> simp [World.account, Std.ExtTreeMap.getD_erase, Std.ExtTreeMap.getD_insert, hab]

theorem CodeKept.setCode {w₀ w : World} (h : CodeKept w₀ w) {b : Address} (hb : Fresh w₀ b)
    (c : ByteArray) : CodeKept w₀ (setCode w b c) := fun a ha => by
  by_cases hab : b = a
  · subst hab; exact absurd hb ha
  · rw [code_setCode_ne w c hab]; exact h a ha

/-- What a frame of the stack satisfies. -/
structure FrameDel (w₀ : World) (f : Frame) : Prop where
  /-- Its snapshot (restored on failure) keeps the code. -/
  snapshot : CodeKept w₀ f.snapshot.1
  /-- Its deletion set holds only accounts without code in `w₀`. -/
  del : ∀ a ∈ f.sub.accountsToDelete, Fresh w₀ a
  /-- A creation frame creates an account without code in `w₀`. -/
  create : f.kind = .create → Fresh w₀ f.msg.currentTarget

/-- The invariant of a machine started from `w₀`. -/
structure DelInv (w₀ : World) (m : Machine) : Prop where
  world : CodeKept w₀ m.world
  frame : FrameDel w₀ m.frame
  parents : ∀ f ∈ m.parents, FrameDel w₀ f
  created : ∀ a ∈ m.createdAccounts, Fresh w₀ a

/-- What a finished message satisfies. -/
structure ResultDel (w₀ : World) (r : MessageResult) : Prop where
  world : CodeKept w₀ r.world
  del : ∀ a ∈ r.accountsToDelete, Fresh w₀ a

theorem frameDel_init {w₀ : World} {msg : Message} {kind : FrameKind}
    {snap : World × TransientStorage} (hs : CodeKept w₀ snap.1)
    (hk : kind = .create → Fresh w₀ msg.currentTarget) :
    FrameDel w₀ (Frame.init msg kind snap) :=
  ⟨hs, fun _ h => by simp [Frame.init] at h, hk⟩

/-! ## One step -/

theorem DelInv.instr {w₀ : World} {m m' : Machine} (h : DelInv w₀ m) (hf : InstrFrame m m')
    (hd : DelPost m .next m') : DelInv w₀ m' where
  world a ha := hd.1 a (h.world a ha)
  frame := by
    refine ⟨?_, fun a ha => ?_, ?_⟩
    · rw [hf.same.snapshot]; exact h.frame.snapshot
    · rcases hd.2 a ha with ha | ha
      · exact h.frame.del a ha
      · exact h.created a ha
    · rw [hf.same.kind, hf.same.msg]; exact h.frame.create
  parents := by rw [hf.same.parents]; exact h.parents
  created := by rw [hf.created]; exact h.created

theorem frameResult_del {w₀ : World} {m : Machine} (h : DelInv w₀ m) (o : Outcome) :
    CodeKept w₀ (frameResult m o).2.1 ∧ (frameResult m o).1.sub = m.frame.sub := by
  cases o with
  | success out =>
    cases hk : m.frame.kind with
    | call a b => simp [frameResult, hk]; exact h.world
    | create =>
      cases hdc : depositCode m.ctx.fork m.frame.gasLeft out with
      | ok g =>
        simp only [frameResult, hk, hdc]
        exact ⟨h.world.setCode (h.frame.create hk) out, by trivial⟩
      | error e => simp only [frameResult, hk, hdc]; exact ⟨h.frame.snapshot, by trivial⟩
  | revert out => simp only [frameResult]; exact ⟨h.frame.snapshot, by trivial⟩
  | halt e => simp only [frameResult]; exact ⟨h.frame.snapshot, by trivial⟩

theorem resume_frame_del {w₀ : World} {M : Machine} {r : ChildResult}
    (hp : FrameDel w₀ M.frame) (hr : ∀ a ∈ r.sub.accountsToDelete, Fresh w₀ a) :
    FrameDel w₀ (resume M r).frame := by
  refine ⟨hp.snapshot, fun a ha => ?_, hp.create⟩
  simp only [resume] at ha
  split at ha
  · rcases mem_union ha with ha | ha
    · exact hp.del a ha
    · exact hr a ha
  · split at ha
    · exact hp.del a ha
    · exact hp.del a ha

theorem finishFrame_del {w₀ : World} {m : Machine} (h : DelInv w₀ m) (o : Outcome) :
    (∀ m', finishFrame m o = .running m' → DelInv w₀ m') ∧
    (∀ r, finishFrame m o = .done r → ResultDel w₀ r) := by
  obtain ⟨hw, hsub⟩ := frameResult_del h o
  rw [finishFrame_eq]
  cases hp : m.parents with
  | nil =>
    refine ⟨fun _ h' => (by cases h'), fun r h' => ?_⟩
    cases h'
    unfold topLevelResult
    split
    · refine ⟨hw, fun a ha => ?_⟩
      simp only at ha
      rw [hsub] at ha
      exact h.frame.del a ha
    · exact ⟨hw, fun a ha => (by simp at ha)⟩
  | cons p ps =>
    refine ⟨fun m' h' => ?_, fun _ h' => (by cases h')⟩
    cases h'
    have hpd : FrameDel w₀ p := h.parents p (by rw [hp]; exact List.mem_cons_self)
    refine ⟨hw, ?_, fun f hf => h.parents f (by rw [hp]; exact List.mem_cons_of_mem _ hf),
      h.created⟩
    exact resume_frame_del (M := { m with frame := p, parents := ps, world := _, transient := _ })
      hpd (fun a ha => by rw [hsub] at ha; exact h.frame.del a ha)

theorem launchCall_del {w₀ : World} {m : Machine} (h : DelInv w₀ m) (req : CallRequest) :
    DelInv w₀ (launchCall m req) := by
  unfold launchCall
  dsimp only
  split
  · rename_i a _
    unfold runPrecompile
    dsimp only
    have hr : ∀ a ∈ (Substate.ofMessage req.msg).accountsToDelete, Fresh w₀ a := fun a ha => by
      simp [Substate.ofMessage] at ha
    split
    · exact ⟨h.world.transferValue _, resume_frame_del h.frame hr, h.parents, h.created⟩
    · exact ⟨h.world, resume_frame_del h.frame hr, h.parents, h.created⟩
  · refine ⟨h.world.transferValue _, frameDel_init h.world (fun hk => by cases hk), ?_,
      h.created⟩
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact h.frame
    · exact h.parents f hf

theorem launchCreate_del {w₀ : World} {m : Machine} (h : DelInv w₀ m) {msg : Message}
    (hc : (m.world.code msg.currentTarget).size = 0) : DelInv w₀ (launchCreate m msg) := by
  have hf : Fresh w₀ msg.currentTarget := h.world.fresh hc
  refine ⟨(h.world.incrementNonce _).transferValue _, frameDel_init h.world (fun _ => hf), ?_, ?_⟩
  · intro f hf'
    rcases List.mem_cons.1 hf' with rfl | hf'
    · exact h.frame
    · exact h.parents f hf'
  · intro a ha
    simp only [launchCreate, beginCreate] at ha
    rcases Std.ExtTreeSet.mem_insert.1 ha with ha | ha
    · rw [← Std.LawfulEqCmp.eq_of_compare ha]; exact hf
    · exact h.created a ha

/-- **How a step goes**, with the deletion postcondition of the instruction. -/
theorem step_cases_del (m : Machine) :
    (∃ m' o, step m = finishFrame m' o ∧ InstrFrame m m' ∧ DelPost m .next m') ∨
    (∃ m', step m = .running m' ∧ InstrFrame m m' ∧ DelPost m .next m') ∨
    (∃ m' req, step m = .running (launchCall m' req) ∧ InstrFrame m m' ∧ DelPost m .next m') ∨
    (∃ m' msg, step m = .running (launchCreate m' msg) ∧ InstrFrame m m' ∧
      DelPost m .next m' ∧ CreateOk m m' msg) := by
  have hrefl : DelPost m .next m := ⟨fun _ h => h, fun _ h => .inl h⟩
  unfold step
  dsimp only
  split
  · rename_i hpc
    have hw := exec_frame (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc]) m
    have hd := exec_del (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc]) m
    split
    · exact .inl ⟨m, _, rfl, .refl m, hrefl⟩
    · rename_i m' h
      exact .inr (.inl ⟨m', rfl, (hw.of_run h).1, ⟨(hd.of_run h).1, (hd.of_run h).2⟩⟩)
    · rename_i out m' h
      exact .inl ⟨m', _, rfl, (hw.of_run h).1, ⟨(hd.of_run h).1, (hd.of_run h).2⟩⟩
    · rename_i out m' h
      exact .inl ⟨m', _, rfl, (hw.of_run h).1, ⟨(hd.of_run h).1, (hd.of_run h).2⟩⟩
    · rename_i req m' h
      exact .inr (.inr (.inl ⟨m', req, rfl, (hw.of_run h).1, ⟨(hd.of_run h).1, (hd.of_run h).2⟩⟩))
    · rename_i msg m' h
      exact .inr (.inr (.inr ⟨m', msg, rfl, (hw.of_run h).1, ⟨(hd.of_run h).1, (hd.of_run h).2⟩, (hw.of_run h).2⟩))
  · exact .inl ⟨m, _, rfl, .refl m, hrefl⟩

/-- **One step keeps the invariant**, and a finished message satisfies `ResultDel`. -/
theorem step_del {w₀ : World} {m : Machine} (h : DelInv w₀ m) :
    (∀ m', step m = .running m' → DelInv w₀ m') ∧
    (∀ r, step m = .done r → ResultDel w₀ r) := by
  rcases step_cases_del m with ⟨m', o, he, hf, hd⟩ | ⟨m', he, hf, hd⟩ | ⟨m', req, he, hf, hd⟩ |
    ⟨m', msg, he, hf, hd, hc⟩
  · rw [he]; exact finishFrame_del (h.instr hf hd) o
  · rw [he]
    exact ⟨fun _ h' => by cases h'; exact h.instr hf hd, fun _ h' => by cases h'⟩
  · rw [he]
    exact ⟨fun _ h' => by cases h'; exact launchCall_del (h.instr hf hd) req,
      fun _ h' => by cases h'⟩
  · rw [he]
    exact ⟨fun _ h' => by cases h'; exact launchCreate_del (h.instr hf hd) hc.code,
      fun _ h' => by cases h'⟩

theorem run_del {w₀ : World} : ∀ (fuel : Nat) (m : Machine) (r : MessageResult),
    DelInv w₀ m → run fuel m = .ok r → ResultDel w₀ r
  | 0, _, _, _, h => by cases h
  | fuel + 1, m, r, hm, h => by
    simp only [run] at h
    split at h
    · rename_i r' he
      cases h
      exact (step_del hm).2 _ he
    · rename_i m' he
      exact run_del fuel m' r ((step_del hm).1 _ he) h

/-! ## A top-level message call -/

theorem initMachine_del {pre : PrecompileImpl} {ctx : Context} {w₀ : World}
    {tr : TransientStorage} {msg : Message} :
    (∀ r, initMachine pre ctx w₀ tr msg = .inl r → ResultDel w₀ r) ∧
    (∀ m₀, initMachine pre ctx w₀ tr msg = .inr m₀ → DelInv w₀ m₀) := by
  have hfail : ∀ e, ResultDel w₀ (failureResult e w₀ tr) :=
    fun _ => ⟨CodeKept.refl _, fun a ha => by simp [failureResult] at ha⟩
  unfold initMachine
  dsimp only
  split
  · exact ⟨fun _ h => (by cases h; exact hfail _), fun _ h => (by cases h)⟩
  split
  · exact ⟨fun _ h => (by cases h; exact hfail _), fun _ h => (by cases h)⟩
  split
  · split
    · exact ⟨fun _ h => (by cases h; exact hfail _), fun _ h => (by cases h)⟩
    · rename_i hdep
      have hdep' : accountDeployable w₀ msg.currentTarget = true := by simpa using hdep
      have hf : Fresh w₀ msg.currentTarget := size_code_of_deployable hdep'
      refine ⟨fun _ h => (by cases h), fun m₀ h => ?_⟩
      cases h
      refine ⟨((CodeKept.refl w₀).incrementNonce _).transferValue _,
        frameDel_init (CodeKept.refl w₀) (fun _ => hf), fun _ h => (by cases h), ?_⟩
      intro a ha
      simp only [beginCreate] at ha
      rcases Std.ExtTreeSet.mem_insert.1 ha with ha | ha
      · rw [← Std.LawfulEqCmp.eq_of_compare ha]; exact hf
      · simp at ha
  · split
    · rename_i a _
      refine ⟨fun r h => ?_, fun _ h => (by cases h)⟩
      cases h
      unfold runPrecompile
      dsimp only
      split
      · unfold topLevelResult
        split
        · exact ⟨(CodeKept.refl w₀).transferValue _,
            fun a ha => by simp [Substate.ofMessage] at ha⟩
        · exact ⟨(CodeKept.refl w₀).transferValue _, fun a ha => (by simp at ha)⟩
      · unfold topLevelResult
        split
        · exact ⟨CodeKept.refl w₀, fun a ha => by simp [Substate.ofMessage] at ha⟩
        · exact ⟨CodeKept.refl w₀, fun a ha => (by simp at ha)⟩
    · refine ⟨fun _ h => (by cases h), fun m₀ h => ?_⟩
      cases h
      exact ⟨(CodeKept.refl w₀).transferValue _,
        frameDel_init (CodeKept.refl w₀) (fun h => by cases h), fun _ h => (by cases h),
        fun a ha => (by simp at ha)⟩

/-- **Which accounts a top-level message call deletes**: with `w₀` the world after the
transaction's EIP-7702 delegations, every account scheduled for deletion held no code in `w₀`,
and every account holding code in `w₀` still holds code in the result. -/
theorem processMessageCallWith_del {pre : PrecompileImpl} {fuel : Nat} {ctx : Context}
    {w : World} {tr : TransientStorage} {msg : Message} {r : MessageResult}
    (h : processMessageCallWith pre fuel ctx w tr msg = .ok r) :
    ResultDel (applyTopLevelDelegation ctx pre.isPrecompile w msg).1 r := by
  unfold processMessageCallWith at h
  generalize applyTopLevelDelegation ctx pre.isPrecompile w msg = d at h ⊢
  obtain ⟨w₀, msg', refund⟩ := d
  dsimp only at h ⊢
  have hi := initMachine_del (pre := pre) (ctx := ctx) (w₀ := w₀) (tr := tr) (msg := msg')
  cases hm : initMachine pre ctx w₀ tr msg' with
  | inl r' =>
    rw [hm] at h; cases h
    exact ⟨(hi.1 r' hm).world, (hi.1 r' hm).del⟩
  | inr m₀ =>
    rw [hm] at h
    dsimp only at h
    cases hrun : run fuel m₀ with
    | error e => rw [hrun] at h; cases h
    | ok r' =>
      rw [hrun] at h; cases h
      have := run_del fuel m₀ r' (hi.2 m₀ hm) hrun
      exact ⟨this.world, this.del⟩

theorem processMessageCall_del {fuel : Nat} {ctx : Context} {w : World} {tr : TransientStorage}
    {msg : Message} {r : MessageResult} (h : processMessageCall fuel ctx w tr msg = .ok r) :
    ResultDel (applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg).1 r :=
  processMessageCallWith_del h

/-! ## EIP-7702 delegations keep real code -/

/-- Code that holds bytes and is not an EIP-7702 designator. -/
def RealCode (c : ByteArray) : Prop := c.size ≠ 0 ∧ isValidDelegation c = false

theorem realCode_of_deleg {c : ByteArray} (hs : c.size ≠ 0) (hd : delegatedAddress? c = none) :
    RealCode c := by
  refine ⟨hs, ?_⟩
  unfold delegatedAddress? at hd
  split at hd
  · cases hd
  · rename_i h; simpa using h

theorem validateAuthorization_ne {crypto : Crypto} {chainId : Nat} {w : World}
    {warm warm' : AddressSet} {auth : Authorization} {authority a : Address}
    (h : validateAuthorization crypto chainId w warm auth = (some authority, warm'))
    (ha : RealCode (w.code a)) : authority ≠ a := by
  intro he
  subst he
  unfold validateAuthorization at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  · rename_i auth' hrec
    dsimp only at h
    split at h
    · cases h
    · rename_i hc
      split at h
      · cases h
      · cases h
        apply hc
        simp only [World.code] at ha
        simp [ha.1, ha.2]

/-- **Authorizations keep real code**: an account whose code is not empty and not a delegation
designator cannot be an authority, so its code is unchanged. -/
theorem setDelegation_code {crypto : Crypto} {chainId : Nat} {a : Address} {w : World}
    (ha : RealCode (w.code a)) (auths : List Authorization) (warm : AddressSet) :
    (setDelegation crypto chainId auths w warm).1.code a = w.code a := by
  unfold setDelegation
  suffices H : ∀ (l : List Authorization) (acc : World × AddressSet × Int),
      acc.1.code a = w.code a → (l.foldl (fun (x : World × AddressSet × Int) auth =>
        match validateAuthorization crypto chainId x.1 x.2.1 auth with
        | (none, warm) => (x.1, warm, x.2.2)
        | (some authority, warm) =>
          ((incrementNonce (setCode x.1 authority
              (if auth.address = 0 then .empty else delegationCode auth.address)) authority),
            warm, if x.1.exists authority then
              x.2.2 + ((authPerEmptyAccount - refundAuthPerExistingAccount : Nat) : Int)
            else x.2.2)) acc).1.code a = w.code a from H auths (w, warm, 0) rfl
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons auth l ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    split
    · rename_i hv; exact h
    · rename_i authority warm' hv
      have hne : authority ≠ a := validateAuthorization_ne hv (by rw [h]; exact ha)
      dsimp only
      rw [code_incrementNonce, code_setCode_ne _ _ hne]
      exact h

/-- **The top-level delegations keep real code.** -/
theorem applyTopLevelDelegation_code {ctx : Context} {isPre : Address → Bool} {w : World}
    {msg : Message} {a : Address} (ha : RealCode (w.code a)) :
    (applyTopLevelDelegation ctx isPre w msg).1.code a = w.code a := by
  unfold applyTopLevelDelegation
  split
  · rfl
  · split
    · rfl
    · rfl
    · dsimp only
      split <;> split <;> first | rfl | exact setDelegation_code ha _ _

/-- **A top-level message call never deletes an account holding real code**, and that account
still holds code afterwards (with or without EIP-7702 authorizations). -/
theorem processMessageCall_realCode {fuel : Nat} {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} {r : MessageResult}
    (h : processMessageCall fuel ctx w tr msg = .ok r) {a : Address} (ha : RealCode (w.code a)) :
    a ∉ r.accountsToDelete ∧ (r.world.code a).size ≠ 0 := by
  have hd := processMessageCall_del h
  have hc := applyTopLevelDelegation_code (ctx := ctx)
    (isPre := (PrecompileImpl.standard ctx).isPrecompile) (msg := msg) ha
  have h0 : ((applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w
      msg).1.code a).size ≠ 0 := by rw [hc]; exact ha.1
  exact ⟨fun hm => h0 (hd.del a hm), hd.world a h0⟩

end EvmLogic.Tx
