import EvmLogic.AbsInt.Frame
import EvmLogic.Step.Basic
import EvmLogic.Program.Nested.Run

/-!
# Abstract interpretation: the code of every account during a frame

No instruction changes the code of any account (`exec_code`: `SSTORE` writes storage, value
transfers and `SELFDESTRUCT` move balances — an account whose balance or nonce changes keeps
its code, and an account deleted for being empty had none —, `CREATE` only bumps the
sender's nonce). Code is only deposited by a finished creation frame. So a frame that starts
no creation and whose children keep the code (`frame_code`) runs, from its start to its exit,
in worlds with the code of its starting world.
-/

section

namespace EvmLean.Program.AbsInt

open Interpreter Nested GasMono

/-- Two worlds with the same code at every address. -/
def SameCode (w w' : World) : Prop := ∀ a, w'.code a = w.code a

theorem SameCode.refl (w : World) : SameCode w w := fun _ => rfl

theorem SameCode.trans {w₁ w₂ w₃ : World} (h₁ : SameCode w₁ w₂) (h₂ : SameCode w₂ w₃) :
    SameCode w₁ w₃ := fun a => (h₂ a).trans (h₁ a)

/-- An empty byte array is `.empty`. -/
theorem eq_empty_of_size {b : ByteArray} (h : b.size = 0) : b = .empty :=
  Classical.byContradiction fun hne => size_ne_zero_of_ne_empty hne h

/-- `modifyState` with a function keeping code keeps every account's code. -/
theorem code_modifyState {w : World} {a : Address} {f : Account → Account}
    (hf : ∀ acc, (f acc).code = acc.code) : SameCode w (modifyState w a f) := by
  intro b
  have hs := size_code_modifyState (w := w) (a := a) (b := b) hf
  unfold modifyState World.code at *
  by_cases hab : a = b
  · subst hab
    dsimp only at hs ⊢
    split
    · rename_i he
      simp only [Account.isEmpty, Bool.and_eq_true, decide_eq_true_eq, hf] at he
      have h1 : (World.account (Std.ExtTreeMap.erase w a) a).code = .empty := by
        simp [World.account]
      rw [h1, eq_empty_of_size he.2]
    · simp [World.account, hf]
  · dsimp only
    split <;> simp [World.account, Std.ExtTreeMap.getD_erase, Std.ExtTreeMap.getD_insert, hab]

theorem code_moveEther (w : World) (src dst : Address) (v : Word) :
    SameCode w (moveEther w src dst v) := by
  unfold moveEther
  exact SameCode.trans (code_modifyState (f := fun acc => { acc with balance := acc.balance - v })
    fun _ => rfl) (code_modifyState fun _ => rfl)

theorem code_setAccountBalance (w : World) (a : Address) (v : Word) :
    SameCode w (setAccountBalance w a v) := code_modifyState fun _ => rfl

theorem code_incrementNonce (w : World) (a : Address) : SameCode w (incrementNonce w a) :=
  code_modifyState fun _ => rfl

theorem code_transferValue (w : World) (msg : Message) : SameCode w (transferValue w msg) := by
  unfold transferValue
  split
  · exact code_moveEther _ _ _ _
  · exact SameCode.refl w

theorem code_sstore' (w : World) (a : Address) (k v : Word) : SameCode w (w.sstore a k v) :=
  fun b => World.code_sstore w a k v b

/-- Postcondition: the world's code is unchanged. -/
abbrev CodePost (m : Machine) (_ : Action) (m' : Machine) : Prop := SameCode m.world m'.world

set_option maxHeartbeats 1000000 in
/-- The `CALL` family. -/
theorem execCall_code (k : CallKind) (m : Machine) : Wp (execCall k) (CodePost m) m := by
  cases k <;> simp [CodePost, SameCode.refl, execCall, memoryExpansion, expandMemory,
    readMemory, setReturnData, genericCall]

set_option maxHeartbeats 1000000 in
/-- The `CREATE` family. -/
theorem execCreate_code (b : Bool) (m : Machine) : Wp (execCreate b) (CodePost m) m := by
  cases b <;> simp [CodePost, SameCode.refl, code_incrementNonce, execCreate, requireNonStatic,
    memoryExpansion, expandMemory, readMemory, setReturnData]

set_option maxHeartbeats 4000000 in
/-- **No instruction changes the code of any account.** -/
theorem exec_code (op : Opcode) (m : Machine) : Wp (exec op) (CodePost m) m := by
  cases op
  case create => exact execCreate_code false m
  case create2 => exact execCreate_code true m
  case call => exact execCall_code .call m
  case callcode => exact execCall_code .callcode m
  case delegatecall => exact execCall_code .delegatecall m
  case staticcall => exact execCall_code .staticcall m
  all_goals simp [CodePost, SameCode.refl, exec, binOp, unOp, ternOp, pushValue, copyToMemory,
    readOutput, execLog, memoryExpansion, expandMemory, writeMemory, readMemory,
    accessStorageKey, requireNonStatic, execSstore, execSelfdestruct, setStorage, code_sstore']
  case dup => intro _; split <;> simp [SameCode.refl]
  case swap => intro _; split <;> simp [SameCode.refl]
  case selfdestruct =>
    intro x _ _ _ _
    have h := code_moveEther m.world m.frame.msg.currentTarget (Word.toAddress x)
      (m.world.balance m.frame.msg.currentTarget)
    have h' := h.trans (code_setAccountBalance _ m.frame.msg.currentTarget 0)
    exact ⟨fun _ => ⟨fun _ => h', fun _ => h'⟩, fun _ => ⟨fun _ => h, fun _ => h⟩⟩

/-- **A step staying in the frame keeps the code** (an instruction, or a precompile call: the
value transfer or the rollback). -/
theorem within_code {m m' m₁ : Machine} {b : UInt8} {a : Action}
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m')) (hw : Within m' a m₁) :
    SameCode m.world m₁.world := by
  have h := (exec_code _ m).of_run he
  rcases hw with ⟨-, rfl⟩ | ⟨req, -, hpre, rfl⟩
  · exact h
  · obtain ⟨w, tr, r, hl, hw⟩ := launchCall_some hpre
    rw [hl]
    show SameCode m.world w
    rcases hw with rfl | rfl
    · exact h.trans (code_transferValue _ _)
    · exact h

/-- A pushed call frame starts after the value transfer. -/
theorem pushCall_code (m : Machine) (req : CallRequest) : SameCode m.world (pushCall m req).world :=
  code_transferValue _ _

/-- The world a call frame hands back: its own (success) or its snapshot (failure). -/
theorem resumeAfter_world {p : Frame} {ps : List Frame} {mf : Machine} {o : Outcome}
    {ko ks : Nat} (hk : mf.frame.kind = .call ko ks) :
    (resumeAfter p ps mf o).world = mf.world ∨
      (resumeAfter p ps mf o).world = mf.frame.snapshot.1 := by
  cases o with
  | success out => left; simp [resumeAfter, frameResult, hk, resume]
  | revert out => right; simp [resumeAfter, frameResult, resume]
  | halt e => right; simp [resumeAfter, frameResult, resume]

end EvmLean.Program.AbsInt

end

section

/-!
## Code properties along a whole message call

A property `P` of worlds that depends only on the code (`CodeProp`: invariant under `SameCode`)
and survives the deposit of code that passed the deposit checks (no `0xEF` prefix, EIP-3541)
holds of every world a message call goes through: instructions keep all code (`exec_code`),
value transfers and nonce bumps keep it, a finished creation deposits checked code, and a
failed frame restores a snapshot, which held `P` when it was taken (`AllWorlds`: the current
world and every frame's snapshot). `reaches_allWorlds`: every machine a top-level message call
reaches (`Reaches`, before Prague or without authorizations) satisfies `AllWorlds P` if the
world before the call does.

Instance (`noDesignator`): an account holds no EIP-7702 designator (designators start with
`0xEF`, so no deployed code is one). Only a transaction's authorizations can delegate an
account, and they are applied before the call.
-/

namespace EvmLean.Program.AbsInt

open Interpreter Nested

/-- A property of worlds depending only on their code, kept by checked code deposits. -/
structure CodeProp (P : World → Prop) : Prop where
  /-- Only the code matters. -/
  congr : ∀ {w w' : World}, SameCode w w' → P w → P w'
  /-- Depositing code without the `0xEF` prefix keeps it. -/
  deposit : ∀ {w : World} {a : Address} {out : ByteArray}, ¬ out[0]? = some 0xef → P w →
    P (setCode w a out)

/-- The current world and every frame's rollback snapshot satisfy `P`. -/
def AllWorlds (P : World → Prop) (m : Machine) : Prop :=
  P m.world ∧ ∀ f ∈ m.frame :: m.parents, P f.snapshot.1

variable {P : World → Prop}

/-- A finished frame hands over a world satisfying `P`. -/
theorem frameResult_P (hP : CodeProp P) {mf : Machine} (h : AllWorlds P mf) (o : Outcome) :
    P (frameResult mf o).2.1 := by
  have hs : P mf.frame.snapshot.1 := h.2 _ List.mem_cons_self
  cases o with
  | success out =>
    cases hk : mf.frame.kind with
    | call a b => simpa [frameResult, hk] using h.1
    | create =>
      cases hd : depositCode mf.ctx.fork mf.frame.gasLeft out with
      | ok g =>
        simp only [frameResult, hk, hd]
        refine hP.deposit ?_ h.1
        intro he
        simp [depositCode, he] at hd
      | error e => simpa [frameResult, hk, hd] using hs
  | revert out => simpa [frameResult] using hs
  | halt e => simpa [frameResult] using hs

/-- `finishFrame` keeps `AllWorlds`. -/
theorem finishFrame_allWorlds (hP : CodeProp P) {mf m' : Machine} {o : Outcome}
    (h : AllWorlds P mf) (hst : finishFrame mf o = .running m') : AllWorlds P m' := by
  rw [finishFrame_eq] at hst
  split at hst
  · cases hst
  · rename_i p ps hp
    cases hst
    refine ⟨frameResult_P hP h o, ?_⟩
    have hpar : ∀ f ∈ p :: ps, P f.snapshot.1 := fun f hf =>
      h.2 f (List.mem_cons_of_mem _ (hp ▸ hf))
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact hpar p List.mem_cons_self
    · exact hpar f (List.mem_cons_of_mem _ hf)

/-- An instruction step keeps `AllWorlds`. -/
theorem instr_allWorlds (hP : CodeProp P) {m m' : Machine} {a : Action} {op : Opcode}
    (h : AllWorlds P m) (he : (exec op).run m = .ok (a, m')) : AllWorlds P m' := by
  have hc := (exec_code op m).of_run he
  have hf := ((exec_frame op m).of_run he).1
  refine ⟨hP.congr hc h.1, ?_⟩
  rw [hf.same.parents]
  intro f hf'
  rcases List.mem_cons.1 hf' with rfl | hf'
  · rw [hf.same.snapshot]; exact h.2 _ List.mem_cons_self
  · exact h.2 f (List.mem_cons_of_mem _ hf')

/-- **One step keeps `AllWorlds`.** -/
theorem step_allWorlds (hP : CodeProp P) {m m' : Machine} (h : AllWorlds P m)
    (hst : step m = .running m') : AllWorlds P m' := by
  unfold step at hst
  by_cases hpc : m.frame.pc < m.frame.code.size
  · simp only [hpc, ↓reduceDIte] at hst
    cases he : (exec (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc])).run m with
    | error e => rw [he] at hst; exact finishFrame_allWorlds hP h hst
    | ok p =>
      obtain ⟨a, m₁⟩ := p
      rw [he] at hst
      have h₁ := instr_allWorlds hP h he
      cases a with
      | next => cases hst; exact h₁
      | stop out => exact finishFrame_allWorlds hP h₁ hst
      | revert out => exact finishFrame_allWorlds hP h₁ hst
      | call req =>
        cases hst
        unfold launchCall
        dsimp only
        split
        · unfold runPrecompile
          dsimp only
          split
          · refine ⟨hP.congr (code_transferValue _ _) h₁.1, fun f hf => ?_⟩
            rcases List.mem_cons.1 hf with rfl | hf
            · exact h₁.2 m₁.frame List.mem_cons_self
            · exact h₁.2 f (List.mem_cons_of_mem _ hf)
          · refine ⟨h₁.1, fun f hf => ?_⟩
            rcases List.mem_cons.1 hf with rfl | hf
            · exact h₁.2 m₁.frame List.mem_cons_self
            · exact h₁.2 f (List.mem_cons_of_mem _ hf)
        · refine ⟨hP.congr (code_transferValue _ _) h₁.1, ?_⟩
          intro f hf
          rcases List.mem_cons.1 hf with rfl | hf
          · exact h₁.1
          · exact h₁.2 f hf
      | create msg =>
        cases hst
        unfold launchCreate beginCreate
        dsimp only
        refine ⟨hP.congr ((code_incrementNonce _ _).trans (code_transferValue _ _)) h₁.1, ?_⟩
        intro f hf
        rcases List.mem_cons.1 hf with rfl | hf
        · exact h₁.1
        · exact h₁.2 f hf
  · simp only [hpc, ↓reduceDIte] at hst
    exact finishFrame_allWorlds hP h hst

/-- **Every machine of a run keeps `AllWorlds`.** -/
theorem stepN_allWorlds (hP : CodeProp P) : ∀ (n : Nat) {m m' : Machine}, AllWorlds P m →
    stepN n m = .running m' → AllWorlds P m'
  | 0, _, _, h, hst => by simp only [stepN_zero, StepResult.running.injEq] at hst; exact hst ▸ h
  | n + 1, m, m', h, hst => by
    cases hs : step m with
    | done r =>
      rw [show n + 1 = 1 + n by omega, stepN_add_of_done (by rw [stepN_one, hs])] at hst
      cases hst
    | running m₁ =>
      rw [stepN_succ_of_running hs] at hst
      exact stepN_allWorlds hP n (step_allWorlds hP h hs) hst

/-- Without authorizations to apply, top-level delegation keeps the world. -/
theorem applyTopLevelDelegation_world {ctx : Context} {isPre : Address → Bool} {w : World}
    {msg : Message} (h : ctx.fork < .prague ∨ ctx.tx.authorizations = []) :
    (applyTopLevelDelegation ctx isPre w msg).1 = w := by
  unfold applyTopLevelDelegation
  split
  · rfl
  · rename_i hf
    have hauth : ctx.tx.authorizations = [] := h.resolve_left hf
    split
    · rfl
    · rfl
    · simp only [hauth, List.isEmpty_nil, ↓reduceIte]
      split <;> rfl

/-- **Every machine a top-level message call reaches keeps `AllWorlds`.** -/
theorem reaches_allWorlds (hP : CodeProp P) {ctx : Context} {w : World} {tr : TransientStorage}
    {msg : Message} (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hw : P w)
    {m : Machine} (hm : Reaches ctx w tr msg m) : AllWorlds P m := by
  obtain ⟨m₀, n, hs, hn⟩ := hm
  refine stepN_allWorlds hP n ?_ hn
  unfold StartsAt at hs
  rw [applyTopLevelDelegation_world hdeleg] at hs
  unfold initMachine at hs
  dsimp only at hs
  split at hs
  · cases hs
  split at hs
  · cases hs
  split at hs
  · split at hs
    · cases hs
    · cases hs
      refine ⟨hP.congr ((code_incrementNonce _ _).trans (code_transferValue _ _)) hw, ?_⟩
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf; exact hw
  · split at hs
    · cases hs
    · cases hs
      refine ⟨hP.congr (code_transferValue _ _) hw, ?_⟩
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf; exact hw

/-- Top-level delegation keeps the message's gas. -/
theorem applyTopLevelDelegation_gas (ctx : Context) (isPre : Address → Bool) (w : World)
    (msg : Message) : (applyTopLevelDelegation ctx isPre w msg).2.1.gas = msg.gas := by
  unfold applyTopLevelDelegation
  split
  · rfl
  · split
    · rfl
    · rfl
    · dsimp only
      split <;> split <;> rfl

/-- **The frames a top-level message call reaches hold at most its gas.** -/
theorem Reaches.gas_le {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    {m : Machine} (hm : Reaches ctx w tr msg m) : m.frame.gasLeft ≤ msg.gas := by
  obtain ⟨m₀, n, hs, hn⟩ := hm
  have h0 : m₀.precompiles = PrecompileImpl.standard ctx ∧
      gasSum m₀ = (applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w
        msg).2.1.gas := by
    unfold StartsAt initMachine at hs
    dsimp only at hs
    split at hs
    · cases hs
    split at hs
    · cases hs
    split at hs
    · split at hs
      · cases hs
      · cases hs; exact ⟨rfl, by simp [gasSum, Frame.init]⟩
    · split at hs
      · cases hs
      · cases hs; exact ⟨rfl, by simp [gasSum, Frame.init]⟩
  have hg := stepN_gas (m := m₀) (by rw [h0.1]; exact precompilesOk_standard _) n
  rw [hn, h0.2, applyTopLevelDelegation_gas] at hg
  simp only [resultGas, gasSum] at hg
  omega

/-! ## No designator -/

/-- A designator starts with `0xEF`. -/
theorem getElem?_zero_of_delegated {code : ByteArray} {d : Address}
    (h : delegatedAddress? code = some d) : code[0]? = some 0xef := by
  unfold delegatedAddress? at h
  split at h
  · rename_i hv
    simp only [isValidDelegation, Bool.and_eq_true] at hv
    obtain ⟨hsz, hm⟩ := hv
    have hd : (code.extract 0 3).data = eoaDelegationMarker.data :=
      beq_iff_eq.1 (show ((code.extract 0 3).data == eoaDelegationMarker.data) = true from hm)
    have hsz' : code.size = 23 := by simpa [eoaDelegatedCodeLength] using hsz
    have h0 : Bytes.getD (code.extract 0 3) 0 = 0xef := by
      have : code.extract 0 3 = eoaDelegationMarker := by
        cases h1 : code.extract 0 3; cases h2 : eoaDelegationMarker
        rw [h1, h2] at hd; cases hd; rfl
      rw [this]; rfl
    rw [Bytes.getD_extract] at h0
    simp only [Nat.zero_add] at h0
    have hlt : 0 < code.size := by omega
    rw [getElem?_pos code 0 hlt, ← h0]
    simp [Bytes.getD, hlt]
  · cases h

/-- **The account `a` holds no EIP-7702 designator** (or the fork predates them). -/
def NoDesignator (fork : Fork) (a : Address) (w : World) : Prop :=
  fork < .prague ∨ delegatedAddress? (w.code a) = none

/-- `setCode` elsewhere keeps the code. -/
theorem code_setCode_ne {w : World} {a b : Address} {out : ByteArray} (h : b ≠ a) :
    (setCode w b out).code a = w.code a := by
  unfold setCode modifyState World.code
  dsimp only
  split <;> simp [World.account, Std.ExtTreeMap.getD_erase, Std.ExtTreeMap.getD_insert, h]

/-- `setCode` sets the code (or deletes an account left empty). -/
theorem code_setCode_self (w : World) (a : Address) (out : ByteArray) :
    (setCode w a out).code a = out ∨ (setCode w a out).code a = .empty := by
  unfold setCode modifyState World.code
  dsimp only
  split
  · right; simp [World.account]
  · left; simp [World.account]

/-- No designator is a code property. -/
theorem noDesignator (fork : Fork) (a : Address) : CodeProp (NoDesignator fork a) where
  congr hc h := by unfold NoDesignator; rw [hc a]; exact h
  deposit {w b out} hout h := by
    rcases h with h | h
    · exact .inl h
    · right
      by_cases hba : b = a
      · subst hba
        rcases code_setCode_self w b out with he | he <;> rw [he]
        · cases hd : delegatedAddress? out with
          | none => rfl
          | some d => exact absurd (getElem?_zero_of_delegated hd) hout
        · rfl
      · rw [code_setCode_ne hba]; exact h

end EvmLean.Program.AbsInt

end
