import EvmLogic.Chain.SystemCode

/-!
# A top-level call of isolated code stays in one frame

A frame running `Isolated` code (`EvmLogic.Chain.SystemCode`: no `GAS`, `CALL`-family,
`CREATE`-family or `SELFDESTRUCT` instruction in the linear decoding) executes only instructions
at boundaries: the pc starts at `0`, moves past one instruction and its immediate, or jumps to a
valid jump destination, which is a boundary (`GasMono.mem_boundaries_of_validJumpDests`). So
it never requests a child: a top-level message call of such code reaches only machines whose
single frame is the call's own (`Lone`, `reaches_lone`). With its target unprotected, no
protected frame ever starts (`reaches_not_dangerStart`), and the frame-summary hypothesis of the
nested simulation (`hsum` of `processMessageCall_good`, `systemCall_good`) holds vacuously.

* `systemCall_good_isolated`: a system call to an unprotected account holding isolated code that
  is not an EIP-7702 designator keeps every `GoodOk` predicate.
* `systemCall_good_systemCode`: the same for a system contract holding its canonical code
  (`systemCode`) or no code at all.
-/

namespace EvmLogic.Chain
open EvmLean EvmLean.Interpreter EvmLean.Block EvmLogic.Program EvmLogic.Program.Nested
  EvmLogic.GasMono

/-! ## The pc stays on instruction boundaries -/

/-- The pc of a frame running `code` is an instruction boundary, or past the end of the code. -/
def PcIn (code : ByteArray) (pc : Nat) : Prop := pc ∈ boundaries code ∨ code.size ≤ pc

theorem pcIn_zero (code : ByteArray) : PcIn code 0 := by
  cases hs : code.size with
  | zero => exact .inr (by omega)
  | succ k => left; simp [boundaries, hs, boundariesFrom_succ]

theorem pcIn_next {code : ByteArray} {pc : Nat} (h : pc ∈ boundaries code) :
    PcIn code (nextPc code pc) := by
  by_cases hn : nextPc code pc < code.size
  · exact .inl (next_mem_boundaries h hn)
  · exact .inr (Nat.le_of_not_lt hn)

/-- **A lone frame**: the only frame of the machine, at `target`, running `code` with its own
jump destinations, at an instruction boundary or past the end. -/
structure Lone (tgt : Address) (c : ByteArray) (m : Machine) : Prop where
  parents : m.parents = []
  target : m.frame.msg.currentTarget = tgt
  code : m.frame.code = c
  jumpDests : m.frame.jumpDests = validJumpDests c
  pc : PcIn c m.frame.pc

variable {target : Address} {code : ByteArray}

/-- **A step of a lone frame running isolated code** stays a lone frame (or ends the call). -/
theorem Lone.of_step (hc : Isolated code) {m m' : Machine} (h : Lone target code m)
    (hst : EvmLean.Interpreter.step m = .running m') : Lone target code m' := by
  unfold EvmLean.Interpreter.step at hst
  by_cases hpc : m.frame.pc < m.frame.code.size
  · simp only [hpc, ↓reduceDIte] at hst
    have hb : m.frame.pc ∈ boundaries code := by
      rcases h.pc with hb | hb
      · exact hb
      · rw [h.code] at hpc; omega
    have hout : outwardB m.frame.code[m.frame.pc] = false := by
      have := hc _ hb
      rw [← h.code, getD_eq_getElem hpc] at this
      exact this
    have hrg := readsGasB_decode_of_not_outward m.ctx.fork hout
    cases he : (exec (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc])).run m with
    | error e =>
      rw [he] at hst; dsimp only at hst
      rw [finishFrame_of_top _ h.parents] at hst; cases hst
    | ok p =>
      obtain ⟨a, m₁⟩ := p
      rw [he] at hst
      have hf := ((exec_frame _ m).of_run he).1.same
      have hnc := (exec_noChild _ hrg m).of_run he
      cases a with
      | next =>
        cases hst
        have hp := (exec_pc _ m).of_run he
        simp only [PcPost, immOf_decode] at hp
        refine ⟨hf.parents.trans h.parents, by rw [hf.msg]; exact h.target,
          hf.code.trans h.code, hf.jumpDests.trans h.jumpDests, ?_⟩
        rcases hp with hp | hp
        · rw [hp, ← getD_eq_getElem hpc, h.code]; exact pcIn_next hb
        · rw [h.jumpDests] at hp; exact .inl (mem_boundaries_of_validJumpDests hp).1
      | stop out =>
        dsimp only at hst; rw [finishFrame_of_top _ (hf.parents.trans h.parents)] at hst; cases hst
      | revert out =>
        dsimp only at hst; rw [finishFrame_of_top _ (hf.parents.trans h.parents)] at hst; cases hst
      | call req => exact hnc.elim
      | create msg => exact hnc.elim
  · simp only [hpc, ↓reduceDIte] at hst
    rw [finishFrame_of_top _ h.parents] at hst; cases hst

theorem Lone.stepN (hc : Isolated code) :
    ∀ (n : Nat) {m m' : Machine}, Lone target code m → stepN n m = .running m' →
      Lone target code m'
  | 0, _, _, h, hst => by simp only [stepN_zero, StepResult.running.injEq] at hst; exact hst ▸ h
  | n + 1, m, m', h, hst => by
    cases hs : EvmLean.Interpreter.step m with
    | done r =>
      rw [show n + 1 = 1 + n by omega, stepN_add_of_done (by rw [stepN_one, hs])] at hst
      cases hst
    | running m₁ =>
      rw [stepN_succ_of_running hs] at hst
      exact Lone.stepN hc n (h.of_step hc hs) hst

/-! ## Top-level calls -/

/-- **Every machine a top-level call of isolated code reaches is a lone frame** at the call's
target. `hdeleg`: no EIP-7702 authorization runs first (true of system calls);
`hcode`: the code is not a delegation designator; `htarget`: a message call, not a creation. -/
theorem reaches_lone {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hcode : delegatedAddress? msg.code = none) (htarget : msg.target = some msg.currentTarget)
    (hc : Isolated msg.code) {m : Machine} (hm : Reaches ctx w tr msg m) :
    Lone msg.currentTarget msg.code m := by
  obtain ⟨m₀, n, hs, hn⟩ := hm
  obtain ⟨msg', hd, -, -, -, -, -, -, hsame⟩ :=
    applyTopLevelDelegation_spec (isPre := (PrecompileImpl.standard ctx).isPrecompile) (w := w)
      (msg := msg) hdeleg
  have hm' : msg' = msg := hsame hcode
  subst hm'
  refine Lone.stepN hc n ?_ hn
  unfold StartsAt at hs
  rw [hd] at hs
  dsimp only at hs
  unfold initMachine at hs
  dsimp only at hs
  split at hs
  · cases hs
  split at hs
  · cases hs
  split at hs
  · rename_i hnone; rw [htarget] at hnone; cases hnone
  · split at hs
    · cases hs
    · cases hs
      exact ⟨rfl, rfl, rfl, rfl, pcIn_zero _⟩

/-- **A top-level call of isolated code at an unprotected account starts no dangerous frame.** -/
theorem reaches_not_dangerStart {P : Address → Prop} {Good : World → Prop} {G : Nat}
    {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hcode : delegatedAddress? msg.code = none) (htarget : msg.target = some msg.currentTarget)
    (hc : Isolated msg.code) (hP : ¬ P msg.currentTarget) {m : Machine}
    (hm : Reaches ctx w tr msg m) : ¬ DangerStart P Good G m := fun hd =>
  hP ((reaches_lone hdeleg hcode htarget hc hm).target ▸ hd.danger.1)

/-- Empty code is isolated: it has no instruction. -/
theorem isolated_of_size_eq_zero {c : ByteArray} (h : c.size = 0) : Isolated c := fun _ hq => by
  have := lt_size_of_mem_boundaries hq; omega

/-! ## System calls -/

/-- **A system contract holding its canonical code, or no code, runs alone**: every machine a
system call to it reaches has a single frame, the call's own, at the system contract. So a
system call starts no frame at any other account, protected or not. -/
theorem reaches_systemMessage {crypto : Crypto} {fork : Fork} {env : BlockEnv} {world : World}
    {target : Address} {data : ByteArray} {m : Machine} (ht : target ∈ systemContracts)
    (hcode : world.code target = systemCode target ∨ (world.code target).size = 0)
    (hm : Reaches (systemContext crypto fork env) world ∅ (systemMessage world target data) m) :
    m.parents = [] ∧ m.frame.msg.currentTarget = target := by
  have hc : delegatedAddress? (world.code target) = none ∧ Isolated (world.code target) := by
    rcases hcode with hc | hc
    · rw [hc]; exact ⟨delegatedAddress?_systemCode _ ht, isolated_systemCode _ ht⟩
    · exact ⟨by rw [byteArray_eq_empty hc]; exact delegatedAddress?_empty,
        isolated_of_size_eq_zero hc⟩
  have hl := reaches_lone (msg := systemMessage world target data) (.inr rfl) hc.1 rfl hc.2 hm
  exact ⟨hl.parents, hl.target⟩

/-- **A system call to isolated code keeps every `GoodOk` predicate**, with no frame summary:
`systemCall_good` whose `hsum` is vacuous. Hypotheses: `SYSTEM_ADDRESS` is not protected (as in
`systemCall_good`), the target is not protected (a protected account's storage may be written
by its own code, so the call must not run at one), its code is isolated and is not an EIP-7702
designator (else another account's code would run). The four system contracts satisfy the last
two when they hold their canonical code (`isolated_systemCode`, `delegatedAddress?_systemCode`). -/
theorem systemCall_good_isolated {P : Address → Prop} {Good : World → Prop} (S : GoodOk P Good)
    (hsys : ¬ P systemAddress) {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {world : World} {target : Address} {data : ByteArray} {w' : World} {res : MessageResult}
    (hw : Good world) (htgt : ¬ P target) (hdel : delegatedAddress? (world.code target) = none)
    (hiso : Isolated (world.code target))
    (h : systemCall fuel crypto fork env world target data = .ok (w', res)) : Good w' :=
  systemCall_good S hsys hw (fun _ hm hd _ =>
    absurd hd (reaches_not_dangerStart (msg := systemMessage world target data) (.inr rfl) hdel rfl
      hiso htgt hm)) h

/-- **A system call to a system contract holding its canonical code, or no code, keeps every
`GoodOk` predicate**: `systemCall_good` with `hsum` replaced by the code of the target.
`hsys`: `SYSTEM_ADDRESS` is not protected; `htgt`: the system contract is not protected (the
call writes its storage). -/
theorem systemCall_good_systemCode {P : Address → Prop} {Good : World → Prop}
    (S : GoodOk P Good)
    (hsys : ¬ P systemAddress) {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {world : World} {target : Address} {data : ByteArray} {w' : World} {res : MessageResult}
    (ht : target ∈ systemContracts) (htgt : ¬ P target) (hw : Good world)
    (hcode : world.code target = systemCode target ∨ (world.code target).size = 0)
    (h : systemCall fuel crypto fork env world target data = .ok (w', res)) : Good w' := by
  rcases hcode with hc | hc
  · exact systemCall_good_isolated S hsys hw htgt (hc ▸ delegatedAddress?_systemCode _ ht)
      (hc ▸ isolated_systemCode _ ht) h
  · exact systemCall_good_of_code_empty S hw hc (isPrecompile_of_mem_systemContracts fork ht) h

end EvmLogic.Chain
