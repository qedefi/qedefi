import EvmLogic.Program.Nested.Gas
import EvmLogic.GasMono.Interface

/-!
# Gas monotonicity: where the program counter can go

The lockstep carries the invariant `PcOk`: the pc is an instruction boundary below the region
end. `exec_pc` gives the pc after every instruction and `pcOk_of_exec` preserves `PcOk`.
`CallsFed` (every `CALL`/`CREATE`-family byte follows a `GAS`) with `GasFeedsCall` makes every
call a `CALL`/`STATICCALL` returning to a point of `callReturnPoints` (`callsFed_call`).
-/

namespace EvmLogic.GasMono
open EvmLean EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested

/-! ## Boundaries -/

/-- The scan's successor of position `p`: past the opcode and its `PUSH` immediate. -/
def nextPc (code : ByteArray) (p : Nat) : Nat := p + 1 + immSize (Bytes.getD code p)

theorem boundariesFrom_succ (code : ByteArray) (f p : Nat) :
    boundariesFrom code (f + 1) p =
      if p < code.size then p :: boundariesFrom code f (nextPc code p) else [] := rfl

theorem boundariesFrom_ge {code : ByteArray} :
    ∀ {fuel p q : Nat}, q ∈ boundariesFrom code fuel p → p ≤ q ∧ q < code.size := by
  intro fuel
  induction fuel with
  | zero => intro p q h; simp [boundariesFrom] at h
  | succ f ih =>
    intro p q h
    rw [boundariesFrom_succ] at h
    split at h
    · rename_i hp
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨Nat.le_refl _, hp⟩
      · have := ih h; unfold nextPc at this; exact ⟨by omega, this.2⟩
    · simp at h

theorem lt_size_of_mem_boundaries {code : ByteArray} {q : Nat} (h : q ∈ boundaries code) :
    q < code.size := (boundariesFrom_ge h).2

theorem next_mem_boundariesFrom {code : ByteArray} :
    ∀ {fuel p q : Nat}, code.size ≤ fuel + p → q ∈ boundariesFrom code fuel p →
      nextPc code q < code.size → nextPc code q ∈ boundariesFrom code fuel p := by
  intro fuel
  induction fuel with
  | zero => intro p q _ h; simp [boundariesFrom] at h
  | succ f ih =>
    intro p q hf h hn
    rw [boundariesFrom_succ] at h ⊢
    split at h
    · rename_i hp
      simp only [hp, ↓reduceIte]
      rcases List.mem_cons.1 h with rfl | h
      · apply List.mem_cons_of_mem
        cases f with
        | zero => unfold nextPc at hn; omega
        | succ f =>
          rw [boundariesFrom_succ]
          simp only [hn, ↓reduceIte]
          exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih (by unfold nextPc; omega) h hn)
    · simp at h

theorem next_mem_boundaries {code : ByteArray} {q : Nat} (h : q ∈ boundaries code)
    (hn : nextPc code q < code.size) : nextPc code q ∈ boundaries code :=
  next_mem_boundariesFrom (by omega) h hn

theorem boundariesFrom_sorted {code : ByteArray} :
    ∀ {fuel p q r : Nat}, q ∈ boundariesFrom code fuel p → r ∈ boundariesFrom code fuel p →
      q < r → nextPc code q ≤ r := by
  intro fuel
  induction fuel with
  | zero => intro p q r h; simp [boundariesFrom] at h
  | succ f ih =>
    intro p q r hq hr hlt
    rw [boundariesFrom_succ] at hq hr
    split at hq
    · rename_i hp
      simp only [hp, ↓reduceIte] at hr
      rcases List.mem_cons.1 hq with rfl | hq <;> rcases List.mem_cons.1 hr with rfl | hr
      · omega
      · exact (boundariesFrom_ge hr).1
      · have := (boundariesFrom_ge hq).1; unfold nextPc at this; omega
      · exact ih hq hr hlt
    · simp at hq

theorem boundaries_sorted {code : ByteArray} {q r : Nat} (hq : q ∈ boundaries code)
    (hr : r ∈ boundaries code) (hlt : q < r) : nextPc code q ≤ r :=
  boundariesFrom_sorted hq hr hlt

theorem getD_eq_getElem {code : ByteArray} {p : Nat} (h : p < code.size) :
    Bytes.getD code p = code[p] := by
  simp [Bytes.getD, h]

theorem jumpDestLoop_mem {code : ByteArray} :
    ∀ {fuel p : Nat} {acc : Array Bool} {i fuel' : Nat}, code.size ≤ fuel' + p →
      (jumpDestLoop code fuel p acc)[i]? = some true →
      acc[i]? = some true ∨ i ∈ boundariesFrom code fuel' p := by
  intro fuel
  induction fuel with
  | zero => intro p acc i fuel' _ h; exact .inl h
  | succ f ih =>
    intro p acc i fuel' hf h
    unfold jumpDestLoop at h
    split at h
    · rename_i hp
      obtain ⟨f', rfl⟩ : ∃ f', fuel' = f' + 1 := ⟨fuel' - 1, by omega⟩
      rw [boundariesFrom_succ]
      simp only [hp, ↓reduceIte]
      have hg := getD_eq_getElem hp
      simp only [] at h
      split at h
      · rename_i h5b
        have hn : nextPc code p = p + 1 := by
          simp only [nextPc, immSize, hg, h5b]
          rfl
        rcases ih (fuel' := f') (by omega) h with h' | h'
        · rw [Array.getElem?_setIfInBounds] at h'
          split at h'
          · subst_vars; exact .inr List.mem_cons_self
          · exact .inl h'
        · rw [← hn] at h'; exact .inr (List.mem_cons_of_mem _ h')
      · split at h
        · rename_i _ hpush
          have hn : nextPc code p = p + 1 + (code[p].toNat - 0x5f) := by
            have : 0x60 ≤ code[p].toNat ∧ code[p].toNat ≤ 0x7f := ⟨hpush.1, hpush.2⟩
            simp only [nextPc, immSize, hg, this, and_self, ↓reduceIte]
          rcases ih (fuel' := f') (by omega) h with h' | h'
          · exact .inl h'
          · rw [← hn] at h'; exact .inr (List.mem_cons_of_mem _ h')
        · rename_i _ hpush
          have hn : nextPc code p = p + 1 := by
            have : ¬ (0x60 ≤ code[p].toNat ∧ code[p].toNat ≤ 0x7f) :=
              fun hc => hpush ⟨hc.1, hc.2⟩
            simp only [nextPc, immSize, hg, this, ↓reduceIte, Nat.add_zero]
          rcases ih (fuel' := f') (by omega) h with h' | h'
          · exact .inl h'
          · rw [← hn] at h'; exact .inr (List.mem_cons_of_mem _ h')
    · exact .inl h

theorem mem_boundaries_of_validJumpDests {code : ByteArray} {i : Nat}
    (h : isValidJumpDest (validJumpDests code) i = true) :
    i ∈ boundaries code ∧ Bytes.getD code i = 0x5b := by
  have h' : (validJumpDests code)[i]? = some true := by
    unfold isValidJumpDest at h
    cases hi : (validJumpDests code)[i]? with
    | none => rw [hi] at h; cases h
    | some b => rw [hi] at h; simp at h; rw [h]
  refine ⟨?_, ?_⟩
  · rcases jumpDestLoop_mem (fuel' := code.size) (by omega) h' with h'' | h''
    · simp [Array.getElem?_replicate] at h''
    · exact h''
  · have := validJumpDests_true code i h'
    rw [getElem?_eq_some_iff] at this
    obtain ⟨hi, hb⟩ := this
    rw [getD_eq_getElem hi, hb]

/-! ## Opcodes -/

/-- Length of the immediate of an opcode (`PUSHn`: `n`). -/
def immOf : Opcode → Nat
  | .push n => n.val
  | _ => 0

/-- `ReadsGas` as a Boolean. -/
def readsGasB : Opcode → Bool
  | .gas | .call | .callcode | .delegatecall | .staticcall | .create | .create2 => true
  | _ => false

theorem readsGas_iff (op : Opcode) : ReadsGas op ↔ readsGasB op = true := by
  cases op <;> simp [ReadsGas, readsGasB]

set_option maxRecDepth 4000 in
theorem immOf_decode (fork : Fork) (b : UInt8) : immOf (Opcode.decode fork b) = immSize b := by
  have key : ∀ n, n < 256 → immOf (Opcode.decode fork (UInt8.ofNat n)) = immSize (UInt8.ofNat n) := by
    cases fork <;> decide
  have := key b.toNat b.toNat_lt
  rwa [UInt8.ofNat_toNat] at this

set_option maxRecDepth 4000 in
theorem readsGas_decode (fork : Fork) (b : UInt8) (h : readsGasB (Opcode.decode fork b) = true) :
    b = 0x5a ∨ b = 0xf0 ∨ b = 0xf1 ∨ b = 0xf2 ∨ b = 0xf4 ∨ b = 0xf5 ∨ b = 0xfa := by
  have key : ∀ n, n < 256 → readsGasB (Opcode.decode fork (UInt8.ofNat n)) = true →
      UInt8.ofNat n = 0x5a ∨ UInt8.ofNat n = 0xf0 ∨ UInt8.ofNat n = 0xf1 ∨ UInt8.ofNat n = 0xf2 ∨
        UInt8.ofNat n = 0xf4 ∨ UInt8.ofNat n = 0xf5 ∨ UInt8.ofNat n = 0xfa := by
    cases fork <;> decide
  have := key b.toNat b.toNat_lt
  rw [UInt8.ofNat_toNat] at this
  exact this h

/-! ## The pc after an instruction -/

/-- Where an instruction leaves the pc: `Action.next` moves it past the instruction (and its
immediate) or to a valid jump destination; a call or creation request leaves it (`resume`
advances it after the child). -/
def PcPost (op : Opcode) (m : Machine) : Action → Machine → Prop
  | .next, m' => m'.frame.pc = m.frame.pc + 1 + immOf op ∨
      isValidJumpDest m.frame.jumpDests m'.frame.pc = true
  | .call _, m' => m'.frame.pc = m.frame.pc
  | .create _, m' => m'.frame.pc = m.frame.pc
  | .stop _, _ => True
  | .revert _, _ => True

set_option maxHeartbeats 4000000 in
/-- **The pc after every instruction.** -/
theorem exec_pc (op : Opcode) (m : Machine) : Wp (exec op) (PcPost op m) m := by
  cases op
  all_goals simp [PcPost, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    execSstore, execSelfdestruct, execCall, execCreate, genericCall, setReturnData, immOf]
  case jump => intros; right; assumption
  case jumpi => intros; right; assumption
  case push => intros; left; omega
  case dup => intro _; split <;> simp [PcPost, immOf]
  case swap => intro _; split <;> simp [PcPost, immOf]

/-- The instructions that do not read the gas never request a child. -/
def NoChild : Action → Prop
  | .next | .stop _ | .revert _ => True
  | .call _ | .create _ => False

set_option maxHeartbeats 4000000 in
/-- **Only the `CALL` and `CREATE` families start children.** -/
theorem exec_noChild (op : Opcode) (hop : readsGasB op = false) (m : Machine) :
    Wp (exec op) (fun a _ => NoChild a) m := by
  cases op
  all_goals first
    | (simp [readsGasB] at hop; done)
    | (simp [NoChild, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
        memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
        execSstore, execSelfdestruct])
  case dup => intro _; split <;> simp
  case swap => intro _; split <;> simp

/-! ## The pc invariant -/

/-- The pc is an instruction boundary inside the region `[0, n)`. -/
def PcOk (code : ByteArray) (n pc : Nat) : Prop := pc ∈ boundaries code ∧ pc < n

theorem RegionOk.lt_size {code : ByteArray} {n : Nat} (h : RegionOk code n) :
    n - 1 < code.size := lt_size_of_mem_boundaries h.2.1

theorem PcOk.lt_size {code : ByteArray} {n pc : Nat} (h : PcOk code n pc) : pc < code.size :=
  lt_size_of_mem_boundaries h.1

theorem pcOk_next {code : ByteArray} {n pc pc' : Nat} (hreg : RegionOk code n)
    (hpc : PcOk code n pc) (hb : Bytes.getD code pc ≠ 0xfe)
    (h : pc' = nextPc code pc ∨ isValidJumpDest (validJumpDests code) pc' = true) :
    PcOk code n pc' := by
  obtain ⟨hn0, hlast, hinv, hjd⟩ := hreg
  rcases h with rfl | h
  · have hne : pc ≠ n - 1 := by rintro rfl; exact hb hinv
    have hle := boundaries_sorted hpc.1 hlast (by have := hpc.2; omega)
    have hsz := lt_size_of_mem_boundaries hlast
    exact ⟨next_mem_boundaries hpc.1 (by omega), by omega⟩
  · obtain ⟨hm, h5b⟩ := mem_boundaries_of_validJumpDests h
    exact ⟨hm, Nat.lt_of_not_le (fun hge => hjd pc' hm hge h5b)⟩

theorem exec_invalid_run (fork : Fork) (m : Machine) :
    (exec (Opcode.decode fork 0xfe)).run m = .error .invalidOpcode := by
  cases fork <;> rfl

/-- **The pc invariant after an instruction of the frame** that continues. -/
theorem pcOk_of_exec {code : ByteArray} {n : Nat} (hreg : RegionOk code n) {m m' : Machine}
    (hc : m.frame.code = code) (hj : m.frame.jumpDests = validJumpDests code)
    (hpc : PcOk code n m.frame.pc) (hlt : m.frame.pc < m.frame.code.size)
    (h : (exec (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc])).run m = .ok (.next, m')) :
    PcOk code n m'.frame.pc := by
  have hpost := (exec_pc _ m).of_run h
  simp only [PcPost, immOf_decode] at hpost
  have hg : Bytes.getD code m.frame.pc = m.frame.code[m.frame.pc] := by
    subst hc; exact getD_eq_getElem hlt
  refine pcOk_next hreg hpc ?_ ?_
  · rw [hg]
    intro h5
    rw [h5, exec_invalid_run] at h
    cases h
  · rcases hpost with h1 | h1
    · left; rw [h1, nextPc, hg]
    · right; rw [← hj]; exact h1

theorem pcOk_return {code : ByteArray} {n pc : Nat} (hreg : RegionOk code n)
    (hpc : PcOk code n pc) (hb : Bytes.getD code pc = 0xf1 ∨ Bytes.getD code pc = 0xfa) :
    PcOk code n (pc + 1) := by
  refine pcOk_next hreg hpc (by rcases hb with h | h <;> rw [h] <;> decide) (.inl ?_)
  rcases hb with h | h <;> simp only [nextPc, immSize, h] <;> rfl

/-! ## Calls fed by `GAS` -/

/-- The bytes of the `CALL` and `CREATE` families. -/
def IsCallByte (b : UInt8) : Prop :=
  b = 0xf0 ∨ b = 0xf1 ∨ b = 0xf2 ∨ b = 0xf4 ∨ b = 0xf5 ∨ b = 0xfa

instance (b : UInt8) : Decidable (IsCallByte b) := inferInstanceAs (Decidable (_ ∨ _))

/-- Every `CALL`-family or `CREATE`-family byte at a boundary below `n` immediately follows a
`GAS` at a boundary. -/
def CallsFed (code : ByteArray) (n : Nat) : Prop :=
  ∀ q ∈ boundaries code, q < n → IsCallByte (Bytes.getD code q) →
    0 < q ∧ q - 1 ∈ boundaries code ∧ Bytes.getD code (q - 1) = 0x5a

instance (code : ByteArray) (n : Nat) : Decidable (CallsFed code n) :=
  inferInstanceAs (Decidable (∀ q ∈ boundaries code, _))

/-- **A call in the region** is a `CALL` or `STATICCALL` returning to a point of
`callReturnPoints`. -/
theorem callsFed_call {code : ByteArray} {n q : Nat} (hfeed : GasFeedsCall code n)
    (hcf : CallsFed code n) (hq : q ∈ boundaries code) (hqn : q < n)
    (hb : IsCallByte (Bytes.getD code q)) :
    (Bytes.getD code q = 0xf1 ∨ Bytes.getD code q = 0xfa) ∧ q + 1 ∈ callReturnPoints code n := by
  obtain ⟨h0, hm, hg⟩ := hcf q hq hqn hb
  have := hfeed (q - 1) hm (by omega) hg
  rw [show q - 1 + 1 = q by omega] at this
  refine ⟨this, ?_⟩
  unfold callReturnPoints
  rw [List.mem_filterMap]
  exact ⟨q - 1, hm, by
    simp only [show q - 1 < n by omega, hg, and_self, ↓reduceIte, Option.some.injEq]; omega⟩

end EvmLogic.GasMono
