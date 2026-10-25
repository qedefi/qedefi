import EvmLogic.Program.Nested.Gas
import EvmLogic.GasMono.Exit
import EvmLogic.GasMono.CodeScan

/-!
# Exact at high gas, failing or exact at any gas: a lockstep for gas-blind code

The bytecode spec asks every obligation for **any gas**: with enough gas (`g₀`) the frame ends
exactly as the model says, and with less it may also fail, but never do anything else. A frame
whose code never reads the amount of gas (no `GAS`, no `CALL`/`CREATE` family) does the same
thing with any amount of gas, until it runs out: this file proves that once, for a frame of a
code `c` that agrees with a gas-blind code `c'` on every instruction the frame executes.

* `withCode c m`, `lift c' d m`: the frame `m` running `c'` with `d` more gas, at the top level.
* `exec_withCode`, `exec_withCode_push`: an instruction that reads neither the gas nor the code
  (`codeFree`), or a `PUSH` whose immediate the two codes share, does the same with another
  code; with `exec_bump`, the same with more gas.
* `PatchOk c c' R`: `c'` is `c` with the bytes at the positions `R` replaced by `INVALID`, and no
  instruction of `c'` reads the gas or the code (`goodByte`). For USDT, `R` are the `GAS`/`CALL`
  bytes of the deprecation forwarding (`Patched.lean`, checked in `PatchedFacts.lean`).
* `lockstep`: if the high frame `lift c' d m` reaches (in its own frame) a machine that is not at
  a patched position and whose next instruction ends the frame with `H` (`ExitsWith`), then the
  frame `m` of `c` ends failing (only if `d > 0`) or with `H` of its lifted end. The patched
  positions halt the high frame, so reaching the exit avoids them: the frame of `c` never
  executes a patched byte.
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested EvmLogic.GasMono

/-! ## Running another code -/

/-- The machine `m` with its frame running code `c` (frame and message). -/
def withCode (c : ByteArray) (m : Machine) : Machine :=
  { m with frame := { m.frame with code := c, msg := { m.frame.msg with code := c } } }

/-- The instructions that read neither the gas nor the code (`PUSH` reads its immediate from
the code and is treated apart). -/
def codeFree : Opcode → Bool
  | .gas | .call | .callcode | .delegatecall | .staticcall | .create | .create2 | .codesize
  | .codecopy | .push _ => false
  | _ => true

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
theorem exec_withCode_wp_0 (op : Opcode) (hk : op.ctorIdx ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])
    (hop : codeFree op = true) (m : Machine) (c : ByteArray) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = withCode c m') (withCode c m)) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals first | (exfalso; revert hop; decide) | (simp [codeFree] at hop; done) | skip
  all_goals simp [exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    withCode, execSstore, execSelfdestruct] <;> intros <;> (try simp_all) <;> omega

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
theorem exec_withCode_wp_1 (op : Opcode) (hk : op.ctorIdx ∈ [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23])
    (hop : codeFree op = true) (m : Machine) (c : ByteArray) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = withCode c m') (withCode c m)) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals first | (exfalso; revert hop; decide) | (simp [codeFree] at hop; done) | skip
  all_goals simp [exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    withCode, execSstore, execSelfdestruct] <;> intros <;> (try simp_all) <;> omega

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
theorem exec_withCode_wp_2 (op : Opcode) (hk : op.ctorIdx ∈ [24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35])
    (hop : codeFree op = true) (m : Machine) (c : ByteArray) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = withCode c m') (withCode c m)) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals first | (exfalso; revert hop; decide) | (simp [codeFree] at hop; done) | skip
  all_goals simp [exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    withCode, execSstore, execSelfdestruct] <;> intros <;> (try simp_all) <;> omega

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
theorem exec_withCode_wp_3 (op : Opcode) (hk : op.ctorIdx ∈ [36, 37, 38, 39, 40, 41, 43, 44, 45, 46, 47, 48])
    (hop : codeFree op = true) (m : Machine) (c : ByteArray) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = withCode c m') (withCode c m)) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals first | (exfalso; revert hop; decide) | (simp [codeFree] at hop; done) | skip
  all_goals simp [exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    withCode, execSstore, execSelfdestruct] <;> intros <;> (try simp_all) <;> omega

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
theorem exec_withCode_wp_4 (op : Opcode) (hk : op.ctorIdx ∈ [49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60])
    (hop : codeFree op = true) (m : Machine) (c : ByteArray) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = withCode c m') (withCode c m)) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals first | (exfalso; revert hop; decide) | (simp [codeFree] at hop; done) | skip
  all_goals simp [exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    withCode, execSstore, execSelfdestruct] <;> intros <;> (try simp_all) <;> omega

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
theorem exec_withCode_wp_5 (op : Opcode) (hk : op.ctorIdx ∈ [61, 62, 63, 64, 65, 66, 67, 68, 69, 70])
    (hop : codeFree op = true) (m : Machine) (c : ByteArray) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = withCode c m') (withCode c m)) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals first | (exfalso; revert hop; decide) | (simp [codeFree] at hop; done) | skip
  all_goals simp [exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    withCode, execSstore, execSelfdestruct] <;> intros <;> (try simp_all) <;> omega

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
theorem exec_withCode_wp_6 (op : Opcode) (hk : op.ctorIdx ∈ [74, 75, 76, 77, 78, 79, 80, 81, 82, 83])
    (hop : codeFree op = true) (m : Machine) (c : ByteArray) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = withCode c m') (withCode c m)) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals first | (exfalso; revert hop; decide) | (simp [codeFree] at hop; done) | skip
  all_goals simp [exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    withCode, execSstore, execSelfdestruct] <;> intros <;> (try simp_all) <;> omega

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
theorem exec_withCode_wp_s (op : Opcode) (hk : op.ctorIdx ∈ [42, 71, 72, 73])
    (hop : codeFree op = true) (m : Machine) (c : ByteArray) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = withCode c m') (withCode c m)) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  case dup n =>
    simp [exec, withCode]
    intro _
    split <;> simp <;> intros <;> omega
  case swap n =>
    simp [exec, withCode]
    intro _
    split <;> simp <;> intros <;> omega
  case log n =>
    simp [exec, execLog, withCode, memoryExpansion, expandMemory, requireNonStatic, readMemory]
    intros
    subst_vars
    simp_all
  case returndatacopy =>
    simp [exec, memoryExpansion, expandMemory, writeMemory, withCode]
    intros
    simp_all
    intro hz
    simp only [hz] at *
    exact ⟨by omega, by omega, .inl (by omega)⟩

set_option maxHeartbeats 8000000 in
/-- **An instruction reading neither the gas nor the code** does the same with another code. -/
theorem exec_withCode_wp (op : Opcode) (hop : codeFree op = true) (m : Machine) (c : ByteArray) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = withCode c m') (withCode c m)) m := by
  cases op
  all_goals first
    | (exfalso; revert hop; decide) |
      exact exec_withCode_wp_s _ (by dsimp only [Opcode.ctorIdx]; decide) hop m c |
      exact exec_withCode_wp_0 _ (by dsimp only [Opcode.ctorIdx]; decide) hop m c |
      exact exec_withCode_wp_1 _ (by dsimp only [Opcode.ctorIdx]; decide) hop m c |
      exact exec_withCode_wp_2 _ (by dsimp only [Opcode.ctorIdx]; decide) hop m c |
      exact exec_withCode_wp_3 _ (by dsimp only [Opcode.ctorIdx]; decide) hop m c |
      exact exec_withCode_wp_4 _ (by dsimp only [Opcode.ctorIdx]; decide) hop m c |
      exact exec_withCode_wp_5 _ (by dsimp only [Opcode.ctorIdx]; decide) hop m c |
      exact exec_withCode_wp_6 _ (by dsimp only [Opcode.ctorIdx]; decide) hop m c
    | fail "exec_withCode_wp: no group"

theorem exec_withCode {op : Opcode} (hop : codeFree op = true) {m m' : Machine} {a : Action}
    (h : (exec op).run m = .ok (a, m')) (c : ByteArray) :
    (exec op).run (withCode c m) = .ok (a, withCode c m') := by
  have hw := (exec_withCode_wp op hop m c).of_run h
  unfold Twp at hw
  split at hw
  · rename_i a' m'' he
    obtain ⟨rfl, rfl⟩ := hw
    exact he
  · exact hw.elim

set_option maxHeartbeats 4000000 in
/-- **A `PUSH`** does the same with another code that has the same immediate. -/
theorem exec_withCode_push (n : Fin 33) {m m' : Machine} {a : Action}
    (h : (exec (.push n)).run m = .ok (a, m')) (c : ByteArray)
    (hb : readBytes c (m.frame.pc + 1) n.val = readBytes m.frame.code (m.frame.pc + 1) n.val) :
    (exec (.push n)).run (withCode c m) = .ok (a, withCode c m') := by
  have hw : Wp (exec (.push n)) (fun a m' => Twp (exec (.push n))
      (fun a' m'' => a' = a ∧ m'' = withCode c m') (withCode c m)) m := by
    simp [exec, withCode, hb]
    exact fun h1 h2 => ⟨h1, h2⟩
  have hw := hw.of_run h
  unfold Twp at hw
  split at hw
  · rename_i a' m'' he
    obtain ⟨rfl, rfl⟩ := hw
    exact he
  · exact hw.elim

/-! ## Patched code -/

/-- A byte that does not encode an instruction reading the gas or the code (`GAS`, the
`CALL`/`CREATE` families, `CODESIZE`, `CODECOPY`). -/
def goodByte (b : UInt8) : Bool :=
  !([0x5a, 0xf0, 0xf1, 0xf2, 0xf4, 0xf5, 0xfa, 0x38, 0x39] : List UInt8).contains b

/-- `PUSHn`, as a Boolean. -/
def isPushB : Opcode → Bool
  | .push _ => true
  | _ => false

set_option maxRecDepth 4000 in
theorem goodByte_decode (fork : Fork) (b : UInt8) (h : goodByte b = true) :
    codeFree (Opcode.decode fork b) = true ∨ isPushB (Opcode.decode fork b) = true := by
  have key : ∀ n, n < 256 → goodByte (UInt8.ofNat n) = true →
      codeFree (Opcode.decode fork (UInt8.ofNat n)) = true ∨
        isPushB (Opcode.decode fork (UInt8.ofNat n)) = true := by
    cases fork <;> decide
  have := key b.toNat b.toNat_lt
  rw [UInt8.ofNat_toNat] at this
  exact this h

theorem readsGasB_of_codeFree {op : Opcode} (h : codeFree op = true) : readsGasB op = false := by
  cases op <;> simp_all [codeFree, readsGasB]

theorem not_readsGas_of_readsGasB {op : Opcode} (h : readsGasB op = false) : ¬ ReadsGas op := by
  rw [readsGas_iff, h]; simp

/-- **`c'` is `c` with the bytes at `R` replaced by `INVALID`**, and no instruction of `c'` reads
the gas or the code. The replaced bytes are neither `JUMPDEST` nor `PUSH` (so both codes have
the same instructions and jump destinations) and lie in no `PUSH` immediate of `c'`. -/
structure PatchOk (c c' : ByteArray) (R : List Nat) : Prop where
  size : c'.size = c.size
  same : ∀ i, i ∉ R → Bytes.getD c' i = Bytes.getD c i
  inv : ∀ r ∈ R, Bytes.getD c' r = 0xfe
  orig : ∀ r ∈ R, Bytes.getD c r ≠ 0x5b ∧ (Bytes.getD c r < 0x60 ∨ 0x7f < Bytes.getD c r)
  good : ∀ q ∈ boundaries c', goodByte (Bytes.getD c' q) = true
  imm : ∀ q ∈ boundaries c', ∀ r ∈ R, q < r → q + immSize (Bytes.getD c' q) < r

namespace PatchOk

variable {c c' : ByteArray} {R : List Nat}

theorem jumpDestLoop_eq (hp : PatchOk c c' R) :
    ∀ fuel pc acc, jumpDestLoop c' fuel pc acc = jumpDestLoop c fuel pc acc := by
  intro fuel
  induction fuel with
  | zero => intro pc acc; rfl
  | succ f ih =>
    intro pc acc
    unfold jumpDestLoop
    by_cases hpc : pc < c.size
    · have hpc' : pc < c'.size := by rw [hp.size]; exact hpc
      simp only [hpc, hpc', ↓reduceDIte]
      have hb' := getD_eq_getElem hpc'
      have hb := getD_eq_getElem hpc
      by_cases hR : pc ∈ R
      · have h1 := hp.inv pc hR
        have h2 := hp.orig pc hR
        rw [← hb', ← hb, h1]
        have h3 : ¬ (0x60 ≤ Bytes.getD c pc ∧ Bytes.getD c pc ≤ 0x7f) := by
          rintro ⟨h3, h4⟩
          simp only [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt] at h3 h4 h2
          omega
        simp only [show ¬ ((0xfe : UInt8) = 0x5b) by decide,
          show ¬ ((0x60 : UInt8) ≤ 0xfe ∧ (0xfe : UInt8) ≤ 0x7f) by decide, h2.1, h3, ↓reduceIte]
        exact ih _ _
      · rw [← hb', ← hb, hp.same pc hR]
        split
        · exact ih _ _
        · split <;> exact ih _ _
    · have hpc' : ¬ pc < c'.size := by rw [hp.size]; exact hpc
      simp only [hpc, hpc', ↓reduceDIte]

/-- Both codes have the same jump destinations. -/
theorem jumpDests (hp : PatchOk c c' R) : validJumpDests c' = validJumpDests c := by
  unfold validJumpDests
  rw [hp.size]
  exact hp.jumpDestLoop_eq _ _ _

/-- A `PUSH` of `c'` reads the same immediate in both codes. -/
theorem readBytes_imm (hp : PatchOk c c' R) {q : Nat} (hq : q ∈ boundaries c') :
    readBytes c' (q + 1) (immSize (Bytes.getD c' q)) =
      readBytes c (q + 1) (immSize (Bytes.getD c' q)) := by
  rw [readBytes_eq_readPadded, readBytes_eq_readPadded]
  apply Bytes.ext_getD (by rw [Bytes.size_readPadded, Bytes.size_readPadded])
  intro j hj
  rw [Bytes.size_readPadded] at hj
  simp only [Bytes.getD_readPadded, hj, ↓reduceIte]
  apply hp.same
  intro hR
  have := hp.imm q hq _ hR (by omega)
  omega

end PatchOk

/-! ## The lift -/

/-- **The high frame of `m`**: running `c'`, with `d` more gas (the message's gas raised alike),
at the top level. -/
def lift (c' : ByteArray) (d : Nat) (m : Machine) : Machine :=
  bump d (m.frame.msg.gas + d) [] (withCode c' m)

/-- An instruction at `pc` that `c` and `c'` run alike. -/
def Agrees (c c' : ByteArray) (op : Opcode) (pc : Nat) : Prop :=
  codeFree op = true ∨ ∃ n, op = .push n ∧ readBytes c' (pc + 1) n.val = readBytes c (pc + 1) n.val

theorem Agrees.readsGasB {c c' : ByteArray} {op : Opcode} {pc : Nat} (h : Agrees c c' op pc) :
    readsGasB op = false := by
  rcases h with h | ⟨n, rfl, -⟩
  · exact readsGasB_of_codeFree h
  · rfl

theorem Agrees.symm {c c' : ByteArray} {op : Opcode} {pc : Nat} (h : Agrees c c' op pc) :
    Agrees c' c op pc := by
  rcases h with h | ⟨n, rfl, hn⟩
  · exact .inl h
  · exact .inr ⟨n, rfl, hn.symm⟩

theorem exec_withCode_agrees {c c' : ByteArray} {op : Opcode} {m m' : Machine} {a : Action}
    (hag : Agrees c c' op m.frame.pc) (hc : m.frame.code = c)
    (h : (exec op).run m = .ok (a, m')) : (exec op).run (withCode c' m) = .ok (a, withCode c' m') := by
  rcases hag with hag | ⟨n, rfl, hn⟩
  · exact exec_withCode hag h c'
  · exact exec_withCode_push n h c' (by rw [hc]; exact hn)

/-- **Forward**: what the low frame does, the lifted frame does, lifted. -/
theorem exec_lift {c c' : ByteArray} {op : Opcode} {m m' : Machine} {a : Action}
    (hag : Agrees c c' op m.frame.pc) (hc : m.frame.code = c)
    (h : (exec op).run m = .ok (a, m')) (d : Nat) :
    (exec op).run (lift c' d m) = .ok (a, lift c' d m') := by
  have h1 := exec_withCode_agrees hag hc h
  have h2 := exec_bump op (not_readsGas_of_readsGasB hag.readsGasB) h1 d
    (m.frame.msg.gas + d) []
  have hmsg : m'.frame.msg = m.frame.msg := ((exec_frame op m).of_run h).1.same.msg
  unfold lift
  rw [hmsg]
  exact h2

/-- `lift` with no extra gas is undone by running `c` again with the old message gas and
parents. -/
theorem unlift {c c' : ByteArray} {m : Machine} (hc : m.frame.code = c)
    (hmc : m.frame.msg.code = c) :
    bump 0 m.frame.msg.gas m.parents (withCode c (lift c' 0 m)) = m := by
  obtain ⟨ctx, pre, w, tr, ow, ca, ⟨msg, code, jd, pc, stk, mem, gas, rd, sub, snap, kind⟩, ps⟩ := m
  obtain ⟨caller, target, ct, value, sval, data, mcode, mgas, depth, isStatic, wa, wk, deleg⟩ :=
    msg
  simp only at hc hmc
  subst hc hmc
  rfl

/-- **Backward, with no extra gas**: if the lifted frame's instruction succeeds, so does the low
frame's. -/
theorem exec_unlift {c c' : ByteArray} {op : Opcode} {m x : Machine} {a : Action}
    (hag : Agrees c c' op m.frame.pc) (hc : m.frame.code = c) (hmc : m.frame.msg.code = c)
    (h : (exec op).run (lift c' 0 m) = .ok (a, x)) :
    ∃ m', (exec op).run m = .ok (a, m') := by
  have h1 := exec_withCode_agrees (m := lift c' 0 m) hag.symm rfl h
  have h2 := exec_bump op (not_readsGas_of_readsGasB hag.readsGasB) h1 0 m.frame.msg.gas
    m.parents
  rw [unlift hc hmc] at h2
  exact ⟨_, h2⟩


/-! ## The lockstep -/

/-- The next instruction of `m` ends its frame, from `mf` with outcome `o`, and `H mf o`. -/
def ExitsWith (H : Machine → Outcome → Prop) (m : Machine) : Prop :=
  ∃ mf o, exitOf m = some (mf, o) ∧ H mf o

/-- A frame of `c` the lockstep follows: its code and jump destinations are `c`'s, and it is at
an instruction boundary of `c'` (or past the end). -/
structure Low (c c' : ByteArray) (m : Machine) : Prop where
  code : m.frame.code = c
  msgCode : m.frame.msg.code = c
  jd : m.frame.jumpDests = validJumpDests c
  pc : m.frame.pc ∈ boundaries c' ∨ c'.size ≤ m.frame.pc

theorem exitOf_eq_of_code {m : Machine} {b : UInt8} (hcode : m.frame.code[m.frame.pc]? = some b) :
    exitOf m = match (exec (Opcode.decode m.ctx.fork b)).run m with
      | .error e => some (m, .halt e)
      | .ok (.stop out, m') => some (m', .success out)
      | .ok (.revert out, m') => some (m', .revert out)
      | .ok (.next, _) => none
      | .ok (.call _, _) => none
      | .ok (.create _, _) => none := by
  rw [getElem?_eq_some_iff] at hcode
  obtain ⟨hlt, hb⟩ := hcode
  simp only [exitOf, hlt, dite_true, hb]
  rfl

theorem getElem?_eq_getD {code : ByteArray} {p : Nat} (h : p < code.size) :
    code[p]? = some (Bytes.getD code p) := by
  rw [getD_eq_getElem h]; exact getElem?_pos code p h

@[simp] theorem lift_code (c' : ByteArray) (d : Nat) (m : Machine) :
    (lift c' d m).frame.code = c' := rfl
@[simp] theorem lift_pc (c' : ByteArray) (d : Nat) (m : Machine) :
    (lift c' d m).frame.pc = m.frame.pc := rfl
@[simp] theorem lift_parents (c' : ByteArray) (d : Nat) (m : Machine) :
    (lift c' d m).parents = [] := rfl
@[simp] theorem lift_ctx (c' : ByteArray) (d : Nat) (m : Machine) :
    (lift c' d m).ctx = m.ctx := rfl

variable {c c' : ByteArray} {R : List Nat}

/-- At an instruction the two codes share, the instruction agrees. -/
theorem agrees_at (hp : PatchOk c c' R) {fork : Fork} {pc : Nat} (hbd : pc ∈ boundaries c')
    (hR : pc ∉ R) :
    Agrees c c' (Opcode.decode fork (Bytes.getD c pc)) pc := by
  have hb := hp.same pc hR
  have hg := hp.good pc hbd
  rw [hb] at hg
  rcases goodByte_decode fork _ hg with h | h
  · exact .inl h
  · right
    generalize hop : Opcode.decode fork (Bytes.getD c pc) = op at h
    cases op <;> simp only [isPushB, Bool.false_eq_true] at h
    rename_i n
    refine ⟨n, rfl, ?_⟩
    have himm := immOf_decode fork (Bytes.getD c pc)
    rw [hop] at himm
    simp only [immOf] at himm
    have := hp.readBytes_imm hbd
    rw [hb] at this
    rw [himm]
    exact this

/-- **The last step**: from a low frame whose lift is at its exit (with `H`), the low frame ends
failing (only with more gas in the lift) or with `H` of its lift. -/
theorem lockstep_exit (hp : PatchOk c c' R) {H : Machine → Outcome → Prop}
    (hH : ∀ mf e e', H mf (.halt e) → H mf (.halt e')) {d : Nat} {ml : Machine}
    (hl : Low c c' ml) (hR : ml.frame.pc ∉ R) (hx : ExitsWith H (lift c' d ml)) :
    Halts ml (fun mfl ol => ((∀ out, ol ≠ .success out) ∧ 0 < d) ∨ H (lift c' d mfl) ol) := by
  obtain ⟨mf, o, hex, hHo⟩ := hx
  by_cases hpc : ml.frame.pc < c.size
  · have hpc' : ml.frame.pc < c'.size := by rw [hp.size]; exact hpc
    have hbd : ml.frame.pc ∈ boundaries c' := by
      rcases hl.pc with h | h
      · exact h
      · omega
    have hag := agrees_at hp (fork := ml.ctx.fork) hbd hR
    have hcl : ml.frame.code[ml.frame.pc]? = some (Bytes.getD c ml.frame.pc) := by
      rw [hl.code]; exact getElem?_eq_getD hpc
    have hch : (lift c' d ml).frame.code[(lift c' d ml).frame.pc]? =
        some (Bytes.getD c ml.frame.pc) := by
      rw [lift_code, lift_pc, getElem?_eq_getD hpc', hp.same _ hR]
    rw [exitOf_eq_of_code hch, lift_ctx] at hex
    cases hel : (exec (Opcode.decode ml.ctx.fork (Bytes.getD c ml.frame.pc))).run ml with
    | error e =>
      refine ⟨1, ml, .halt e, by rw [stepN_one, step_eq_of_code hcl, hel], .refl _, ?_⟩
      by_cases hd : 0 < d
      · exact .inl ⟨fun out h => (by cases h), hd⟩
      · have hd0 : d = 0 := by omega
        subst hd0
        cases heh : (exec (Opcode.decode ml.ctx.fork (Bytes.getD c ml.frame.pc))).run
            (lift c' 0 ml) with
        | ok p =>
          obtain ⟨_, h'⟩ := exec_unlift hag hl.code hl.msgCode heh
          rw [hel] at h'; cases h'
        | error e' =>
          rw [heh] at hex
          cases hex
          exact .inr (hH _ _ _ hHo)
    | ok p =>
      obtain ⟨a, ml1⟩ := p
      have heh := exec_lift hag hl.code hel d
      have hfr := ((exec_frame _ ml).of_run hel).1
      rw [heh] at hex
      cases a with
      | next => cases hex
      | stop out =>
        cases hex
        exact ⟨1, ml1, .success out, by rw [stepN_one, step_eq_of_code hcl, hel], hfr.same,
          .inr hHo⟩
      | revert out =>
        cases hex
        exact ⟨1, ml1, .revert out, by rw [stepN_one, step_eq_of_code hcl, hel], hfr.same,
          .inr hHo⟩
      | call req => cases hex
      | create msg => cases hex
  · have hpc' : ¬ ml.frame.pc < c'.size := by rw [hp.size]; exact hpc
    have hex' : exitOf (lift c' d ml) = some (lift c' d ml, .success .empty) := by
      simp only [exitOf, lift_code, lift_pc, hpc', ↓reduceDIte]
    rw [hex'] at hex
    cases hex
    refine ⟨1, ml, .success .empty, ?_, .refl _, .inr hHo⟩
    rw [stepN_one]
    unfold step
    simp only [hl.code, hpc, ↓reduceDIte]


theorem finishFrame_ne_running {m x : Machine} {o : Outcome} (hp : m.parents = []) :
    finishFrame m o ≠ .running x := by
  rw [finishFrame_of_top o hp]; intro h; cases h

/-- **One step in lockstep**: if the lift steps within its frame, the low frame takes the same
step (and stays a `Low` frame), or, with more gas in the lift, fails. -/
theorem lockstep_next (hp : PatchOk c c' R) {d : Nat} {ml x : Machine} (hl : Low c c' ml)
    (hst : step (lift c' d ml) = .running x) :
    (∃ ml1, step ml = .running ml1 ∧ SameFrame ml ml1 ∧ Low c c' ml1 ∧ x = lift c' d ml1) ∨
      (0 < d ∧ Halts ml (fun _ o => ∀ out, o ≠ .success out)) := by
  by_cases hpc : ml.frame.pc < c.size
  · have hpc' : ml.frame.pc < c'.size := by rw [hp.size]; exact hpc
    have hbd : ml.frame.pc ∈ boundaries c' := by
      rcases hl.pc with h | h
      · exact h
      · omega
    by_cases hR : ml.frame.pc ∈ R
    · have hch : (lift c' d ml).frame.code[(lift c' d ml).frame.pc]? = some 0xfe := by
        rw [lift_code, lift_pc, getElem?_eq_getD hpc', hp.inv _ hR]
      rw [step_invalid hch] at hst
      exact absurd hst (finishFrame_ne_running rfl)
    have hag := agrees_at hp (fork := ml.ctx.fork) hbd hR
    have hcl : ml.frame.code[ml.frame.pc]? = some (Bytes.getD c ml.frame.pc) := by
      rw [hl.code]; exact getElem?_eq_getD hpc
    have hch : (lift c' d ml).frame.code[(lift c' d ml).frame.pc]? =
        some (Bytes.getD c ml.frame.pc) := by
      rw [lift_code, lift_pc, getElem?_eq_getD hpc', hp.same _ hR]
    rw [step_eq_of_code hch, lift_ctx] at hst
    cases hel : (exec (Opcode.decode ml.ctx.fork (Bytes.getD c ml.frame.pc))).run ml with
    | error e =>
      by_cases hd : 0 < d
      · exact .inr ⟨hd, 1, ml, .halt e, by rw [stepN_one, step_eq_of_code hcl, hel], .refl _,
          fun out h => by cases h⟩
      · have hd0 : d = 0 := by omega
        subst hd0
        cases heh : (exec (Opcode.decode ml.ctx.fork (Bytes.getD c ml.frame.pc))).run
            (lift c' 0 ml) with
        | ok p =>
          obtain ⟨_, h'⟩ := exec_unlift hag hl.code hl.msgCode heh
          rw [hel] at h'; cases h'
        | error e' =>
          rw [heh] at hst
          exact absurd hst (finishFrame_ne_running rfl)
    | ok p =>
      obtain ⟨a, ml1⟩ := p
      have heh := exec_lift hag hl.code hel d
      have hfr := ((exec_frame _ ml).of_run hel).1
      rw [heh] at hst
      cases a with
      | next =>
        simp only [StepResult.running.injEq] at hst
        refine .inl ⟨ml1, by rw [step_eq_of_code hcl, hel], hfr.same, ?_, hst.symm⟩
        have hpcp := (exec_pc _ ml).of_run hel
        simp only [PcPost, immOf_decode] at hpcp
        refine ⟨hfr.same.code.trans hl.code, by rw [hfr.same.msg]; exact hl.msgCode,
          hfr.same.jumpDests.trans hl.jd, ?_⟩
        rcases hpcp with h | h
        · have hn : ml1.frame.pc = nextPc c' ml.frame.pc := by
            rw [h, nextPc, hp.same _ hR]
          rw [hn]
          by_cases hlt : nextPc c' ml.frame.pc < c'.size
          · exact .inl (next_mem_boundaries hbd hlt)
          · exact .inr (by omega)
        · rw [hl.jd, ← hp.jumpDests] at h
          exact .inl (mem_boundaries_of_validJumpDests h).1
      | stop out => exact absurd hst (finishFrame_ne_running rfl)
      | revert out => exact absurd hst (finishFrame_ne_running rfl)
      | call req =>
        have := (exec_noChild _ hag.readsGasB ml).of_run hel
        exact this.elim
      | create msg =>
        have := (exec_noChild _ hag.readsGasB ml).of_run hel
        exact this.elim
  · have hpc' : ¬ ml.frame.pc < c'.size := by rw [hp.size]; exact hpc
    have : step (lift c' d ml) = finishFrame (lift c' d ml) (.success .empty) := by
      unfold step
      simp only [lift_code, lift_pc, hpc', ↓reduceDIte]
    rw [this] at hst
    exact absurd hst (finishFrame_ne_running rfl)

/-- **The lockstep.** If the lift of a low frame reaches, within its frame, an exit with `H` at
an unpatched position (`H` not distinguishing exceptional halts), the low frame ends failing
(only with more gas in the lift) or with `H` of its lift. -/
theorem lockstep (hp : PatchOk c c' R) {H : Machine → Outcome → Prop}
    (hH : ∀ mf e e', H mf (.halt e) → H mf (.halt e')) (d : Nat) :
    ∀ j ml mh', Low c c' ml → stepN j (lift c' d ml) = .running mh' →
      mh'.frame.pc ∉ R → ExitsWith H mh' →
      Halts ml (fun mfl ol => ((∀ out, ol ≠ .success out) ∧ 0 < d) ∨ H (lift c' d mfl) ol) := by
  intro j
  induction j with
  | zero =>
    intro ml mh' hl hst hR hx
    simp only [stepN_zero, StepResult.running.injEq] at hst
    subst hst
    exact lockstep_exit hp hH hl hR hx
  | succ j ih =>
    intro ml mh' hl hst hR hx
    cases hs : step (lift c' d ml) with
    | done r =>
      rw [stepN_succ_of_done hs] at hst; cases hst
    | running x =>
      rw [stepN_succ_of_running hs] at hst
      rcases lockstep_next hp hl hs with ⟨ml1, hs1, hsf, hl1, rfl⟩ | ⟨hd, hfail⟩
      · exact Halts.of_steps (Steps.of_step hs1 hsf) (ih ml1 mh' hl1 hst hR hx)
      · exact hfail.mono fun _ _ _ h => .inl ⟨h, hd⟩


/-- **The lockstep from a symbolic run of the lift**: a `WP` of the lift that reaches an exit
with `H` at an unpatched position (and never halts otherwise) gives the low frame's end. -/
theorem halts_of_lift (hp : PatchOk c c' R) {H : Machine → Outcome → Prop}
    (hH : ∀ mf e e', H mf (.halt e) → H mf (.halt e')) {d : Nat} {ml : Machine}
    (hl : Low c c' ml)
    (hw : WP (lift c' d ml) (fun mh' => mh'.frame.pc ∉ R ∧ ExitsWith H mh') (fun _ _ => False)) :
    Halts ml (fun mfl ol => ((∀ out, ol ≠ .success out) ∧ 0 < d) ∨ H (lift c' d mfl) ol) := by
  rcases hw with ⟨mh', ⟨j, hj, -⟩, hR, hx⟩ | ⟨_, _, _, _, _, hf⟩
  · exact lockstep hp hH d j ml mh' hl hj hR hx
  · exact hf.elim

end Verified.WeirdERC20.USDT.Spec
