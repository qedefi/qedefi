import EvmLeanProofs.Program.NestedExtraGas
import EvmLeanProofs.Program.GasMono.Interface

/-!
# Abstract interpretation: the stack effect of every instruction

The certified abstract interpreter (`AbsInt/*.lean`) tracks, per reachable program point, the
exact stack depth and, for some stack slots, the value (a constant or a symbolic immutable).
Its soundness rests on one theorem about the concrete semantics, proved here once for all
opcodes with the weakest-precondition calculus of `NestedExtraWp`:

* `effOf op`: the shape of `op` (`Eff`): generic (`gen pops pushes`: pops `pops` words,
  pushes `pushes` unknown words, continues at `pc + 1`), halting (never continues), or one of
  the shapes the interpreter tracks precisely (`PUSHn`, `DUPn`, `SWAPn`, `JUMP`, `JUMPI`,
  `SHL`, `SUB`, `AND`, the `CALL` and `CREATE` families).
* `exec_eff`: whatever `exec op` does from `m`, if it succeeds the result satisfies
  `EffPost (effOf op) m`: a `.next` action moves pc and stack as the shape says
  (`NextPost`), a `.call`/`.create` action leaves the frame at the same pc with the arguments
  popped (`ChildPost`), and stops, reverts and exceptional halts constrain nothing.
* `exec_eff_byte`: the same for the decoded byte, for every fork (`decode fork b` is
  `decode .osaka b` or `invalid`, which always halts).
-/

namespace EvmLean.Program.AbsInt

open Interpreter Nested

/-- The shape of an instruction. -/
inductive Eff where
  /-- Pops `pops` words, pushes `pushes` unknown words, continues at `pc + 1`. -/
  | gen (pops pushes : Nat)
  /-- Never continues (`STOP`, `RETURN`, `REVERT`, `INVALID`, `SELFDESTRUCT`). -/
  | halt
  /-- `PUSHn` (`n` immediate bytes). -/
  | push (n : Nat)
  /-- `DUP(n+1)`. -/
  | dup (n : Nat)
  /-- `SWAP(n+1)`. -/
  | swap (n : Nat)
  /-- `JUMP`. -/
  | jump
  /-- `JUMPI`. -/
  | jumpi
  /-- `SHL`. -/
  | shl
  /-- `SUB`. -/
  | sub
  /-- `AND`. -/
  | and
  /-- A member of the `CALL` family, popping `pops` arguments (target second from the top). -/
  | call (pops : Nat)
  /-- A member of the `CREATE` family, popping `pops` arguments. -/
  | create (pops : Nat)

/-- The shape of an opcode. -/
def effOf : Opcode → Eff
  | .stop | .«return» | .revert | .invalid | .selfdestruct => .halt
  | .push n => .push n.val
  | .dup n => .dup n.val
  | .swap n => .swap n.val
  | .jump => .jump
  | .jumpi => .jumpi
  | .shl => .shl
  | .sub => .sub
  | .and => .and
  | .call | .callcode => .call 7
  | .delegatecall | .staticcall => .call 6
  | .create => .create 3
  | .create2 => .create 4
  | .log n => .gen (n.val + 2) 0
  | .add | .mul | .div | .sdiv | .mod | .smod | .exp | .signextend | .lt | .gt | .slt | .sgt
  | .eq | .or | .xor | .byte | .shr | .sar | .keccak256 => .gen 2 1
  | .addmod | .mulmod => .gen 3 1
  | .iszero | .not | .clz | .balance | .calldataload | .extcodesize | .extcodehash
  | .blockhash | .blobhash | .mload | .sload | .tload => .gen 1 1
  | .address | .origin | .caller | .callvalue | .calldatasize | .codesize | .gasprice
  | .returndatasize | .coinbase | .timestamp | .number | .prevrandao | .gaslimit | .chainid
  | .selfbalance | .basefee | .blobbasefee | .pc | .msize | .gas => .gen 0 1
  | .calldatacopy | .codecopy | .returndatacopy | .mcopy => .gen 3 0
  | .extcodecopy => .gen 4 0
  | .pop => .gen 1 0
  | .mstore | .mstore8 | .sstore | .tstore => .gen 2 0
  | .jumpdest => .gen 0 0

/-- The stack `s'` is `s` with `p` words popped and `k` words pushed. -/
def Shape (p k : Nat) (s s' : List Word) : Prop :=
  p ≤ s.length ∧ s'.length + p = s.length + k ∧ s'.drop k = s.drop p

/-- What a `.next` action of an instruction of shape `e` does to pc and stack. -/
def NextPost : Eff → Machine → Machine → Prop
  | .gen p k, m, m' => m'.frame.pc = m.frame.pc + 1 ∧ Shape p k m.frame.stack m'.frame.stack
  | .halt, _, _ => False
  | .push n, m, m' => m'.frame.pc = m.frame.pc + (1 + n) ∧
      m'.frame.stack = Bytes.toWord (readBytes m.frame.code (m.frame.pc + 1) n) :: m.frame.stack
  | .dup n, m, m' => m'.frame.pc = m.frame.pc + 1 ∧
      ∃ x, m.frame.stack[n]? = some x ∧ m'.frame.stack = x :: m.frame.stack
  | .swap n, m, m' => m'.frame.pc = m.frame.pc + 1 ∧
      ∃ t r x, m.frame.stack = t :: r ∧ (t :: r)[n + 1]? = some x ∧
        m'.frame.stack = ((t :: r).set 0 x).set (n + 1) t
  | .jump, m, m' => ∃ d r, m.frame.stack = d :: r ∧ m'.frame.stack = r ∧ m'.frame.pc = d.toNat
  | .jumpi, m, m' => ∃ d c r, m.frame.stack = d :: c :: r ∧ m'.frame.stack = r ∧
      (m'.frame.pc = d.toNat ∨ m'.frame.pc = m.frame.pc + 1)
  | .shl, m, m' => m'.frame.pc = m.frame.pc + 1 ∧
      ∃ x y r, m.frame.stack = x :: y :: r ∧ m'.frame.stack = Word.shl x y :: r
  | .sub, m, m' => m'.frame.pc = m.frame.pc + 1 ∧
      ∃ x y r, m.frame.stack = x :: y :: r ∧ m'.frame.stack = (x - y) :: r
  | .and, m, m' => m'.frame.pc = m.frame.pc + 1 ∧
      ∃ x y r, m.frame.stack = x :: y :: r ∧ m'.frame.stack = (x &&& y) :: r
  | .call p, m, m' => m'.frame.pc = m.frame.pc + 1 ∧ Shape p 1 m.frame.stack m'.frame.stack
  | .create p, m, m' => m'.frame.pc = m.frame.pc + 1 ∧ Shape p 1 m.frame.stack m'.frame.stack

/-- The machine an instruction hands to `step` when it requests a child: same pc, arguments
popped. -/
def Popped (p : Nat) (m m' : Machine) : Prop :=
  m'.frame.pc = m.frame.pc ∧ p ≤ m.frame.stack.length ∧ m'.frame.stack = m.frame.stack.drop p

/-- A `.call` action: only from the `CALL` family. -/
def CallPost : Eff → Machine → Machine → Prop
  | .call p, m, m' => Popped p m m'
  | _, _, _ => False

/-- A `.create` action: only from the `CREATE` family. -/
def CreatePost : Eff → Machine → Machine → Prop
  | .create p, m, m' => Popped p m m'
  | _, _, _ => False

/-- The postcondition of an instruction of shape `e` from `m`. -/
def EffPost (e : Eff) (m : Machine) : Action → Machine → Prop
  | .next, m' => NextPost e m m'
  | .call _, m' => CallPost e m m'
  | .create _, m' => CreatePost e m m'
  | .stop _, _ => True
  | .revert _, _ => True

/-- Arguments popped by a member of the `CALL` family. -/
def callPops : CallKind → Nat
  | .call | .callcode => 7
  | .delegatecall | .staticcall => 6

set_option maxHeartbeats 1000000 in
/-- The `CALL` family. -/
theorem execCall_eff (k : CallKind) (m : Machine) :
    Wp (execCall k) (EffPost (.call (callPops k)) m) m := by
  cases k <;> simp [EffPost, callPops, execCall, memoryExpansion, expandMemory, readMemory,
    setReturnData, genericCall, NextPost, CallPost, Popped, Shape] <;>
  intros <;> subst_vars <;> simp_all

set_option maxHeartbeats 1000000 in
/-- The `CREATE` family. -/
theorem execCreate_eff (b : Bool) (m : Machine) :
    Wp (execCreate b) (EffPost (.create (if b then 4 else 3)) m) m := by
  cases b <;> simp [EffPost, execCreate, requireNonStatic, memoryExpansion, expandMemory,
    readMemory, setReturnData, NextPost, CreatePost, Popped, Shape] <;>
  intros <;> subst_vars <;> simp_all

set_option maxHeartbeats 4000000 in
/-- **The stack effect of every instruction.** -/
theorem exec_eff (op : Opcode) (m : Machine) : Wp (exec op) (EffPost (effOf op) m) m := by
  cases op
  case create => exact execCreate_eff false m
  case create2 => exact execCreate_eff true m
  case call => exact execCall_eff .call m
  case callcode => exact execCall_eff .callcode m
  case delegatecall => exact execCall_eff .delegatecall m
  case staticcall => exact execCall_eff .staticcall m
  all_goals simp [EffPost, effOf, exec, binOp, unOp, ternOp, pushValue, copyToMemory,
    readOutput, execLog, memoryExpansion, expandMemory, writeMemory, readMemory,
    accessStorageKey, requireNonStatic, execSstore, execSelfdestruct, NextPost, Shape, wp_popN']
  all_goals (intros; subst_vars; try simp_all)
  case sub | and | shl => exact ⟨_, _, ⟨rfl, rfl⟩, rfl⟩
  case jump => exact ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  case jumpi => intro _ _; exact ⟨_, _, _, ⟨rfl, rfl, rfl⟩, rfl, .inl rfl⟩
  case log => omega
  case dup =>
    split
    · simp
    · simp_all [EffPost, NextPost]
  case swap =>
    split
    · rename_i t r x hs hx
      simp only [wp_bind, wp_modifyFrame, wp_map, wp_advance, EffPost, NextPost]
      exact ⟨trivial, t, r, x, hs, hs ▸ hx, by rw [hs]⟩
    · simp

/-! ## Bytes -/

/-- Every byte decodes, in every fork, as in Osaka or to `invalid` (only `0x1e`, `CLZ`, is
fork-dependent). -/
theorem decode_osaka_or_invalid_lt : ∀ n < 256, ∀ fork : Fork,
    Opcode.decode fork n.toUInt8 = Opcode.decode .osaka n.toUInt8 ∨
      Opcode.decode fork n.toUInt8 = .invalid := by
  intro n hn fork; cases fork <;> revert n <;> decide +kernel

/-- Every byte decodes, in every fork, as in Osaka or to `invalid`. -/
theorem decode_osaka_or_invalid (fork : Fork) (b : UInt8) :
    Opcode.decode fork b = Opcode.decode .osaka b ∨ Opcode.decode fork b = .invalid := by
  simpa using decode_osaka_or_invalid_lt b.toNat b.toNat_lt fork

/-- The shape of a byte (decoded as in the latest fork). -/
def byteEff (b : UInt8) : Eff := effOf (Opcode.decode .osaka b)

/-- **The stack effect of the instruction at a byte**, in every fork. -/
theorem exec_eff_byte (fork : Fork) (b : UInt8) (m : Machine) :
    Wp (exec (Opcode.decode fork b)) (EffPost (byteEff b) m) m := by
  rcases decode_osaka_or_invalid fork b with h | h <;> rw [h]
  · exact exec_eff _ m
  · simp [exec]

/-- The width of a `PUSHn` shape agrees with `immSize`. -/
def pushWidthOk (b : UInt8) : Bool :=
  match byteEff b with
  | .push n => n == GasMono.immSize b
  | _ => true

/-- `pushWidthOk` holds for every byte. -/
theorem pushWidthOk_lt : ∀ k < 256, pushWidthOk k.toUInt8 = true := by decide +kernel

/-- `PUSHn` bytes push their `immSize` immediate bytes. -/
theorem byteEff_push {b : UInt8} {n : Nat} (h : byteEff b = .push n) : n = GasMono.immSize b := by
  have := pushWidthOk_lt b.toNat b.toNat_lt
  rw [show b.toNat.toUInt8 = b by simp] at this
  simpa only [pushWidthOk, h, beq_iff_eq] using this

/-! ## Call targets -/

/-- What a requested call runs: the code at the target (the second stack item), unless the
target holds an EIP-7702 designator (from Prague). -/
def CallTarget (m : Machine) (req : CallRequest) : Prop :=
  ∃ t, m.frame.stack[1]? = some t ∧
    ((m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress t)) = none) →
      req.msg.codeAddress = some (Word.toAddress t) ∧
      req.msg.code = m.world.code (Word.toAddress t) ∧ req.msg.disablePrecompiles = false)

set_option maxHeartbeats 1000000 in
/-- The target of a member of the `CALL` family. -/
theorem execCall_target (k : CallKind) (m : Machine) :
    Wp (execCall k) (fun a _ => ∀ req, a = .call req → CallTarget m req) m := by
  cases k <;> simp [CallTarget, execCall, memoryExpansion, expandMemory, readMemory,
    setReturnData, genericCall] <;>
  intros <;> subst_vars <;> simp_all

/-- **The target of every requested call.** -/
theorem exec_target (op : Opcode) (m : Machine) :
    Wp (exec op) (fun a _ => ∀ req, a = .call req → CallTarget m req) m := by
  cases op
  case call => exact execCall_target .call m
  case callcode => exact execCall_target .callcode m
  case delegatecall => exact execCall_target .delegatecall m
  case staticcall => exact execCall_target .staticcall m
  all_goals exact (exec_eff _ m).mono fun a m' h req ha => absurd (ha ▸ h) (by simp [EffPost, CallPost, effOf])

end EvmLean.Program.AbsInt
