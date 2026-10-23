import EvmLogic.AbsInt.Effect

/-!
# Guarded abstract interpretation: instruction effects

The shapes of `EvmLogic.AbsInt.Effect`, refined for the instructions the guarded analysis
interprets exactly: comparisons (`EQ`, `ISZERO`, `SUB`), the sender (`CALLER`), storage reads
and writes (`SLOAD`, `SSTORE`), and `JUMPI` with its condition (taken iff nonzero).
`gexec_eff`: whatever `exec op` does, a successful result satisfies `GEffPost (geffOf op)`.
-/

namespace EvmLogic.AbsInt.Guard
open EvmLean EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested EvmLogic.AbsInt

/-- The shape of an instruction, for the guarded analysis. -/
inductive GEff where
  | gen (pops pushes : Nat)
  | halt
  | push (n : Nat)
  | dup (n : Nat)
  | swap (n : Nat)
  | jump
  | jumpi
  | shl
  | sub
  | and
  | eq
  | iszero
  | caller
  | sload
  | sstore
  | call (pops : Nat)
  | create (pops : Nat)
  deriving DecidableEq

/-- The shape of an opcode. -/
def geffOf : Opcode → GEff
  | .stop | .«return» | .revert | .invalid | .selfdestruct => .halt
  | .push n => .push n.val
  | .dup n => .dup n.val
  | .swap n => .swap n.val
  | .jump => .jump
  | .jumpi => .jumpi
  | .shl => .shl
  | .sub => .sub
  | .and => .and
  | .eq => .eq
  | .iszero => .iszero
  | .caller => .caller
  | .sload => .sload
  | .sstore => .sstore
  | .call | .callcode => .call 7
  | .delegatecall | .staticcall => .call 6
  | .create => .create 3
  | .create2 => .create 4
  | .log n => .gen (n.val + 2) 0
  | .add | .mul | .div | .sdiv | .mod | .smod | .exp | .signextend | .lt | .gt | .slt | .sgt
  | .or | .xor | .byte | .shr | .sar | .keccak256 => .gen 2 1
  | .addmod | .mulmod => .gen 3 1
  | .not | .clz | .balance | .calldataload | .extcodesize | .extcodehash
  | .blockhash | .blobhash | .mload | .tload => .gen 1 1
  | .address | .origin | .callvalue | .calldatasize | .codesize | .gasprice
  | .returndatasize | .coinbase | .timestamp | .number | .prevrandao | .gaslimit | .chainid
  | .selfbalance | .basefee | .blobbasefee | .pc | .msize | .gas => .gen 0 1
  | .calldatacopy | .codecopy | .returndatacopy | .mcopy => .gen 3 0
  | .extcodecopy => .gen 4 0
  | .pop => .gen 1 0
  | .mstore | .mstore8 | .tstore => .gen 2 0
  | .jumpdest => .gen 0 0

/-- What a `.next` action of an instruction of shape `e` does to pc and stack. -/
def GNextPost : GEff → Machine → Machine → Prop
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
      ((c ≠ 0 ∧ m'.frame.pc = d.toNat) ∨ (c = 0 ∧ m'.frame.pc = m.frame.pc + 1))
  | .shl, m, m' => m'.frame.pc = m.frame.pc + 1 ∧
      ∃ x y r, m.frame.stack = x :: y :: r ∧ m'.frame.stack = Word.shl x y :: r
  | .sub, m, m' => m'.frame.pc = m.frame.pc + 1 ∧
      ∃ x y r, m.frame.stack = x :: y :: r ∧ m'.frame.stack = (x - y) :: r
  | .and, m, m' => m'.frame.pc = m.frame.pc + 1 ∧
      ∃ x y r, m.frame.stack = x :: y :: r ∧ m'.frame.stack = (x &&& y) :: r
  | .eq, m, m' => m'.frame.pc = m.frame.pc + 1 ∧
      ∃ x y r, m.frame.stack = x :: y :: r ∧ m'.frame.stack = Word.eq x y :: r
  | .iszero, m, m' => m'.frame.pc = m.frame.pc + 1 ∧
      ∃ x r, m.frame.stack = x :: r ∧ m'.frame.stack = Word.iszero x :: r
  | .caller, m, m' => m'.frame.pc = m.frame.pc + 1 ∧
      m'.frame.stack = Word.ofAddress m.frame.msg.caller :: m.frame.stack
  | .sload, m, m' => m'.frame.pc = m.frame.pc + 1 ∧
      ∃ k r, m.frame.stack = k :: r ∧
        m'.frame.stack = m.world.sload m.frame.msg.currentTarget k :: r
  | .sstore, m, m' => m'.frame.pc = m.frame.pc + 1 ∧
      ∃ k v r, m.frame.stack = k :: v :: r ∧ m'.frame.stack = r
  | .call p, m, m' => m'.frame.pc = m.frame.pc + 1 ∧ Shape p 1 m.frame.stack m'.frame.stack
  | .create p, m, m' => m'.frame.pc = m.frame.pc + 1 ∧ Shape p 1 m.frame.stack m'.frame.stack

def GCallPost : GEff → Machine → Machine → Prop
  | .call p, m, m' => Popped p m m'
  | _, _, _ => False

def GCreatePost : GEff → Machine → Machine → Prop
  | .create p, m, m' => Popped p m m'
  | _, _, _ => False

/-- The postcondition of an instruction of shape `e` from `m`. -/
def GEffPost (e : GEff) (m : Machine) : Action → Machine → Prop
  | .next, m' => GNextPost e m m'
  | .call _, m' => GCallPost e m m'
  | .create _, m' => GCreatePost e m m'
  | .stop _, _ => True
  | .revert _, _ => True

set_option maxHeartbeats 1000000 in
theorem gexecCall_eff (k : CallKind) (m : Machine) :
    Wp (execCall k) (GEffPost (.call (callPops k)) m) m := by
  cases k <;> simp [GEffPost, callPops, execCall, memoryExpansion, expandMemory, readMemory,
    setReturnData, genericCall, GNextPost, GCallPost, Popped, Shape] <;>
  intros <;> subst_vars <;> simp_all

set_option maxHeartbeats 1000000 in
theorem gexecCreate_eff (b : Bool) (m : Machine) :
    Wp (execCreate b) (GEffPost (.create (if b then 4 else 3)) m) m := by
  cases b <;> simp [GEffPost, execCreate, requireNonStatic, memoryExpansion, expandMemory,
    readMemory, setReturnData, GNextPost, GCreatePost, Popped, Shape] <;>
  intros <;> subst_vars <;> simp_all

set_option maxHeartbeats 4000000 in
/-- **The stack effect of every instruction.** -/
theorem gexec_eff (op : Opcode) (m : Machine) : Wp (exec op) (GEffPost (geffOf op) m) m := by
  cases op
  case create => exact gexecCreate_eff false m
  case create2 => exact gexecCreate_eff true m
  case call => exact gexecCall_eff .call m
  case callcode => exact gexecCall_eff .callcode m
  case delegatecall => exact gexecCall_eff .delegatecall m
  case staticcall => exact gexecCall_eff .staticcall m
  all_goals simp [GEffPost, geffOf, exec, binOp, unOp, ternOp, pushValue, copyToMemory,
    readOutput, execLog, memoryExpansion, expandMemory, writeMemory, readMemory,
    accessStorageKey, requireNonStatic, execSstore, execSelfdestruct, GNextPost, Shape, wp_popN']
  all_goals (intros; subst_vars; try simp_all)
  case sub | and | shl | eq => exact ⟨_, _, ⟨rfl, rfl⟩, rfl⟩
  case jump => exact ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  case jumpi =>
    exact ⟨fun _ => ⟨_, _, _, ⟨rfl, rfl, rfl⟩, rfl, .inr rfl⟩,
      fun hc _ => ⟨_, _, _, ⟨rfl, rfl, rfl⟩, rfl, .inl ⟨hc, rfl⟩⟩⟩
  case log => omega
  case dup =>
    split
    · simp
    · simp_all [GEffPost, GNextPost]
  case swap =>
    split
    · rename_i t r x hs hx
      simp only [wp_bind, wp_modifyFrame, wp_map, wp_advance, GEffPost, GNextPost]
      exact ⟨trivial, t, r, x, hs, hs ▸ hx, by rw [hs]⟩
    · simp

/-- The shape of a byte (decoded as in the latest fork). -/
def gbyteEff (b : UInt8) : GEff := geffOf (Opcode.decode .osaka b)

/-- **The stack effect of the instruction at a byte**, in every fork. -/
theorem gexec_eff_byte (fork : Fork) (b : UInt8) (m : Machine) :
    Wp (exec (Opcode.decode fork b)) (GEffPost (gbyteEff b) m) m := by
  rcases decode_osaka_or_invalid fork b with h | h <;> rw [h]
  · exact gexec_eff _ m
  · simp [exec]

def gpushWidthOk (b : UInt8) : Bool :=
  match gbyteEff b with
  | .push n => n == GasMono.immSize b
  | _ => true

theorem gpushWidthOk_lt : ∀ k < 256, gpushWidthOk k.toUInt8 = true := by decide +kernel

theorem gbyteEff_push {b : UInt8} {n : Nat} (h : gbyteEff b = .push n) :
    n = GasMono.immSize b := by
  have := gpushWidthOk_lt b.toNat b.toNat_lt
  rw [show b.toNat.toUInt8 = b by simp] at this
  simpa only [gpushWidthOk, h, beq_iff_eq] using this

/-- The shape of the decoded byte is that of the opcode, unless the fork decodes it as
`invalid` (which halts). -/
theorem gbyteEff_sstore {fork : Fork} {b : UInt8} (h : gbyteEff b = .sstore) :
    Opcode.decode fork b = .sstore ∨ Opcode.decode fork b = .invalid := by
  rcases decode_osaka_or_invalid fork b with h' | h'
  · left; rw [h']
    revert h; unfold gbyteEff
    generalize Opcode.decode .osaka b = op
    intro h; cases op <;> simp_all [geffOf]
  · exact .inr h'

end EvmLogic.AbsInt.Guard
