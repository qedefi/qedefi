import Verified.WeirdERC20.YAMV2.Spec.Views
import Verified.WeirdERC20.AMPL.Spec.Transfer

/-!
# YAMv2 under the spec: shared tools

solc 0.6.12 builds its revert reasons in memory: the reason string is copied from the code
(`CODECOPY` of 34 to 40 bytes, a `Memory.write` that is not a whole word) and then
ABI-encoded. The exact-gas stepper (`pwp_xsteps`) computes memory sizes for its gas side
conditions with a fixed simp set that has no rule for the size of such a `write`; the
`pwp_step_ext` rules below step `MLOAD`, `MSTORE`, `KECCAK256`, `LOG3`, `RETURN` and `REVERT`
with a gas discharger
that also knows `Memory.size_write`. They are tried only after the table of `pwp_xsteps`
failed, so they change no other proof.
-/

namespace Verified.WeirdERC20.YAMV2.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.YAMV2.Contracts

/-- The `_allowances` row of `(o, sp)` (slot 2). -/
abbrev allowSlot (crypto : Crypto) (o sp : Address) : Word :=
  mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) 2#256

/-- The `_balances` row of `a` (slot 1). -/
abbrev balSlot (crypto : Crypto) (a : Address) : Word :=
  mappingSlot crypto (Word.ofAddress a) 1#256

/-- An address word is zero only for the zero address. -/
theorem ofAddress_ne_zero {a : Address} (h : a ≠ 0) : Word.ofAddress a ≠ 0 := fun e => h (by
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat e
  have hs : a.toNat < 2 ^ 160 := a.isLt
  simp only [Word.ofAddress, BitVec.toNat_setWidth] at this
  rw [Nat.mod_eq_of_lt (by omega)] at this
  simpa using this)

/-- A word read below a `write` (a `CODECOPY` of a reason string) is the word before it. -/
theorem loadWord_write_of_disjoint (mem : Memory) (off off' : Nat) (data : ByteArray)
    (h : off' + 32 ≤ off ∨ off + data.size ≤ off') :
    (mem.write off data).loadWord off' = mem.loadWord off' := by
  rw [Memory.loadWord, Memory.loadWord, Memory.read_write_of_disjoint mem off off' 32 data h]

/-- A gas side condition over a memory with `write`s of copied code. -/
macro "yam_gas" : tactic => `(tactic| (
  try simp only [memoryCost, outputCost, Gas.extendMemory, List.foldl, Gas.ceil32,
    Gas.memoryCost, Gas.words, Gas.memoryPerWord, Memory.size_storeWord, Memory.size_expand,
    Memory.size_write, size_readBytes, Memory.size_empty, Memory.wordsAfter, Memory.words,
    Gas.logCost, Gas.logBase, Gas.logDataPerByte, Gas.logTopic, Gas.keccak256Cost,
    Gas.keccak256Base, Gas.keccak256PerWord, BitVec.reduceToNat,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceSub, Nat.reduceLeDiff,
    Nat.reduceEqDiff, Nat.max_def, ↓reduceIte]
  evm_gas))

-- `MLOAD` over a memory with `write`s.
macro_rules
  | `(tactic| pwp_step_ext [$extra,*]) => `(tactic| (
    apply WP.of_step
    case h =>
      apply step_mload
      case hcode => pcode_fact
      case hstk => exact rfl
      case hlen => pwp_disch
      case hgas => yam_gas
    case hs => same_frame
    pwp_norm [$extra,*]))

-- `MSTORE` over a memory with `write`s.
macro_rules
  | `(tactic| pwp_step_ext [$extra,*]) => `(tactic| (
    apply WP.of_step
    case h =>
      apply step_mstore
      case hcode => pcode_fact
      case hstk => exact rfl
      case hgas => yam_gas
    case hs => same_frame
    pwp_norm [$extra,*]))

-- `REVERT` over a memory with `write`s.
macro_rules
  | `(tactic| pwp_step_ext [$extra,*]) => `(tactic| (
    apply WP.halt_of_step
    case h =>
      apply step_revert
      case hcode => pcode_fact
      case hstk => exact rfl
      case hgas => yam_gas
    case hs => same_frame
    pwp_norm [$extra,*]))

-- `RETURN` over a memory with `write`s.
macro_rules
  | `(tactic| pwp_step_ext [$extra,*]) => `(tactic| (
    apply WP.halt_of_step
    case h =>
      apply step_return
      case hcode => pcode_fact
      case hstk => exact rfl
      case hgas => yam_gas
    case hs => same_frame
    pwp_norm [$extra,*]))

-- `KECCAK256` over a memory with `write`s.
macro_rules
  | `(tactic| pwp_step_ext [$extra,*]) => `(tactic| (
    apply WP.of_step
    case h =>
      apply step_keccak256
      case hcode => pcode_fact
      case hstk => exact rfl
      case hlen => pwp_disch
      case hgas => yam_gas
    case hs => same_frame
    pwp_norm [$extra,*]))

-- `LOG3` over a memory with `write`s.
macro_rules
  | `(tactic| pwp_step_ext [$extra,*]) => `(tactic| (
    apply WP.of_step
    case h =>
      apply step_log3
      case hcode => pcode_fact
      case hstk => exact rfl
      case hstatic => assumption
      case hgas => yam_gas
    case hs => same_frame
    pwp_norm [$extra,*]))

end Verified.WeirdERC20.YAMV2.Spec
