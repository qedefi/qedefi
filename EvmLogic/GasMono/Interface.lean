import EvmLogic.Program.Logic

/-!
# Gas monotonicity: shared interface

Definitions shared by the generic gas-lockstep theorem (`GasMono/Lockstep*.lean`) and the
code-specific facts about the compiled Solmate contracts (`specs/…/Refinement/LowGas*.lean`).

The argument: a frame running code in which `GAS` only ever feeds the gas argument of the
immediately following `CALL`/`STATICCALL` executes in lockstep with the same frame given more
gas (`exec_bump` covers every other instruction), except where a child call fails in the
low-gas run. If, after every call site, a failed call makes the frame revert
(`FailureReverts`), then a *successful* low-gas frame did exactly what the high-gas frame does.

* `boundaries code`: the instruction boundaries, scanning from 0 and skipping `PUSH`
  immediates (the same scan as jump-destination analysis).
* `GasFeedsCall code n`: every `GAS` at a boundary below `n` is immediately followed by `CALL`
  or `STATICCALL`.
* `RegionOk code n`: execution never leaves `[0, n)`: `n - 1` is a boundary holding `INVALID`,
  and every valid jump destination is below `n`. (Solidity appends data after a final
  `INVALID`; it is unreachable.)
* `FailureReverts code p`: from any machine executing `code` at `pc = p` with `0` on top of the
  stack (a failed call's success flag), the frame halts, and not successfully.
-/

namespace EvmLean.Program.GasMono

open Interpreter

/-- Number of immediate bytes following opcode byte `b` (`PUSH1`–`PUSH32`). -/
def immSize (b : UInt8) : Nat := if 0x60 ≤ b.toNat ∧ b.toNat ≤ 0x7f then b.toNat - 0x5f else 0

/-- Instruction boundaries from `p`, with structural fuel. -/
def boundariesFrom (code : ByteArray) : (fuel p : Nat) → List Nat
  | 0, _ => []
  | fuel + 1, p =>
    if p < code.size then p :: boundariesFrom code fuel (p + 1 + immSize (Bytes.getD code p))
    else []

/-- The instruction boundaries of `code` (fuel `code.size` suffices: each step advances). -/
def boundaries (code : ByteArray) : List Nat := boundariesFrom code code.size 0

/-- Every `GAS` (`0x5a`) at a boundary below `n` is immediately followed by `CALL` (`0xf1`) or
`STATICCALL` (`0xfa`). -/
def GasFeedsCall (code : ByteArray) (n : Nat) : Prop :=
  ∀ q ∈ boundaries code, q < n → Bytes.getD code q = 0x5a →
    Bytes.getD code (q + 1) = 0xf1 ∨ Bytes.getD code (q + 1) = 0xfa

instance (code : ByteArray) (n : Nat) : Decidable (GasFeedsCall code n) :=
  inferInstanceAs (Decidable (∀ q ∈ boundaries code, _))

/-- Execution stays in `[0, n)`: `n - 1` is a boundary holding `INVALID` (`0xfe`), and no byte at
or after `n` is a `JUMPDEST` (`0x5b`) at a boundary. -/
def RegionOk (code : ByteArray) (n : Nat) : Prop :=
  0 < n ∧ n - 1 ∈ boundaries code ∧ Bytes.getD code (n - 1) = 0xfe ∧
    ∀ j ∈ boundaries code, n ≤ j → Bytes.getD code j ≠ 0x5b

instance (code : ByteArray) (n : Nat) : Decidable (RegionOk code n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The return points of the calls fed by `GAS` below `n`: `q + 2` for each `GAS` at `q`. -/
def callReturnPoints (code : ByteArray) (n : Nat) : List Nat :=
  (boundaries code).filterMap fun q => if q < n ∧ Bytes.getD code q = 0x5a then some (q + 2) else none

/-- After a failed call returning to `p`, the frame cannot succeed: from any machine executing
`code` at `pc = p` with `0` on top of the stack, the frame halts with a revert or an exceptional
halt. -/
def FailureReverts (code : ByteArray) (p : Nat) : Prop :=
  ∀ m : Machine, m.frame.code = code → m.frame.pc = p → m.frame.stack.head? = some 0 →
    Halts m (fun _ o => ∀ out, o ≠ .success out)

end EvmLean.Program.GasMono
