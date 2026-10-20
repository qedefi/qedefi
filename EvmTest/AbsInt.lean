import EvmLogic.AbsInt.Check

/-!
# Tests: the certified abstract interpreter

`certify` on small programs: constant jumps resolve, a jump to an unknown target or a call to a
disallowed target makes the exploration fail, creations are rejected, loops terminate (the
abstract state repeats), and the scan reads `PUSHn` immediates and the listed symbolic
`PUSH32`s.
-/

namespace EvmLeanTest.AbsInt

open EvmLean EvmLean.Program.AbsInt

/-- A code from its bytes. -/
def code (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-- Calls to `0x01` only. -/
def only1 : AVal → Bool
  | .const n => n == 1
  | .sym _ => false
  | .top => false

/-- Calls to the symbolic immutable `0` only. -/
def onlySym : AVal → Bool
  | .sym k => k == 0
  | .const _ => false
  | .top => false

/-- `PUSH1 3 JUMP JUMPDEST STOP`. -/
def jumpCode : ByteArray := code [0x60, 0x03, 0x56, 0x5b, 0x00]

/-- `PUSH0 CALLDATALOAD JUMP`: a jump to an unknown target. -/
def dynJump : ByteArray := code [0x5f, 0x35, 0x56]

/-- `PUSH0 ×4, PUSH1 1, GAS, STATICCALL, STOP`: a call to `0x01`. -/
def callOne : ByteArray := code [0x5f, 0x5f, 0x5f, 0x5f, 0x60, 0x01, 0x5a, 0xfa, 0x00]

/-- `PUSH0 ×3, CREATE, STOP`. -/
def createCode : ByteArray := code [0x5f, 0x5f, 0x5f, 0xf0, 0x00]

/-- A loop: `JUMPDEST PUSH0 POP PUSH0 JUMP` (back to 0). -/
def loopCode : ByteArray := code [0x5b, 0x5f, 0x50, 0x5f, 0x56]

/-- A masked `PUSH32` immutable called: `PUSH0 ×5, PUSH32 i, PUSH1 1 PUSH1 1 PUSH1 0xa0 SHL SUB
AND, GAS, CALL, STOP`. -/
def callSym : ByteArray := code ([0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x7f] ++ List.replicate 32 0xab ++
  [0x60, 0x01, 0x60, 0x01, 0x60, 0xa0, 0x1b, 0x03, 0x16, 0x5a, 0xf1, 0x00])

#guard (certify only1 jumpCode [] [] 100).isSome
#guard (certify only1 dynJump [] [] 100).isNone
#guard (certify only1 callOne [] [] 100).isSome
#guard (certify onlySym callOne [] [] 100).isNone
#guard (certify only1 createCode [] [] 100).isNone
#guard (certify only1 loopCode [] [] 100).isSome
#guard (certify onlySym callSym [(5, 0)] [] 100).isSome
#guard (certify onlySym callSym [] [] 100).isNone
#guard (ascan jumpCode []).map (·.1) = [0, 2, 3, 4]
#guard (ascan callSym [(5, 0)]).map (·.2.2) |>.contains (.sym 0)

/-- The kernel accepts a certificate. -/
example : (certify only1 callOne [] [] 100).isSome = true := by decide +kernel

end EvmLeanTest.AbsInt
