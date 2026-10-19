import EvmLean.Prelude.Word

/-! Unit tests for `EvmLean.Prelude.Word`. -/

open EvmLean

#guard Word.div 5 0 = 0
#guard Word.mod 5 0 = 0
#guard Word.smod (-5) 0 = 0
#guard Word.smod (-7) 2 = -1
#guard Word.smod 7 (-2) = 1
#guard Word.sdiv (BitVec.intMin 256) (-1) = BitVec.intMin 256
#guard Word.sdiv (-7) 2 = -3
#guard Word.sdiv 5 0 = 0
#guard Word.exp 2 255 = BitVec.intMin 256
#guard Word.exp 2 256 = 0
#guard Word.exp 0 0 = 1
#guard Word.addmod (-1) 2 3 = BitVec.ofNat 256 ((2^256 - 1 + 2) % 3)
#guard Word.mulmod (-1) (-1) 7 = BitVec.ofNat 256 (((2^256 - 1) * (2^256 - 1)) % 7)
#guard Word.signextend 0 0xff = -1
#guard Word.signextend 0 0x7f = 0x7f
#guard Word.signextend 31 0x80 = 0x80
#guard Word.signextend 300 0xff = 0xff
#guard Word.byte 31 0x1234 = 0x34
#guard Word.byte 30 0x1234 = 0x12
#guard Word.byte 32 (-1) = 0
#guard Word.shl 1 1 = 2
#guard Word.shl 256 1 = 0
#guard Word.shr 256 (-1) = 0
#guard Word.sar 256 (-1) = -1
#guard Word.sar 300 (BitVec.intMin 256) = -1
#guard Word.sar 1 (-2) = -1
#guard Word.clz 0 = 256
#guard Word.clz 1 = 255
#guard Word.clz (-1) = 0
#guard Word.slt (-1) 0 = 1
#guard Word.sgt (-1) 0 = 0
#guard Word.shl (BitVec.intMin 256) 1 = 0
#guard Word.shr (BitVec.intMin 256) (-1) = 0
#guard Word.sar (BitVec.intMin 256) (-1) = -1
#guard Word.sar (BitVec.intMin 256) 1 = 0
#guard Word.exp 3 (-1) = BitVec.ofNat 256 (Nat.powMod 3 (2^256 - 1) (2^256))
#guard Word.exp 7 3 = 343
