/-!
# Machine words

Words are `BitVec 256`. Every EVM arithmetic opcode has one definition here, wrapping
`BitVec` where semantics differ (`MOD`/`SMOD` by zero, `EXP`, `SHL` clamping, `SIGNEXTEND`).
Inside `namespace Word`, dot notation resolves to `Word.*` first, so reused names are
called as `BitVec.f x y`.
-/

namespace EvmLean

/-- A 256-bit EVM word. -/
abbrev Word := BitVec 256

/-- A 160-bit account address. -/
abbrev Address := BitVec 160

namespace Word

/-- `1` for `true`, `0` for `false`. -/
def ofBool (b : Bool) : Word := if b then 1 else 0

/-- The low 160 bits of a word, as an address. -/
def toAddress (w : Word) : Address := w.setWidth 160

/-- An address, zero-extended to a word. -/
def ofAddress (a : Address) : Word := a.setWidth 256

/-- `DIV`: unsigned division; division by zero yields zero (as for `BitVec`). -/
def div (x y : Word) : Word := x / y

/-- `MOD`: unsigned remainder; modulo zero yields zero. -/
def mod (x y : Word) : Word := if y = 0 then 0 else x % y

/-- `SDIV`: signed, truncating; `SDIV(-2²⁵⁵, -1) = -2²⁵⁵`, `/0 = 0` (as `BitVec.sdiv`). -/
def sdiv (x y : Word) : Word := BitVec.sdiv x y

/-- `SMOD`: signed remainder with the sign of the dividend; modulo zero yields zero. -/
def smod (x y : Word) : Word := if y = 0 then 0 else x.srem y

/-- `ADDMOD`: `(x + y) mod n` without intermediate wrap-around; `n = 0` yields zero. -/
def addmod (x y n : Word) : Word :=
  if n = 0 then 0 else BitVec.ofNat 256 ((x.toNat + y.toNat) % n.toNat)

/-- `MULMOD`: `(x * y) mod n` without intermediate wrap-around; `n = 0` yields zero. -/
def mulmod (x y n : Word) : Word :=
  if n = 0 then 0 else BitVec.ofNat 256 ((x.toNat * y.toNat) % n.toNat)

/-- `EXP`: `b ^ e mod 2²⁵⁶` via `Nat.powMod` (`^` on words iterates `e` times). -/
def exp (b e : Word) : Word := BitVec.ofNat 256 (Nat.powMod b.toNat e.toNat (2 ^ 256))

/-- `SIGNEXTEND`: extend the sign of byte `b` (from the LSB); unchanged for `b ≥ 31`. -/
def signextend (b x : Word) : Word :=
  if b.toNat < 31 then (x.setWidth (8 * (b.toNat + 1))).signExtend 256 else x

/-- `BYTE`: the `i`-th byte of `x`, counting from the most significant byte. -/
def byte (i x : Word) : Word :=
  if i.toNat < 32 then (x >>> (8 * (31 - i.toNat))) &&& 0xff else 0

/-- `SHL`: shifts ≥ 256 yield zero; clamped first since a huge `Nat` shift panics at runtime. -/
def shl (shift x : Word) : Word := if shift.toNat < 256 then x <<< shift.toNat else 0

/-- `SHR`: logical shift right; shifts of 256 or more yield zero. -/
def shr (shift x : Word) : Word := x >>> shift

/-- `SAR`: arithmetic shift right; large shifts yield `0` or `-1` by sign. -/
def sar (shift x : Word) : Word := x.sshiftRight' shift

/-- `LT`. -/
def lt (x y : Word) : Word := ofBool (BitVec.ult x y)
/-- `GT`. -/
def gt (x y : Word) : Word := ofBool (BitVec.ult y x)
/-- `SLT`. -/
def slt (x y : Word) : Word := ofBool (BitVec.slt x y)
/-- `SGT`. -/
def sgt (x y : Word) : Word := ofBool (BitVec.slt y x)
/-- `EQ`. -/
def eq (x y : Word) : Word := ofBool (x == y)
/-- `ISZERO`. -/
def iszero (x : Word) : Word := ofBool (x == 0)

/-- `CLZ` (EIP-7939, Osaka): number of leading zero bits; `256` for zero. -/
def clz (x : Word) : Word :=
  BitVec.ofNat 256 (if x = 0 then 256 else 255 - x.toNat.log2)

end Word

end EvmLean
