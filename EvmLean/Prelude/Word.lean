/-!
# Machine words

The EVM operates on 256-bit words. We model them as `BitVec 256`, which gives us
Lean core's `BitVec` API and its automation (`bv_decide`, `bv_omega`, `grind`).

Inside `namespace Word`, dot notation on a `Word` resolves to `Word.*` first, so `BitVec`
operations whose names we reuse are called as `BitVec.f x y`.

Where `BitVec` semantics differ from the EVM's we define a wrapper here; every
EVM arithmetic opcode has exactly one definition in this file.

| Opcode       | `BitVec` behaviour         | EVM behaviour              |
|--------------|----------------------------|----------------------------|
| `MOD`        | `x % 0 = x`                | `x % 0 = 0`                |
| `SMOD`       | `x.srem 0 = x`             | `0`                        |
| `EXP`        | `^` iterates `e` times     | `Nat.powMod`               |
| `SHL`        | huge `Nat` amount panics   | clamp to 256               |
| `SIGNEXTEND` | width-changing             | byte-index argument        |
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

/-- `SDIV`: signed division truncating toward zero. `SDIV(-2²⁵⁵, -1) = -2²⁵⁵` and
division by zero yields zero, both exactly as `BitVec.sdiv`. -/
def sdiv (x y : Word) : Word := BitVec.sdiv x y

/-- `SMOD`: signed remainder with the sign of the dividend; modulo zero yields zero. -/
def smod (x y : Word) : Word := if y = 0 then 0 else x.srem y

/-- `ADDMOD`: `(x + y) mod n` without intermediate wrap-around; `n = 0` yields zero. -/
def addmod (x y n : Word) : Word :=
  if n = 0 then 0 else BitVec.ofNat 256 ((x.toNat + y.toNat) % n.toNat)

/-- `MULMOD`: `(x * y) mod n` without intermediate wrap-around; `n = 0` yields zero. -/
def mulmod (x y n : Word) : Word :=
  if n = 0 then 0 else BitVec.ofNat 256 ((x.toNat * y.toNat) % n.toNat)

/-- `EXP`: `b ^ e` modulo `2²⁵⁶`. `Nat.powMod` is square-and-multiply in the kernel and
GMP-backed at runtime (never use `^` on words: it iterates `e` times). -/
def exp (b e : Word) : Word := BitVec.ofNat 256 (Nat.powMod b.toNat e.toNat (2 ^ 256))

/-- `SIGNEXTEND`: extend the sign of byte `b` (counting from the least significant byte).
For `b ≥ 31` the word is unchanged. -/
def signextend (b x : Word) : Word :=
  if b.toNat < 31 then (x.setWidth (8 * (b.toNat + 1))).signExtend 256 else x

/-- `BYTE`: the `i`-th byte of `x`, counting from the most significant byte. -/
def byte (i x : Word) : Word :=
  if i.toNat < 32 then (x >>> (8 * (31 - i.toNat))) &&& 0xff else 0

/-- `SHL`: shift left; shifts of 256 or more yield zero. The amount is clamped first:
shifting by a huge `Nat` panics the runtime. -/
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
