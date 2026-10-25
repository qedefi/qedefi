import QEDefi.ERC20.Spec.Storage
import QEDefi.ERC20.Spec.Instances.Solady
import Verified.Solady.Contracts.SoladyToken

/-!
# Solady `ERC20` under the ERC-20 spec: the abstraction and the statement

`soladySpec : Prop` is `ERC20Spec` for the compiled `SoladyToken` (`runtimeCode`, no
immutables) against `soladyModel PERMIT2` (`QEDefi.ERC20.Spec.Instances.Solady`), through
`soladyAbs`.

**Storage** (Solady's inline-assembly layout, no Solidity state variables). The rows are hashed
from one word `o₂₀ ‖ 0⁸ ‖ seed₄` (the owner's 20 bytes, 8 zero bytes, a 4-byte seed), which the
code assembles in scratch memory:

* `totalSupply` at the constant slot `0x05345cdf77eb68f44c` (`supplySlot`);
* `balanceOf(o)` at `keccak256(o ‖ 0⁸ ‖ 0x87a211a2)` (`balSlot`, 32 bytes);
* `allowance(o, sp)` at `keccak256(o ‖ 0⁸ ‖ 0x7f5e9f20 ‖ sp)` (`allowSlot`, 52 bytes);
* `nonces(o)` at `keccak256(o ‖ 0⁸ ‖ 0x38377508)` (`nonceSlot`).

The read functions are Solady's own (not `readMap`, which is Solidity's `keccak(pad(k) ‖ p)`).
The model fields the token does not have are constants (`scale = 1`, no admin, nothing paused,
blacklisted or frozen, no fee); `ether` is the token's ether balance (it never changes: every
entry point is non-payable).

**Hash hypotheses** (`SoladySound`): distinct addresses have distinct balance rows and distinct
nonce rows, and the four families (balance rows, nonce rows, allowance rows, the supply slot)
are pairwise disjoint. They concern `2 · 2¹⁶⁰` 32-byte preimages that must hash injectively,
outside the supply slot and the image of the `2³²⁰` allowance preimages: some `Crypto`
satisfies all of them (map the address-keyed preimages injectively into a set of `2¹⁶¹` slots
and every other input outside it), and Keccak is believed to. Injectivity of the allowance rows
is **not** assumed: by pigeonhole no `Crypto` has it (`2³²⁰` pairs, `2²⁵⁶` slots).
-/

namespace Verified.Solady.Spec
open EvmLean EvmLogic EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec
open QEDefi.ERC20.Spec.Solady EvmLean.Interpreter Verified.Solady.Contracts

/-! ## Layout -/

/-- Solady's hardcoded Permit2 (`_PERMIT2`). -/
def PERMIT2 : Address := 0x000000000022D473030F116dDEE9F6B43aC78BA3

/-- `_TOTAL_SUPPLY_SLOT`. -/
def supplySlot : Word := 0x05345cdf77eb68f44c

/-- `_BALANCE_SLOT_SEED`. -/
def balSeed : Word := 0x87a211a2

/-- `_ALLOWANCE_SLOT_SEED`. -/
def allowSeed : Word := 0x7f5e9f20

/-- `_NONCES_SLOT_SEED`. -/
def nonceSeed : Word := 0x38377508

/-- The word `o₂₀ ‖ 0⁸ ‖ seed₄` (`or(shl(96, o), seed)`). -/
def rowWord (o : Address) (seed : Word) : Word := (Word.ofAddress o <<< 96) ||| seed

/-- The slot of `balanceOf(o)`. -/
def balSlot (crypto : Crypto) (o : Address) : Word :=
  crypto.keccak256 (Bytes.ofWord (rowWord o balSeed))

/-- The slot of `allowance(o, sp)` (52 bytes: the row word, then the spender's 20 bytes). -/
def allowSlot (crypto : Crypto) (o sp : Address) : Word :=
  crypto.keccak256 (Bytes.ofWord (rowWord o allowSeed) ++ Bytes.ofAddress sp)

/-- The slot of `nonces(o)`. -/
def nonceSlot (crypto : Crypto) (o : Address) : Word :=
  crypto.keccak256 (Bytes.ofWord (rowWord o nonceSeed))

/-! ## The abstraction -/

/-- The balances, as a finitely supported function. -/
noncomputable def balances (crypto : Crypto) (w : World) (token : Address) : Address →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun a => (w.sload token (balSlot crypto a)).toNat

/-- The nonces, as a finitely supported function. -/
noncomputable def nonceMap (crypto : Crypto) (w : World) (token : Address) : Address →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun a => (w.sload token (nonceSlot crypto a)).toNat

/-- The model state of the Solady token at `token`. -/
noncomputable def read (crypto : Crypto) (w : World) (token : Address) : VState Address where
  self := token
  bal := balances crypto w token
  supply := readSlot w token supplySlot
  allowance o sp := (w.sload token (allowSlot crypto o sp)).toNat
  scale := 1
  admin := 0
  paused := false
  blacklisted _ := false
  feeBps := 0
  feeMax := 0
  ether := (w.balance token).toNat
  frozen := 0
  nonces := nonceMap crypto w token

/-- The slots `read` depends on. -/
def Footprint (crypto : Crypto) (k : Word) : Prop :=
  k = supplySlot ∨ (∃ a, k = balSlot crypto a) ∨ (∃ o sp, k = allowSlot crypto o sp) ∨
    ∃ a, k = nonceSlot crypto a

/-- **The hash hypotheses** (see the module docstring for why they are satisfiable). -/
structure SoladySound (crypto : Crypto) : Prop where
  /-- Distinct addresses have distinct balance rows. -/
  bal_inj : ∀ a b, balSlot crypto a = balSlot crypto b → a = b
  /-- Distinct addresses have distinct nonce rows. -/
  nonce_inj : ∀ a b, nonceSlot crypto a = nonceSlot crypto b → a = b
  /-- No balance row is a nonce row. -/
  bal_nonce : ∀ a b, balSlot crypto a ≠ nonceSlot crypto b
  /-- No balance row is the supply slot. -/
  bal_supply : ∀ a, balSlot crypto a ≠ supplySlot
  /-- No nonce row is the supply slot. -/
  nonce_supply : ∀ a, nonceSlot crypto a ≠ supplySlot
  /-- No allowance row is a balance row. -/
  allow_bal : ∀ o sp a, allowSlot crypto o sp ≠ balSlot crypto a
  /-- No allowance row is a nonce row. -/
  allow_nonce : ∀ o sp a, allowSlot crypto o sp ≠ nonceSlot crypto a
  /-- No allowance row is the supply slot. -/
  allow_supply : ∀ o sp, allowSlot crypto o sp ≠ supplySlot

theorem read_congr (crypto : Crypto) (w w' : World) (token : Address)
    (h : ∀ k, Footprint crypto k → w'.sload token k = w.sload token k)
    (hb : w'.balance token = w.balance token) : read crypto w' token = read crypto w token := by
  have hbal : ∀ a, w'.sload token (balSlot crypto a) = w.sload token (balSlot crypto a) :=
    fun a => h _ (.inr (.inl ⟨a, rfl⟩))
  have hnon : ∀ a, w'.sload token (nonceSlot crypto a) = w.sload token (nonceSlot crypto a) :=
    fun a => h _ (.inr (.inr (.inr ⟨a, rfl⟩)))
  have hall : ∀ o sp, w'.sload token (allowSlot crypto o sp) =
      w.sload token (allowSlot crypto o sp) := fun o sp => h _ (.inr (.inr (.inl ⟨o, sp, rfl⟩)))
  have hsup : readSlot w' token supplySlot = readSlot w token supplySlot :=
    readSlot_congr (h _ (.inl rfl))
  simp only [read, balances, nonceMap, hbal, hnon, hall, hsup, hb]

/-- **The storage abstraction of `SoladyToken`.** -/
noncomputable def soladyAbs : TokenAbs (VState Address) where
  read := read
  footprint := Footprint
  read_congr := read_congr
  Sound := SoladySound

/-! ## The statement -/

/-- The model: Solady `ERC20` with Permit2 at `PERMIT2`. -/
noncomputable abbrev M : TokenModel (VState Address) Address (Variant.Op Address) :=
  soladyModel PERMIT2

/-- The gas from which every obligation is exact. -/
def g₀ : Nat := 100000

/-- The dispatcher's selectors (`SoladyToken.selectors`). -/
def sel : List Nat := SoladyToken.selectors.map (·.2.toNat)

/-- An address argument word, if it is clean (Solidity ≥ 0.8 reverts on dirty ones). -/
def addrArg (x : Word) : Option Address := if x.toNat < 2 ^ 160 then some x.toAddress else none

/-- The `i`-th argument word of `data`. -/
def argWord (data : ByteArray) (i : Nat) : Word := Bytes.toWord (readBytes data (4 + 32 * i) 32)

/-- **The other entry points**: `mint(to, v)` and `burn(from, v)` of `SoladyToken` (anyone, for
any account), with two well-formed arguments (a clean address and a word) and no value (every
entry point is non-payable). -/
def ops (caller : Address) (data : ByteArray) (value : ℕ) : Option (Variant.Op Address) :=
  if value ≠ 0 ∨ data.size < 68 then none
  else if Abi.selectorOf data = 0x40c10f19 then
    (addrArg (argWord data 0)).map fun a => .mint caller a (argWord data 1).toNat
  else if Abi.selectorOf data = 0x9dc29fac then
    (addrArg (argWord data 0)).map fun a => .burn caller a (argWord data 1).toNat
  else none

/-- **The bytecode spec of `SoladyToken`.** -/
abbrev soladySpec : Prop := ERC20Spec SoladyToken.runtimeCode soladyAbs M g₀ sel ops

end Verified.Solady.Spec
