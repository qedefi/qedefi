import EvmLogic.Solidity.Layout
import EvmLogic.Solidity.Abi

/-!
# Keccak non-collision as explicit hypotheses

Solidity's storage layout is only meaningful if hashed slots do not collide: two mapping
entries, or a mapping entry and a fixed variable, must not share a slot. Since the semantics
is parametric in `Crypto`, this is never derived; theorems take it as a **hypothesis about
the specific preimages they touch**. This file defines the hypotheses and derives slot
disequalities from them.

## Why not "Keccak is injective"

Global injectivity of `crypto.keccak256 : ByteArray → BitVec 256` is false for *every*
`Crypto` (pigeonhole), so a theorem assuming it is vacuous. Injectivity on a set `S` of
preimages is satisfiable iff `|S| ≤ 2²⁵⁶`, but satisfiable is not the same as plausible for
the real Keccak. Modelling Keccak as a random function, a fixed set of `N` preimages is
collision-free with probability about `1 - N²/2²⁵⁷`:

| hypothesis | preimages | status for the real Keccak |
|---|---|---|
| injective on all `pad(a) ‖ p`, `a : Address`, one base `p` | `2¹⁶⁰` | consistent, but *false* with overwhelming probability (birthday bound: `2³²⁰/2²⁵⁷`) |
| injective on all nested-mapping preimages (`allowance[o][s]`, all `o`, `s`) | `2³²⁰` | **unsatisfiable** (more preimages than hashes) |
| the slot of one given entry is hit by no other `pad(a) ‖ p`, `p` among a few bases | `2¹⁶²` candidates, one target | plausible (`≈ 2¹⁶²/2²⁵⁶ = 2⁻⁹⁴`) |
| the slot of one given entry is hit by no nested-mapping entry | `2³²⁰` candidates | false with overwhelming probability (`≈ 2⁶⁴` expected hits) |
| injective on a finite list of `N ≪ 2¹²⁸` preimages | `N` | plausible |

Hence the shapes provided here:

* `KeccakFresh crypto S x`: no *other* preimage in `S` hashes to the hash of `x` (one target
  against a possibly large candidate set: the third row). This is what a frame condition
  "every other entry of the mapping is unchanged" needs, and it is plausible for `S` = all
  address-keyed entries of a few single-level mappings.
* `KeccakInjOn crypto S`: injectivity on `S`; use it only for small (finite) `S`, e.g.
  `NoCollision` on an explicit list of preimages (the last row).
* `KeccakAvoids crypto S slots`: no hash of a preimage in `S` is one of the fixed slots.

Frame conditions over nested mappings (e.g. "a `transfer` changes no allowance") cannot be
stated for *all* pairs under plausible hypotheses; they are stated pointwise instead
("`allowance[o][s]` is unchanged unless its slot is one of the written slots"), and a user
instantiates them for the finitely many pairs they care about with `NoCollision`.

All of these are assumptions about the hash function, unprovable for the real Keccak; they
are kept as explicit hypotheses of each theorem (never axioms), so `#print axioms` shows only
the standard ones.
-/

namespace EvmLogic.Solidity
open EvmLean

open EvmLean.Bytes

/-! ## Hypotheses -/

/-- Keccak-256 is injective on the preimages satisfying `S`. Plausible only for small `S`
(see the module docstring). -/
def KeccakInjOn (crypto : Crypto) (S : ByteArray → Prop) : Prop :=
  ∀ x y, S x → S y → crypto.keccak256 x = crypto.keccak256 y → x = y

/-- The hash of `x` is the hash of no other preimage satisfying `S`. -/
def KeccakFresh (crypto : Crypto) (S : ByteArray → Prop) (x : ByteArray) : Prop :=
  ∀ y, S y → crypto.keccak256 y = crypto.keccak256 x → y = x

/-- No preimage satisfying `S` hashes to one of `slots` (the fixed slots of the layout). -/
def KeccakAvoids (crypto : Crypto) (S : ByteArray → Prop) (slots : List Word) : Prop :=
  ∀ x, S x → crypto.keccak256 x ∉ slots

/-- Collision-freedom of an explicit finite list of preimages, which also avoid `slots`. -/
structure NoCollision (crypto : Crypto) (xs : List ByteArray) (slots : List Word) : Prop where
  /-- Distinct listed preimages have distinct hashes. -/
  inj : KeccakInjOn crypto (· ∈ xs)
  /-- No listed preimage hashes to a fixed slot. -/
  avoids : KeccakAvoids crypto (· ∈ xs) slots

/-- Injectivity on `S` makes every member of `S` fresh. -/
theorem KeccakInjOn.fresh {crypto : Crypto} {S : ByteArray → Prop} {x : ByteArray}
    (h : KeccakInjOn crypto S) (hx : S x) : KeccakFresh crypto S x :=
  fun y hy he => h y x hy hx he

/-- Injectivity is inherited by subsets. -/
theorem KeccakInjOn.mono {crypto : Crypto} {S T : ByteArray → Prop} (h : KeccakInjOn crypto S)
    (hTS : ∀ x, T x → S x) : KeccakInjOn crypto T :=
  fun x y hx hy => h x y (hTS x hx) (hTS y hy)

/-- Freshness is inherited by subsets of candidates. -/
theorem KeccakFresh.mono {crypto : Crypto} {S T : ByteArray → Prop} {x : ByteArray}
    (h : KeccakFresh crypto S x) (hTS : ∀ y, T y → S y) : KeccakFresh crypto T x :=
  fun y hy => h y (hTS y hy)

/-! ## Two-word preimages -/

/-- The preimage of a mapping slot: `key ‖ base`. -/
def slotPreimage (key base : Word) : ByteArray := ofWord key ++ ofWord base

/-- `mappingSlot` is the hash of `slotPreimage`. -/
theorem mappingSlot_eq (crypto : Crypto) (key base : Word) :
    mappingSlot crypto key base = crypto.keccak256 (slotPreimage key base) := rfl

/-- Two-word preimages determine both words. -/
theorem slotPreimage_inj {k b k' b' : Word} (h : slotPreimage k b = slotPreimage k' b') :
    k = k' ∧ b = b' := by
  unfold slotPreimage at h
  constructor
  · have := congrArg (fun d => toWord (Interpreter.readBytes d 0 32)) h
    simpa only [Interpreter.toWord_readBytes_ofWord_append_left] using this
  · have := congrArg (fun d => toWord (Interpreter.readBytes d 32 32)) h
    simpa only [Interpreter.toWord_readBytes_ofWord_append_right] using this

/-- The preimages `pad32(a) ‖ p` of address-keyed entries of mappings at the slots `bases`
(every address `a`). For `bases = [p]` this is all `2¹⁶⁰` entries of one mapping. -/
def AddressKeyed (bases : List Word) (x : ByteArray) : Prop :=
  ∃ a : Address, ∃ p ∈ bases, x = slotPreimage (Word.ofAddress a) p

/-- **Distinct entries, distinct slots**: if the slot of `key ‖ base` is fresh among `S`,
any other entry in `S` has a different slot. -/
theorem mappingSlot_ne_of_fresh {crypto : Crypto} {S : ByteArray → Prop} {k b k' b' : Word}
    (h : KeccakFresh crypto S (slotPreimage k b)) (hS : S (slotPreimage k' b'))
    (hne : k' ≠ k ∨ b' ≠ b) : mappingSlot crypto k' b' ≠ mappingSlot crypto k b := by
  intro he
  have := slotPreimage_inj (h _ hS he)
  rcases hne with hne | hne
  · exact hne this.1
  · exact hne this.2

/-- A fresh entry of an address-keyed mapping: every other address has another slot. -/
theorem mappingSlot_ne_of_fresh_addr {crypto : Crypto} {bases : List Word} {a a' : Address}
    {p p' : Word} (h : KeccakFresh crypto (AddressKeyed bases) (slotPreimage (Word.ofAddress a) p))
    (hp' : p' ∈ bases) (hne : a' ≠ a ∨ p' ≠ p) :
    mappingSlot crypto (Word.ofAddress a') p' ≠ mappingSlot crypto (Word.ofAddress a) p := by
  apply mappingSlot_ne_of_fresh h ⟨a', p', hp', rfl⟩
  rcases hne with hne | hne
  · exact .inl fun e => hne (Word.ofAddress_injective e)
  · exact .inr hne

/-- **Hashed slots avoid fixed slots.** -/
theorem mappingSlot_ne_of_avoids {crypto : Crypto} {S : ByteArray → Prop} {slots : List Word}
    {k b c : Word} (h : KeccakAvoids crypto S slots) (hS : S (slotPreimage k b)) (hc : c ∈ slots) :
    mappingSlot crypto k b ≠ c := by
  intro he
  rw [mappingSlot_eq] at he
  exact h _ hS (he ▸ hc)

/-- Members of a collision-free list have distinct slots. -/
theorem NoCollision.mappingSlot_ne {crypto : Crypto} {xs : List ByteArray} {slots : List Word}
    {k b k' b' : Word} (h : NoCollision crypto xs slots) (h₁ : slotPreimage k b ∈ xs)
    (h₂ : slotPreimage k' b' ∈ xs) (hne : k' ≠ k ∨ b' ≠ b) :
    mappingSlot crypto k' b' ≠ mappingSlot crypto k b :=
  mappingSlot_ne_of_fresh (h.inj.fresh h₁) h₂ hne

end EvmLogic.Solidity
