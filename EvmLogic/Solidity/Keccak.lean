import EvmLogic.Solidity.Layout
import EvmLogic.Solidity.Abi

/-!
# Keccak non-collision as explicit hypotheses

Hashed storage slots must not collide; since the semantics is parametric in `Crypto`, each
theorem takes this as a hypothesis about the specific preimages it touches. Global injectivity
is false for every `Crypto` (pigeonhole) and is never assumed. `KeccakFresh crypto S x` (one
target against a large candidate set, e.g. all address-keyed entries) is plausible for the real
Keccak; `KeccakInjOn` only for small finite `S` (`NoCollision`). Nested-mapping frames are
stated pointwise for that reason. See `docs/proving.md` §4.
-/

namespace EvmLogic.Solidity
open EvmLean EvmLean.Bytes

/-! ## Hypotheses -/

/-- Keccak-256 is injective on `S`. Plausible only for small `S` (see the module doc). -/
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
  inj : KeccakInjOn crypto (· ∈ xs)
  avoids : KeccakAvoids crypto (· ∈ xs) slots

theorem KeccakInjOn.fresh {crypto : Crypto} {S : ByteArray → Prop} {x : ByteArray}
    (h : KeccakInjOn crypto S) (hx : S x) : KeccakFresh crypto S x :=
  fun y hy he => h y x hy hx he

theorem KeccakInjOn.mono {crypto : Crypto} {S T : ByteArray → Prop} (h : KeccakInjOn crypto S)
    (hTS : ∀ x, T x → S x) : KeccakInjOn crypto T :=
  fun x y hx hy => h x y (hTS x hx) (hTS y hy)

theorem KeccakFresh.mono {crypto : Crypto} {S T : ByteArray → Prop} {x : ByteArray}
    (h : KeccakFresh crypto S x) (hTS : ∀ y, T y → S y) : KeccakFresh crypto T x :=
  fun y hy => h y (hTS y hy)

/-! ## Two-word preimages -/

/-- The preimage of a mapping slot: `key ‖ base`. -/
def slotPreimage (key base : Word) : ByteArray := ofWord key ++ ofWord base

theorem mappingSlot_eq (crypto : Crypto) (key base : Word) :
    mappingSlot crypto key base = crypto.keccak256 (slotPreimage key base) := rfl

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

theorem NoCollision.mappingSlot_ne {crypto : Crypto} {xs : List ByteArray} {slots : List Word}
    {k b k' b' : Word} (h : NoCollision crypto xs slots) (h₁ : slotPreimage k b ∈ xs)
    (h₂ : slotPreimage k' b' ∈ xs) (hne : k' ≠ k ∨ b' ≠ b) :
    mappingSlot crypto k' b' ≠ mappingSlot crypto k b :=
  mappingSlot_ne_of_fresh (h.inj.fresh h₁) h₂ hne

end EvmLogic.Solidity
