import QEDefi.ERC20.Spec.Bytecode
import EvmLogic.Solidity.Layout
import QEDefi.Solvency.Deps

/-!
# Reading Solidity storage into model states

Helpers for writing a token's `TokenAbs`, for a finite set of actors `Act` (see
`QEDefi.ERC20.Spec.Bytecode` for why the spec is stated per set of actors): a
`mapping(address => uint)` at slot `base` read for the actors as a finitely supported
`ℕ`-valued function, zero elsewhere (`readMap`), a nested
`mapping(address => mapping(address => uint))` read for pairs of actors (`readMap2`), a plain
slot (`readSlot`), the footprints they read (`MapSlots`, `Map2Slots`), and the `*_congr`
lemmas that `read_congr` is assembled from.

Reading needs no hash hypothesis. A token's `TokenAbs.Sound crypto Act` states those its
writes need, for the actors' rows only (`ActorRows` for the common case: the actors' rows are
pairwise distinct and avoid the token's fixed slots).
-/

namespace QEDefi.ERC20.Spec
open EvmLean EvmLogic EvmLogic.Solidity

/-- The value in slot `k` of `token`, as a number. -/
def readSlot (w : World) (token : Address) (k : Word) : ℕ := (w.sload token k).toNat

/-- **A `mapping(address => uint)` at slot `base`, for the actors**: their rows, zero for
every other account. -/
noncomputable def readMap (crypto : Crypto) (Act : Finset Address) (w : World)
    (token : Address) (base : Word) : Address →₀ ℕ :=
  Finsupp.onFinset Act
    (fun a => if a ∈ Act then (w.sload token (mappingSlot crypto (Word.ofAddress a) base)).toNat
      else 0)
    (fun a h => by by_contra ha; simp [ha] at h)

/-- **A `mapping(address => mapping(address => uint))` at slot `base`, for pairs of actors**,
zero for every other pair. -/
def readMap2 (crypto : Crypto) (Act : Finset Address) (w : World) (token : Address)
    (base : Word) : Address → Address → ℕ :=
  fun o sp => if o ∈ Act ∧ sp ∈ Act then
    (w.sload token (mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) base)).toNat
  else 0

/-- The slots of the actors' rows of a `mapping(address => _)` at `base`. -/
def MapSlots (crypto : Crypto) (Act : Finset Address) (base : Word) (k : Word) : Prop :=
  ∃ a ∈ Act, k = mappingSlot crypto (Word.ofAddress a) base

/-- The slots of the rows of pairs of actors of a `mapping(address => mapping(address => _))`
at `base`. -/
def Map2Slots (crypto : Crypto) (Act : Finset Address) (base : Word) (k : Word) : Prop :=
  ∃ o ∈ Act, ∃ sp ∈ Act, k = mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) base

/-- **The common hash hypothesis**: the actors' rows of the one-level mappings at `bases1` and
of the nested mappings at `bases2` are pairwise distinct (different keys or mappings, different
slots), and none is one of the token's fixed slots `fixed`. A finite set of rows, so the
hypothesis is plausible for Keccak. -/
structure ActorRows (crypto : Crypto) (Act : Finset Address) (bases1 bases2 fixed : List Word) :
    Prop where
  /-- One-level rows are distinct. -/
  inj1 : ∀ b ∈ bases1, ∀ b' ∈ bases1, ∀ a ∈ Act, ∀ a' ∈ Act,
    mappingSlot crypto (Word.ofAddress a) b = mappingSlot crypto (Word.ofAddress a') b' →
      a = a' ∧ b = b'
  /-- Nested rows are distinct. -/
  inj2 : ∀ b ∈ bases2, ∀ b' ∈ bases2, ∀ o ∈ Act, ∀ sp ∈ Act, ∀ o' ∈ Act, ∀ sp' ∈ Act,
    mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) b =
      mappingSlot2 crypto (Word.ofAddress o') (Word.ofAddress sp') b' →
      o = o' ∧ sp = sp' ∧ b = b'
  /-- One-level and nested rows are distinct. -/
  disj : ∀ b ∈ bases1, ∀ b' ∈ bases2, ∀ a ∈ Act, ∀ o ∈ Act, ∀ sp ∈ Act,
    mappingSlot crypto (Word.ofAddress a) b ≠
      mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) b'
  /-- No one-level row is a fixed slot. -/
  fixed1 : ∀ b ∈ bases1, ∀ a ∈ Act, mappingSlot crypto (Word.ofAddress a) b ∉ fixed
  /-- No nested row is a fixed slot. -/
  fixed2 : ∀ b ∈ bases2, ∀ o ∈ Act, ∀ sp ∈ Act,
    mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) b ∉ fixed

theorem readMap_apply (crypto : Crypto) (Act : Finset Address) (w : World) (token : Address)
    (base : Word) (a : Address) :
    readMap crypto Act w token base a =
      if a ∈ Act then (w.sload token (mappingSlot crypto (Word.ofAddress a) base)).toNat
      else 0 := rfl

@[simp] theorem readMap_of_mem {crypto : Crypto} {Act : Finset Address} {a : Address}
    (h : a ∈ Act) (w : World) (token : Address) (base : Word) :
    readMap crypto Act w token base a =
      (w.sload token (mappingSlot crypto (Word.ofAddress a) base)).toNat := by
  simp [readMap_apply, h]

@[simp] theorem readMap_of_not_mem {crypto : Crypto} {Act : Finset Address} {a : Address}
    (h : a ∉ Act) (w : World) (token : Address) (base : Word) :
    readMap crypto Act w token base a = 0 := by
  simp [readMap_apply, h]

theorem readSlot_congr {w w' : World} {token : Address} {k : Word}
    (h : w'.sload token k = w.sload token k) : readSlot w' token k = readSlot w token k := by
  simp only [readSlot, h]

theorem readMap_congr {crypto : Crypto} {Act : Finset Address} {w w' : World} {token : Address}
    {base : Word} (h : ∀ k, MapSlots crypto Act base k → w'.sload token k = w.sload token k) :
    readMap crypto Act w' token base = readMap crypto Act w token base := by
  ext a
  by_cases ha : a ∈ Act
  · rw [readMap_of_mem ha, readMap_of_mem ha, h _ ⟨a, ha, rfl⟩]
  · rw [readMap_of_not_mem ha, readMap_of_not_mem ha]

theorem readMap2_congr {crypto : Crypto} {Act : Finset Address} {w w' : World} {token : Address}
    {base : Word} (h : ∀ k, Map2Slots crypto Act base k → w'.sload token k = w.sload token k) :
    readMap2 crypto Act w' token base = readMap2 crypto Act w token base := by
  funext o sp
  simp only [readMap2]
  split
  · rename_i hm; rw [h _ ⟨o, hm.1, sp, hm.2, rfl⟩]
  · rfl

end QEDefi.ERC20.Spec
