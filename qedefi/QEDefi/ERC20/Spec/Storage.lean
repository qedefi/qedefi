import QEDefi.ERC20.Spec.Bytecode
import EvmLogic.Solidity.Layout
import QEDefi.Solvency.Deps

/-!
# Reading Solidity storage into model states

Helpers for writing a token's `TokenAbs`: a `mapping(address => uint)` at slot `base` read as a
finitely supported `ℕ`-valued function (`readMap`; finitely supported because there are
finitely many addresses, so no hash hypothesis is needed to read), a nested
`mapping(address => mapping(address => uint))` (`readMap2`), a plain slot (`readSlot`), the
footprints they read (`MapSlots`, `Map2Slots`), and the `*_congr` lemmas that `read_congr`
is assembled from.

The hash hypotheses belong to writes, not reads: a token's `TokenAbs.Sound` states those its
proofs need (typically that its mapping rows are distinct and avoid its fixed slots, as
`EvmLogic.Solidity.ERC20.BalanceSlotOk` does per row).
-/

namespace QEDefi.ERC20.Spec
open EvmLean EvmLogic EvmLogic.Solidity

/-- The value in slot `k` of `token`, as a number. -/
def readSlot (w : World) (token : Address) (k : Word) : ℕ := (w.sload token k).toNat

/-- **A `mapping(address => uint)` at slot `base`**, as a finitely supported function. -/
noncomputable def readMap (crypto : Crypto) (w : World) (token : Address) (base : Word) :
    Address →₀ ℕ :=
  Finsupp.ofSupportFinite
    (fun a => (w.sload token (mappingSlot crypto (Word.ofAddress a) base)).toNat)
    (Set.toFinite _)

/-- **A `mapping(address => mapping(address => uint))` at slot `base`.** -/
def readMap2 (crypto : Crypto) (w : World) (token : Address) (base : Word) :
    Address → Address → ℕ :=
  fun o sp => (w.sload token (mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) base)).toNat

/-- The slots of the rows of a `mapping(address => _)` at `base`. -/
def MapSlots (crypto : Crypto) (base : Word) (k : Word) : Prop :=
  ∃ a : Address, k = mappingSlot crypto (Word.ofAddress a) base

/-- The slots of the rows of a `mapping(address => mapping(address => _))` at `base`. -/
def Map2Slots (crypto : Crypto) (base : Word) (k : Word) : Prop :=
  ∃ o sp : Address, k = mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) base

@[simp] theorem readMap_apply (crypto : Crypto) (w : World) (token : Address) (base : Word)
    (a : Address) :
    readMap crypto w token base a =
      (w.sload token (mappingSlot crypto (Word.ofAddress a) base)).toNat := rfl

theorem readSlot_congr {w w' : World} {token : Address} {k : Word}
    (h : w'.sload token k = w.sload token k) : readSlot w' token k = readSlot w token k := by
  simp only [readSlot, h]

theorem readMap_congr {crypto : Crypto} {w w' : World} {token : Address} {base : Word}
    (h : ∀ k, MapSlots crypto base k → w'.sload token k = w.sload token k) :
    readMap crypto w' token base = readMap crypto w token base := by
  ext a
  simp only [readMap_apply]
  rw [h _ ⟨a, rfl⟩]

theorem readMap2_congr {crypto : Crypto} {w w' : World} {token : Address} {base : Word}
    (h : ∀ k, Map2Slots crypto base k → w'.sload token k = w.sload token k) :
    readMap2 crypto w' token base = readMap2 crypto w token base := by
  funext o sp
  simp only [readMap2]
  rw [h _ ⟨o, sp, rfl⟩]

end QEDefi.ERC20.Spec
