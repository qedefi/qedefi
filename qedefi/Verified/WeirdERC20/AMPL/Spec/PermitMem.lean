import Verified.WeirdERC20.AMPL.Spec.PermitRules
import EvmLogic.Solidity.Strings

/-!
# The memory of AMPL's `name()` copy loop

`loopMem`: the memory after the copy loop stored `k` words of storage from slot `p` at `dst`
(each store expanding the memory first, as `MSTORE` does). It leaves the memory below `dst`
as it was (`loopMem_read_below`), and the words read back as `Str.wordsFrom` (`read_loopMem`).
-/

set_option linter.unusedSimpArgs false

namespace Verified.WeirdERC20.AMPL.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter

/-- The memory after the copy loop stored `k` words of `sl` from slot `p` at `dst`. -/
def loopMem (sl : Word → Word) (M : Memory) (dst p : Word) : Nat → Memory
  | 0 => M
  | k + 1 => loopMem sl ((M.expand dst.toNat 32).storeWord dst.toNat (sl p)) (32#256 + dst)
      (1#256 + p) k

theorem loopMem_zero (sl : Word → Word) (M : Memory) (dst p : Word) :
    loopMem sl M dst p 0 = M := by
  unfold loopMem; rfl

theorem loopMem_succ (sl : Word → Word) (M : Memory) (dst p : Word) (k : Nat) :
    loopMem sl M dst p (k + 1) = loopMem sl ((M.expand dst.toNat 32).storeWord dst.toNat (sl p))
      (32#256 + dst) (1#256 + p) k := by
  conv_lhs => unfold loopMem

theorem toNat_32_add {dst : Word} (h : dst.toNat + 32 < 2 ^ 256) :
    (32#256 + dst).toNat = dst.toNat + 32 := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simpa [Nat.add_comm] using h)]
  simp only [BitVec.toNat_ofNat]
  omega

/-- The loop leaves memory below `dst` as it was. -/
theorem loopMem_read_below (sl : Word → Word) :
    ∀ (k : Nat) (M : Memory) (dst p : Word) (off len : Nat), off + len ≤ dst.toNat →
      dst.toNat + 32 * k < 2 ^ 256 → (loopMem sl M dst p k).read off len = M.read off len := by
  intro k
  induction k with
  | zero => intro M dst p off len _ _; rw [loopMem_zero]
  | succ k ih =>
    intro M dst p off len hle hb
    have hd32 := toNat_32_add (dst := dst) (by omega)
    rw [loopMem_succ, ih _ _ _ _ _ (by omega) (by omega),
      Memory.read_storeWord_of_disjoint _ _ _ _ _ (.inl hle), Memory.read_expand]

theorem eqEmpty {b : ByteArray} (h : b.size = 0) : b = ByteArray.empty :=
  ByteArray.ext (Array.eq_empty_of_size_eq_zero h)

theorem wordsFrom_zero (sl : Word → Word) (p : Word) : Str.wordsFrom sl p 0 = ByteArray.empty :=
  eqEmpty (by rw [Str.size_wordsFrom])

/-- `wordsFrom`, first word first. -/
theorem wordsFrom_cons (sl : Word → Word) (p : Word) :
    ∀ k, Str.wordsFrom sl p (k + 1) = Bytes.ofWord (sl p) ++ Str.wordsFrom sl (1#256 + p) k := by
  intro k
  induction k with
  | zero =>
    rw [Str.wordsFrom_succ, wordsFrom_zero, wordsFrom_zero, ByteArray.empty_append,
      ByteArray.append_empty]
    congr 2
    exact BitVec.add_zero p
  | succ k ih =>
    have hp : p + BitVec.ofNat 256 (k + 1) = 1#256 + p + BitVec.ofNat 256 k := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rewrite [Str.wordsFrom_succ, ih, Str.wordsFrom_succ, ByteArray.append_assoc, hp]
    rfl

/-- **The copied words read back**: `k` words of `sl` from slot `p`. -/
theorem read_loopMem (sl : Word → Word) :
    ∀ (k : Nat) (M : Memory) (dst p : Word), dst.toNat + 32 * k < 2 ^ 256 →
      (loopMem sl M dst p k).read dst.toNat (32 * k) = Str.wordsFrom sl p k := by
  intro k
  induction k with
  | zero =>
    intro M dst p _
    rw [wordsFrom_zero]
    apply eqEmpty
    simp only [Memory.read, Bytes.size_readPadded, Nat.mul_zero]
  | succ k ih =>
    intro M dst p hb
    have hd32 := toNat_32_add (dst := dst) (by omega)
    have e : 32 * (k + 1) = 32 + 32 * k := by ring
    rewrite [e, Memory.read_add, wordsFrom_cons, loopMem_succ]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · rewrite [loopMem_read_below _ _ _ _ _ _ _ (by omega) (by omega)]
      exact Memory.read_storeWord _ _ _
    · rewrite [← hd32]
      exact ih _ _ _ (by omega)

end Verified.WeirdERC20.AMPL.Spec.Malformed
