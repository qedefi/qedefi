import EvmLogic.Bytes
import EvmLogic.Step.Stack

/-!
# Step lemmas: `PUSH1` and `PUSH2` with evaluated immediates

`step_push` leaves the pushed value as `Bytes.toWord (readBytes code (pc + 1) n)`. For the
two most common widths the value is computed here from the immediate bytes, given as
`getElem?` hypotheses (`code[pc + 1]? = some v`), so that applying the lemma to concrete
bytecode determines `v` by unification.
-/

namespace EvmLean.Interpreter

open EvmLean.Bytes

variable {m : Machine}

/-- `getD` agrees with `getElem?` on bytes that exist. -/
theorem getD_of_getElem?_eq_some {b : ByteArray} {i : Nat} {v : UInt8} (h : b[i]? = some v) :
    getD b i = v := by
  rw [getElem?_eq_some_iff] at h
  obtain ⟨hi, rfl⟩ := h
  simp only [getD, hi, ↓reduceDIte]

/-- The bytes read by `PUSH1`. -/
theorem readBytes_one {b : ByteArray} {off : Nat} {v : UInt8} (h : b[off]? = some v) :
    readBytes b off 1 = ⟨#[v]⟩ := by
  rw [readBytes_eq_readPadded]
  apply ext_getD (by rw [size_readPadded]; rfl)
  intro j hj
  rw [size_readPadded] at hj
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [getD_readPadded, hj, ↓reduceIte, Nat.add_zero, getD_of_getElem?_eq_some h]
  rfl

/-- The bytes read by `PUSH2`. -/
theorem readBytes_two {b : ByteArray} {off : Nat} {v w : UInt8} (h₁ : b[off]? = some v)
    (h₂ : b[off + 1]? = some w) : readBytes b off 2 = ⟨#[v, w]⟩ := by
  rw [readBytes_eq_readPadded]
  apply ext_getD (by rw [size_readPadded]; rfl)
  intro j hj
  rw [size_readPadded] at hj
  simp only [getD_readPadded, hj, ↓reduceIte]
  match j, hj with
  | 0, _ => rw [Nat.add_zero, getD_of_getElem?_eq_some h₁]; rfl
  | 1, _ => rw [getD_of_getElem?_eq_some h₂]; rfl

/-- A one-byte big-endian word. -/
theorem toWord_singleton (v : UInt8) : toWord ⟨#[v]⟩ = BitVec.ofNat 256 v.toNat := by
  simp only [toWord, toNat_eq_foldl, List.foldl_toArray', List.foldl_cons, List.foldl_nil,
    Nat.zero_mul, Nat.zero_add]

/-- A two-byte big-endian word. -/
theorem toWord_pair (v w : UInt8) :
    toWord ⟨#[v, w]⟩ = BitVec.ofNat 256 (v.toNat * 256 + w.toNat) := by
  simp only [toWord, toNat_eq_foldl, List.foldl_toArray', List.foldl_cons, List.foldl_nil,
    Nat.zero_mul, Nat.zero_add]

/-- `PUSH1 v`. -/
theorem step_push1 {v : UInt8} (hcode : m.frame.code[m.frame.pc]? = some 0x60)
    (himm : m.frame.code[m.frame.pc + 1]? = some v)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := BitVec.ofNat 256 v.toNat :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 2 } } := by
  rw [step_push 1 hcode hlen hgas]
  simp only [Fin.val_one, readBytes_one himm, toWord_singleton, Nat.one_ne_zero, ite_false,
    Nat.reduceAdd]

/-- `PUSH2 v w`: push `256 · v + w`. -/
theorem step_push2 {v w : UInt8} (hcode : m.frame.code[m.frame.pc]? = some 0x61)
    (himm₁ : m.frame.code[m.frame.pc + 1]? = some v)
    (himm₂ : m.frame.code[m.frame.pc + 2]? = some w)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := BitVec.ofNat 256 (v.toNat * 256 + w.toNat) :: m.frame.stack,
      gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 3 } } := by
  rw [step_push 2 hcode hlen hgas]
  have h₂ : m.frame.code[m.frame.pc + 1 + 1]? = some w := himm₂
  rw [show ((2 : Fin 33) : Nat) = 2 from rfl, readBytes_two himm₁ h₂, toWord_pair]
  rfl

end EvmLean.Interpreter
