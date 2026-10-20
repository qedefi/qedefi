import EvmLogic.AbsInt.Effect
import EvmLogic.GasMono.CodeScan
import EvmLogic.Bytes

/-!
# Abstract interpretation: values, stacks and the instruction scan

* `AVal`: an abstract word: unknown (`top`), a constant (`const n`, the word with `toNat = n`),
  or a **symbolic immutable** (`sym k`: the address `ρ k` zero-extended, for a valuation
  `ρ : Nat → Address` of the code's address immutables). Symbolic values make one certificate
  valid for every choice of immutables (the vault's `asset`).
* `AStack := List AVal`, related to a concrete stack of the **same length** pointwise
  (`StackOk`: the abstract interpreter tracks the exact stack depth).
* `ashl`, `asub`, `aand`: the folded operations (constants for `SHL`/`SUB`/`AND`, and
  `AND` with a mask whose low 160 bits are set keeps a symbolic address: solc masks addresses
  with `(1 << 160) - 1`, built by `SHL` and `SUB`).
* `ascan code syms`: the instruction scan of `code` (one structural pass over
  `code.data.toList`, as `GasMono.insns`) decorated with each instruction's shape (`byteEff`)
  and its abstract immediate: a constant for `PUSH0`–`PUSH31`, and for `PUSH32` the symbolic
  immutable `sym k` if its position is listed in `syms`, else `top`. `PUSH32` immediates are
  never read, so patching immutables leaves the scan unchanged. `ascan_ok`: every entry is
  right (`InsOk`) for every valuation under which the listed `PUSH32`s push the immutables
  (`SymOk`).
-/

namespace EvmLogic.AbsInt
open EvmLean EvmLogic.Program

open EvmLean.Interpreter

/-! ## Abstract values -/

/-- An abstract word. -/
inductive AVal where
  /-- Any word. -/
  | top
  /-- The word with `toNat = n`. -/
  | const (n : Nat)
  /-- The address immutable number `k`, zero-extended. -/
  | sym (k : Nat)
  deriving DecidableEq, Repr

namespace AVal
open EvmLean EvmLogic.Program

/-- Concretisation: `w` is described by `a` under the valuation `ρ` of the immutables. -/
def Holds (ρ : Nat → Address) : AVal → Word → Prop
  | .top, _ => True
  | .const n, w => w.toNat = n
  | .sym k, w => w = Word.ofAddress (ρ k)

/-- Equality test (structural, for kernel evaluation). -/
def beq : AVal → AVal → Bool
  | .top, .top => true
  | .const a, .const b => Nat.beq a b
  | .sym a, .sym b => Nat.beq a b
  | _, _ => false

theorem eq_of_beq {a b : AVal} (h : a.beq b = true) : a = b := by
  cases a <;> cases b <;> simp_all [beq, Nat.beq_eq]

end AVal

/-- An abstract stack (head = top). -/
abbrev AStack := List AVal

/-- A concrete stack described by an abstract one: same length, pointwise. -/
def StackOk (ρ : Nat → Address) : AStack → List Word → Prop
  | [], [] => True
  | a :: s, w :: st => a.Holds ρ w ∧ StackOk ρ s st
  | _, _ => False

/-- Equality test of abstract stacks (structural). -/
def stackBeq : AStack → AStack → Bool
  | [], [] => true
  | a :: s, b :: t => a.beq b && stackBeq s t
  | _, _ => false

theorem eq_of_stackBeq : ∀ {s t : AStack}, stackBeq s t = true → s = t
  | [], [], _ => rfl
  | a :: s, b :: t, h => by
    simp only [stackBeq, Bool.and_eq_true] at h
    rw [AVal.eq_of_beq h.1, eq_of_stackBeq h.2]
  | [], _ :: _, h => by simp [stackBeq] at h
  | _ :: _, [], h => by simp [stackBeq] at h

/-- Membership test of an abstract stack in a list (structural). -/
def memS (s : AStack) : List AStack → Bool
  | [] => false
  | t :: ts => stackBeq s t || memS s ts

theorem mem_of_memS {s : AStack} : ∀ {ss : List AStack}, memS s ss = true → s ∈ ss
  | [], h => by simp [memS] at h
  | t :: ts, h => by
    simp only [memS, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [eq_of_stackBeq h]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_memS h)

/-! ## Folded operations -/

/-- Abstract `SHL` (shift on top). -/
def ashl : AVal → AVal → AVal
  | .const x, .const y => .const (if x < 256 then (y <<< x) % 2 ^ 256 else 0)
  | _, _ => .top

/-- Abstract `SUB`. -/
def asub : AVal → AVal → AVal
  | .const x, .const y => .const ((x + (2 ^ 256 - y)) % 2 ^ 256)
  | _, _ => .top

/-- Does `c` have its low 160 bits set (an address mask)? -/
def isAddrMask (c : Nat) : Bool := c % 2 ^ 160 == 2 ^ 160 - 1

/-- Abstract `AND`: constants, and an address mask keeps a symbolic address. -/
def aand : AVal → AVal → AVal
  | .const x, .const y => .const (x &&& y)
  | .const c, .sym k => if isAddrMask c then .sym k else .top
  | .sym k, .const c => if isAddrMask c then .sym k else .top
  | _, _ => .top

variable {ρ : Nat → Address}

theorem ashl_holds {a b : AVal} {x y : Word} (ha : a.Holds ρ x) (hb : b.Holds ρ y) :
    (ashl a b).Holds ρ (Word.shl x y) := by
  cases a <;> cases b <;> simp only [ashl, AVal.Holds] at ha hb ⊢
  subst ha hb
  unfold Word.shl
  split <;> simp [BitVec.toNat_shiftLeft, *]

theorem asub_holds {a b : AVal} {x y : Word} (ha : a.Holds ρ x) (hb : b.Holds ρ y) :
    (asub a b).Holds ρ (x - y) := by
  cases a <;> cases b <;> simp only [asub, AVal.Holds] at ha hb ⊢
  subst ha hb
  rw [BitVec.toNat_sub, Nat.add_comm]

/-- An address mask keeps an address. -/
theorem land_of_addrMask {c w : Nat} (hc : isAddrMask c = true) (hw : w < 2 ^ 160) :
    c &&& w = w := by
  simp only [isAddrMask, beq_iff_eq] at hc
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < 160
  · have : c.testBit i = true := by
      have h1 := Nat.testBit_mod_two_pow c 160 i
      rw [hc, Nat.testBit_two_pow_sub_one] at h1
      simp only [hi, decide_true, Bool.true_and] at h1
      exact h1.symm
    rw [this, Bool.true_and]
  · have : w.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [this, Bool.and_false]

theorem toNat_ofAddress (a : Address) : (Word.ofAddress a).toNat = a.toNat := by
  unfold Word.ofAddress
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by omega) (by omega)))

theorem and_ofAddress {c : Word} {a : Address} (hc : isAddrMask c.toNat = true) :
    (c &&& Word.ofAddress a) = Word.ofAddress a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofAddress]
  exact land_of_addrMask hc a.isLt

theorem aand_holds {a b : AVal} {x y : Word} (ha : a.Holds ρ x) (hb : b.Holds ρ y) :
    (aand a b).Holds ρ (x &&& y) := by
  cases a <;> cases b <;> simp only [aand, AVal.Holds] at ha hb ⊢
  · subst ha hb; rw [BitVec.toNat_and]
  · rename_i c k
    subst hb
    by_cases h : isAddrMask c = true
    · simp only [h, ite_true]; subst ha; exact and_ofAddress h
    · simp only [h, Bool.false_eq_true, ite_false]
  · rename_i k c
    subst ha
    by_cases h : isAddrMask c = true
    · simp only [h, ite_true]; subst hb; rw [BitVec.and_comm]; exact and_ofAddress h
    · simp only [h, Bool.false_eq_true, ite_false]

/-! ## The scan -/

/-- The big-endian value of the first `n` bytes of a list, zero-padded, after `acc`. -/
def beTake : Nat → List UInt8 → Nat → Nat
  | 0, _, acc => acc
  | n + 1, [], acc => beTake n [] (acc * 256)
  | n + 1, b :: bs, acc => beTake n bs (acc * 256 + b.toNat)

/-- The immutable number of the `PUSH32` at `q`, if listed. -/
def symAt (q : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | (p, k) :: ps => if q == p then some k else symAt q ps

/-- The abstract immediate of the instruction `b` at `p`, followed by the bytes `bs`. -/
def immOf (syms : List (Nat × Nat)) (p : Nat) (b : UInt8) (bs : List UInt8) : AVal :=
  if GasMono.immSize b = 32 then
    match symAt p syms with
    | some k => .sym k
    | none => .top
  else .const (beTake (GasMono.immSize b) bs 0)

/-- The decorated scan from position `p` of a suffix `bytes` of the code (structural fuel):
`(q, shape, abstract immediate)` per instruction boundary `q`. -/
def ascanFrom (syms : List (Nat × Nat)) : (fuel : Nat) → List UInt8 → Nat →
    List (Nat × Eff × AVal)
  | 0, _, _ => []
  | _ + 1, [], _ => []
  | f + 1, b :: bs, p =>
    (p, byteEff b, immOf syms p b bs) ::
      ascanFrom syms f (bs.drop (GasMono.immSize b)) (p + 1 + GasMono.immSize b)

/-- The decorated scan of the whole code. -/
def ascan (code : ByteArray) (syms : List (Nat × Nat)) : List (Nat × Eff × AVal) :=
  ascanFrom syms code.size code.data.toList 0

/-- The listed `PUSH32`s push the immutables of `ρ`. -/
def SymOk (ρ : Nat → Address) (code : ByteArray) (syms : List (Nat × Nat)) : Prop :=
  ∀ q k, symAt q syms = some k →
    Bytes.toWord (readBytes code (q + 1) 32) = Word.ofAddress (ρ k)

/-- A scan entry is right: the byte at `q` has shape `e`, and `imm` describes its immediate
(the value a `PUSHn` pushes; `0` for other instructions). -/
def InsOk (ρ : Nat → Address) (code : ByteArray) (q : Nat) (e : Eff) (imm : AVal) : Prop :=
  ∃ b, code[q]? = some b ∧ e = byteEff b ∧
    imm.Holds ρ (Bytes.toWord (readBytes code (q + 1) (GasMono.immSize b)))

/-- `beTake` as a fold over the padded bytes. -/
theorem beTake_eq (n : Nat) : ∀ (bs : List UInt8) (acc : Nat),
    beTake n bs acc =
      (List.ofFn fun j : Fin n => (bs[j.val]?).getD 0).foldl (fun a x => a * 256 + x.toNat) acc := by
  induction n with
  | zero => intro bs acc; rfl
  | succ n ih =>
    intro bs acc
    cases bs with
    | nil =>
      rw [beTake, ih, List.ofFn_succ, List.foldl_cons]
      simp
    | cons b bs =>
      rw [beTake, ih, List.ofFn_succ, List.foldl_cons]
      simp

/-- A bound on `beTake`. -/
theorem beTake_lt (n : Nat) : ∀ (bs : List UInt8) (acc : Nat),
    beTake n bs acc < (acc + 1) * 256 ^ n := by
  induction n with
  | zero => intro bs acc; simp [beTake]
  | succ n ih =>
    intro bs acc
    have key : ∀ d < 256, beTake n bs.tail (acc * 256 + d) < (acc + 1) * 256 ^ (n + 1) := by
      intro d hd
      have h1 := ih bs.tail (acc * 256 + d)
      have h2 : (acc * 256 + d + 1) * 256 ^ n ≤ (acc + 1) * 256 ^ (n + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm (256 ^ n) 256, ← Nat.mul_assoc]
        apply Nat.mul_le_mul_right
        rw [Nat.add_mul]; omega
      exact Nat.lt_of_lt_of_le h1 h2
    cases bs with
    | nil => simpa [beTake] using key 0 (by omega)
    | cons b bs => simpa [beTake] using key b.toNat b.toNat_lt

/-- The bytes of a padded read. -/
theorem data_readPadded (code : ByteArray) (off n : Nat) :
    (Bytes.readPadded code off n).data.toList =
      List.ofFn fun j : Fin n => (code.data.toList.drop off)[j.val]?.getD 0 := by
  apply List.ext_getElem
  · simp [Bytes.size_readPadded]
  · intro j h₁ h₂
    simp only [List.length_ofFn] at h₂
    have hg := Bytes.getD_readPadded code off n j
    simp only [h₂, ↓reduceIte] at hg
    rw [GasMono.getD_eq_toList, GasMono.getD_eq_toList] at hg
    rw [List.getElem?_eq_getElem h₁, Option.getD_some] at hg
    rw [hg, List.getElem_ofFn, List.getElem?_drop]

/-- The value of a `PUSHn` immediate, `n ≤ 31`, by the scan. -/
theorem toNat_toWord_readBytes (code : ByteArray) (off n : Nat) (hn : n ≤ 31) :
    (Bytes.toWord (readBytes code off n)).toNat = beTake n (code.data.toList.drop off) 0 := by
  rw [readBytes_eq_readPadded, Bytes.toWord, BitVec.toNat_ofNat, Bytes.toNat_eq_foldl,
    ← Array.foldl_toList, data_readPadded, ← beTake_eq]
  apply Nat.mod_eq_of_lt
  have h := beTake_lt n (code.data.toList.drop off) 0
  have h2 : 256 ^ n ≤ 256 ^ 31 := Nat.pow_le_pow_right (by omega) hn
  simp only [Nat.zero_add, Nat.one_mul] at h
  have h3 : (256 : Nat) ^ 31 < 2 ^ 256 := by decide
  omega

/-- Immediates have at most 32 bytes. -/
theorem immSize_le (b : UInt8) : GasMono.immSize b ≤ 32 := by
  unfold GasMono.immSize; split <;> omega

/-- The byte at the head of a suffix of the code. -/
theorem getElem?_of_drop {code : ByteArray} {p : Nat} {b : UInt8} {bs : List UInt8}
    (h : code.data.toList.drop p = b :: bs) : code[p]? = some b := by
  have h1 : (code.data.toList.drop p)[0]? = some b := by rw [h]; rfl
  rw [List.getElem?_drop, Nat.add_zero] at h1
  rw [List.getElem?_eq_some_iff] at h1
  obtain ⟨hlt, hb⟩ := h1
  rw [getElem?_eq_some_iff]
  refine ⟨by simpa using hlt, ?_⟩
  rw [ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList, hb]

/-- **The scan is right**, for every valuation of the immutables under which the listed
`PUSH32`s push them. -/
theorem ascanFrom_ok {ρ : Nat → Address} {code : ByteArray} {syms : List (Nat × Nat)}
    (hs : SymOk ρ code syms) (fuel : Nat) :
    ∀ p, ∀ x ∈ ascanFrom syms fuel (code.data.toList.drop p) p, InsOk ρ code x.1 x.2.1 x.2.2 := by
  induction fuel with
  | zero => intro p x hx; simp [ascanFrom] at hx
  | succ f ih =>
    intro p x hx
    cases hd : code.data.toList.drop p with
    | nil => rw [hd] at hx; simp [ascanFrom] at hx
    | cons b bs =>
      rw [hd] at hx
      simp only [ascanFrom, List.mem_cons] at hx
      have htail : bs = code.data.toList.drop (p + 1) := by
        rw [← List.drop_drop, hd]; rfl
      rcases hx with rfl | hx
      · refine ⟨b, getElem?_of_drop hd, rfl, ?_⟩
        unfold immOf
        split
        · rename_i h32
          split
          · rename_i k hk
            rw [h32]; exact hs p k hk
          · trivial
        · rename_i h32
          simp only [AVal.Holds]
          rw [toNat_toWord_readBytes _ _ _ (by have := immSize_le b; omega), htail]
      · have := ih (p + 1 + GasMono.immSize b) x (by
          rw [htail, List.drop_drop] at hx; exact hx)
        exact this

/-- **The scan is right.** -/
theorem ascan_ok {ρ : Nat → Address} {code : ByteArray} {syms : List (Nat × Nat)}
    (hs : SymOk ρ code syms) : ∀ x ∈ ascan code syms, InsOk ρ code x.1 x.2.1 x.2.2 := by
  intro x hx
  exact ascanFrom_ok hs code.size 0 x (by simpa [ascan] using hx)

end EvmLogic.AbsInt
