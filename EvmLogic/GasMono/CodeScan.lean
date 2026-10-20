import EvmLogic.GasMono.Interface
import EvmLogic.GasMono.Pc

/-!
# Gas monotonicity: a fast instruction scan for the code predicates

`GasFeedsCall`, `RegionOk` and `callReturnPoints` (`GasMono.Interface`) are stated with
`boundaries` and `Bytes.getD`. On a 5 KB runtime code that is far too slow for the kernel:
`Bytes.getD` indexes a list-backed `ByteArray`, so every lookup walks the list.

`insns code` is the same scan written over `code.data.toList`, structurally: it walks the byte
list once and returns, for each instruction boundary `q`, the triple
`(q, opcode byte, following byte)` (the following byte only for instructions without immediate;
`0` for `PUSHn`). `insns_eq` identifies it with `boundaries code` decorated with `Bytes.getD`,
and the three predicates are restated over it (`gasFeedsCall_iff`, `regionOk_iff`,
`callReturnPoints_eq`), so that `decide +kernel` evaluates them in one pass.

The triple deliberately does not record `PUSHn` immediates: patching immutables (which only
rewrites `PUSH32` immediates) leaves `insns` unchanged, which is a closed equation that the
kernel checks for symbolic immutables (the scan skips the patched bytes).
-/

section

namespace EvmLogic.GasMono
open EvmLean EvmLogic.Program

/-- The decoded scan: `(q, opcode byte at q, byte at q + 1 if the opcode has no immediate,
else 0)` for each instruction boundary `q`, from position `p` of a suffix `bytes` of the code,
with structural fuel. -/
def insnsFrom : (fuel : Nat) → List UInt8 → Nat → List (Nat × UInt8 × UInt8)
  | 0, _, _ => []
  | _ + 1, [], _ => []
  | f + 1, b :: bs, p =>
    (p, b, if immSize b = 0 then bs.headD 0 else 0) ::
      insnsFrom f (bs.drop (immSize b)) (p + 1 + immSize b)

/-- The decoded scan of the whole code. -/
def insns (code : ByteArray) : List (Nat × UInt8 × UInt8) :=
  insnsFrom code.size code.data.toList 0

/-- What `insns` records about the instruction at boundary `q`. -/
def insnInfo (code : ByteArray) (q : Nat) : Nat × UInt8 × UInt8 :=
  (q, Bytes.getD code q, if immSize (Bytes.getD code q) = 0 then Bytes.getD code (q + 1) else 0)

/-- `Bytes.getD` is a lookup in the byte list. -/
theorem getD_eq_toList (code : ByteArray) (k : Nat) :
    Bytes.getD code k = (code.data.toList[k]?).getD 0 := by
  unfold Bytes.getD
  by_cases h : k < code.size
  · have h' : k < code.data.toList.length := by simpa using h
    simp only [h, ↓reduceDIte, List.getElem?_eq_getElem h', Option.getD_some,
      ByteArray.getElem_eq_getElem_data, Array.getElem_toList]
  · have h' : ¬ k < code.data.toList.length := by simpa using h
    simp only [h, ↓reduceDIte, List.getElem?_eq_none (Nat.le_of_not_lt h'), Option.getD_none]

/-- The scan from `p` is `boundariesFrom` from `p`, decorated. -/
theorem insnsFrom_eq (code : ByteArray) (fuel p : Nat) :
    insnsFrom fuel (code.data.toList.drop p) p =
      (boundariesFrom code fuel p).map (insnInfo code) := by
  induction fuel generalizing p with
  | zero => rfl
  | succ f ih =>
    by_cases hp : p < code.size
    · have hlen : p < code.data.toList.length := by simpa using hp
      have hb : Bytes.getD code p = code.data.toList[p] := by
        rw [getD_eq_toList, List.getElem?_eq_getElem hlen, Option.getD_some]
      rw [List.drop_eq_getElem_cons hlen]
      simp only [insnsFrom, boundariesFrom, hp, ↓reduceIte, List.map_cons, insnInfo, hb]
      congr 2
      · simp only [List.headD_eq_head?_getD, List.head?_drop, getD_eq_toList]
      · rw [List.drop_drop, ← ih]
    · have hnil : code.data.toList.drop p = [] :=
        List.drop_of_length_le (by simpa using Nat.le_of_not_lt hp)
      rw [hnil]
      simp only [insnsFrom, boundariesFrom, hp, ↓reduceIte, List.map_nil]

/-- **The scan is the decorated boundaries.** -/
theorem insns_eq (code : ByteArray) : insns code = (boundaries code).map (insnInfo code) := by
  simpa [insns, boundaries] using insnsFrom_eq code code.size 0

/-- `GAS` feeds a call, over the scan. -/
def GasFeedsCallL (l : List (Nat × UInt8 × UInt8)) (n : Nat) : Prop :=
  ∀ t ∈ l, t.1 < n → t.2.1 = 0x5a → t.2.2 = 0xf1 ∨ t.2.2 = 0xfa

instance (l : List (Nat × UInt8 × UInt8)) (n : Nat) : Decidable (GasFeedsCallL l n) :=
  inferInstanceAs (Decidable (∀ t ∈ l, _))

/-- `RegionOk`, over the scan. -/
def RegionOkL (l : List (Nat × UInt8 × UInt8)) (n : Nat) : Prop :=
  0 < n ∧ (∃ t ∈ l, t.1 = n - 1 ∧ t.2.1 = 0xfe) ∧ ∀ t ∈ l, n ≤ t.1 → t.2.1 ≠ 0x5b

instance (l : List (Nat × UInt8 × UInt8)) (n : Nat) : Decidable (RegionOkL l n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- `callReturnPoints`, over the scan. -/
def callReturnPointsL (l : List (Nat × UInt8 × UInt8)) (n : Nat) : List Nat :=
  l.filterMap fun t => if t.1 < n ∧ t.2.1 = 0x5a then some (t.1 + 2) else none

/-- `GasFeedsCall` from the scan. -/
theorem gasFeedsCall_iff (code : ByteArray) (n : Nat) :
    GasFeedsCall code n ↔ GasFeedsCallL (insns code) n := by
  unfold GasFeedsCall GasFeedsCallL
  rw [insns_eq, List.forall_mem_map]
  apply forall_congr'; intro q
  apply forall_congr'; intro _
  apply forall_congr'; intro _
  simp only [insnInfo]
  constructor
  · intro h hg
    have h0 : immSize (Bytes.getD code q) = 0 := by rw [hg]; decide
    simpa [h0] using h hg
  · intro h hg
    have h0 : immSize (Bytes.getD code q) = 0 := by rw [hg]; decide
    simpa [h0] using h hg

/-- `RegionOk` from the scan. -/
theorem regionOk_iff (code : ByteArray) (n : Nat) :
    RegionOk code n ↔ RegionOkL (insns code) n := by
  unfold RegionOk RegionOkL
  rw [insns_eq, List.forall_mem_map]
  simp only [List.mem_map, insnInfo]
  constructor
  · rintro ⟨h0, hm, hb, hj⟩
    exact ⟨h0, ⟨_, ⟨n - 1, hm, rfl⟩, rfl, hb⟩, hj⟩
  · rintro ⟨h0, ⟨_, ⟨q, hm, rfl⟩, rfl, hb⟩, hj⟩
    exact ⟨h0, hm, hb, hj⟩

/-- `callReturnPoints` from the scan. -/
theorem callReturnPoints_eq (code : ByteArray) (n : Nat) :
    callReturnPoints code n = callReturnPointsL (insns code) n := by
  unfold callReturnPoints callReturnPointsL
  rw [insns_eq, List.filterMap_map]
  rfl

end EvmLogic.GasMono

end

section

/-!
## Gas monotonicity: `CallsFed` over the instruction scan

`CallsFed code n` (`GasMono/Pc.lean`) asks that every `CALL`/`CREATE`-family byte at a boundary
below `n` directly follows a `GAS` at a boundary. `callsFedB n prev l` checks it in one pass over
the scan `insns code` (`GasMono/CodeScan.lean`), comparing each instruction with its
predecessor; `callsFed_of_scan` turns a successful check into `CallsFed`, so that
`decide +kernel` establishes it for a concrete code.
-/

namespace EvmLogic.GasMono
open EvmLean EvmLogic.Program

/-- `IsCallByte` as a Boolean. -/
def isCallByteB (b : UInt8) : Bool :=
  b == 0xf0 || b == 0xf1 || b == 0xf2 || b == 0xf4 || b == 0xf5 || b == 0xfa

theorem isCallByteB_of {b : UInt8} (h : IsCallByte b) : isCallByteB b = true := by
  unfold IsCallByte at h
  rcases h with h | h | h | h | h | h <;> subst h <;> rfl

/-- One pass over the scan: every call byte below `n` follows a `GAS` (`prev` is the previous
instruction's position and opcode). -/
def callsFedB (n : Nat) : Nat × UInt8 → List (Nat × UInt8 × UInt8) → Bool
  | _, [] => true
  | prev, t :: l =>
    (!(decide (t.1 < n) && isCallByteB t.2.1) || (prev.2 == 0x5a && prev.1 + 1 == t.1)) &&
      callsFedB n (t.1, t.2.1) l

theorem callsFedB_spec {n : Nat} :
    ∀ (l : List (Nat × UInt8 × UInt8)) (prev : Nat × UInt8), callsFedB n prev l = true →
      ∀ t ∈ l, t.1 < n → isCallByteB t.2.1 = true →
        (prev.2 = 0x5a ∧ prev.1 + 1 = t.1) ∨ ∃ t' ∈ l, t'.2.1 = 0x5a ∧ t'.1 + 1 = t.1 := by
  intro l
  induction l with
  | nil => intro _ _ t ht; cases ht
  | cons s l ih =>
    intro prev h t ht hn hc
    simp only [callsFedB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.1 ht with rfl | ht
    · rcases h1 with (h1 | h1) | h1
      · exact absurd hn h1
      · rw [hc] at h1; cases h1
      · exact .inl h1
    · rcases ih _ h2 t ht hn hc with h3 | ⟨t', ht', h3⟩
      · exact .inr ⟨s, List.mem_cons_self, h3⟩
      · exact .inr ⟨t', List.mem_cons_of_mem _ ht', h3⟩

/-- **`CallsFed` from the scan.** -/
theorem callsFed_of_scan {code : ByteArray} {n : Nat}
    (h : callsFedB n (0, 0) (insns code) = true) : CallsFed code n := by
  intro q hq hqn hb
  have hmem : insnInfo code q ∈ insns code := by
    rw [insns_eq]; exact List.mem_map_of_mem hq
  rcases callsFedB_spec _ _ h _ hmem hqn (isCallByteB_of hb) with h1 | ⟨t', ht', h5, h1⟩
  · simp at h1
  · rw [insns_eq] at ht'
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 ht'
    simp only [insnInfo] at h5 h1
    refine ⟨by omega, ?_, ?_⟩
    · rw [show q - 1 = q' by omega]; exact hq'
    · rw [show q - 1 = q' by omega]; exact h5

end EvmLogic.GasMono

end
