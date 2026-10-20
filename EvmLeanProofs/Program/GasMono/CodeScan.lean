import EvmLeanProofs.Program.GasMono.Interface

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

namespace EvmLean.Program.GasMono

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

end EvmLean.Program.GasMono
