import EvmLogic.Bytes
import EvmLogic.Solidity.JumpDest

/-!
# Code tables: logarithmic-time code facts in the kernel

In the kernel a `ByteArray` literal is a list, so `code[pc]?` costs a walk of the whole code
(its size) plus `pc` steps, and a jump destination a scan of the code: on compiled contracts
each fact costs 0.1–0.5 s of kernel time, and symbolic execution checks one per instruction.

A `CodeTable` holds the bytes and the `JUMPDEST` positions of one code as binary tries of fixed
depth, checked once against the code (`CodeTable.Ok`, by kernel evaluation). Every fact is
then a lookup of `depth` levels: `CodeTable.getElem?_eq` (code bytes),
`CodeTable.toWord_readBytes` (`PUSHn` immediates), `CodeTable.mem_jumpDestList` (jump
destinations, as `isValidJumpDest_of_mem` and `isValidJumpDest_of_agree` expect them).
The `code_table` command (`EvmLogic.Program.Code`) builds and checks the table of a code
constant; the symbolic-execution tactics use it whenever it exists.
-/

namespace EvmLogic.Program
open EvmLean

/-- A binary trie of bytes indexed by position (bits of the position, most significant first,
at a depth fixed by the caller). -/
inductive ByteTrie where
  /-- No byte below this node. -/
  | nil
  /-- A byte (at depth `0`). -/
  | leaf (b : UInt8)
  /-- Positions below `2 ^ d` on the left, the rest (shifted) on the right. -/
  | node (lo hi : ByteTrie)
  deriving Inhabited

namespace ByteTrie

/-- The trie of depth `d` of a list of at most `2 ^ d` bytes. -/
def ofList : Nat → List UInt8 → ByteTrie
  | _, [] => nil
  | 0, b :: _ => leaf b
  | d + 1, b :: bs => node (ofList d ((b :: bs).take (2 ^ d))) (ofList d ((b :: bs).drop (2 ^ d)))

/-- The byte at position `i` of a trie of depth `d`. -/
def get : Nat → ByteTrie → Nat → Option UInt8
  | _, nil, _ => none
  | _, leaf b, i => cond (Nat.beq i 0) (some b) none
  | 0, node _ _, _ => none
  | d + 1, node lo hi, i => cond (Nat.blt i (2 ^ d)) (get d lo i) (get d hi (i - 2 ^ d))

/-- Set position `i` (below `2 ^ d`) of a trie of depth `d` to `b`; other positions, and
malformed tries, are left alone. -/
def set : Nat → ByteTrie → Nat → UInt8 → ByteTrie
  | 0, t, i, b => cond (Nat.beq i 0) (leaf b) t
  | d + 1, nil, i, b =>
    cond (Nat.blt i (2 ^ d)) (node (set d nil i b) nil) (node nil (set d nil (i - 2 ^ d) b))
  | _ + 1, leaf c, _, _ => leaf c
  | d + 1, node lo hi, i, b =>
    cond (Nat.blt i (2 ^ d)) (node (set d lo i b) hi) (node lo (set d hi (i - 2 ^ d) b))

/-- The trie of depth `d` with byte `1` at each listed position. -/
def ofKeys (d : Nat) (keys : List Nat) : ByteTrie :=
  keys.foldr (fun k t => set d t k 1) nil

theorem blt_true {i n : Nat} (h : i < n) : Nat.blt i n = true := Nat.blt_eq.mpr h

theorem blt_false {i n : Nat} (h : ¬ i < n) : Nat.blt i n = false := by
  cases hb : Nat.blt i n
  · rfl
  · exact absurd (Nat.blt_eq.mp hb) h

theorem get_ofList : ∀ (d : Nat) (l : List UInt8) (i : Nat), l.length ≤ 2 ^ d →
    get d (ofList d l) i = l[i]?
  | d, [], i, _ => by cases d <;> simp [ofList, get]
  | 0, [b], i, _ => by
    cases i <;> simp [ofList, get, Nat.beq]
  | 0, b :: c :: l, _, h => by simp at h
  | d + 1, b :: bs, i, h => by
    simp only [ofList, get]
    by_cases hi : i < 2 ^ d
    · rw [blt_true hi, Bool.cond_true, get_ofList d _ i (by simp only [List.length_take]; omega),
        List.getElem?_take]
      simp only [hi, ↓reduceIte]
    · rw [blt_false hi, Bool.cond_false, get_ofList d _ _ (by
        simp only [List.length_drop, List.length_cons] at h ⊢; rw [Nat.pow_succ] at h; omega),
        List.getElem?_drop]
      congr 1; omega

theorem get_nil (d i : Nat) : get d nil i = none := by cases d <;> rfl

theorem get_node (d : Nat) (lo hi : ByteTrie) (i : Nat) :
    get (d + 1) (node lo hi) i = if i < 2 ^ d then get d lo i else get d hi (i - 2 ^ d) := by
  simp only [get]
  by_cases h : i < 2 ^ d
  · simp only [h, ↓reduceIte, blt_true h, Bool.cond_true]
  · simp only [h, ↓reduceIte, blt_false h, Bool.cond_false]

/-- Setting a position changes only that position. -/
theorem get_set_some : ∀ (d : Nat) (t : ByteTrie) (i : Nat) (b v : UInt8) (j : Nat),
    get d (set d t i b) j = some v → (j = i ∧ v = b) ∨ get d t j = some v
  | 0, t, i, b, v, j, h => by
    simp only [set] at h
    cases hi : Nat.beq i 0 <;> simp only [hi, Bool.cond_true, Bool.cond_false] at h
    · exact .inr h
    · have hi0 : i = 0 := Nat.eq_of_beq_eq_true hi
      cases hj : Nat.beq j 0 <;> simp only [get, hj, Bool.cond_true, Bool.cond_false] at h
      · cases h
      · exact .inl ⟨by rw [Nat.eq_of_beq_eq_true hj, hi0], (Option.some.inj h).symm⟩
  | d + 1, t, i, b, v, j, h => by
    have key : ∀ (lo hi : ByteTrie),
        get (d + 1) (cond (Nat.blt i (2 ^ d)) (node (set d lo i b) hi)
          (node lo (set d hi (i - 2 ^ d) b))) j = some v →
        (j = i ∧ v = b) ∨ get (d + 1) (node lo hi) j = some v := by
      intro lo hi h
      by_cases hi' : i < 2 ^ d
      · rw [blt_true hi', Bool.cond_true, get_node] at h
        rw [get_node]
        by_cases hj : j < 2 ^ d
        · simp only [hj, ↓reduceIte] at h ⊢
          exact get_set_some d lo i b v j h
        · simp only [hj, ↓reduceIte] at h ⊢; exact .inr h
      · rw [blt_false hi', Bool.cond_false, get_node] at h
        rw [get_node]
        by_cases hj : j < 2 ^ d
        · simp only [hj, ↓reduceIte] at h ⊢; exact .inr h
        · simp only [hj, ↓reduceIte] at h ⊢
          rcases get_set_some d hi (i - 2 ^ d) b v (j - 2 ^ d) h with ⟨e, hv⟩ | h'
          · exact .inl ⟨by omega, hv⟩
          · exact .inr h'
    cases t with
    | nil =>
      rcases key nil nil h with h' | h'
      · exact .inl h'
      · rw [get_node, get_nil, get_nil] at h'; simp at h'
    | leaf c => exact .inr h
    | node lo hi => exact key lo hi h

theorem mem_of_get_ofKeys (d : Nat) : ∀ (keys : List Nat) (j : Nat),
    get d (ofKeys d keys) j = some 1 → j ∈ keys
  | [], j, h => by simp [ofKeys, get_nil] at h
  | k :: ks, j, h => by
    simp only [ofKeys, List.foldr_cons] at h
    rcases get_set_some d _ k 1 1 j h with ⟨rfl, -⟩ | h'
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_get_ofKeys d ks j h')

/-- Big-endian value of the `n` bytes from `off` (zero where absent), accumulated onto `acc`. -/
def readNat (d : Nat) (t : ByteTrie) : (off n acc : Nat) → Nat
  | _, 0, acc => acc
  | off, n + 1, acc => readNat d t (off + 1) n (acc * 256 + ((get d t off).getD 0).toNat)

theorem readNat_eq (d : Nat) (t : ByteTrie) : ∀ (n off acc : Nat),
    readNat d t off n acc =
      (List.range' off n).foldl (fun acc j => acc * 256 + ((get d t j).getD 0).toNat) acc
  | 0, _, _ => rfl
  | n + 1, off, acc => by
    rw [readNat, readNat_eq d t n, List.range'_succ, List.foldl_cons]

end ByteTrie

end EvmLogic.Program

section

namespace EvmLogic.Program
open EvmLean EvmLean.Interpreter

/-- The table of one code: its bytes and its `JUMPDEST` positions as tries of depth
`depth`. -/
structure CodeTable where
  /-- Depth of both tries (the code has at most `2 ^ depth` bytes). -/
  depth : Nat
  /-- The bytes. -/
  bytes : ByteTrie
  /-- Byte `1` at each valid jump destination. -/
  jumpDests : ByteTrie

/-- A table is right for `code` (checked once, by kernel evaluation). -/
structure CodeTable.Ok (code : ByteArray) (t : CodeTable) : Prop where
  size : Nat.ble code.size (2 ^ t.depth) = true
  bytes : ByteTrie.ofList t.depth code.data.toList = t.bytes
  jumpDests :
    ByteTrie.ofKeys t.depth (Solidity.jumpDestList (code.size + 1) code.data.toList 0) =
      t.jumpDests

namespace CodeTable

variable {code : ByteArray} {t : CodeTable}

theorem Ok.size_le (h : Ok code t) : code.data.toList.length ≤ 2 ^ t.depth := by
  have := Nat.le_of_ble_eq_true h.size
  simpa using this

theorem Ok.get (h : Ok code t) (i : Nat) : t.bytes.get t.depth i = code.data.toList[i]? := by
  rw [← h.bytes, ByteTrie.get_ofList _ _ _ h.size_le]

/-- **A code byte** from a table lookup. -/
theorem getElem?_eq (h : Ok code t) {pc : Nat} {b : UInt8} (hb : t.bytes.get t.depth pc = some b) :
    code[pc]? = some b := by
  rw [h.get] at hb
  rw [← hb]
  by_cases hk : pc < code.size
  · have hk' : pc < code.data.toList.length := by simpa using hk
    rw [getElem?_pos code pc hk, List.getElem?_eq_getElem hk']
    simp [ByteArray.getElem_eq_getElem_data]
  · have hk' : ¬ pc < code.data.toList.length := by simpa using hk
    rw [getElem?_neg code pc hk, List.getElem?_eq_none (Nat.le_of_not_lt hk')]

/-- **A jump destination** from a table lookup. -/
theorem mem_jumpDestList (h : Ok code t) {d : Nat} (hd : t.jumpDests.get t.depth d = some 1) :
    d ∈ Solidity.jumpDestList (code.size + 1) code.data.toList 0 := by
  rw [← h.jumpDests] at hd
  exact ByteTrie.mem_of_get_ofKeys _ _ _ hd

theorem getD_eq (h : Ok code t) (k : Nat) : Bytes.getD code k = ((t.bytes.get t.depth k).getD 0) := by
  rw [h.get]
  unfold Bytes.getD
  by_cases hk : k < code.size
  · have hk' : k < code.data.toList.length := by simpa using hk
    simp only [hk, ↓reduceDIte, List.getElem?_eq_getElem hk', Option.getD_some,
      ByteArray.getElem_eq_getElem_data, Array.getElem_toList]
  · have hk' : ¬ k < code.data.toList.length := by simpa using hk
    simp only [hk, ↓reduceDIte, List.getElem?_eq_none (Nat.le_of_not_lt hk'), Option.getD_none]

theorem data_readBytes (b : ByteArray) (off n : Nat) :
    (readBytes b off n).data.toList = (List.range' off n).map (Bytes.getD b) := by
  apply List.ext_getElem
  · simp [readBytes_eq_readPadded, Bytes.size_readPadded]
  · intro j h₁ h₂
    have hj : j < n := by simpa using h₂
    have hg := Bytes.getD_readPadded b off n j
    rw [← readBytes_eq_readPadded] at hg
    simp only [hj, ↓reduceIte] at hg
    rw [List.getElem_map, List.getElem_range', Nat.one_mul, ← hg]
    unfold Bytes.getD
    have : j < (readBytes b off n).size := by simpa using h₁
    simp only [this, ↓reduceDIte, ByteArray.getElem_eq_getElem_data, Array.getElem_toList]

/-- **A `PUSHn` immediate** (or any code word) from table lookups. -/
theorem toWord_readBytes (h : Ok code t) {off n v : Nat}
    (hv : ByteTrie.readNat t.depth t.bytes off n 0 = v) :
    Bytes.toWord (readBytes code off n) = BitVec.ofNat 256 v := by
  rw [Bytes.toWord, Bytes.toNat_eq_foldl, ← Array.foldl_toList, data_readBytes, List.foldl_map,
    ← hv, ByteTrie.readNat_eq]
  simp only [getD_eq h]

end CodeTable

end EvmLogic.Program

end
