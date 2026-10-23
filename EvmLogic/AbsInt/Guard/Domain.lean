import EvmLogic.AbsInt.Guard.Effect
import EvmLogic.AbsInt.Domain

/-!
# Guarded abstract interpretation: values and the scan

`GVal` extends the values of `EvmLogic.AbsInt` (`top`, constants, address immutables `sym k`)
with **atoms** (`atom i`: an address fixed for the frame, such as its sender or the address held
in a pinned storage slot) and `nz` (some nonzero word). A configuration `Cfg` says which
instructions produce atoms (`CALLER`, `SLOAD` of listed constant keys), which addresses are
known to differ (`distinct`: e.g. the sender is not the owner), and which call targets and
storage keys are allowed. With distinctness, `EQ` of two different addresses is `0` and `SUB` is
`nz`, so the branch a guard such as `onlyOwner` takes is known (`Check.lean`).
-/

namespace EvmLogic.AbsInt.Guard
open EvmLean EvmLogic.Program EvmLean.Interpreter EvmLogic.AbsInt

/-! ## Values -/

/-- An abstract word. -/
inductive GVal where
  | top
  | const (n : Nat)
  /-- The address immutable number `k`. -/
  | sym (k : Nat)
  /-- The address atom number `i`. -/
  | atom (i : Nat)
  /-- A nonzero word. -/
  | nz
  deriving DecidableEq, Repr

/-- A valuation of immutables and atoms (all addresses). -/
structure Env where
  ρ : Nat → Address
  ε : Nat → Address

namespace GVal

/-- Concretisation. -/
def Holds (ν : Env) : GVal → Word → Prop
  | .top, _ => True
  | .const n, w => w.toNat = n
  | .sym k, w => w = Word.ofAddress (ν.ρ k)
  | .atom i, w => w = Word.ofAddress (ν.ε i)
  | .nz, w => w ≠ 0

/-- The address an immutable or atom denotes. -/
def addr (ν : Env) : GVal → Option Address
  | .sym k => some (ν.ρ k)
  | .atom i => some (ν.ε i)
  | _ => none

theorem holds_of_addr {ν : Env} {a : GVal} {x : Address} {w : Word} (h : a.addr ν = some x)
    (hw : a.Holds ν w) : w = Word.ofAddress x := by
  cases a <;> simp only [addr, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> exact hw

end GVal

abbrev GStack := List GVal

/-- A concrete stack described by an abstract one: same length, pointwise. -/
def GStackOk (ν : Env) : GStack → List Word → Prop
  | [], [] => True
  | a :: s, w :: st => a.Holds ν w ∧ GStackOk ν s st
  | _, _ => False

def memS (s : GStack) : List GStack → Bool
  | [] => false
  | t :: ts => s == t || memS s ts

theorem mem_of_memS {s : GStack} : ∀ {ss : List GStack}, memS s ss = true → s ∈ ss
  | [], h => by simp [memS] at h
  | t :: ts, h => by
    simp only [memS, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_memS h)

/-! ## Configurations -/

/-- What the analysis may assume about a frame, and what it checks. -/
structure Cfg where
  /-- `CALLER` pushes this atom. -/
  callerAtom : Option Nat := none
  /-- `SLOAD` of the constant key `k` pushes the atom `i`, for `(k, i)` listed. -/
  slots : List (Nat × Nat) := []
  /-- Pairs of immutables or atoms denoting different addresses. -/
  distinct : List (GVal × GVal) := []
  /-- Allowed call targets (the second stack item of a `CALL`-family instruction). -/
  callAllowed : GVal → Bool
  /-- Allowed `SSTORE` keys. -/
  sstoreAllowed : GVal → Bool

namespace Cfg

def Differ (cfg : Cfg) (a b : GVal) : Bool :=
  cfg.distinct.contains (a, b) || cfg.distinct.contains (b, a)

/-- The atom for the constant key `k`, if any. -/
def slotAtom (cfg : Cfg) (k : Nat) : Option Nat :=
  (cfg.slots.find? (fun p => p.1 == k)).map Prod.snd

end Cfg

/-- The distinctness facts hold. -/
def DistinctOk (ν : Env) (cfg : Cfg) : Prop :=
  ∀ a b, (a, b) ∈ cfg.distinct → ∃ x y, a.addr ν = some x ∧ b.addr ν = some y ∧ x ≠ y

theorem DistinctOk.differ {ν : Env} {cfg : Cfg} (h : DistinctOk ν cfg) {a b : GVal}
    (hd : cfg.Differ a b = true) : ∃ x y, a.addr ν = some x ∧ b.addr ν = some y ∧ x ≠ y := by
  simp only [Cfg.Differ, Bool.or_eq_true, List.contains_iff_mem] at hd
  rcases hd with hd | hd
  · exact h a b hd
  · obtain ⟨x, y, hx, hy, hne⟩ := h b a hd
    exact ⟨y, x, hy, hx, Ne.symm hne⟩

/-! ## Folded operations -/

theorem ofAddress_injective {x y : Address} (h : Word.ofAddress x = Word.ofAddress y) : x = y := by
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h
  rwa [toNat_ofAddress, toNat_ofAddress] at this

/-- Abstract `SHL`. -/
def gshl : GVal → GVal → GVal
  | .const x, .const y => .const (if x < 256 then (y <<< x) % 2 ^ 256 else 0)
  | _, _ => .top

/-- Abstract `SUB`: constants; two different addresses give a nonzero word. -/
def gsub (cfg : Cfg) : GVal → GVal → GVal
  | .const x, .const y => .const ((x + (2 ^ 256 - y)) % 2 ^ 256)
  | a, b => if cfg.Differ a b then .nz else .top

/-- Abstract `AND`: constants, and an address mask keeps an address. -/
def gand : GVal → GVal → GVal
  | .const x, .const y => .const (x &&& y)
  | .const c, .sym k => if isAddrMask c then .sym k else .top
  | .sym k, .const c => if isAddrMask c then .sym k else .top
  | .const c, .atom i => if isAddrMask c then .atom i else .top
  | .atom i, .const c => if isAddrMask c then .atom i else .top
  | _, _ => .top

/-- Abstract `EQ`: constants; two different addresses are unequal; an address equals itself. -/
def geq (cfg : Cfg) : GVal → GVal → GVal
  | .const x, .const y => .const (if x = y then 1 else 0)
  | .sym k, .sym k' => if k = k' then .const 1 else if cfg.Differ (.sym k) (.sym k') then .const 0
      else .top
  | .atom i, .atom i' => if i = i' then .const 1 else if cfg.Differ (.atom i) (.atom i') then
      .const 0 else .top
  | a, b => if cfg.Differ a b then .const 0 else .top

/-- Abstract `ISZERO`. -/
def giszero : GVal → GVal
  | .const n => .const (if n = 0 then 1 else 0)
  | .nz => .const 0
  | _ => .top

variable {ν : Env} {cfg : Cfg}

theorem gshl_holds {a b : GVal} {x y : Word} (ha : a.Holds ν x) (hb : b.Holds ν y) :
    (gshl a b).Holds ν (Word.shl x y) := by
  cases a <;> cases b <;> simp only [gshl, GVal.Holds] at ha hb ⊢
  subst ha hb
  unfold Word.shl
  split <;> simp [BitVec.toNat_shiftLeft, *]

theorem sub_ne_zero_of_differ (hd : DistinctOk ν cfg) {a b : GVal} {x y : Word}
    (hdiff : cfg.Differ a b = true) (ha : a.Holds ν x) (hb : b.Holds ν y) : x - y ≠ 0 := by
  obtain ⟨u, v, hu, hv, hne⟩ := hd.differ hdiff
  rw [GVal.holds_of_addr hu ha, GVal.holds_of_addr hv hb]
  intro h
  exact hne (ofAddress_injective (by bv_omega))

theorem gsub_holds (hd : DistinctOk ν cfg) {a b : GVal} {x y : Word} (ha : a.Holds ν x)
    (hb : b.Holds ν y) : (gsub cfg a b).Holds ν (x - y) := by
  have hgen : (if cfg.Differ a b then GVal.nz else .top).Holds ν (x - y) := by
    split
    · exact sub_ne_zero_of_differ hd (by assumption) ha hb
    · trivial
  cases a <;> cases b <;> first
    | exact hgen
    | (simp only [gsub, GVal.Holds] at ha hb ⊢; subst ha hb; rw [BitVec.toNat_sub, Nat.add_comm])

theorem gand_holds {a b : GVal} {x y : Word} (ha : a.Holds ν x) (hb : b.Holds ν y) :
    (gand a b).Holds ν (x &&& y) := by
  cases a <;> cases b <;> simp only [gand, GVal.Holds] at ha hb ⊢
  · subst ha hb; rw [BitVec.toNat_and]
  · rename_i c k
    subst hb
    by_cases h : isAddrMask c = true
    · simp only [h, ite_true]; subst ha; exact and_ofAddress h
    · simp only [h, Bool.false_eq_true, ite_false]
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
  · rename_i k c
    subst ha
    by_cases h : isAddrMask c = true
    · simp only [h, ite_true]; subst hb; rw [BitVec.and_comm]; exact and_ofAddress h
    · simp only [h, Bool.false_eq_true, ite_false]

theorem toNat_ofBool (b : Bool) : (Word.ofBool b).toNat = if b then 1 else 0 := by
  cases b <;> rfl

theorem eq_zero_of_differ (hd : DistinctOk ν cfg) {a b : GVal} {x y : Word}
    (hdiff : cfg.Differ a b = true) (ha : a.Holds ν x) (hb : b.Holds ν y) :
    (Word.eq x y).toNat = 0 := by
  have := sub_ne_zero_of_differ hd hdiff ha hb
  have hne : x ≠ y := fun h => this (by rw [h, BitVec.sub_self]; rfl)
  unfold Word.eq
  rw [toNat_ofBool]
  simp [hne]

theorem geq_holds (hd : DistinctOk ν cfg) {a b : GVal} {x y : Word} (ha : a.Holds ν x)
    (hb : b.Holds ν y) : (geq cfg a b).Holds ν (Word.eq x y) := by
  have hgen : (if cfg.Differ a b then GVal.const 0 else .top).Holds ν (Word.eq x y) := by
    split
    · exact eq_zero_of_differ hd (by assumption) ha hb
    · trivial
  cases a <;> cases b <;> first
    | exact hgen
    | skip
  · simp only [geq, GVal.Holds] at ha hb ⊢
    unfold Word.eq
    rw [toNat_ofBool]
    rename_i n n'
    by_cases h : n = n'
    · subst h; simp [BitVec.eq_of_toNat_eq (ha.trans hb.symm)]
    · have : x ≠ y := fun e => h (ha.symm.trans (e ▸ hb))
      simp [h, this]
  · rename_i k k'
    simp only [geq]
    by_cases h : k = k'
    · subst h
      simp only [ite_true, GVal.Holds] at ha hb ⊢
      unfold Word.eq; rw [toNat_ofBool, ha, hb]; simp
    · simp only [h, ite_false]
      split
      · exact eq_zero_of_differ hd (by assumption) ha hb
      · trivial
  · rename_i i i'
    simp only [geq]
    by_cases h : i = i'
    · subst h
      simp only [ite_true, GVal.Holds] at ha hb ⊢
      unfold Word.eq; rw [toNat_ofBool, ha, hb]; simp
    · simp only [h, ite_false]
      split
      · exact eq_zero_of_differ hd (by assumption) ha hb
      · trivial

theorem giszero_holds {a : GVal} {x : Word} (ha : a.Holds ν x) :
    (giszero a).Holds ν (Word.iszero x) := by
  cases a <;> simp only [giszero, GVal.Holds] at ha ⊢ <;> unfold Word.iszero <;> rw [toNat_ofBool]
  · rename_i n
    by_cases h : n = 0
    · subst h
      have hx : x = 0 := BitVec.eq_of_toNat_eq (by simpa using ha)
      simp [hx]
    · have hx : x ≠ 0 := fun e => h (by rw [← ha, e]; rfl)
      simp only [h, ite_false]
      simp only [beq_iff_eq, ite_eq_right_iff]
      exact fun e => absurd e hx
  · simp only [beq_iff_eq, ite_eq_right_iff]
    exact fun e => absurd e ha

/-! ## The scan -/

/-- The abstract immediate of the instruction at `p`: listed `PUSH32`s are immutables, every
other immediate is a constant. -/
def gimmOf (syms : List (Nat × Nat)) (p : Nat) (b : UInt8) (bs : List UInt8) : GVal :=
  if GasMono.immSize b = 32 then
    match symAt p syms with
    | some k => .sym k
    | none => .const (beTake 32 bs 0)
  else .const (beTake (GasMono.immSize b) bs 0)

theorem toNat_toWord_readBytes' (code : ByteArray) (off n : Nat) (hn : n ≤ 32) :
    (Bytes.toWord (readBytes code off n)).toNat = beTake n (code.data.toList.drop off) 0 := by
  rw [readBytes_eq_readPadded, Bytes.toWord, BitVec.toNat_ofNat, Bytes.toNat_eq_foldl,
    ← Array.foldl_toList, data_readPadded, ← beTake_eq]
  apply Nat.mod_eq_of_lt
  have h := beTake_lt n (code.data.toList.drop off) 0
  have h2 : 256 ^ n ≤ 256 ^ 32 := Nat.pow_le_pow_right (by omega) hn
  simp only [Nat.zero_add, Nat.one_mul] at h
  have h3 : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  omega

def gscanFrom (syms : List (Nat × Nat)) : (fuel : Nat) → List UInt8 → Nat →
    List (Nat × GEff × GVal)
  | 0, _, _ => []
  | _ + 1, [], _ => []
  | f + 1, b :: bs, p =>
    (p, gbyteEff b, gimmOf syms p b bs) ::
      gscanFrom syms f (bs.drop (GasMono.immSize b)) (p + 1 + GasMono.immSize b)

/-- The decorated scan of the whole code. -/
def gscan (code : ByteArray) (syms : List (Nat × Nat)) : List (Nat × GEff × GVal) :=
  gscanFrom syms code.size code.data.toList 0

/-- A scan entry is right. -/
def GInsOk (ν : Env) (code : ByteArray) (q : Nat) (e : GEff) (imm : GVal) : Prop :=
  ∃ b, code[q]? = some b ∧ e = gbyteEff b ∧
    imm.Holds ν (Bytes.toWord (readBytes code (q + 1) (GasMono.immSize b)))

theorem gscanFrom_ok {ν : Env} {code : ByteArray} {syms : List (Nat × Nat)}
    (hs : SymOk ν.ρ code syms) (fuel : Nat) :
    ∀ p, ∀ x ∈ gscanFrom syms fuel (code.data.toList.drop p) p, GInsOk ν code x.1 x.2.1 x.2.2 := by
  induction fuel with
  | zero => intro p x hx; simp [gscanFrom] at hx
  | succ f ih =>
    intro p x hx
    cases hd : code.data.toList.drop p with
    | nil => rw [hd] at hx; simp [gscanFrom] at hx
    | cons b bs =>
      rw [hd] at hx
      simp only [gscanFrom, List.mem_cons] at hx
      have htail : bs = code.data.toList.drop (p + 1) := by
        rw [← List.drop_drop, hd]; rfl
      rcases hx with rfl | hx
      · refine ⟨b, getElem?_of_drop hd, rfl, ?_⟩
        unfold gimmOf
        split
        · rename_i h32
          split
          · rename_i k hk
            rw [h32]; exact hs p k hk
          · simp only [GVal.Holds]
            rw [h32, toNat_toWord_readBytes' _ _ _ (by omega), htail]
        · rename_i h32
          simp only [GVal.Holds]
          rw [toNat_toWord_readBytes' _ _ _ (immSize_le b), htail]
      · have := ih (p + 1 + GasMono.immSize b) x (by
          rw [htail, List.drop_drop] at hx; exact hx)
        exact this

/-- **The scan is right.** -/
theorem gscan_ok {ν : Env} {code : ByteArray} {syms : List (Nat × Nat)}
    (hs : SymOk ν.ρ code syms) : ∀ x ∈ gscan code syms, GInsOk ν code x.1 x.2.1 x.2.2 := by
  intro x hx
  exact gscanFrom_ok hs code.size 0 x (by simpa [gscan] using hx)

end EvmLogic.AbsInt.Guard
