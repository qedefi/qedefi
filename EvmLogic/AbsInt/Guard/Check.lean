import EvmLogic.AbsInt.Guard.Domain

/-!
# Guarded abstract interpretation: the abstract step and the certificate

`gsucc` is the abstract step. Unlike `EvmLogic.AbsInt.asucc`, a `JUMPI` whose condition is known
(a constant, or `nz`) has one successor, so code behind a guard that the configuration decides
(`onlyOwner` when the sender is known not to be the owner) is never explored. `gok` checks call
targets and `SSTORE` keys. Soundness (`gsucc_next`) holds for machines satisfying the
configuration's facts (`EnvOk`: the sender atom is the sender, pinned slots hold their atoms, the
distinct addresses differ). `gcertify_sound`: the exploration's result is a certificate.
-/

namespace EvmLogic.AbsInt.Guard
open EvmLean EvmLogic.Program EvmLean.Interpreter EvmLogic.AbsInt

/-! ## The abstract step -/

/-- The abstract successors of `(q, s)` at an instruction of shape `e` with immediate `imm`
(`none`: unresolved jump). -/
def gsucc (cfg : Cfg) : GEff → GVal → Nat → GStack → Option (List (Nat × GStack))
  | .gen p k, _, q, s =>
    some (if p ≤ s.length then [(q + 1, List.replicate k .top ++ s.drop p)] else [])
  | .halt, _, _, _ => some []
  | .push n, imm, q, s => some [(q + (1 + n), imm :: s)]
  | .dup n, _, q, s =>
    some (match s[n]? with
      | some v => [(q + 1, v :: s)]
      | none => [])
  | .swap n, _, q, s =>
    some (match s, s[n + 1]? with
      | t :: r, some x => [(q + 1, ((t :: r).set 0 x).set (n + 1) t)]
      | _, _ => [])
  | .jump, _, _, s =>
    match s with
    | [] => some []
    | .const d :: r => some [(d, r)]
    | _ :: _ => none
  | .jumpi, _, q, s =>
    match s with
    | [] => some []
    | [_] => some []
    | .const d :: c :: r =>
      some (match c with
        | .const 0 => [(q + 1, r)]
        | .const _ => [(d, r)]
        | .nz => [(d, r)]
        | _ => [(d, r), (q + 1, r)])
    | _ :: _ :: _ => none
  | .shl, _, q, s =>
    some (match s with
      | a :: b :: r => [(q + 1, gshl a b :: r)]
      | _ => [])
  | .sub, _, q, s =>
    some (match s with
      | a :: b :: r => [(q + 1, gsub cfg a b :: r)]
      | _ => [])
  | .and, _, q, s =>
    some (match s with
      | a :: b :: r => [(q + 1, gand a b :: r)]
      | _ => [])
  | .eq, _, q, s =>
    some (match s with
      | a :: b :: r => [(q + 1, geq cfg a b :: r)]
      | _ => [])
  | .iszero, _, q, s =>
    some (match s with
      | a :: r => [(q + 1, giszero a :: r)]
      | _ => [])
  | .caller, _, q, s =>
    some [(q + 1, (match cfg.callerAtom with
      | some i => .atom i
      | none => .top) :: s)]
  | .sload, _, q, s =>
    some (match s with
      | .const k :: r => [(q + 1, (match cfg.slotAtom k with
          | some i => .atom i
          | none => .top) :: r)]
      | _ :: r => [(q + 1, .top :: r)]
      | [] => [])
  | .sstore, _, q, s =>
    some (match s with
      | _ :: _ :: r => [(q + 1, r)]
      | _ => [])
  | .call p, _, q, s => some (if p ≤ s.length then [(q + 1, .top :: s.drop p)] else [])
  | .create p, _, q, s => some (if p ≤ s.length then [(q + 1, .top :: s.drop p)] else [])

/-- Calls go to allowed targets, `SSTORE`s to allowed keys; no creations. -/
def gok (cfg : Cfg) : GEff → GStack → Bool
  | .call _, _ :: t :: _ => cfg.callAllowed t
  | .call _, _ => true
  | .create _, _ => false
  | .sstore, k :: _ => cfg.sstoreAllowed k
  | _, _ => true

/-- **The facts a configuration assumes of a machine.** -/
structure EnvOk (ν : Env) (cfg : Cfg) (m : Machine) : Prop where
  caller : ∀ i, cfg.callerAtom = some i → ν.ε i = m.frame.msg.caller
  slots : ∀ k i, cfg.slotAtom k = some i → ∀ key : Word, key.toNat = k →
    m.world.sload m.frame.msg.currentTarget key = Word.ofAddress (ν.ε i)
  distinct : DistinctOk ν cfg

/-! ## Stacks -/

variable {ν : Env} {cfg : Cfg}

theorem GStackOk.length : ∀ {s : GStack} {st : List Word}, GStackOk ν s st → s.length = st.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [GStackOk.length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem GStackOk.drop : ∀ (p : Nat) {s : GStack} {st : List Word}, GStackOk ν s st →
    GStackOk ν (s.drop p) (st.drop p)
  | 0, _, _, h => h
  | _ + 1, [], [], _ => trivial
  | p + 1, _ :: _, _ :: _, h => GStackOk.drop p h.2
  | _ + 1, [], _ :: _, h => h.elim
  | _ + 1, _ :: _, [], h => h.elim

theorem GStackOk.append : ∀ {a b : GStack} {x y : List Word}, GStackOk ν a x → GStackOk ν b y →
    GStackOk ν (a ++ b) (x ++ y)
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, h, h' => ⟨h.1, GStackOk.append h.2 h'⟩
  | [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, h, _ => h.elim

theorem gstackOk_replicate_top : ∀ (x : List Word), GStackOk ν (List.replicate x.length .top) x
  | [] => trivial
  | _ :: x => ⟨trivial, gstackOk_replicate_top x⟩

theorem GStackOk.getElem? : ∀ {s : GStack} {st : List Word} (n : Nat), GStackOk ν s st →
    ∀ {w}, st[n]? = some w → ∃ a, s[n]? = some a ∧ a.Holds ν w
  | [], [], _, _, _, h => by simp at h
  | a :: _, w :: _, 0, h, _, hw => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
    exact ⟨a, rfl, hw ▸ h.1⟩
  | _ :: _, _ :: _, n + 1, h, _, hw => by
    simp only [List.getElem?_cons_succ] at hw ⊢
    exact GStackOk.getElem? n h.2 hw
  | [], _ :: _, _, h, _, _ => h.elim
  | _ :: _, [], _, h, _, _ => h.elim

theorem GStackOk.set : ∀ {s : GStack} {st : List Word} (n : Nat) {a : GVal} {w : Word},
    GStackOk ν s st → a.Holds ν w → GStackOk ν (s.set n a) (st.set n w)
  | [], [], _, _, _, _, _ => trivial
  | _ :: _, _ :: _, 0, _, _, h, ha => ⟨ha, h.2⟩
  | _ :: _, _ :: _, n + 1, _, _, h, ha => ⟨h.1, GStackOk.set n h.2 ha⟩
  | [], _ :: _, _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, _, h, _ => h.elim

theorem gstackOk_shape {p k : Nat} {s : GStack} {st st' : List Word} (h : GStackOk ν s st)
    (hsh : Shape p k st st') : GStackOk ν (List.replicate k .top ++ s.drop p) st' := by
  obtain ⟨hp, hl, hd⟩ := hsh
  have hk : (st'.take k).length = k := by
    rw [List.length_take]; omega
  have := GStackOk.append (gstackOk_replicate_top (ν := ν) (st'.take k))
    (show GStackOk ν (s.drop p) (st'.drop k) by rw [hd]; exact h.drop p)
  rwa [hk, List.take_append_drop] at this


/-! ## Soundness of the abstract step -/

/-- **A `.next` action lands in an abstract successor.** -/
theorem gsucc_next {e : GEff} {imm : GVal} {q : Nat} {s : GStack} {succs : List (Nat × GStack)}
    {m m' : Machine} (henv : EnvOk ν cfg m) (hs : GStackOk ν s m.frame.stack)
    (hpc : m.frame.pc = q)
    (himm : ∀ n, e = .push n → imm.Holds ν (Bytes.toWord (readBytes m.frame.code (q + 1) n)))
    (hpost : GNextPost e m m') (ha : gsucc cfg e imm q s = some succs) :
    ∃ x ∈ succs, x.1 = m'.frame.pc ∧ GStackOk ν x.2 m'.frame.stack := by
  have hlen := hs.length
  cases e with
  | gen p k =>
    obtain ⟨hpc', hsh⟩ := hpost
    simp only [gsucc, Option.some.injEq] at ha
    subst ha
    have hp : p ≤ s.length := by have := hsh.1; omega
    simp only [hp, ↓reduceIte, List.mem_singleton, exists_eq_left]
    exact ⟨by omega, gstackOk_shape hs hsh⟩
  | halt => exact hpost.elim
  | push n =>
    obtain ⟨hpc', hst⟩ := hpost
    simp only [gsucc, Option.some.injEq] at ha
    subst ha
    simp only [List.mem_singleton, exists_eq_left]
    refine ⟨by omega, ?_⟩
    rw [hst]
    exact ⟨hpc ▸ himm n rfl, hs⟩
  | dup n =>
    obtain ⟨hpc', x, hx, hst⟩ := hpost
    obtain ⟨a, ha', hax⟩ := hs.getElem? n hx
    simp only [gsucc, ha', Option.some.injEq] at ha
    subst ha
    simp only [List.mem_singleton, exists_eq_left]
    exact ⟨by omega, by rw [hst]; exact ⟨hax, hs⟩⟩
  | swap n =>
    obtain ⟨hpc', t, r, x, hst, hx, hst'⟩ := hpost
    rw [hst] at hs
    obtain ⟨b, hb, hbx⟩ := hs.getElem? (n + 1) hx
    cases s with
    | nil => exact hs.elim
    | cons a sr =>
      simp only [gsucc, hb, Option.some.injEq] at ha
      subst ha
      simp only [List.mem_singleton, exists_eq_left]
      exact ⟨by omega, by rw [hst']; exact (hs.set 0 hbx).set (n + 1) hs.1⟩
  | jump =>
    obtain ⟨d, r, hst, hst', hpc'⟩ := hpost
    rw [hst] at hs
    cases s with
    | nil => exact hs.elim
    | cons a sr =>
      cases a with
      | const dd =>
        simp only [gsucc, Option.some.injEq] at ha
        subst ha
        simp only [List.mem_singleton, exists_eq_left]
        exact ⟨by rw [hpc']; exact hs.1.symm, by rw [hst']; exact hs.2⟩
      | top => simp [gsucc] at ha
      | sym _ => simp [gsucc] at ha
      | atom _ => simp [gsucc] at ha
      | nz => simp [gsucc] at ha
  | jumpi =>
    obtain ⟨d, c, r, hst, hst', hpc'⟩ := hpost
    rw [hst] at hs
    match s, hs, ha with
    | .const dd :: cv :: sr, hs, ha =>
      simp only [gsucc, Option.some.injEq] at ha
      subst ha
      have hjump : d.toNat = dd := hs.1
      have htake : ∀ l : List (Nat × GStack), (dd, sr) ∈ l → c ≠ 0 → m'.frame.pc = d.toNat →
          ∃ x ∈ l, x.1 = m'.frame.pc ∧ GStackOk ν x.2 m'.frame.stack := fun l hl _ hp =>
        ⟨(dd, sr), hl, by rw [hp, hjump], by rw [hst']; exact hs.2.2⟩
      have hfall : ∀ l : List (Nat × GStack), (q + 1, sr) ∈ l → c = 0 →
          m'.frame.pc = m.frame.pc + 1 →
          ∃ x ∈ l, x.1 = m'.frame.pc ∧ GStackOk ν x.2 m'.frame.stack := fun l hl _ hp =>
        ⟨(q + 1, sr), hl, by rw [hp, hpc], by rw [hst']; exact hs.2.2⟩
      have hc := hs.2.1
      cases cv with
      | const n =>
        by_cases hn : n = 0
        · subst hn
          rcases hpc' with ⟨hne, -⟩ | ⟨hz, hp⟩
          · exact absurd (BitVec.eq_of_toNat_eq (by simpa [GVal.Holds] using hc)) hne
          · exact hfall _ List.mem_cons_self hz hp
        · have hgoal : ∃ x ∈ (match GVal.const n with
              | .const 0 => [(q + 1, sr)] | .const _ => [(dd, sr)] | .nz => [(dd, sr)]
              | _ => [(dd, sr), (q + 1, sr)]), x.1 = m'.frame.pc ∧
              GStackOk ν x.2 m'.frame.stack := by
            rcases hpc' with ⟨hne, hp⟩ | ⟨hz, -⟩
            · match n, hn with
              | n + 1, _ => exact htake _ List.mem_cons_self hne hp
            · exact absurd (by rw [hz] at hc; simpa [GVal.Holds] using hc.symm) hn
          exact hgoal
      | nz =>
        rcases hpc' with ⟨hne, hp⟩ | ⟨hz, -⟩
        · exact htake _ List.mem_cons_self hne hp
        · exact absurd hz hc
      | top =>
        rcases hpc' with ⟨hne, hp⟩ | ⟨hz, hp⟩
        · exact htake _ List.mem_cons_self hne hp
        · exact hfall _ (List.mem_cons_of_mem _ List.mem_cons_self) hz hp
      | sym _ =>
        rcases hpc' with ⟨hne, hp⟩ | ⟨hz, hp⟩
        · exact htake _ List.mem_cons_self hne hp
        · exact hfall _ (List.mem_cons_of_mem _ List.mem_cons_self) hz hp
      | atom _ =>
        rcases hpc' with ⟨hne, hp⟩ | ⟨hz, hp⟩
        · exact htake _ List.mem_cons_self hne hp
        · exact hfall _ (List.mem_cons_of_mem _ List.mem_cons_self) hz hp
    | .top :: _ :: _, _, ha => simp [gsucc] at ha
    | .sym _ :: _ :: _, _, ha => simp [gsucc] at ha
    | .atom _ :: _ :: _, _, ha => simp [gsucc] at ha
    | .nz :: _ :: _, _, ha => simp [gsucc] at ha
    | [], hs, _ => exact hs.elim
    | [_], hs, _ => exact hs.2.elim
  | shl =>
    obtain ⟨hpc', x, y, r, hst, hst'⟩ := hpost
    rw [hst] at hs
    match s, hs, ha with
    | a :: b :: sr, hs, ha =>
      simp only [gsucc, Option.some.injEq] at ha
      subst ha
      simp only [List.mem_singleton, exists_eq_left]
      exact ⟨by omega, by rw [hst']; exact ⟨gshl_holds hs.1 hs.2.1, hs.2.2⟩⟩
    | [], hs, _ => exact hs.elim
    | [_], hs, _ => exact hs.2.elim
  | sub =>
    obtain ⟨hpc', x, y, r, hst, hst'⟩ := hpost
    rw [hst] at hs
    match s, hs, ha with
    | a :: b :: sr, hs, ha =>
      simp only [gsucc, Option.some.injEq] at ha
      subst ha
      simp only [List.mem_singleton, exists_eq_left]
      exact ⟨by omega, by rw [hst']; exact ⟨gsub_holds henv.distinct hs.1 hs.2.1, hs.2.2⟩⟩
    | [], hs, _ => exact hs.elim
    | [_], hs, _ => exact hs.2.elim
  | and =>
    obtain ⟨hpc', x, y, r, hst, hst'⟩ := hpost
    rw [hst] at hs
    match s, hs, ha with
    | a :: b :: sr, hs, ha =>
      simp only [gsucc, Option.some.injEq] at ha
      subst ha
      simp only [List.mem_singleton, exists_eq_left]
      exact ⟨by omega, by rw [hst']; exact ⟨gand_holds hs.1 hs.2.1, hs.2.2⟩⟩
    | [], hs, _ => exact hs.elim
    | [_], hs, _ => exact hs.2.elim
  | eq =>
    obtain ⟨hpc', x, y, r, hst, hst'⟩ := hpost
    rw [hst] at hs
    match s, hs, ha with
    | a :: b :: sr, hs, ha =>
      simp only [gsucc, Option.some.injEq] at ha
      subst ha
      simp only [List.mem_singleton, exists_eq_left]
      exact ⟨by omega, by rw [hst']; exact ⟨geq_holds henv.distinct hs.1 hs.2.1, hs.2.2⟩⟩
    | [], hs, _ => exact hs.elim
    | [_], hs, _ => exact hs.2.elim
  | iszero =>
    obtain ⟨hpc', x, r, hst, hst'⟩ := hpost
    rw [hst] at hs
    match s, hs, ha with
    | a :: sr, hs, ha =>
      simp only [gsucc, Option.some.injEq] at ha
      subst ha
      simp only [List.mem_singleton, exists_eq_left]
      exact ⟨by omega, by rw [hst']; exact ⟨giszero_holds hs.1, hs.2⟩⟩
    | [], hs, _ => exact hs.elim
  | caller =>
    obtain ⟨hpc', hst'⟩ := hpost
    simp only [gsucc, Option.some.injEq] at ha
    subst ha
    simp only [List.mem_singleton, exists_eq_left]
    refine ⟨by omega, ?_⟩
    rw [hst']
    refine ⟨?_, hs⟩
    cases hc : cfg.callerAtom with
    | none => trivial
    | some i => show _ = _; rw [henv.caller i hc]
  | sload =>
    obtain ⟨hpc', k, r, hst, hst'⟩ := hpost
    rw [hst] at hs
    match s, hs, ha with
    | .const kk :: sr, hs, ha =>
      simp only [gsucc, Option.some.injEq] at ha
      subst ha
      simp only [List.mem_singleton, exists_eq_left]
      refine ⟨by omega, ?_⟩
      rw [hst']
      refine ⟨?_, hs.2⟩
      cases hk : cfg.slotAtom kk with
      | none => trivial
      | some i => exact henv.slots kk i hk k hs.1
    | .top :: sr, hs, ha | .sym _ :: sr, hs, ha | .atom _ :: sr, hs, ha | .nz :: sr, hs, ha =>
      simp only [gsucc, Option.some.injEq] at ha
      subst ha
      simp only [List.mem_singleton, exists_eq_left]
      exact ⟨by omega, by rw [hst']; exact ⟨trivial, hs.2⟩⟩
    | [], hs, _ => exact hs.elim
  | sstore =>
    obtain ⟨hpc', k, v, r, hst, hst'⟩ := hpost
    rw [hst] at hs
    match s, hs, ha with
    | a :: b :: sr, hs, ha =>
      simp only [gsucc, Option.some.injEq] at ha
      subst ha
      simp only [List.mem_singleton, exists_eq_left]
      exact ⟨by omega, by rw [hst']; exact hs.2.2⟩
    | [], hs, _ => exact hs.elim
    | [_], hs, _ => exact hs.2.elim
  | call p =>
    obtain ⟨hpc', hsh⟩ := hpost
    simp only [gsucc, Option.some.injEq] at ha
    subst ha
    have hp : p ≤ s.length := by have := hsh.1; omega
    simp only [hp, ↓reduceIte, List.mem_singleton, exists_eq_left]
    exact ⟨by omega, gstackOk_shape (k := 1) hs hsh⟩
  | create p =>
    obtain ⟨hpc', hsh⟩ := hpost
    simp only [gsucc, Option.some.injEq] at ha
    subst ha
    have hp : p ≤ s.length := by have := hsh.1; omega
    simp only [hp, ↓reduceIte, List.mem_singleton, exists_eq_left]
    exact ⟨by omega, gstackOk_shape (k := 1) hs hsh⟩

theorem gsucc_popped {p : Nat} {imm : GVal} {q : Nat} {s : GStack}
    {succs : List (Nat × GStack)} {e : GEff} (he : e = .call p ∨ e = .create p)
    {m m' : Machine} (hs : GStackOk ν s m.frame.stack) (hpop : Popped p m m')
    (ha : gsucc cfg e imm q s = some succs) (w : Word) :
    ∃ x ∈ succs, x.1 = q + 1 ∧ GStackOk ν x.2 (w :: m'.frame.stack) := by
  obtain ⟨-, hp, hst⟩ := hpop
  have hp' : p ≤ s.length := by rw [hs.length]; exact hp
  rcases he with rfl | rfl <;>
  · simp only [gsucc, hp', ↓reduceIte, Option.some.injEq] at ha
    subst ha
    exact ⟨_, List.mem_singleton_self _, rfl, trivial, by rw [hst]; exact hs.drop p⟩

/-- **The continuation after a requested child** (call or creation). -/
theorem gsucc_child {e : GEff} {imm : GVal} {q : Nat} {s : GStack}
    {succs : List (Nat × GStack)} {m m' : Machine} (hs : GStackOk ν s m.frame.stack)
    (hpost : GCallPost e m m' ∨ GCreatePost e m m') (ha : gsucc cfg e imm q s = some succs)
    (w : Word) : ∃ x ∈ succs, x.1 = q + 1 ∧ GStackOk ν x.2 (w :: m'.frame.stack) := by
  cases e <;> simp only [GCallPost, GCreatePost, or_false, false_or] at hpost
  · exact gsucc_popped (.inl rfl) hs hpost ha w
  · exact gsucc_popped (.inr rfl) hs hpost ha w

/-- **Allowed call targets.** -/
theorem gok_target {p : Nat} {s : GStack} {st : List Word}
    (hok : gok cfg (.call p) s = true) (hs : GStackOk ν s st) {t : Word}
    (ht : st[1]? = some t) : ∃ a, cfg.callAllowed a = true ∧ a.Holds ν t := by
  obtain ⟨a, ha, hat⟩ := hs.getElem? 1 ht
  match s, ha, hok with
  | _ :: b :: _, ha, hok =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at ha
    subst ha
    exact ⟨_, hok, hat⟩

/-- **Allowed storage keys.** -/
theorem gok_sstore {s : GStack} {st : List Word} (hok : gok cfg .sstore s = true)
    (hs : GStackOk ν s st) {k : Word} {r : List Word} (hk : st = k :: r) :
    ∃ a, cfg.sstoreAllowed a = true ∧ a.Holds ν k := by
  subst hk
  match s, hs, hok with
  | a :: _, hs, hok => exact ⟨a, hok, hs.1⟩

/-! ## The table -/

/-- The certificate table: a binary tree with, per instruction (pc, shape, abstract
immediate), the abstract stacks reached there. -/
inductive GTree where
  | leaf
  | node (l : GTree) (q : Nat) (e : GEff) (imm : GVal) (ss : List GStack) (r : GTree)

namespace GTree
open EvmLean EvmLogic.Program

def find (q : Nat) : GTree → Option (GEff × GVal × List GStack)
  | leaf => none
  | node l k e imm ss r =>
    if Nat.blt q k then l.find q else if Nat.blt k q then r.find q else some (e, imm, ss)

/-- Record the stack `s` at `q` (no-op if `q` is not an entry). -/
def add (q : Nat) (s : GStack) : GTree → GTree
  | leaf => leaf
  | node l k e imm ss r =>
    if Nat.blt q k then node (l.add q s) k e imm ss r
    else if Nat.blt k q then node l k e imm ss (r.add q s)
    else node l k e imm (s :: ss) r

/-- A balanced tree of the first `n` entries of a sorted list, with no stacks, and the
remaining entries (linear time; structural fuel: the depth). -/
def build : (fuel n : Nat) → List (Nat × GEff × GVal) → GTree × List (Nat × GEff × GVal)
  | 0, _, l => (leaf, l)
  | f + 1, n, l =>
    if n = 0 then (leaf, l) else
    match build f ((n - 1) / 2) l with
    | (lt, []) => (lt, [])
    | (lt, (q, e, imm) :: l₂) =>
      match build f (n - 1 - (n - 1) / 2) l₂ with
      | (rt, l₃) => (node lt q e imm [] rt, l₃)

def Fresh : GTree → Prop
  | leaf => True
  | node l _ _ _ ss r => Fresh l ∧ ss = [] ∧ Fresh r

def All (P : Nat → GEff → GVal → Prop) : GTree → Prop
  | leaf => True
  | node l q e imm _ r => All P l ∧ P q e imm ∧ All P r

theorem find_add (q q' : Nat) (s : GStack) : ∀ t : GTree,
    (add q s t).find q' =
      if q' = q then (t.find q).map (fun x => (x.1, x.2.1, s :: x.2.2)) else t.find q'
  | leaf => by simp [add, find]
  | node l k e imm ss r => by
    have ihl := find_add q q' s l
    have ihr := find_add q q' s r
    by_cases h : q' = q
    · subst h
      by_cases h1 : q' < k
      · simp [add, find, Nat.blt_eq, h1, ihl]
      · by_cases h2 : k < q'
        · simp [add, find, Nat.blt_eq, h1, h2, ihr]
        · simp [add, find, Nat.blt_eq, h1, h2]
    · simp only [h, ↓reduceIte]
      by_cases h1 : q < k
      · by_cases h1' : q' < k
        · simp [add, find, Nat.blt_eq, h1, h1', ihl, h]
        · simp [add, find, Nat.blt_eq, h1, h1']
      · by_cases h2 : k < q
        · by_cases h2' : k < q'
          · simp [add, find, Nat.blt_eq, h1, h2, h2', ihr, h]
          · simp [add, find, Nat.blt_eq, h1, h2, h2']
        · have hk : q = k := by omega
          subst hk
          by_cases h1' : q' < q
          · simp [add, find, Nat.blt_eq, h1, h1']
          · have : q < q' := by omega
            simp [add, find, Nat.blt_eq, h1, h1', this]

theorem All.find {P : Nat → GEff → GVal → Prop} : ∀ {t : GTree}, t.All P → ∀ {q e imm ss},
    t.find q = some (e, imm, ss) → P q e imm
  | leaf, _, _, _, _, _, h => by simp [GTree.find] at h
  | node l k e' imm' ss' r, hA, q, e, imm, ss, h => by
    simp only [GTree.find] at h
    split at h
    · exact All.find hA.1 h
    · split at h
      · exact All.find hA.2.2 h
      · cases h
        rename_i h1 h2
        have : q = k := by simp only [Nat.blt_eq] at h1 h2; omega
        subst this; exact hA.2.1

theorem Fresh.find : ∀ {t : GTree}, t.Fresh → ∀ {q e imm ss}, t.find q = some (e, imm, ss) →
    ss = []
  | leaf, _, _, _, _, _, h => by simp [GTree.find] at h
  | node l k e' imm' ss' r, hF, q, e, imm, ss, h => by
    simp only [GTree.find] at h
    split at h
    · exact Fresh.find hF.1 h
    · split at h
      · exact Fresh.find hF.2.2 h
      · cases h; exact hF.2.1

theorem All.add {P : Nat → GEff → GVal → Prop} (q : Nat) (s : GStack) :
    ∀ {t : GTree}, t.All P → (t.add q s).All P
  | leaf, h => h
  | node l k e imm ss r, h => by
    simp only [GTree.add]
    split
    · exact ⟨All.add q s h.1, h.2.1, h.2.2⟩
    · split
      · exact ⟨h.1, h.2.1, All.add q s h.2.2⟩
      · exact ⟨h.1, h.2.1, h.2.2⟩

theorem build_ok {P : Nat → GEff → GVal → Prop} : ∀ (f n : Nat) (l : List (Nat × GEff × GVal)),
    (∀ x ∈ l, P x.1 x.2.1 x.2.2) →
      (build f n l).1.All P ∧ (build f n l).1.Fresh ∧ ∀ x ∈ (build f n l).2, x ∈ l
  | 0, _, _, _ => ⟨trivial, trivial, fun _ hx => hx⟩
  | f + 1, n, l, h => by
    simp only [build]
    split
    · exact ⟨trivial, trivial, fun _ hx => hx⟩
    · obtain ⟨hA₁, hF₁, hm₁⟩ := build_ok f ((n - 1) / 2) l h
      split
      · rename_i heq
        rw [heq] at hA₁ hF₁
        exact ⟨hA₁, hF₁, fun _ hx => by cases hx⟩
      · rename_i lt q e imm l₂ heq
        rw [heq] at hA₁ hF₁ hm₁
        have hq : (q, e, imm) ∈ l := hm₁ _ List.mem_cons_self
        have h₂ : ∀ x ∈ l₂, x ∈ l := fun x hx => hm₁ x (List.mem_cons_of_mem _ hx)
        obtain ⟨hA₂, hF₂, hm₂⟩ := build_ok f (n - 1 - (n - 1) / 2) l₂ (fun x hx => h x (h₂ x hx))
        exact ⟨⟨hA₁, h _ hq, hA₂⟩, ⟨hF₁, rfl, hF₂⟩, fun x hx => h₂ x (hm₂ x hx)⟩

end GTree

/-! ## Exploration -/

/-- The abstract state `(q, s)` is recorded in `t`. -/
def GInT (t : GTree) (q : Nat) (s : GStack) : Prop :=
  ∃ e imm ss, t.find q = some (e, imm, ss) ∧ s ∈ ss

def GStepOk (cfg : Cfg) (t : GTree) (R : Nat → GStack → Prop) (q : Nat)
    (s : GStack) : Prop :=
  ∃ e imm ss, t.find q = some (e, imm, ss) ∧ gok cfg e s = true ∧
    ∃ succs, gsucc cfg e imm q s = some succs ∧ ∀ x ∈ succs, R x.1 x.2

/-- **A closed table**: every recorded state is allowed and its successors are recorded. -/
def GClosed (cfg : Cfg) (t : GTree) : Prop :=
  ∀ q s, GInT t q s → GStepOk cfg t (GInT t) q s

/-- The worklist exploration of the reachable abstract states. -/
def gexplore (cfg : Cfg) : (fuel : Nat) → GTree → List (Nat × GStack) → Option GTree
  | 0, _, _ => none
  | _ + 1, t, [] => some t
  | f + 1, t, (q, s) :: work =>
    match t.find q with
    | none => none
    | some (e, imm, ss) =>
      if memS s ss then gexplore cfg f t work
      else if gok cfg e s then
        match gsucc cfg e imm q s with
        | none => none
        | some succs => gexplore cfg f (t.add q s) (succs ++ work)
      else none

theorem GInT.add {t : GTree} {q' : Nat} {s' : GStack} (h : GInT t q' s') (q : Nat) (s : GStack) :
    GInT (t.add q s) q' s' := by
  obtain ⟨e, imm, ss, hf, hm⟩ := h
  rw [GInT, GTree.find_add]
  by_cases hq : q' = q
  · subst hq
    simp only [↓reduceIte, hf, Option.map_some, Option.some.injEq]
    exact ⟨e, imm, s :: ss, rfl, List.mem_cons_of_mem _ hm⟩
  · simp only [hq, ↓reduceIte]
    exact ⟨e, imm, ss, hf, hm⟩

theorem GInT.of_add {t : GTree} {q q' : Nat} {s s' : GStack} (h : GInT (t.add q s) q' s') :
    GInT t q' s' ∨ (q' = q ∧ s' = s) := by
  obtain ⟨e, imm, ss, hf, hm⟩ := h
  rw [GTree.find_add] at hf
  by_cases hq : q' = q
  · subst hq
    simp only [↓reduceIte] at hf
    cases hfq : t.find q' with
    | none => rw [hfq] at hf; cases hf
    | some x =>
      rw [hfq] at hf
      simp only [Option.map_some, Option.some.injEq] at hf
      obtain ⟨e', imm', ss'⟩ := x
      simp only [Prod.mk.injEq] at hf
      obtain ⟨-, -, rfl⟩ := hf
      rcases List.mem_cons.1 hm with h | h
      · exact .inr ⟨rfl, h⟩
      · exact .inl ⟨e', imm', ss', hfq, h⟩
  · simp only [hq, ↓reduceIte] at hf
    exact .inl ⟨e, imm, ss, hf, hm⟩

theorem gfind_add_some {t : GTree} {q q' : Nat} {s : GStack} {e : GEff} {imm : GVal}
    {ss : List GStack} (h : t.find q' = some (e, imm, ss)) :
    ∃ ss', (t.add q s).find q' = some (e, imm, ss') := by
  rw [GTree.find_add]
  by_cases hq : q' = q
  · subst hq; simp [h]
  · simp [hq, h]

def GExInv (cfg : Cfg) (t : GTree) (work : List (Nat × GStack)) : Prop :=
  ∀ q s, GInT t q s → GStepOk cfg t (fun q' s' => GInT t q' s' ∨ (q', s') ∈ work) q s

theorem GStepOk.mono {cfg : Cfg} {t t' : GTree} {R R' : Nat → GStack → Prop}
    {q : Nat} {s : GStack} (h : GStepOk cfg t R q s)
    (hf : ∀ {e imm ss}, t.find q = some (e, imm, ss) → ∃ ss', t'.find q = some (e, imm, ss'))
    (hR : ∀ q s, R q s → R' q s) : GStepOk cfg t' R' q s := by
  obtain ⟨e, imm, ss, hfind, hok, succs, ha, hall⟩ := h
  obtain ⟨ss', hf'⟩ := hf hfind
  exact ⟨e, imm, ss', hf', hok, succs, ha, fun x hx => hR _ _ (hall x hx)⟩

/-- **The exploration is sound**: its result is closed and contains every recorded or
pending state. -/
theorem gexplore_sound (cfg : Cfg) : ∀ (f : Nat) (t : GTree)
    (work : List (Nat × GStack)) (t' : GTree), gexplore cfg f t work = some t' →
    GExInv cfg t work →
    GClosed cfg t' ∧ ∀ q s, (GInT t q s ∨ (q, s) ∈ work) → GInT t' q s
  | 0, _, _, _, h, _ => by simp [gexplore] at h
  | f + 1, t, [], t', h, hI => by
    simp only [gexplore, Option.some.injEq] at h
    subst h
    refine ⟨fun q s hs => (hI q s hs).mono (fun hf => ⟨_, hf⟩) ?_, ?_⟩
    · intro q s h; simpa using h
    · intro q s h; simpa using h
  | f + 1, t, (q, s) :: work, t', h, hI => by
    simp only [gexplore] at h
    split at h
    · cases h
    · rename_i e imm ss hfind
      split at h
      · rename_i hmem
        have hin : GInT t q s := ⟨e, imm, ss, hfind, mem_of_memS hmem⟩
        have hI' : GExInv cfg t work := by
          intro q' s' hs'
          refine (hI q' s' hs').mono (fun hf => ⟨_, hf⟩) ?_
          intro q'' s'' h''
          rcases h'' with h'' | h''
          · exact .inl h''
          · rcases List.mem_cons.1 h'' with h'' | h''
            · cases h''; exact .inl hin
            · exact .inr h''
        obtain ⟨hc, hm⟩ := gexplore_sound cfg f t work t' h hI'
        refine ⟨hc, fun q' s' h' => hm q' s' ?_⟩
        rcases h' with h' | h'
        · exact .inl h'
        · rcases List.mem_cons.1 h' with h' | h'
          · cases h'; exact .inl hin
          · exact .inr h'
      · rename_i hmem
        split at h
        · rename_i hok
          split at h
          · cases h
          · rename_i succs hsucc
            have hI' : GExInv cfg (t.add q s) (succs ++ work) := by
              intro q' s' hs'
              rcases GInT.of_add hs' with hs' | ⟨hq, hss⟩
              · refine (hI q' s' hs').mono gfind_add_some ?_
                intro q'' s'' h''
                rcases h'' with h'' | h''
                · exact .inl (h''.add q s)
                · rcases List.mem_cons.1 h'' with h'' | h''
                  · cases h''
                    exact .inl ⟨e, imm, s :: ss, by rw [GTree.find_add]; simp [hfind],
                      List.mem_cons_self⟩
                  · exact .inr (List.mem_append_right _ h'')
              · rw [hq, hss]
                refine ⟨e, imm, s :: ss, by rw [GTree.find_add]; simp [hfind], hok, succs, hsucc,
                  fun x hx => .inr (List.mem_append_left _ hx)⟩
            obtain ⟨hc, hm⟩ := gexplore_sound cfg f (t.add q s) (succs ++ work) t' h hI'
            refine ⟨hc, fun q' s' h' => hm q' s' ?_⟩
            rcases h' with h' | h'
            · exact .inl (h'.add q s)
            · rcases List.mem_cons.1 h' with h' | h'
              · cases h'
                exact .inl ⟨e, imm, s :: ss, by rw [GTree.find_add]; simp [hfind],
                  List.mem_cons_self⟩
              · exact .inr (List.mem_append_right _ h')
        · cases h

theorem gexplore_all {cfg : Cfg} {P : Nat → GEff → GVal → Prop} :
    ∀ (f : Nat) (t : GTree) (work : List (Nat × GStack)) (t' : GTree),
    gexplore cfg f t work = some t' → t.All P → t'.All P
  | 0, _, _, _, h, _ => by simp [gexplore] at h
  | f + 1, t, [], t', h, hA => by
    simp only [gexplore, Option.some.injEq] at h
    exact h ▸ hA
  | f + 1, t, (q, s) :: work, t', h, hA => by
    simp only [gexplore] at h
    split at h
    · cases h
    · split at h
      · exact gexplore_all f t work t' h hA
      · split at h
        · split at h
          · cases h
          · exact gexplore_all f _ _ t' h (hA.add q s)
        · cases h


/-! ## Certificates -/

/-- The initial table of `code`: its instruction scan, no stacks. -/
def gtable (code : ByteArray) (syms : List (Nat × Nat)) : GTree :=
  let l := gscan code syms
  (GTree.build 64 l.length l).1

/-- Explore `code` from pc `0` with the abstract stack `init`. -/
def gcertify (cfg : Cfg) (code : ByteArray) (syms : List (Nat × Nat)) (init : GStack)
    (fuel : Nat) : Option GTree :=
  gexplore cfg fuel (gtable code syms) [(0, init)]

/-- **A certificate**: a closed table, right for the code, containing the initial state. -/
structure GCert (ν : Env) (cfg : Cfg) (code : ByteArray) (init : GStack) (t : GTree) : Prop where
  closed : GClosed cfg t
  ins : t.All (GInsOk ν code)
  init : GInT t 0 init

/-- **The certificate computed by `gcertify` is sound.** -/
theorem gcertify_sound {ν : Env} {cfg : Cfg} {code : ByteArray} {syms : List (Nat × Nat)}
    {init : GStack} {fuel : Nat} {t : GTree} (h : gcertify cfg code syms init fuel = some t)
    (hs : SymOk ν.ρ code syms) : GCert ν cfg code init t := by
  obtain ⟨hA, hF, -⟩ := GTree.build_ok 64 (gscan code syms).length _ (gscan_ok hs)
  have hI : GExInv cfg (gtable code syms) [(0, init)] := by
    intro q s ⟨e, imm, ss, hf, hm⟩
    rw [hF.find hf] at hm
    cases hm
  obtain ⟨hc, hm⟩ := gexplore_sound cfg fuel _ _ t h hI
  exact ⟨hc, gexplore_all fuel _ _ t h hA, hm 0 init (.inr List.mem_cons_self)⟩

end EvmLogic.AbsInt.Guard
