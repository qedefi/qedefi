import EvmLogic.AbsInt.Domain

/-!
# Abstract interpretation: the abstract step and the certificate

`asucc` is the abstract step (`none` on a non-constant jump target); `explore` computes the
reachable abstract states in a `Tree` keyed by pc, in the kernel (`decide +kernel`).
`certify_sound`: its result is a `Cert` (closed, right for the code, containing the start).
`find`/`add` agree without any balance invariant (`find_add`); balancing is only for speed.
-/

namespace EvmLogic.AbsInt
open EvmLean EvmLogic.Program EvmLean.Interpreter

/-! ## The abstract step -/

/-- The abstract successors of `(q, s)` at an instruction of shape `e` with immediate `imm`
(`none`: unresolved jump). -/
def asucc : Eff → AVal → Nat → AStack → Option (List (Nat × AStack))
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
    | .const d :: _ :: r => some [(d, r), (q + 1, r)]
    | _ :: _ :: _ => none
  | .shl, _, q, s =>
    some (match s with
      | a :: b :: r => [(q + 1, ashl a b :: r)]
      | _ => [])
  | .sub, _, q, s =>
    some (match s with
      | a :: b :: r => [(q + 1, asub a b :: r)]
      | _ => [])
  | .and, _, q, s =>
    some (match s with
      | a :: b :: r => [(q + 1, aand a b :: r)]
      | _ => [])
  | .call p, _, q, s => some (if p ≤ s.length then [(q + 1, .top :: s.drop p)] else [])
  | .create p, _, q, s => some (if p ≤ s.length then [(q + 1, .top :: s.drop p)] else [])

/-- Calls go to `allowed` targets; no creations. -/
def callOk (allowed : AVal → Bool) : Eff → AStack → Bool
  | .call _, _ :: t :: _ => allowed t
  | .call _, _ => true
  | .create _, _ => false
  | _, _ => true

/-! ## Stacks -/

variable {ρ : Nat → Address}

theorem StackOk.length : ∀ {s : AStack} {st : List Word}, StackOk ρ s st → s.length = st.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [StackOk.length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem StackOk.drop : ∀ (p : Nat) {s : AStack} {st : List Word}, StackOk ρ s st →
    StackOk ρ (s.drop p) (st.drop p)
  | 0, _, _, h => h
  | _ + 1, [], [], _ => trivial
  | p + 1, _ :: _, _ :: _, h => StackOk.drop p h.2
  | _ + 1, [], _ :: _, h => h.elim
  | _ + 1, _ :: _, [], h => h.elim

theorem StackOk.append : ∀ {a b : AStack} {x y : List Word}, StackOk ρ a x → StackOk ρ b y →
    StackOk ρ (a ++ b) (x ++ y)
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, h, h' => ⟨h.1, StackOk.append h.2 h'⟩
  | [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, h, _ => h.elim

theorem stackOk_replicate_top : ∀ (x : List Word), StackOk ρ (List.replicate x.length .top) x
  | [] => trivial
  | _ :: x => ⟨trivial, stackOk_replicate_top x⟩

theorem StackOk.getElem? : ∀ {s : AStack} {st : List Word} (n : Nat), StackOk ρ s st →
    ∀ {w}, st[n]? = some w → ∃ a, s[n]? = some a ∧ a.Holds ρ w
  | [], [], _, _, _, h => by simp at h
  | a :: _, w :: _, 0, h, _, hw => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
    exact ⟨a, rfl, hw ▸ h.1⟩
  | _ :: _, _ :: _, n + 1, h, _, hw => by
    simp only [List.getElem?_cons_succ] at hw ⊢
    exact StackOk.getElem? n h.2 hw
  | [], _ :: _, _, h, _, _ => h.elim
  | _ :: _, [], _, h, _, _ => h.elim

theorem StackOk.set : ∀ {s : AStack} {st : List Word} (n : Nat) {a : AVal} {w : Word},
    StackOk ρ s st → a.Holds ρ w → StackOk ρ (s.set n a) (st.set n w)
  | [], [], _, _, _, _, _ => trivial
  | _ :: _, _ :: _, 0, _, _, h, ha => ⟨ha, h.2⟩
  | _ :: _, _ :: _, n + 1, _, _, h, ha => ⟨h.1, StackOk.set n h.2 ha⟩
  | [], _ :: _, _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, _, h, _ => h.elim

theorem stackOk_shape {p k : Nat} {s : AStack} {st st' : List Word} (h : StackOk ρ s st)
    (hsh : Shape p k st st') : StackOk ρ (List.replicate k .top ++ s.drop p) st' := by
  obtain ⟨hp, hl, hd⟩ := hsh
  have hk : (st'.take k).length = k := by
    rw [List.length_take]; omega
  have := StackOk.append (stackOk_replicate_top (ρ := ρ) (st'.take k))
    (show StackOk ρ (s.drop p) (st'.drop k) by rw [hd]; exact h.drop p)
  rwa [hk, List.take_append_drop] at this

/-! ## Soundness of the abstract step -/

/-- **A `.next` action lands in an abstract successor.** -/
theorem asucc_next {e : Eff} {imm : AVal} {q : Nat} {s : AStack} {succs : List (Nat × AStack)}
    {m m' : Machine} (hs : StackOk ρ s m.frame.stack) (hpc : m.frame.pc = q)
    (himm : ∀ n, e = .push n → imm.Holds ρ (Bytes.toWord (readBytes m.frame.code (q + 1) n)))
    (hpost : NextPost e m m') (ha : asucc e imm q s = some succs) :
    ∃ x ∈ succs, x.1 = m'.frame.pc ∧ StackOk ρ x.2 m'.frame.stack := by
  have hlen := hs.length
  cases e with
  | gen p k =>
    obtain ⟨hpc', hsh⟩ := hpost
    simp only [asucc, Option.some.injEq] at ha
    subst ha
    have hp : p ≤ s.length := by have := hsh.1; omega
    simp only [hp, ↓reduceIte, List.mem_singleton, exists_eq_left]
    exact ⟨by omega, stackOk_shape hs hsh⟩
  | halt => exact hpost.elim
  | push n =>
    obtain ⟨hpc', hst⟩ := hpost
    simp only [asucc, Option.some.injEq] at ha
    subst ha
    simp only [List.mem_singleton, exists_eq_left]
    refine ⟨by omega, ?_⟩
    rw [hst]
    exact ⟨hpc ▸ himm n rfl, hs⟩
  | dup n =>
    obtain ⟨hpc', x, hx, hst⟩ := hpost
    obtain ⟨a, ha', hax⟩ := hs.getElem? n hx
    simp only [asucc, ha', Option.some.injEq] at ha
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
      simp only [asucc, hb, Option.some.injEq] at ha
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
        simp only [asucc, Option.some.injEq] at ha
        subst ha
        simp only [List.mem_singleton, exists_eq_left]
        exact ⟨by rw [hpc']; exact hs.1.symm, by rw [hst']; exact hs.2⟩
      | top => simp [asucc] at ha
      | sym _ => simp [asucc] at ha
  | jumpi =>
    obtain ⟨d, c, r, hst, hst', hpc'⟩ := hpost
    rw [hst] at hs
    match s, hs, ha with
    | .const dd :: _ :: sr, hs, ha =>
      simp only [asucc, Option.some.injEq] at ha
      subst ha
      rcases hpc' with h | h
      · exact ⟨(dd, sr), List.mem_cons_self, by rw [h]; exact hs.1.symm, by rw [hst']; exact hs.2.2⟩
      · exact ⟨(q + 1, sr), List.mem_cons_of_mem _ List.mem_cons_self, by omega,
          by rw [hst']; exact hs.2.2⟩
    | .top :: _ :: _, _, ha => simp [asucc] at ha
    | .sym _ :: _ :: _, _, ha => simp [asucc] at ha
    | [], hs, _ => exact hs.elim
    | [_], hs, _ => exact hs.2.elim
  | shl =>
    obtain ⟨hpc', x, y, r, hst, hst'⟩ := hpost
    rw [hst] at hs
    match s, hs, ha with
    | a :: b :: sr, hs, ha =>
      simp only [asucc, Option.some.injEq] at ha
      subst ha
      simp only [List.mem_singleton, exists_eq_left]
      exact ⟨by omega, by rw [hst']; exact ⟨ashl_holds hs.1 hs.2.1, hs.2.2⟩⟩
    | [], hs, _ => exact hs.elim
    | [_], hs, _ => exact hs.2.elim
  | sub =>
    obtain ⟨hpc', x, y, r, hst, hst'⟩ := hpost
    rw [hst] at hs
    match s, hs, ha with
    | a :: b :: sr, hs, ha =>
      simp only [asucc, Option.some.injEq] at ha
      subst ha
      simp only [List.mem_singleton, exists_eq_left]
      exact ⟨by omega, by rw [hst']; exact ⟨asub_holds hs.1 hs.2.1, hs.2.2⟩⟩
    | [], hs, _ => exact hs.elim
    | [_], hs, _ => exact hs.2.elim
  | and =>
    obtain ⟨hpc', x, y, r, hst, hst'⟩ := hpost
    rw [hst] at hs
    match s, hs, ha with
    | a :: b :: sr, hs, ha =>
      simp only [asucc, Option.some.injEq] at ha
      subst ha
      simp only [List.mem_singleton, exists_eq_left]
      exact ⟨by omega, by rw [hst']; exact ⟨aand_holds hs.1 hs.2.1, hs.2.2⟩⟩
    | [], hs, _ => exact hs.elim
    | [_], hs, _ => exact hs.2.elim
  | call p =>
    obtain ⟨hpc', hsh⟩ := hpost
    simp only [asucc, Option.some.injEq] at ha
    subst ha
    have hp : p ≤ s.length := by have := hsh.1; omega
    simp only [hp, ↓reduceIte, List.mem_singleton, exists_eq_left]
    exact ⟨by omega, stackOk_shape (k := 1) hs hsh⟩
  | create p =>
    obtain ⟨hpc', hsh⟩ := hpost
    simp only [asucc, Option.some.injEq] at ha
    subst ha
    have hp : p ≤ s.length := by have := hsh.1; omega
    simp only [hp, ↓reduceIte, List.mem_singleton, exists_eq_left]
    exact ⟨by omega, stackOk_shape (k := 1) hs hsh⟩

theorem asucc_popped {p : Nat} {imm : AVal} {q : Nat} {s : AStack}
    {succs : List (Nat × AStack)} {e : Eff} (he : e = .call p ∨ e = .create p)
    {m m' : Machine} (hs : StackOk ρ s m.frame.stack) (hpop : Popped p m m')
    (ha : asucc e imm q s = some succs) (w : Word) :
    ∃ x ∈ succs, x.1 = q + 1 ∧ StackOk ρ x.2 (w :: m'.frame.stack) := by
  obtain ⟨-, hp, hst⟩ := hpop
  have hp' : p ≤ s.length := by rw [hs.length]; exact hp
  rcases he with rfl | rfl <;>
  · simp only [asucc, hp', ↓reduceIte, Option.some.injEq] at ha
    subst ha
    exact ⟨_, List.mem_singleton_self _, rfl, trivial, by rw [hst]; exact hs.drop p⟩

/-- **The continuation after a requested child** (call or creation). -/
theorem asucc_child {e : Eff} {imm : AVal} {q : Nat} {s : AStack}
    {succs : List (Nat × AStack)} {m m' : Machine} (hs : StackOk ρ s m.frame.stack)
    (hpost : CallPost e m m' ∨ CreatePost e m m') (ha : asucc e imm q s = some succs)
    (w : Word) : ∃ x ∈ succs, x.1 = q + 1 ∧ StackOk ρ x.2 (w :: m'.frame.stack) := by
  cases e <;> simp only [CallPost, CreatePost, or_false, false_or] at hpost
  · exact asucc_popped (.inl rfl) hs hpost ha w
  · exact asucc_popped (.inr rfl) hs hpost ha w

/-- **Allowed call targets.** -/
theorem callOk_target {allowed : AVal → Bool} {p : Nat} {s : AStack} {st : List Word}
    (hok : callOk allowed (.call p) s = true) (hs : StackOk ρ s st) {t : Word}
    (ht : st[1]? = some t) : ∃ a, allowed a = true ∧ a.Holds ρ t := by
  obtain ⟨a, ha, hat⟩ := hs.getElem? 1 ht
  match s, ha, hok with
  | _ :: b :: _, ha, hok =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at ha
    subst ha
    exact ⟨_, hok, hat⟩

/-! ## The table -/

/-- The certificate table: a binary tree with, per instruction (pc, shape, abstract
immediate), the abstract stacks reached there. -/
inductive Tree where
  | leaf
  | node (l : Tree) (q : Nat) (e : Eff) (imm : AVal) (ss : List AStack) (r : Tree)

namespace Tree
open EvmLean EvmLogic.Program

def find (q : Nat) : Tree → Option (Eff × AVal × List AStack)
  | leaf => none
  | node l k e imm ss r =>
    if Nat.blt q k then l.find q else if Nat.blt k q then r.find q else some (e, imm, ss)

/-- Record the stack `s` at `q` (no-op if `q` is not an entry). -/
def add (q : Nat) (s : AStack) : Tree → Tree
  | leaf => leaf
  | node l k e imm ss r =>
    if Nat.blt q k then node (l.add q s) k e imm ss r
    else if Nat.blt k q then node l k e imm ss (r.add q s)
    else node l k e imm (s :: ss) r

/-- A balanced tree of the first `n` entries of a sorted list, with no stacks, and the
remaining entries (linear time; structural fuel: the depth). -/
def build : (fuel n : Nat) → List (Nat × Eff × AVal) → Tree × List (Nat × Eff × AVal)
  | 0, _, l => (leaf, l)
  | f + 1, n, l =>
    if n = 0 then (leaf, l) else
    match build f ((n - 1) / 2) l with
    | (lt, []) => (lt, [])
    | (lt, (q, e, imm) :: l₂) =>
      match build f (n - 1 - (n - 1) / 2) l₂ with
      | (rt, l₃) => (node lt q e imm [] rt, l₃)

def Fresh : Tree → Prop
  | leaf => True
  | node l _ _ _ ss r => Fresh l ∧ ss = [] ∧ Fresh r

def All (P : Nat → Eff → AVal → Prop) : Tree → Prop
  | leaf => True
  | node l q e imm _ r => All P l ∧ P q e imm ∧ All P r

theorem find_add (q q' : Nat) (s : AStack) : ∀ t : Tree,
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

theorem All.find {P : Nat → Eff → AVal → Prop} : ∀ {t : Tree}, t.All P → ∀ {q e imm ss},
    t.find q = some (e, imm, ss) → P q e imm
  | leaf, _, _, _, _, _, h => by simp [Tree.find] at h
  | node l k e' imm' ss' r, hA, q, e, imm, ss, h => by
    simp only [Tree.find] at h
    split at h
    · exact All.find hA.1 h
    · split at h
      · exact All.find hA.2.2 h
      · cases h
        rename_i h1 h2
        have : q = k := by simp only [Nat.blt_eq] at h1 h2; omega
        subst this; exact hA.2.1

theorem Fresh.find : ∀ {t : Tree}, t.Fresh → ∀ {q e imm ss}, t.find q = some (e, imm, ss) →
    ss = []
  | leaf, _, _, _, _, _, h => by simp [Tree.find] at h
  | node l k e' imm' ss' r, hF, q, e, imm, ss, h => by
    simp only [Tree.find] at h
    split at h
    · exact Fresh.find hF.1 h
    · split at h
      · exact Fresh.find hF.2.2 h
      · cases h; exact hF.2.1

theorem All.add {P : Nat → Eff → AVal → Prop} (q : Nat) (s : AStack) :
    ∀ {t : Tree}, t.All P → (t.add q s).All P
  | leaf, h => h
  | node l k e imm ss r, h => by
    simp only [Tree.add]
    split
    · exact ⟨All.add q s h.1, h.2.1, h.2.2⟩
    · split
      · exact ⟨h.1, h.2.1, All.add q s h.2.2⟩
      · exact ⟨h.1, h.2.1, h.2.2⟩

theorem build_ok {P : Nat → Eff → AVal → Prop} : ∀ (f n : Nat) (l : List (Nat × Eff × AVal)),
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

end Tree

/-! ## Exploration -/

/-- The abstract state `(q, s)` is recorded in `t`. -/
def InT (t : Tree) (q : Nat) (s : AStack) : Prop :=
  ∃ e imm ss, t.find q = some (e, imm, ss) ∧ s ∈ ss

def StepOk (allowed : AVal → Bool) (t : Tree) (R : Nat → AStack → Prop) (q : Nat)
    (s : AStack) : Prop :=
  ∃ e imm ss, t.find q = some (e, imm, ss) ∧ callOk allowed e s = true ∧
    ∃ succs, asucc e imm q s = some succs ∧ ∀ x ∈ succs, R x.1 x.2

/-- **A closed table**: every recorded state is allowed and its successors are recorded. -/
def Closed (allowed : AVal → Bool) (t : Tree) : Prop :=
  ∀ q s, InT t q s → StepOk allowed t (InT t) q s

/-- The worklist exploration of the reachable abstract states. -/
def explore (allowed : AVal → Bool) : (fuel : Nat) → Tree → List (Nat × AStack) → Option Tree
  | 0, _, _ => none
  | _ + 1, t, [] => some t
  | f + 1, t, (q, s) :: work =>
    match t.find q with
    | none => none
    | some (e, imm, ss) =>
      if memS s ss then explore allowed f t work
      else if callOk allowed e s then
        match asucc e imm q s with
        | none => none
        | some succs => explore allowed f (t.add q s) (succs ++ work)
      else none

theorem InT.add {t : Tree} {q' : Nat} {s' : AStack} (h : InT t q' s') (q : Nat) (s : AStack) :
    InT (t.add q s) q' s' := by
  obtain ⟨e, imm, ss, hf, hm⟩ := h
  rw [InT, Tree.find_add]
  by_cases hq : q' = q
  · subst hq
    simp only [↓reduceIte, hf, Option.map_some, Option.some.injEq]
    exact ⟨e, imm, s :: ss, rfl, List.mem_cons_of_mem _ hm⟩
  · simp only [hq, ↓reduceIte]
    exact ⟨e, imm, ss, hf, hm⟩

theorem InT.of_add {t : Tree} {q q' : Nat} {s s' : AStack} (h : InT (t.add q s) q' s') :
    InT t q' s' ∨ (q' = q ∧ s' = s) := by
  obtain ⟨e, imm, ss, hf, hm⟩ := h
  rw [Tree.find_add] at hf
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

theorem find_add_some {t : Tree} {q q' : Nat} {s : AStack} {e : Eff} {imm : AVal}
    {ss : List AStack} (h : t.find q' = some (e, imm, ss)) :
    ∃ ss', (t.add q s).find q' = some (e, imm, ss') := by
  rw [Tree.find_add]
  by_cases hq : q' = q
  · subst hq; simp [h]
  · simp [hq, h]

def ExInv (allowed : AVal → Bool) (t : Tree) (work : List (Nat × AStack)) : Prop :=
  ∀ q s, InT t q s → StepOk allowed t (fun q' s' => InT t q' s' ∨ (q', s') ∈ work) q s

theorem StepOk.mono {allowed : AVal → Bool} {t t' : Tree} {R R' : Nat → AStack → Prop}
    {q : Nat} {s : AStack} (h : StepOk allowed t R q s)
    (hf : ∀ {e imm ss}, t.find q = some (e, imm, ss) → ∃ ss', t'.find q = some (e, imm, ss'))
    (hR : ∀ q s, R q s → R' q s) : StepOk allowed t' R' q s := by
  obtain ⟨e, imm, ss, hfind, hok, succs, ha, hall⟩ := h
  obtain ⟨ss', hf'⟩ := hf hfind
  exact ⟨e, imm, ss', hf', hok, succs, ha, fun x hx => hR _ _ (hall x hx)⟩

/-- **The exploration is sound**: its result is closed and contains every recorded or
pending state. -/
theorem explore_sound (allowed : AVal → Bool) : ∀ (f : Nat) (t : Tree)
    (work : List (Nat × AStack)) (t' : Tree), explore allowed f t work = some t' →
    ExInv allowed t work →
    Closed allowed t' ∧ ∀ q s, (InT t q s ∨ (q, s) ∈ work) → InT t' q s
  | 0, _, _, _, h, _ => by simp [explore] at h
  | f + 1, t, [], t', h, hI => by
    simp only [explore, Option.some.injEq] at h
    subst h
    refine ⟨fun q s hs => (hI q s hs).mono (fun hf => ⟨_, hf⟩) ?_, ?_⟩
    · intro q s h; simpa using h
    · intro q s h; simpa using h
  | f + 1, t, (q, s) :: work, t', h, hI => by
    simp only [explore] at h
    split at h
    · cases h
    · rename_i e imm ss hfind
      split at h
      · rename_i hmem
        have hin : InT t q s := ⟨e, imm, ss, hfind, mem_of_memS hmem⟩
        have hI' : ExInv allowed t work := by
          intro q' s' hs'
          refine (hI q' s' hs').mono (fun hf => ⟨_, hf⟩) ?_
          intro q'' s'' h''
          rcases h'' with h'' | h''
          · exact .inl h''
          · rcases List.mem_cons.1 h'' with h'' | h''
            · cases h''; exact .inl hin
            · exact .inr h''
        obtain ⟨hc, hm⟩ := explore_sound allowed f t work t' h hI'
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
            have hI' : ExInv allowed (t.add q s) (succs ++ work) := by
              intro q' s' hs'
              rcases InT.of_add hs' with hs' | ⟨hq, hss⟩
              · refine (hI q' s' hs').mono find_add_some ?_
                intro q'' s'' h''
                rcases h'' with h'' | h''
                · exact .inl (h''.add q s)
                · rcases List.mem_cons.1 h'' with h'' | h''
                  · cases h''
                    exact .inl ⟨e, imm, s :: ss, by rw [Tree.find_add]; simp [hfind],
                      List.mem_cons_self⟩
                  · exact .inr (List.mem_append_right _ h'')
              · rw [hq, hss]
                refine ⟨e, imm, s :: ss, by rw [Tree.find_add]; simp [hfind], hok, succs, hsucc,
                  fun x hx => .inr (List.mem_append_left _ hx)⟩
            obtain ⟨hc, hm⟩ := explore_sound allowed f (t.add q s) (succs ++ work) t' h hI'
            refine ⟨hc, fun q' s' h' => hm q' s' ?_⟩
            rcases h' with h' | h'
            · exact .inl (h'.add q s)
            · rcases List.mem_cons.1 h' with h' | h'
              · cases h'
                exact .inl ⟨e, imm, s :: ss, by rw [Tree.find_add]; simp [hfind],
                  List.mem_cons_self⟩
              · exact .inr (List.mem_append_right _ h')
        · cases h

theorem explore_all {allowed : AVal → Bool} {P : Nat → Eff → AVal → Prop} :
    ∀ (f : Nat) (t : Tree) (work : List (Nat × AStack)) (t' : Tree),
    explore allowed f t work = some t' → t.All P → t'.All P
  | 0, _, _, _, h, _ => by simp [explore] at h
  | f + 1, t, [], t', h, hA => by
    simp only [explore, Option.some.injEq] at h
    exact h ▸ hA
  | f + 1, t, (q, s) :: work, t', h, hA => by
    simp only [explore] at h
    split at h
    · cases h
    · split at h
      · exact explore_all f t work t' h hA
      · split at h
        · split at h
          · cases h
          · exact explore_all f _ _ t' h (hA.add q s)
        · cases h

/-! ## Certificates -/

/-- The initial table of `code`: its instruction scan, no stacks. -/
def table (code : ByteArray) (syms : List (Nat × Nat)) : Tree :=
  let l := ascan code syms
  (Tree.build 64 l.length l).1

/-- Explore `code` from pc `0` with the abstract stack `init` (fuel: the number of worklist
steps). -/
def certify (allowed : AVal → Bool) (code : ByteArray) (syms : List (Nat × Nat))
    (init : AStack) (fuel : Nat) : Option Tree :=
  explore allowed fuel (table code syms) [(0, init)]

/-- **A certificate**: a closed table, right for the code, containing the initial state. -/
structure Cert (ρ : Nat → Address) (allowed : AVal → Bool) (code : ByteArray) (init : AStack)
    (t : Tree) : Prop where
  closed : Closed allowed t
  ins : t.All (InsOk ρ code)
  init : InT t 0 init

/-- **The certificate computed by `certify` is sound.** -/
theorem certify_sound {ρ : Nat → Address} {allowed : AVal → Bool} {code : ByteArray}
    {syms : List (Nat × Nat)} {init : AStack} {fuel : Nat} {t : Tree}
    (h : certify allowed code syms init fuel = some t) (hs : SymOk ρ code syms) :
    Cert ρ allowed code init t := by
  obtain ⟨hA, hF, -⟩ := Tree.build_ok 64 (ascan code syms).length _ (ascan_ok hs)
  have hI : ExInv allowed (table code syms) [(0, init)] := by
    intro q s ⟨e, imm, ss, hf, hm⟩
    rw [hF.find hf] at hm
    cases hm
  obtain ⟨hc, hm⟩ := explore_sound allowed fuel _ _ t h hI
  exact ⟨hc, explore_all fuel _ _ t h hA, hm 0 init (.inr List.mem_cons_self)⟩

end EvmLogic.AbsInt
