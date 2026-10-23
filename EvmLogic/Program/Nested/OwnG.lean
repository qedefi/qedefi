import EvmLogic.Program.Nested.Own
import EvmLogic.Program.Nested.Frame

/-!
# Own steps with external calls: every path of a frame ends it

`OwnB Halt G R S C Dm D B m` generalizes `Own` to frames that make real calls. From `m`, every path
of the frame by its own instructions ends it: each instruction satisfies `S`; at a *doom point*
(`Dm m`) every requested call leaves the frame satisfying `D` when it resumes, whatever the
child did; elsewhere every requested call satisfies `C` (the issuance predicate) and the frame
continues after a precompile as `launchCall` makes it continue, and after a real child from any
resumed machine whose world satisfies `G`; no creation is requested; and a successful halt
(`STOP`, `RETURN`, running off the end) is allowed only if `Halt`. A revert or an exceptional
halt is always allowed. Each step may assume the run predicate `R` of the machine before it
(a run-level hypothesis, such as what a storage slot reads during the transaction). Like `Own`, it is universal over the outcomes of `exec` (any gas) and
inductive (every path is finite).

`Doomed m := OwnG False …` (no successful halt, no condition on calls) says the frame reverts,
whatever its children do: every effect of the frame and of its children is rolled back. It is
the frame invariant of a frame whose remaining effect is nil (`simulateAndRevert`), used by
`EvmLogic.Program.Nested.Sandbox`.

The rules (`OwnG.binOp`, …) are those of `Own` with `OwnG` goals, plus `EXP`, `EXTCODESIZE`,
`LOG`, real `STATICCALL`/`CALL` and a `DELEGATECALL` at a doom point.
-/

namespace EvmLogic.Program.Nested
open EvmLean EvmLean.Interpreter

/-- **Every own path from `m` ends the frame or reaches `B`** (see the module docstring). -/
inductive OwnB (Halt : Prop) (G : World → Prop) (R : Machine → Prop) (S : Machine → Prop)
    (C : Machine → CallRequest → Prop) (Dm : Machine → Prop) (D : Machine → Prop)
    (B : Machine → Prop) : Machine → Prop
  | intro {m : Machine} (hS : R m → S m)
      (hnext : ∀ b m', R m → m.frame.code[m.frame.pc]? = some b →
        (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.next, m') → OwnB Halt G R S C Dm D B m')
      (hiss : ∀ b req m', R m → m.frame.code[m.frame.pc]? = some b →
        (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m') → ¬ Dm m → C m req)
      (hpre : ∀ b req m', R m → m.frame.code[m.frame.pc]? = some b →
        (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m') → ¬ Dm m →
        precompileOf m'.precompiles req.msg ≠ none → OwnB Halt G R S C Dm D B (launchCall m' req))
      (hreal : ∀ b req m', R m → m.frame.code[m.frame.pc]? = some b →
        (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m') → ¬ Dm m →
        precompileOf m'.precompiles req.msg = none →
        ∀ (M : Machine) (res : ChildResult), M.frame = m'.frame → M.parents = m.parents →
          M.ctx = m.ctx → M.precompiles = m.precompiles →
          res.kind = .call req.retOffset req.retSize → G M.world →
          OwnB Halt G R S C Dm D B (resume M res))
      (hdoom : ∀ b req m', R m → m.frame.code[m.frame.pc]? = some b →
        (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m') → Dm m →
        ∀ (M : Machine) (res : ChildResult), M.frame = m'.frame → M.parents = m.parents →
          M.ctx = m.ctx → M.precompiles = m.precompiles →
          res.kind = .call req.retOffset req.retSize → D (resume M res))
      (hcreate : ∀ b msg m', R m → m.frame.code[m.frame.pc]? = some b →
        (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.create msg, m') → False)
      (hstop : ∀ b out m', R m → m.frame.code[m.frame.pc]? = some b →
        (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.stop out, m') → Halt)
      (hend : R m → m.frame.code[m.frame.pc]? = none → Halt) :
      OwnB Halt G R S C Dm D B m
  /-- A state of `B`: the exploration stops (a loop head, a state proved elsewhere). -/
  | leaf {m : Machine} (h : B m) : OwnB Halt G R S C Dm D B m

variable {Halt : Prop} {G : World → Prop} {R : Machine → Prop} {S : Machine → Prop}
  {C : Machine → CallRequest → Prop} {Dm D B : Machine → Prop} {m m' : Machine} {b : UInt8}

theorem _root_.EvmLogic.Program.Nested.Wp.and {α : Type} {x : M α} {Q Q' : α → Machine → Prop}
    (h : Wp x Q m) (h' : Wp x Q' m) : Wp x (fun a m' => Q a m' ∧ Q' a m') m := by
  unfold Wp at *
  split at h <;> rename_i heq <;> rw [heq] at h' <;> simp_all

/-! ## One step -/

/-- **One step**: the conditions `OwnB` puts on the instruction at `m`, with successors in `P`. -/
structure Step (Halt : Prop) (G : World → Prop) (R : Machine → Prop) (S : Machine → Prop)
    (C : Machine → CallRequest → Prop) (Dm : Machine → Prop) (D : Machine → Prop)
    (P : Machine → Prop) (m : Machine) : Prop where
  safe : R m → S m
  next : ∀ b m', R m → m.frame.code[m.frame.pc]? = some b →
    (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.next, m') → P m'
  iss : ∀ b req m', R m → m.frame.code[m.frame.pc]? = some b →
    (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m') → ¬ Dm m → C m req
  pre : ∀ b req m', R m → m.frame.code[m.frame.pc]? = some b →
    (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m') → ¬ Dm m →
    precompileOf m'.precompiles req.msg ≠ none → P (launchCall m' req)
  real : ∀ b req m', R m → m.frame.code[m.frame.pc]? = some b →
    (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m') → ¬ Dm m →
    precompileOf m'.precompiles req.msg = none →
    ∀ (M : Machine) (res : ChildResult), M.frame = m'.frame → M.parents = m.parents →
      M.ctx = m.ctx → M.precompiles = m.precompiles →
      res.kind = .call req.retOffset req.retSize → G M.world → P (resume M res)
  doom : ∀ b req m', R m → m.frame.code[m.frame.pc]? = some b →
    (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m') → Dm m →
    ∀ (M : Machine) (res : ChildResult), M.frame = m'.frame → M.parents = m.parents →
      M.ctx = m.ctx → M.precompiles = m.precompiles →
      res.kind = .call req.retOffset req.retSize → D (resume M res)
  create : ∀ b msg m', R m → m.frame.code[m.frame.pc]? = some b →
    (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.create msg, m') → False
  stop : ∀ b out m', R m → m.frame.code[m.frame.pc]? = some b →
    (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.stop out, m') → Halt
  end_ : R m → m.frame.code[m.frame.pc]? = none → Halt

theorem Step.mono {P Q : Machine → Prop} (h : Step Halt G R S C Dm D P m)
    (hPQ : ∀ x, P x → Q x) : Step Halt G R S C Dm D Q m :=
  ⟨h.safe, fun b m' hR hb he => hPQ _ (h.next b m' hR hb he), h.iss,
    fun b req m' hR hb he hd hp => hPQ _ (h.pre b req m' hR hb he hd hp),
    fun b req m' hR hb he hd hp M res hM hMp hMc hMpre hk hG =>
      hPQ _ (h.real b req m' hR hb he hd hp M res hM hMp hMc hMpre hk hG),
    h.doom, h.create, h.stop, h.end_⟩

namespace OwnB

theorem ofStep (h : Step Halt G R S C Dm D (OwnB Halt G R S C Dm D B) m) :
    OwnB Halt G R S C Dm D B m :=
  .intro h.safe h.next h.iss h.pre h.real h.doom h.create h.stop h.end_

/-- An exploration from `m` takes a step, when the states of `B` do. -/
theorem toStep (hB : ∀ x, B x → Step Halt G R S C Dm D (OwnB Halt G R S C Dm D B) x)
    (h : OwnB Halt G R S C Dm D B m) : Step Halt G R S C Dm D (OwnB Halt G R S C Dm D B) m := by
  cases h with
  | intro hS hn hi hp hr hd hc hs he => exact ⟨hS, hn, hi, hp, hr, hd, hc, hs, he⟩
  | leaf h => exact hB _ h

theorem mono {B' : Machine → Prop} (hBB : ∀ x, B x → B' x) :
    ∀ {m}, OwnB Halt G R S C Dm D B m → OwnB Halt G R S C Dm D B' m := by
  intro m h
  induction h with
  | intro hS _ hi _ _ hd hc hs he ihn ihp ihr =>
    exact .intro hS (fun b m' hR hb he' => ihn b m' hR hb he') hi
      (fun b req m' hR hb he' hd' hp => ihp b req m' hR hb he' hd' hp)
      (fun b req m' hR hb he' hd' hp M res hM hMp hMc hMpre hk hG =>
        ihr b req m' hR hb he' hd' hp M res hM hMp hMc hMpre hk hG) hd hc hs he
  | leaf h => exact .leaf (hBB _ h)

/-- The run predicate may be assumed of the machine at hand (when the states of `B` step). -/
theorem withR (hB : ∀ x, B x → Step Halt G R S C Dm D (OwnB Halt G R S C Dm D B) x)
    (h : R m → OwnB Halt G R S C Dm D B m) : OwnB Halt G R S C Dm D B m := by
  refine .intro (fun hR => (toStep hB (h hR)).safe hR) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro b m' hR; exact (toStep hB (h hR)).next b m' hR
  · intro b req m' hR; exact (toStep hB (h hR)).iss b req m' hR
  · intro b req m' hR; exact (toStep hB (h hR)).pre b req m' hR
  · intro b req m' hR; exact (toStep hB (h hR)).real b req m' hR
  · intro b req m' hR; exact (toStep hB (h hR)).doom b req m' hR
  · intro b msg m' hR; exact (toStep hB (h hR)).create b msg m' hR
  · intro b out m' hR; exact (toStep hB (h hR)).stop b out m' hR
  · intro hR; exact (toStep hB (h hR)).end_ hR

/-! ## The generic rule -/

/-- What an instruction's outcome must satisfy. -/
def Cont (Halt : Prop) (G : World → Prop) (R : Machine → Prop) (S : Machine → Prop) (C : Machine → CallRequest → Prop)
    (Dm D B : Machine → Prop) (m : Machine) : Action → Machine → Prop
  | .next, m' => OwnB Halt G R S C Dm D B m'
  | .call req, m' =>
    (¬ Dm m → C m req ∧
      (precompileOf m'.precompiles req.msg ≠ none → OwnB Halt G R S C Dm D B (launchCall m' req)) ∧
      (precompileOf m'.precompiles req.msg = none →
        ∀ (M : Machine) (res : ChildResult), M.frame = m'.frame → M.parents = m.parents →
          M.ctx = m.ctx → M.precompiles = m.precompiles →
          res.kind = .call req.retOffset req.retSize → G M.world →
          OwnB Halt G R S C Dm D B (resume M res))) ∧
    (Dm m → ∀ (M : Machine) (res : ChildResult), M.frame = m'.frame → M.parents = m.parents →
      M.ctx = m.ctx → M.precompiles = m.precompiles →
      res.kind = .call req.retOffset req.retSize → D (resume M res))
  | .create _, _ => False
  | .stop _, _ => Halt
  | .revert _, _ => True

/-- **The generic rule**: the instruction at `m` (byte `b`) satisfies `S`, and, when `R m` holds,
every successful outcome continues as `Cont` says. -/
theorem stepOf_wpR (hb : m.frame.code[m.frame.pc]? = some b) (hS : S m)
    (h : R m → Wp (exec (Opcode.decode m.ctx.fork b)) (Cont Halt G R S C Dm D B m) m) :
    Step Halt G R S C Dm D (OwnB Halt G R S C Dm D B) m := by
  refine ⟨fun _ => hS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b' m' hR hb' he; rw [hb] at hb'; cases hb'; exact (h hR).of_run he
  · intro b' req m' hR hb' he hd; rw [hb] at hb'; cases hb'; exact (((h hR).of_run he).1 hd).1
  · intro b' req m' hR hb' he hd hp; rw [hb] at hb'; cases hb'
    exact (((h hR).of_run he).1 hd).2.1 hp
  · intro b' req m' hR hb' he hd hp; rw [hb] at hb'; cases hb'
    exact (((h hR).of_run he).1 hd).2.2 hp
  · intro b' req m' hR hb' he hd; rw [hb] at hb'; cases hb'; exact ((h hR).of_run he).2 hd
  · intro b' msg m' hR hb' he; rw [hb] at hb'; cases hb'; exact (h hR).of_run he
  · intro b' out m' hR hb' he; rw [hb] at hb'; cases hb'; exact (h hR).of_run he
  · intro _ hn; rw [hb] at hn; cases hn

theorem of_wpR (hb : m.frame.code[m.frame.pc]? = some b) (hS : S m)
    (h : R m → Wp (exec (Opcode.decode m.ctx.fork b)) (Cont Halt G R S C Dm D B m) m) :
    OwnB Halt G R S C Dm D B m := ofStep (stepOf_wpR hb hS h)

/-- `of_wpR` without the run predicate. -/
theorem of_wp (hb : m.frame.code[m.frame.pc]? = some b) (hS : S m)
    (h : Wp (exec (Opcode.decode m.ctx.fork b)) (Cont Halt G R S C Dm D B m) m) :
    OwnB Halt G R S C Dm D B m := of_wpR hb hS fun _ => h

variable {k : Fix} {pc : Nat} {st : List Word} {mem : Memory} {w : World} {x y z : Word}
  {rest : List Word}

/-! ## Rules: one per instruction shape (as for `Own`) -/

theorem binOp {cost : Nat} {f : Word → Word → Word}
    (hop : ∀ fk, exec (Opcode.decode fk b) = Interpreter.binOp cost f)
    (hF : Fr k m pc (x :: y :: rest) mem w) (hb : k.code[pc]? = some b) (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) (f x y :: rest) mem w → OwnB Halt G R S C Dm D B m') : OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [hop]
  simp only [Interpreter.binOp, wp_bind, wp_pop, wp_push, wp_charge, wp_advance, wp_pure, Cont]
  intro x' xs hx y' ys hy _ _
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hy
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], rfl, hF.mem, hF.world⟩

theorem unOp {cost : Nat} {f : Word → Word}
    (hop : ∀ fk, exec (Opcode.decode fk b) = Interpreter.unOp cost f)
    (hF : Fr k m pc (x :: rest) mem w) (hb : k.code[pc]? = some b) (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) (f x :: rest) mem w → OwnB Halt G R S C Dm D B m') : OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [hop]
  simp only [Interpreter.unOp, wp_bind, wp_pop, wp_push, wp_charge, wp_advance, wp_pure, Cont]
  intro x' xs hx _ _
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], rfl, hF.mem, hF.world⟩

/-- An instruction pushing a value computed from the message and the context. -/
theorem pushValue {cost : Nat} {v : Machine → Word} {a : Word}
    (hop : ∀ fk, exec (Opcode.decode fk b) = Interpreter.pushValue cost v)
    (hv : ∀ m'', m''.frame.msg = k.msg → m''.ctx = k.ctx → v m'' = a)
    (hF : Fr k m pc st mem w) (hb : k.code[pc]? = some b) (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) (a :: st) mem w → OwnB Halt G R S C Dm D B m') : OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [hop]
  simp only [Interpreter.pushValue, wp_bind, wp_get, wp_push, wp_charge, wp_advance, wp_pure, Cont]
  intro _ _
  refine h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], ?_, hF.mem, hF.world⟩
  exact List.cons_eq_cons.2 ⟨hv _ hF.msg hF.ctx, hF.stack⟩

/-- An instruction pushing some value (`GAS`, `RETURNDATASIZE`). -/
theorem pushAny {cost : Nat} {v : Machine → Word}
    (hop : ∀ fk, exec (Opcode.decode fk b) = Interpreter.pushValue cost v)
    (hF : Fr k m pc st mem w) (hb : k.code[pc]? = some b) (hS : S m)
    (h : ∀ a m', Fr k m' (pc + 1) (a :: st) mem w → OwnB Halt G R S C Dm D B m') : OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [hop]
  simp only [Interpreter.pushValue, wp_bind, wp_get, wp_push, wp_charge, wp_advance, wp_pure, Cont]
  intro _ _
  exact h _ _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], List.cons_eq_cons.2 ⟨rfl, hF.stack⟩,
    hF.mem, hF.world⟩

theorem push (n : Fin 33) {v : Word} (hF : Fr k m pc st mem w)
    (hb : k.code[pc]? = some (0x5f + n.val).toUInt8)
    (hv : Bytes.toWord (readBytes k.code (pc + 1) n.val) = v) (hS : S m)
    (h : ∀ m', Fr k m' (pc + (1 + n.val)) (v :: st) mem w → OwnB Halt G R S C Dm D B m') : OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [decode_push]
  simp only [exec, wp_bind, wp_charge, wp_getFrame, wp_push, wp_advance, wp_pure, Cont]
  intro _ _
  refine h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], ?_, hF.mem, hF.world⟩
  rw [hF.code, hF.pc] at *
  exact List.cons_eq_cons.2 ⟨hv, hF.stack⟩

theorem dup (n : Fin 16) (hF : Fr k m pc st mem w)
    (hb : k.code[pc]? = some (0x80 + n.val).toUInt8) (hx : st[n.val]? = some x) (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) (x :: st) mem w → OwnB Halt G R S C Dm D B m') : OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [decode_dup]
  simp only [exec, wp_bind, wp_charge, wp_getFrame, hF.stack, hx, wp_push, wp_advance, wp_pure,
    Cont]
  intro _ _
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], by simp, hF.mem, hF.world⟩

theorem swap (n : Fin 16) (hF : Fr k m pc (y :: rest) mem w)
    (hb : k.code[pc]? = some (0x90 + n.val).toUInt8) (hx : (y :: rest)[n.val + 1]? = some x)
    (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) (((y :: rest).set 0 x).set (n.val + 1) y) mem w → OwnB Halt G R S C Dm D B m') :
    OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [decode_swap]
  simp only [exec, wp_bind, wp_charge, wp_getFrame, hF.stack, hx, wp_modifyFrame, wp_advance,
    wp_pure, Cont]
  intro _
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], rfl, hF.mem, hF.world⟩

theorem pop (hF : Fr k m pc (x :: rest) mem w) (hb : k.code[pc]? = some 0x50) (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) rest mem w → OwnB Halt G R S C Dm D B m') : OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [show Opcode.decode m.ctx.fork 0x50 = .pop by cases m.ctx.fork <;> rfl]
  simp only [exec, wp_bind, wp_pop, wp_charge, wp_advance, wp_pure, Cont]
  intro x' xs hx _
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], rfl, hF.mem, hF.world⟩

theorem jumpdest (hF : Fr k m pc st mem w) (hb : k.code[pc]? = some 0x5b) (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) st mem w → OwnB Halt G R S C Dm D B m') : OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [show Opcode.decode m.ctx.fork 0x5b = .jumpdest by cases m.ctx.fork <;> rfl]
  simp only [exec, wp_bind, wp_charge, wp_advance, wp_pure, Cont]
  intro _
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], hF.stack, hF.mem, hF.world⟩

/-- `JUMPDEST`, as one `Step` (a loop head, for `OwnG.coind`). -/
theorem jumpdestStep (hF : Fr k m pc st mem w) (hb : k.code[pc]? = some 0x5b) (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) st mem w → OwnB Halt G R S C Dm D B m') :
    Step Halt G R S C Dm D (OwnB Halt G R S C Dm D B) m := by
  apply stepOf_wpR (Own.byte hF hb) hS fun _ => ?_
  rw [show Opcode.decode m.ctx.fork 0x5b = .jumpdest by cases m.ctx.fork <;> rfl]
  simp only [exec, wp_bind, wp_charge, wp_advance, wp_pure, Cont]
  intro _
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], hF.stack, hF.mem, hF.world⟩

/-- `JUMP`: whether or not the destination is valid, the frame continues there if at all. -/
theorem jump (hF : Fr k m pc (x :: rest) mem w) (hb : k.code[pc]? = some 0x56) (hS : S m)
    (h : ∀ m', Fr k m' x.toNat rest mem w → OwnB Halt G R S C Dm D B m') : OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [show Opcode.decode m.ctx.fork 0x56 = .jump by cases m.ctx.fork <;> rfl]
  simp only [exec, wp_bind, wp_popNat, wp_charge, wp_getFrame, wp_ite, wp_throw, wp_modifyFrame,
    wp_pure, Cont]
  intro x' xs hx _
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  exact ⟨fun _ => trivial, fun _ => h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, rfl, rfl, hF.mem,
    hF.world⟩⟩

theorem jumpi (hF : Fr k m pc (x :: y :: rest) mem w) (hb : k.code[pc]? = some 0x57) (hS : S m)
    (h0 : y = 0 → ∀ m', Fr k m' (pc + 1) rest mem w → OwnB Halt G R S C Dm D B m')
    (h1 : y ≠ 0 → ∀ m', Fr k m' x.toNat rest mem w → OwnB Halt G R S C Dm D B m') : OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [show Opcode.decode m.ctx.fork 0x57 = .jumpi by cases m.ctx.fork <;> rfl]
  simp only [exec, wp_bind, wp_popNat, wp_pop, wp_charge, wp_getFrame, wp_ite, wp_throw,
    wp_modifyFrame, wp_advance, wp_pure, Cont]
  intro x' xs hx y' ys hy _
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hy
  refine ⟨fun hy0 => h0 hy0 _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], rfl, hF.mem,
    hF.world⟩, fun hy0 => ⟨fun _ => trivial, fun _ => h1 hy0 _ ⟨hF.msg, hF.ctx, hF.pre, hF.code,
    rfl, rfl, hF.mem, hF.world⟩⟩⟩

theorem calldataload (hF : Fr k m pc (x :: rest) mem w) (hb : k.code[pc]? = some 0x35)
    (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) (Bytes.toWord (readBytes k.msg.data x.toNat 32) :: rest) mem w →
      OwnB Halt G R S C Dm D B m') : OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [show Opcode.decode m.ctx.fork 0x35 = .calldataload by cases m.ctx.fork <;> rfl]
  simp only [exec, wp_bind, wp_popNat, wp_charge, wp_getFrame, wp_push, wp_advance, wp_pure, Cont]
  intro x' xs hx _ _
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], by simp [hF.msg], hF.mem, hF.world⟩

theorem mload (hF : Fr k m pc (x :: rest) mem w) (hb : k.code[pc]? = some 0x51) (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) ((mem.expand x.toNat 32).loadWord x.toNat :: rest)
      (mem.expand x.toNat 32) w → OwnB Halt G R S C Dm D B m') : OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [show Opcode.decode m.ctx.fork 0x51 = .mload by cases m.ctx.fork <;> rfl]
  simp only [exec, memoryExpansion, expandMemory, List.foldl, wp_bind, wp_popNat, wp_getFrame,
    wp_charge, wp_modifyFrame, wp_push, wp_advance, wp_pure, Cont]
  intro x' xs hx _ _
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], by simp [hF.mem], by simp [hF.mem],
    hF.world⟩

theorem mstore (hF : Fr k m pc (x :: y :: rest) mem w) (hb : k.code[pc]? = some 0x52)
    (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) rest ((mem.expand x.toNat 32).storeWord x.toNat y) w →
      OwnB Halt G R S C Dm D B m') : OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [show Opcode.decode m.ctx.fork 0x52 = .mstore by cases m.ctx.fork <;> rfl]
  simp only [exec, memoryExpansion, expandMemory, List.foldl, wp_bind, wp_popNat, wp_pop,
    wp_getFrame, wp_charge, wp_modifyFrame, wp_advance, wp_pure, Cont]
  intro x' xs hx y' ys hy _
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hy
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], rfl, by simp [hF.mem], hF.world⟩

theorem sload (hF : Fr k m pc (x :: rest) mem w) (hb : k.code[pc]? = some 0x54) (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) (w.sload k.msg.currentTarget x :: rest) mem w → OwnB Halt G R S C Dm D B m') :
    OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [show Opcode.decode m.ctx.fork 0x54 = .sload by cases m.ctx.fork <;> rfl]
  simp only [exec, accessStorageKey, wp_bind, wp_pop, wp_getFrame, wp_get, wp_charge, wp_push,
    wp_advance, wp_pure, Cont]
  intro x' xs hx
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  split <;> simp only [wp_bind, wp_pure, wp_modifySub] <;> intro _ _ <;>
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], by simp [hF.msg, hF.world], hF.mem,
    hF.world⟩

/-- `SLOAD`, telling the continuation that the run predicate held of a machine with this
world. -/
theorem sloadR (hF : Fr k m pc (x :: rest) mem w) (hb : k.code[pc]? = some 0x54) (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) (w.sload k.msg.currentTarget x :: rest) mem w →
      (∃ m₀ : Machine, m₀.world = w ∧ R m₀) → OwnB Halt G R S C Dm D B m') :
    OwnB Halt G R S C Dm D B m := by
  apply of_wpR (Own.byte hF hb) hS
  intro hR
  rw [show Opcode.decode m.ctx.fork 0x54 = .sload by cases m.ctx.fork <;> rfl]
  simp only [exec, accessStorageKey, wp_bind, wp_pop, wp_getFrame, wp_get, wp_charge, wp_push,
    wp_advance, wp_pure, Cont]
  intro x' xs hx
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  split <;> simp only [wp_bind, wp_pure, wp_modifySub] <;> intro _ _ <;>
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], by simp [hF.msg, hF.world], hF.mem,
    hF.world⟩ ⟨m, hF.world, hR⟩

/-- `MSTORE8`. -/
theorem mstore8 (hF : Fr k m pc (x :: y :: rest) mem w) (hb : k.code[pc]? = some 0x53)
    (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) rest ((mem.expand x.toNat 1).storeByte x.toNat y) w →
      OwnB Halt G R S C Dm D B m') : OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [show Opcode.decode m.ctx.fork 0x53 = .mstore8 by cases m.ctx.fork <;> rfl]
  simp only [exec, memoryExpansion, expandMemory, List.foldl, wp_bind, wp_popNat, wp_pop,
    wp_getFrame, wp_charge, wp_modifyFrame, wp_advance, wp_pure, Cont]
  intro x' xs hx y' ys hy _
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hy
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], rfl, by simp [hF.mem], hF.world⟩

theorem sstore (hF : Fr k m pc (x :: y :: rest) mem w) (hb : k.code[pc]? = some 0x55)
    (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) rest mem (w.sstore k.msg.currentTarget x y) → OwnB Halt G R S C Dm D B m') :
    OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [show Opcode.decode m.ctx.fork 0x55 = .sstore by cases m.ctx.fork <;> rfl]
  simp only [exec, execSstore, accessStorageKey, requireNonStatic, setStorage, wp_bind, wp_pop,
    wp_getFrame, wp_get, wp_charge, wp_ite, wp_throw, wp_modifySub, wp_modifyWorld, wp_advance,
    wp_pure, Cont]
  intro x' xs hx y' ys hy
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hy
  have hF' : ∀ m', m'.frame.msg = m.frame.msg → m'.ctx = m.ctx → m'.precompiles = m.precompiles →
      m'.frame.code = m.frame.code → m'.frame.pc = m.frame.pc + 1 → m'.frame.stack = rest →
      m'.frame.memory = m.frame.memory →
      m'.world = m.world.sstore m.frame.msg.currentTarget x y → OwnB Halt G R S C Dm D B m' := by
    intro m' h1 h2 h3 h4 h5 h6 h7 h8
    exact h m' ⟨h1.trans hF.msg, h2.trans hF.ctx, h3.trans hF.pre, h4.trans hF.code,
      by rw [h5, hF.pc], h6, h7.trans hF.mem, by rw [h8, hF.world, hF.msg]⟩
  refine ⟨fun _ => trivial, fun _ => ⟨fun _ _ => ⟨fun _ => trivial, fun _ => ?_⟩,
    fun _ _ => ⟨fun _ => trivial, fun _ => ?_⟩⟩⟩ <;>
    exact hF' _ rfl rfl rfl rfl rfl rfl rfl rfl

theorem keccak256 (hF : Fr k m pc (x :: y :: rest) mem w) (hb : k.code[pc]? = some 0x20)
    (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1)
      (k.ctx.crypto.keccak256 (readBytes (mem.expand x.toNat y.toNat).bytes x.toNat y.toNat) ::
        rest) (mem.expand x.toNat y.toNat) w → OwnB Halt G R S C Dm D B m') : OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [show Opcode.decode m.ctx.fork 0x20 = .keccak256 by cases m.ctx.fork <;> rfl]
  simp only [exec, memoryExpansion, expandMemory, readMemory, List.foldl, wp_bind, wp_popNat,
    wp_getFrame, wp_get, wp_charge, wp_modifyFrame, wp_push, wp_advance, wp_pure, Cont]
  intro x' xs hx y' ys hy _ _
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hy
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], by simp [hF.mem, hF.ctx],
    by simp [hF.mem], hF.world⟩

/-- `CALLDATACOPY`. -/
theorem calldatacopy (hF : Fr k m pc (x :: y :: z :: rest) mem w)
    (hb : k.code[pc]? = some 0x37) (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) rest
      (Own.copyIn mem x.toNat z.toNat (readBytes k.msg.data y.toNat z.toNat)) w → OwnB Halt G R S C Dm D B m') :
    OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [show Opcode.decode m.ctx.fork 0x37 = .calldatacopy by cases m.ctx.fork <;> rfl]
  simp only [exec, copyToMemory, memoryExpansion, expandMemory, writeMemory, List.foldl, wp_bind,
    wp_popNat, wp_getFrame, wp_get, wp_charge, wp_modifyFrame, wp_ite, wp_advance, wp_pure, Cont]
  intro x' xs hx y' ys hy z' zs hz _
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hy
  obtain ⟨rfl, rfl⟩ := List.cons.inj hz
  have hsz : (readBytes k.msg.data y.toNat z.toNat).size = z.toNat := size_readBytes _ _ _
  refine ⟨fun h0 => h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], rfl, ?_, hF.world⟩,
    fun h0 => h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], rfl, ?_, hF.world⟩⟩
  · rw [hF.msg, hsz] at h0
    show _ = Own.copyIn _ _ _ _
    rw [Own.copyIn, ite_eq_left h0, hF.mem]
  · rw [hF.msg, hsz] at h0
    show _ = Own.copyIn _ _ _ _
    rw [Own.copyIn, ite_eq_right h0, hF.mem, hF.msg]

/-- `RETURNDATACOPY`: the memory afterwards is left unknown. -/
theorem returndatacopy (hF : Fr k m pc (x :: y :: z :: rest) mem w)
    (hb : k.code[pc]? = some 0x3e) (hS : S m)
    (h : ∀ mem' m', Fr k m' (pc + 1) rest mem' w → OwnB Halt G R S C Dm D B m') : OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [show Opcode.decode m.ctx.fork 0x3e = .returndatacopy by cases m.ctx.fork <;> rfl]
  simp only [exec, memoryExpansion, expandMemory, writeMemory, List.foldl, wp_bind,
    wp_popNat, wp_getFrame, wp_charge, wp_modifyFrame, wp_ite, wp_throw, wp_advance, wp_pure, Cont]
  intro x' xs hx y' ys hy z' zs hz _
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hy
  obtain ⟨rfl, rfl⟩ := List.cons.inj hz
  refine ⟨fun _ => trivial, fun _ => ⟨fun _ => h _ _ ⟨hF.msg, hF.ctx, hF.pre, hF.code,
    by simp [hF.pc], rfl, rfl, hF.world⟩, fun _ => h _ _ ⟨hF.msg, hF.ctx, hF.pre, hF.code,
    by simp [hF.pc], rfl, rfl, hF.world⟩⟩⟩


/-! ## Calls -/

/-- What the guards need of the message a `CALL`-family instruction requests. -/
def CallMsg (kind : CallKind) (m : Machine) (toW : Word) (msg : Message) : Prop :=
  ((m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none) →
    msg.code = m.world.code (Word.toAddress toW) ∧ msg.codeAddress = some (Word.toAddress toW)) ∧
  match kind with
  | .call => msg.currentTarget = Word.toAddress toW ∧ msg.caller = m.frame.msg.currentTarget ∧
      msg.isStatic = m.frame.msg.isStatic
  | .callcode => True
  | .delegatecall => msg.currentTarget = m.frame.msg.currentTarget ∧
      msg.caller = m.frame.msg.caller ∧ msg.isStatic = m.frame.msg.isStatic
  | .staticcall => msg.currentTarget = Word.toAddress toW ∧
      msg.caller = m.frame.msg.currentTarget ∧ msg.isStatic = true

theorem callMsg_static {m : Machine} {toW : Word} {msg : Message}
    (h : CallMsg .staticcall m toW msg) : msg.isStatic = true := h.2.2.2

/-- What a `CALL`-family instruction leaves: the frame continues with `0` (depth limit,
insufficient balance), or the call is requested. -/
def CallPost (kind : CallKind) (m : Machine) (toW inOff inSize outOff outSize : Word)
    (rest : List Word) : Action → Machine → Prop := fun a m' =>
  m'.frame.msg = m.frame.msg ∧ m'.ctx = m.ctx ∧ m'.precompiles = m.precompiles ∧
    m'.frame.code = m.frame.code ∧ m'.world = m.world ∧
    m'.frame.memory = (m.frame.memory.expand inOff.toNat inSize.toNat).expand outOff.toNat
      outSize.toNat ∧
    ((a = .next ∧ m'.frame.stack = 0 :: rest ∧ m'.frame.pc = m.frame.pc + 1) ∨
     (∃ req, a = .call req ∧ m'.frame.stack = rest ∧ m'.frame.pc = m.frame.pc ∧
       req.retOffset = outOff.toNat ∧ req.retSize = outSize.toNat ∧ CallMsg kind m toW req.msg))

theorem exec_call_post {g toW value inOff inSize outOff outSize : Word}
    (hs : m.frame.stack = g :: toW :: value :: inOff :: inSize :: outOff :: outSize :: rest) :
    Wp (exec .call) (CallPost .call m toW inOff inSize outOff outSize rest) m := by
  simp only [exec, execCall, genericCall, memoryExpansion, expandMemory, readMemory,
    setReturnData, List.foldl, wp_bind, wp_popNat, wp_popAddress, wp_pop,
    wp_getFrame, wp_get, wp_charge, wp_modifyFrame, wp_ite, wp_throw, wp_advance,
    wp_push, wp_refundGas, wp_pure, wp_accessAddress, wp_accessDelegation, hs, List.cons.injEq,
    and_imp, forall_apply_eq_imp_iff, forall_eq']
  refine ⟨fun hd => ?_, fun d hf hd => ?_⟩ <;> intro _ <;>
    refine ⟨fun _ => trivial, fun _ => ⟨fun _ _ => ?_, fun _ => ⟨fun _ _ => ?_, fun _ => ?_⟩⟩⟩ <;>
    simp [CallPost, CallMsg, hd] <;> exact fun h => absurd h ‹_›

theorem exec_staticcall_post {g toW inOff inSize outOff outSize : Word}
    (hs : m.frame.stack = g :: toW :: inOff :: inSize :: outOff :: outSize :: rest) :
    Wp (exec .staticcall) (CallPost .staticcall m toW inOff inSize outOff outSize rest) m := by
  simp only [exec, execCall, genericCall, memoryExpansion, expandMemory, readMemory,
    setReturnData, List.foldl, wp_bind, wp_popNat, wp_popAddress,
    wp_getFrame, wp_get, wp_charge, wp_modifyFrame, wp_ite, wp_throw, wp_advance,
    wp_push, wp_refundGas, wp_pure, wp_accessAddress, wp_accessDelegation, hs, List.cons.injEq,
    and_imp, forall_apply_eq_imp_iff, forall_eq']
  refine ⟨fun hd => ?_, fun d hf hd => ?_⟩
  · simp [CallPost, CallMsg, hd]
  · simp [CallPost, CallMsg, hd, hf]

theorem exec_delegatecall_post {g toW inOff inSize outOff outSize : Word}
    (hs : m.frame.stack = g :: toW :: inOff :: inSize :: outOff :: outSize :: rest) :
    Wp (exec .delegatecall) (CallPost .delegatecall m toW inOff inSize outOff outSize rest) m := by
  simp only [exec, execCall, genericCall, memoryExpansion, expandMemory, readMemory,
    setReturnData, List.foldl, wp_bind, wp_popNat, wp_popAddress,
    wp_getFrame, wp_get, wp_charge, wp_modifyFrame, wp_ite, wp_throw, wp_advance,
    wp_push, wp_refundGas, wp_pure, wp_accessAddress, wp_accessDelegation, hs, List.cons.injEq,
    and_imp, forall_apply_eq_imp_iff, forall_eq']
  refine ⟨fun hd => ?_, fun d hf hd => ?_⟩
  · simp [CallPost, CallMsg, hd]
  · simp [CallPost, CallMsg, hd, hf]

theorem launchCall_some_kind {m : Machine} {req : CallRequest}
    (h : precompileOf m.precompiles req.msg ≠ none) :
    ∃ w t r, launchCall m req = resume { m with world := w, transient := t } r ∧
      (w = transferValue m.world req.msg ∨ w = m.world) ∧
      r.kind = .call req.retOffset req.retSize := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 h
  unfold launchCall runPrecompile
  simp only [ha]
  split
  · exact ⟨_, _, _, rfl, .inl rfl, rfl⟩
  · exact ⟨_, _, _, rfl, .inr rfl, rfl⟩

theorem returnMemory_empty (mem : Memory) (o s : Nat) :
    EvmLogic.Program.returnMemory mem o s .empty = mem := by
  simp [EvmLogic.Program.returnMemory]

/-- The machine resumed after a child of the kind requested. -/
theorem fr_resume {m' M : Machine} {res : ChildResult} {ro rs : Nat} {rest : List Word}
    (hmsg : m'.frame.msg = k.msg) (hctx : M.ctx = k.ctx) (hpre : M.precompiles = k.pre)
    (hcode : m'.frame.code = k.code) (hpc : m'.frame.pc = pc) (hst : m'.frame.stack = rest)
    (hmem : m'.frame.memory = mem) (hM : M.frame = m'.frame) (hk : res.kind = .call ro rs) :
    Fr k (resume M res) (pc + 1) ((if res.success then 1 else 0) :: rest)
      (EvmLogic.Program.returnMemory mem ro rs res.output) M.world := by
  unfold resume
  simp only [hk]
  refine ⟨by simp [hM, hmsg], hctx, hpre, by simp [hM, hcode], by simp [hM, hpc],
    by simp [hM, hst], ?_, rfl⟩
  simp only [hM, hmem, EvmLogic.Program.returnMemory]

/-- **A `CALL`-family instruction** (with its `CallPost`): away from a doom point the request
satisfies `C`, and the frame continues after the child (or at once with `0`) with the output
written back and any world; at a doom point it continues as `D`. -/
theorem callAny {kind : CallKind} {op : Opcode} {toW inOff inSize outOff outSize : Word}
    {args : List Word}
    (hF : Fr k m pc (args ++ rest) mem w) (hb : k.code[pc]? = some b)
    (hop : ∀ fk, Opcode.decode fk b = op)
    (hpost : ∀ m₀ : Machine, m₀.frame.stack = args ++ rest →
      Wp (exec op) (CallPost kind m₀ toW inOff inSize outOff outSize rest) m₀)
    (hS : S m)
    (hC : R m → ¬ Dm m → ∀ req : CallRequest, CallMsg kind m toW req.msg → C m req)
    (hk : ∀ m'' res out w', Fr k m'' (pc + 1) (res :: rest)
      (EvmLogic.Program.returnMemory ((mem.expand inOff.toNat inSize.toNat).expand outOff.toNat
        outSize.toNat) outOff.toNat outSize.toNat out) w' → OwnB Halt G R S C Dm D B m'')
    (hD : Dm m → ∀ m'' res out w', Fr k m'' (pc + 1) (res :: rest)
      (EvmLogic.Program.returnMemory ((mem.expand inOff.toNat inSize.toNat).expand outOff.toNat
        outSize.toNat) outOff.toNat outSize.toNat out) w' → D m'') :
    OwnB Halt G R S C Dm D B m := by
  apply of_wpR (Own.byte hF hb) hS
  intro hR
  rw [hop]
  refine (hpost m hF.stack).mono ?_
  rintro a m' ⟨hmsg, hctx, hpre, hcode, hw, hmem, hcase⟩
  have hmem' : m'.frame.memory = (mem.expand inOff.toNat inSize.toNat).expand outOff.toNat
      outSize.toNat := by rw [hmem, hF.mem]
  rcases hcase with ⟨rfl, hst, hpc⟩ | ⟨req, rfl, hst, hpc, hro, hrs, hcm⟩
  · refine hk m' 0 .empty m'.world ⟨hmsg.trans hF.msg, hctx.trans hF.ctx, hpre.trans hF.pre,
      hcode.trans hF.code, by rw [hpc, hF.pc], hst, ?_, rfl⟩
    rw [returnMemory_empty, hmem']
  · have hres : ∀ M res, M.frame = m'.frame → M.ctx = m.ctx → M.precompiles = m.precompiles →
        res.kind = .call req.retOffset req.retSize →
        Fr k (resume M res) (pc + 1) ((if res.success then 1 else 0) :: rest)
          (EvmLogic.Program.returnMemory ((mem.expand inOff.toNat inSize.toNat).expand
            outOff.toNat outSize.toNat) outOff.toNat outSize.toNat res.output) M.world := by
      intro M res hM hMc hMpre hk'
      rw [hro, hrs] at hk'
      exact fr_resume (hmsg.trans hF.msg) (hMc.trans hF.ctx) (hMpre.trans hF.pre)
        (hcode.trans hF.code) (by rw [hpc, hF.pc]) hst hmem' hM hk'
    refine ⟨fun hd => ⟨hC hR hd req hcm, fun hp => ?_, fun _ M res hM _ hMc hMpre hk' _ =>
      hk _ _ _ _ (hres M res hM hMc hMpre hk')⟩, fun hd M res hM _ hMc hMpre hk' =>
        hD hd _ _ _ _ (hres M res hM hMc hMpre hk')⟩
    obtain ⟨w', t, r, hl, -, hrk⟩ := launchCall_some_kind hp
    rw [hl]
    exact hk _ _ _ _ (hres _ r rfl hctx hpre hrk)

theorem call {g toW value inOff inSize outOff outSize : Word}
    (hF : Fr k m pc (g :: toW :: value :: inOff :: inSize :: outOff :: outSize :: rest) mem w)
    (hb : k.code[pc]? = some 0xf1) (hS : S m)
    (hC : R m → ¬ Dm m → ∀ req : CallRequest, CallMsg .call m toW req.msg → C m req)
    (hk : ∀ m'' res out w', Fr k m'' (pc + 1) (res :: rest)
      (EvmLogic.Program.returnMemory ((mem.expand inOff.toNat inSize.toNat).expand outOff.toNat
        outSize.toNat) outOff.toNat outSize.toNat out) w' → OwnB Halt G R S C Dm D B m'')
    (hD : Dm m → ∀ m'' res out w', Fr k m'' (pc + 1) (res :: rest)
      (EvmLogic.Program.returnMemory ((mem.expand inOff.toNat inSize.toNat).expand outOff.toNat
        outSize.toNat) outOff.toNat outSize.toNat out) w' → D m'') :
    OwnB Halt G R S C Dm D B m :=
  callAny (args := [g, toW, value, inOff, inSize, outOff, outSize]) hF hb
    (fun fk => by cases fk <;> rfl) (fun _ hs => exec_call_post hs) hS hC hk hD

theorem staticcall {g toW inOff inSize outOff outSize : Word}
    (hF : Fr k m pc (g :: toW :: inOff :: inSize :: outOff :: outSize :: rest) mem w)
    (hb : k.code[pc]? = some 0xfa) (hS : S m)
    (hC : R m → ¬ Dm m → ∀ req : CallRequest, CallMsg .staticcall m toW req.msg → C m req)
    (hk : ∀ m'' res out w', Fr k m'' (pc + 1) (res :: rest)
      (EvmLogic.Program.returnMemory ((mem.expand inOff.toNat inSize.toNat).expand outOff.toNat
        outSize.toNat) outOff.toNat outSize.toNat out) w' → OwnB Halt G R S C Dm D B m'')
    (hD : Dm m → ∀ m'' res out w', Fr k m'' (pc + 1) (res :: rest)
      (EvmLogic.Program.returnMemory ((mem.expand inOff.toNat inSize.toNat).expand outOff.toNat
        outSize.toNat) outOff.toNat outSize.toNat out) w' → D m'') :
    OwnB Halt G R S C Dm D B m :=
  callAny (args := [g, toW, inOff, inSize, outOff, outSize]) hF hb
    (fun fk => by cases fk <;> rfl) (fun _ hs => exec_staticcall_post hs) hS hC hk hD

theorem delegatecall {g toW inOff inSize outOff outSize : Word}
    (hF : Fr k m pc (g :: toW :: inOff :: inSize :: outOff :: outSize :: rest) mem w)
    (hb : k.code[pc]? = some 0xf4) (hS : S m)
    (hC : R m → ¬ Dm m → ∀ req : CallRequest, CallMsg .delegatecall m toW req.msg → C m req)
    (hk : ∀ m'' res out w', Fr k m'' (pc + 1) (res :: rest)
      (EvmLogic.Program.returnMemory ((mem.expand inOff.toNat inSize.toNat).expand outOff.toNat
        outSize.toNat) outOff.toNat outSize.toNat out) w' → OwnB Halt G R S C Dm D B m'')
    (hD : Dm m → ∀ m'' res out w', Fr k m'' (pc + 1) (res :: rest)
      (EvmLogic.Program.returnMemory ((mem.expand inOff.toNat inSize.toNat).expand outOff.toNat
        outSize.toNat) outOff.toNat outSize.toNat out) w' → D m'') :
    OwnB Halt G R S C Dm D B m :=
  callAny (args := [g, toW, inOff, inSize, outOff, outSize]) hF hb
    (fun fk => by cases fk <;> rfl) (fun _ hs => exec_delegatecall_post hs) hS hC hk hD

/-- **`STATICCALL` of a precompile** away from a doom point (standard precompiles, not disabled
by a delegation): the frame continues at once with `0`, or with `1` and the precompile's
output written back; the world is unchanged. -/
theorem staticcallPre {g toW inOff inSize outOff outSize : Word}
    (hF : Fr k m pc (g :: toW :: inOff :: inSize :: outOff :: outSize :: rest) mem w)
    (hb : k.code[pc]? = some 0xfa) (hS : S m) (hnd : ¬ Dm m)
    (hpre : k.pre.isPrecompile (Word.toAddress toW) = true)
    (hdel : R m → k.ctx.fork < .prague ∨ delegatedAddress? (w.code (Word.toAddress toW)) = none)
    (hC : ∀ req : CallRequest, req.msg.currentTarget = Word.toAddress toW →
      req.msg.isStatic = true → C m req)
    (h : ∀ m' res mem', Fr k m' (pc + 1) (res :: rest) mem' w →
      (res ≠ 0 → ∃ gas' : Nat,
        (k.pre.run (Word.toAddress toW) (readBytes ((mem.expand inOff.toNat inSize.toNat).expand
          outOff.toNat outSize.toNat).bytes inOff.toNat inSize.toNat) gas').success = true ∧
        mem' = EvmLogic.Program.returnMemory ((mem.expand inOff.toNat inSize.toNat).expand
          outOff.toNat outSize.toNat) outOff.toNat outSize.toNat (k.pre.run (Word.toAddress toW)
            (readBytes ((mem.expand inOff.toNat inSize.toNat).expand outOff.toNat
              outSize.toNat).bytes inOff.toNat inSize.toNat) gas').output) →
      OwnB Halt G R S C Dm D B m') :
    OwnB Halt G R S C Dm D B m := by
  have hdec : Opcode.decode m.ctx.fork 0xfa = .staticcall := by cases m.ctx.fork <;> rfl
  apply of_wpR (Own.byte hF hb) hS
  intro hR
  have hdel' : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none :=
    by rw [Own.fork hF, hF.world]; exact hdel hR
  rw [hdec]
  refine (Wp.and (Own.exec_staticcall hF.stack hdel') (exec_staticcall_post hF.stack)).mono ?_
  rintro a m' ⟨⟨hw, hmsg, hctx, hpr, hcode, hmem, hcase⟩, -, -, -, -, -, -, hcase'⟩
  rcases hcase with ⟨rfl, hst, hpc⟩ | ⟨req, rfl, hst, hpc, htgt, hca, hdis, hval, hdata, hro, hrs⟩
  · exact h m' 0 _ ⟨hmsg.trans hF.msg, hctx.trans hF.ctx, hpr.trans hF.pre,
      hcode.trans hF.code, by rw [hpc, hF.pc], hst, by rw [hmem, hF.mem], hw.trans hF.world⟩
      (fun h0 => absurd rfl h0)
  · have hpc' : precompileOf m'.precompiles req.msg = some (Word.toAddress toW) := by
      simp [precompileOf, hdis, hca, hpr, hF.pre, hpre]
    have hst' : req.msg.isStatic = true := by
      rcases hcase' with ⟨h1, -⟩ | ⟨req', h1, -, -, -, -, -, hcm⟩
      · cases h1
      · cases h1; exact hcm.2.2
    refine ⟨fun _ => ⟨hC _ htgt hst', fun _ => ?_, fun hn => absurd hpc' (by rw [hn]; simp)⟩,
      fun hd => absurd hd hnd⟩
    have htv : transferValue m'.world req.msg = m'.world := transferValue_zero _ _ hval
    simp only [launchCall, hpc', runPrecompile, htv]
    have hpr' : m'.precompiles = k.pre := hpr.trans hF.pre
    have hdata' : req.msg.data = readBytes ((mem.expand inOff.toNat inSize.toNat).expand
        outOff.toNat outSize.toNat).bytes inOff.toNat inSize.toNat := by rw [hdata, hF.mem]
    rw [hpr', hdata']
    split
    · rename_i hsucc
      refine h _ 1 _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ (fun _ => ⟨req.msg.gas, hsucc, rfl⟩) <;>
        simp [resume, ChildResult.success, EvmLogic.Program.returnMemory, hmsg, hF.msg, hctx,
          hF.ctx, hcode, hF.code, hpc, hF.pc, hst, hmem, hF.mem, hro, hrs, hw, hF.world]
    · refine h _ 0 _ ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩ (fun h0 => absurd rfl h0) <;>
        simp [resume, ChildResult.success, hmsg, hF.msg, hctx, hF.ctx, hcode, hF.code, hpc, hF.pc,
          hst, hw, hF.world]

/-! ## Other instructions -/

/-- `EXP` (its gas depends on the exponent). -/
theorem exp (hF : Fr k m pc (x :: y :: rest) mem w) (hb : k.code[pc]? = some 0x0a) (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) (Word.exp x y :: rest) mem w → OwnB Halt G R S C Dm D B m') :
    OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [show Opcode.decode m.ctx.fork 0x0a = .exp by cases m.ctx.fork <;> rfl]
  simp only [exec, wp_bind, wp_pop, wp_charge, wp_push, wp_advance, wp_pure, Cont]
  intro x' xs hx y' ys hy _ _
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hy
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], rfl, hF.mem, hF.world⟩

/-- `EXTCODESIZE`. -/
theorem extcodesize (hF : Fr k m pc (x :: rest) mem w) (hb : k.code[pc]? = some 0x3b)
    (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) (ofNat (w.code (Word.toAddress x)).size :: rest) mem w →
      OwnB Halt G R S C Dm D B m') : OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [show Opcode.decode m.ctx.fork 0x3b = .extcodesize by cases m.ctx.fork <;> rfl]
  simp only [exec, wp_bind, wp_popAddress, wp_accessAddress, wp_get, wp_charge, wp_push,
    wp_advance, wp_pure, Cont]
  intro x' xs hx _ _
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], by simp [hF.world], hF.mem,
    hF.world⟩

/-- `EXTCODESIZE`, telling the continuation that the run predicate held of a machine with this
world. -/
theorem extcodesizeR (hF : Fr k m pc (x :: rest) mem w) (hb : k.code[pc]? = some 0x3b)
    (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) (ofNat (w.code (Word.toAddress x)).size :: rest) mem w →
      (∃ m₀ : Machine, m₀.world = w ∧ R m₀) → OwnB Halt G R S C Dm D B m') :
    OwnB Halt G R S C Dm D B m := by
  apply of_wpR (Own.byte hF hb) hS
  intro hR
  rw [show Opcode.decode m.ctx.fork 0x3b = .extcodesize by cases m.ctx.fork <;> rfl]
  simp only [exec, wp_bind, wp_popAddress, wp_accessAddress, wp_get, wp_charge, wp_push,
    wp_advance, wp_pure, Cont]
  intro x' xs hx _ _
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], by simp [hF.world], hF.mem,
    hF.world⟩ ⟨m, hF.world, hR⟩

theorem wp_popN_eq {Q : List Word → Machine → Prop} {m : Machine} :
    ∀ (ts rest : List Word), m.frame.stack = ts ++ rest →
      Q ts { m with frame := { m.frame with stack := rest } } → Wp (popN ts.length) Q m
  | [], rest, hs, h => by
    simp only [List.nil_append] at hs
    show Wp (pure []) Q m
    rw [wp_pure]
    have : m = { m with frame := { m.frame with stack := rest } } := by rw [← hs]
    rw [this]; exact h
  | t :: ts, rest, hs, h => by
    show Wp (popN (ts.length + 1)) Q m
    unfold popN
    simp only [wp_bind, wp_pop, wp_pure]
    intro x xs hx
    rw [hs, List.cons_append] at hx
    have hx' := List.cons.inj hx
    rw [← hx'.1]
    exact wp_popN_eq (Q := fun ys m' => Q (t :: ys) m') ts rest hx'.2.symm h

theorem exec_log0 (fk : Fork) : exec (Opcode.decode fk 0xa0) = execLog 0 := by cases fk <;> rfl
theorem exec_log1 (fk : Fork) : exec (Opcode.decode fk 0xa1) = execLog 1 := by cases fk <;> rfl
theorem exec_log2 (fk : Fork) : exec (Opcode.decode fk 0xa2) = execLog 2 := by cases fk <;> rfl
theorem exec_log3 (fk : Fork) : exec (Opcode.decode fk 0xa3) = execLog 3 := by cases fk <;> rfl
theorem exec_log4 (fk : Fork) : exec (Opcode.decode fk 0xa4) = execLog 4 := by cases fk <;> rfl

/-- `LOG0`–`LOG4`: memory expanded, the frame continues. -/
theorem log {ts : List Word} (hF : Fr k m pc (x :: y :: (ts ++ rest)) mem w)
    (hb : k.code[pc]? = some b) (hop : ∀ fk, exec (Opcode.decode fk b) = execLog ts.length)
    (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) rest (mem.expand x.toNat y.toNat) w →
      OwnB Halt G R S C Dm D B m') : OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [hop]
  simp only [execLog, wp_bind, wp_popNat]
  intro x' xs hx y' ys hy
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hy
  refine wp_popN_eq ts rest rfl ?_
  simp only [memoryExpansion, expandMemory, requireNonStatic, readMemory, List.foldl, wp_bind,
    wp_getFrame, wp_charge, wp_modifyFrame, wp_ite, wp_throw, wp_modifySub, wp_advance, wp_pure,
    Cont]
  intro _
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], rfl, by simp [hF.mem], hF.world⟩

/-- `REVERT`, `INVALID`: the frame ends without effect. -/
theorem haltRevert (hF : Fr k m pc st mem w) (hb : k.code[pc]? = some b)
    (hop : Opcode.decode k.ctx.fork b = .revert ∨ Opcode.decode k.ctx.fork b = .invalid)
    (hS : S m) : OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [Own.fork hF]
  rcases hop with h | h <;> rw [h] <;>
    simp [exec, readOutput, memoryExpansion, expandMemory, readMemory, Cont]

/-- `RETURN`, `STOP`: a successful halt, allowed by `Halt`. -/
theorem haltStop (hF : Fr k m pc st mem w) (hb : k.code[pc]? = some b)
    (hop : Opcode.decode k.ctx.fork b = .«return» ∨ Opcode.decode k.ctx.fork b = .stop)
    (hH : Halt) (hS : S m) : OwnB Halt G R S C Dm D B m := by
  apply of_wp (Own.byte hF hb) hS
  rw [Own.fork hF]
  rcases hop with h | h <;> rw [h] <;>
    simp [exec, readOutput, memoryExpansion, expandMemory, readMemory, Cont, hH]

end OwnB

/-! ## The frame judgment: coinductive -/

/-- **Every own path from `m` stays safe**: `m` lies in a set `L` of machines each of which
takes a `Step` and continues by explorations (`OwnB`) that end the frame or come back to `L`.
Unlike an inductive judgment it needs no termination argument: a loop is proved by an
invariant (`OwnG.coind`). -/
def OwnG (Halt : Prop) (G : World → Prop) (R : Machine → Prop) (S : Machine → Prop)
    (C : Machine → CallRequest → Prop) (Dm : Machine → Prop) (D : Machine → Prop)
    (m : Machine) : Prop :=
  ∃ L : Machine → Prop, L m ∧ ∀ x, L x → Step Halt G R S C Dm D (OwnB Halt G R S C Dm D L) x

namespace OwnG

/-- Coinduction: a set `L` whose machines step, continuing to `L` or to `OwnG`. -/
theorem coind (L : Machine → Prop)
    (h : ∀ x, L x → Step Halt G R S C Dm D
      (OwnB Halt G R S C Dm D fun y => L y ∨ OwnG Halt G R S C Dm D y) x) :
    ∀ x, L x → OwnG Halt G R S C Dm D x := by
  intro x hx
  refine ⟨fun y => L y ∨ OwnG Halt G R S C Dm D y, .inl hx, ?_⟩
  rintro y (hy | ⟨L', hy, hcl⟩)
  · exact h y hy
  · have hL' : ∀ z, OwnB Halt G R S C Dm D L' z →
        OwnB Halt G R S C Dm D (fun y => L y ∨ OwnG Halt G R S C Dm D y) z :=
      fun z hz => OwnB.mono (fun w hw => .inr ⟨L', hw, hcl⟩) hz
    exact (hcl y hy).mono hL'

/-- **One step of the judgment**, with successors satisfying it. -/
theorem step (h : OwnG Halt G R S C Dm D m) :
    Step Halt G R S C Dm D (OwnG Halt G R S C Dm D) m := by
  obtain ⟨L, hm, hcl⟩ := h
  refine (hcl m hm).mono fun x hx => ⟨fun y => L y ∨ OwnB Halt G R S C Dm D L y, .inr hx, ?_⟩
  rintro y (hy | hy)
  · exact (hcl y hy).mono fun z hz => OwnB.mono (fun w hw => .inl hw) hz
  · exact (OwnB.toStep hcl hy).mono fun z hz => OwnB.mono (fun w hw => .inl hw) hz

/-- An exploration whose leaves satisfy the judgment proves it. -/
theorem ofB (hB : ∀ x, B x → OwnG Halt G R S C Dm D x) (h : OwnB Halt G R S C Dm D B m) :
    OwnG Halt G R S C Dm D m := by
  refine ⟨fun y => OwnB Halt G R S C Dm D B y ∨ OwnG Halt G R S C Dm D y, .inl h, ?_⟩
  have hlift : ∀ z, OwnG Halt G R S C Dm D z →
      OwnB Halt G R S C Dm D (fun y => OwnB Halt G R S C Dm D B y ∨ OwnG Halt G R S C Dm D y) z :=
    fun z hz => .leaf (.inr hz)
  rintro y (hy | hy)
  · cases hy with
    | intro hS hn hi hp hr hd hc hs he =>
      exact ⟨hS, fun b m' hR hb he' => .leaf (.inl (hn b m' hR hb he')), hi,
        fun b req m' hR hb he' hd' hp' => .leaf (.inl (hp b req m' hR hb he' hd' hp')),
        fun b req m' hR hb he' hd' hp' M res hM hMp hMc hMpre hk hG =>
          .leaf (.inl (hr b req m' hR hb he' hd' hp' M res hM hMp hMc hMpre hk hG)),
        hd, hc, hs, he⟩
    | leaf h => exact (step (hB _ h)).mono hlift
  · exact (step hy).mono hlift

/-- Exploration with the judgment itself at the leaves. -/
theorem ofSelf (h : OwnB Halt G R S C Dm D (OwnG Halt G R S C Dm D) m) :
    OwnG Halt G R S C Dm D m :=
  ofB (fun _ hx => hx) h

/-- The states of the judgment take a step (for `OwnB.withR`). -/
theorem stepB (h : OwnG Halt G R S C Dm D m) :
    Step Halt G R S C Dm D (OwnB Halt G R S C Dm D (OwnG Halt G R S C Dm D)) m :=
  (step h).mono fun _ hx => .leaf hx

/-- The run predicate may be assumed of the machine at hand. -/
theorem withR (h : R m → OwnG Halt G R S C Dm D m) : OwnG Halt G R S C Dm D m :=
  ofSelf (OwnB.withR (fun _ hx => stepB hx) fun hR => .leaf (h hR))

theorem safe (h : OwnG Halt G R S C Dm D m) (hR : R m) : S m := (step h).safe hR

theorem next (h : OwnG Halt G R S C Dm D m) (hR : R m) (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.next, m')) :
    OwnG Halt G R S C Dm D m' := (step h).next b m' hR hb he

theorem iss {req : CallRequest} (h : OwnG Halt G R S C Dm D m)
    (hR : R m) (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m')) (hd : ¬ Dm m) :
    C m req := (step h).iss b req m' hR hb he hd

theorem pre {req : CallRequest} (h : OwnG Halt G R S C Dm D m)
    (hR : R m) (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m')) (hd : ¬ Dm m)
    (hp : precompileOf m'.precompiles req.msg ≠ none) :
    OwnG Halt G R S C Dm D (launchCall m' req) := (step h).pre b req m' hR hb he hd hp

theorem real {req : CallRequest} (h : OwnG Halt G R S C Dm D m)
    (hR : R m) (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m')) (hd : ¬ Dm m)
    (hp : precompileOf m'.precompiles req.msg = none) {M : Machine} (res : ChildResult)
    (hM : M.frame = m'.frame) (hMp : M.parents = m.parents) (hMc : M.ctx = m.ctx)
    (hMpre : M.precompiles = m.precompiles) (hk : res.kind = .call req.retOffset req.retSize)
    (hG : G M.world) : OwnG Halt G R S C Dm D (resume M res) :=
  (step h).real b req m' hR hb he hd hp M res hM hMp hMc hMpre hk hG

theorem doom {req : CallRequest} (h : OwnG Halt G R S C Dm D m)
    (hR : R m) (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m')) (hd : Dm m)
    {M : Machine} (res : ChildResult) (hM : M.frame = m'.frame) (hMp : M.parents = m.parents)
    (hMc : M.ctx = m.ctx) (hMpre : M.precompiles = m.precompiles)
    (hk : res.kind = .call req.retOffset req.retSize) : D (resume M res) :=
  (step h).doom b req m' hR hb he hd M res hM hMp hMc hMpre hk

theorem create {msg : Message} (h : OwnG Halt G R S C Dm D m)
    (hR : R m) (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.create msg, m')) : False :=
  (step h).create b msg m' hR hb he

theorem stop {out : ByteArray} (h : OwnG Halt G R S C Dm D m)
    (hR : R m) (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.stop out, m')) : Halt :=
  (step h).stop b out m' hR hb he

theorem end_ (h : OwnG Halt G R S C Dm D m) (hR : R m) (hn : m.frame.code[m.frame.pc]? = none) :
    Halt := (step h).end_ hR hn

end OwnG

/-- **A doomed frame**: every own path reverts (or halts exceptionally), whatever its children
do. Its effects and those of its children are rolled back. -/
abbrev Doomed : Machine → Prop :=
  OwnG False (fun _ => True) (fun _ => True) (fun _ => True) (fun _ _ => True) (fun _ => False) (fun _ => False)

end EvmLogic.Program.Nested
