import EvmLogic.Program.Nested.Wp
import EvmLogic.Program.PrecompileCall
import EvmLogic.Step.Stack

/-!
# Own steps: every path of a frame ends it, by safe instructions

`Own S C m`: from `m`, every path of the frame by its own instructions ends the frame (a halt,
a revert, a return, or an exceptional halt). Each instruction on the way satisfies `S`, each call
it requests is answered by a precompile and satisfies `C`, and none requests a creation. Unlike
`WP` (`EvmLogic.Program.Logic`), it is universal over the outcomes of `exec`: an instruction
that fails (out of gas, stack overflow, invalid jump) needs no argument, so it holds for every
gas. It is inductive, so it also says the frame cannot run forever without a precompile call
outside the paths it describes: every path is finite.

A frame invariant `Own S C m` is kept by every instruction continuing the frame (`Own.next`) and
by every precompile call (`Own.call`), so it serves as the frame invariant of a relay in
`EvmLogic.Program.Nested.GuardInv`, where `S` gives the world invariant and `C` the issuance
predicate. The rules below (`Own.binOp`, `Own.push`, …) prove it by symbolic execution, one
instruction shape at a time, for any gas.
-/

namespace EvmLogic.Program.Nested
open EvmLean EvmLean.Interpreter

/-- **Every own path from `m` ends the frame safely** (see the module docstring). -/
inductive Own (S : Machine → Prop) (C : Machine → CallRequest → Prop) : Machine → Prop
  | intro {m : Machine} (hS : S m)
      (hnext : ∀ b m', m.frame.code[m.frame.pc]? = some b →
        (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.next, m') → Own S C m')
      (hcall : ∀ b req m', m.frame.code[m.frame.pc]? = some b →
        (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m') →
        precompileOf m'.precompiles req.msg ≠ none ∧ C m req)
      (hcallOwn : ∀ b req m', m.frame.code[m.frame.pc]? = some b →
        (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m') →
        Own S C (launchCall m' req))
      (hcreate : ∀ b msg m', m.frame.code[m.frame.pc]? = some b →
        (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.create msg, m') → False) :
      Own S C m

variable {S : Machine → Prop} {C : Machine → CallRequest → Prop} {m m' : Machine} {b : UInt8}

namespace Own

theorem safe (h : Own S C m) : S m := by cases h; assumption

theorem next (h : Own S C m) (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.next, m')) : Own S C m' := by
  cases h with | intro _ hn _ _ _ => exact hn b m' hb he

theorem call {req : CallRequest} (h : Own S C m) (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m')) :
    precompileOf m'.precompiles req.msg ≠ none ∧ C m req ∧ Own S C (launchCall m' req) := by
  cases h with | intro _ _ hc ho _ => exact ⟨(hc b req m' hb he).1, (hc b req m' hb he).2, ho b req m' hb he⟩

theorem create {msg : Message} (h : Own S C m) (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.create msg, m')) : False := by
  cases h with | intro _ _ _ _ hc => exact hc b msg m' hb he

/-! ## The generic rule -/

/-- What an instruction's outcome must satisfy. -/
def Cont (S : Machine → Prop) (C : Machine → CallRequest → Prop) (m : Machine) :
    Action → Machine → Prop
  | .next, m' => Own S C m'
  | .call req, m' => precompileOf m'.precompiles req.msg ≠ none ∧ C m req ∧
      Own S C (launchCall m' req)
  | .create _, _ => False
  | _, _ => True

/-- **The generic rule**: the instruction at `m` (byte `b`) satisfies `S`, and every successful
outcome continues as `Cont` says. -/
theorem of_wp (hb : m.frame.code[m.frame.pc]? = some b) (hS : S m)
    (h : Wp (exec (Opcode.decode m.ctx.fork b)) (Cont S C m) m) : Own S C m := by
  refine .intro hS ?_ ?_ ?_ ?_
  · intro b' m' hb' he
    rw [hb] at hb'; cases hb'
    exact h.of_run he
  · intro b' req m' hb' he
    rw [hb] at hb'; cases hb'
    exact ⟨(h.of_run he).1, (h.of_run he).2.1⟩
  · intro b' req m' hb' he
    rw [hb] at hb'; cases hb'
    exact (h.of_run he).2.2
  · intro b' msg m' hb' he
    rw [hb] at hb'; cases hb'
    exact h.of_run he

/-- Past the end of the code, the frame stops. -/
theorem of_end (hS : S m) (h : m.frame.code.size ≤ m.frame.pc) : Own S C m := by
  have hn : m.frame.code[m.frame.pc]? = none := by simp [getElem?_neg, Nat.not_lt.2 h]
  refine .intro hS ?_ ?_ ?_ ?_ <;> intros <;> simp_all

end Own

/-! ## The tracked state -/

/-- The constants of a frame: its message, context, precompiles and code. -/
structure Fix where
  msg : Message
  ctx : Context
  pre : PrecompileImpl
  code : ByteArray

/-- **What symbolic execution tracks** of a machine of the frame `k`: pc, stack, memory and
world (everything else is left unknown). -/
structure Fr (k : Fix) (m : Machine) (pc : Nat) (st : List Word) (mem : Memory) (w : World) :
    Prop where
  msg : m.frame.msg = k.msg
  ctx : m.ctx = k.ctx
  pre : m.precompiles = k.pre
  code : m.frame.code = k.code
  pc : m.frame.pc = pc
  stack : m.frame.stack = st
  mem : m.frame.memory = mem
  world : m.world = w

namespace Own

variable {k : Fix} {pc : Nat} {st : List Word} {mem : Memory} {w : World} {x y z : Word}
  {rest : List Word}

theorem byte (hF : Fr k m pc st mem w) (hb : k.code[pc]? = some b) :
    m.frame.code[m.frame.pc]? = some b := by
  rw [hF.code, hF.pc]; exact hb

theorem fork (hF : Fr k m pc st mem w) : m.ctx.fork = k.ctx.fork := by rw [hF.ctx]

/-! ## Rules: one per instruction shape -/

theorem binOp {cost : Nat} {f : Word → Word → Word}
    (hop : ∀ fk, exec (Opcode.decode fk b) = Interpreter.binOp cost f)
    (hF : Fr k m pc (x :: y :: rest) mem w) (hb : k.code[pc]? = some b) (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) (f x y :: rest) mem w → Own S C m') : Own S C m := by
  apply of_wp (byte hF hb) hS
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
    (h : ∀ m', Fr k m' (pc + 1) (f x :: rest) mem w → Own S C m') : Own S C m := by
  apply of_wp (byte hF hb) hS
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
    (h : ∀ m', Fr k m' (pc + 1) (a :: st) mem w → Own S C m') : Own S C m := by
  apply of_wp (byte hF hb) hS
  rw [hop]
  simp only [Interpreter.pushValue, wp_bind, wp_get, wp_push, wp_charge, wp_advance, wp_pure, Cont]
  intro _ _
  refine h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], ?_, hF.mem, hF.world⟩
  exact List.cons_eq_cons.2 ⟨hv _ hF.msg hF.ctx, hF.stack⟩

/-- An instruction pushing some value (`GAS`, `RETURNDATASIZE`). -/
theorem pushAny {cost : Nat} {v : Machine → Word}
    (hop : ∀ fk, exec (Opcode.decode fk b) = Interpreter.pushValue cost v)
    (hF : Fr k m pc st mem w) (hb : k.code[pc]? = some b) (hS : S m)
    (h : ∀ a m', Fr k m' (pc + 1) (a :: st) mem w → Own S C m') : Own S C m := by
  apply of_wp (byte hF hb) hS
  rw [hop]
  simp only [Interpreter.pushValue, wp_bind, wp_get, wp_push, wp_charge, wp_advance, wp_pure, Cont]
  intro _ _
  exact h _ _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], List.cons_eq_cons.2 ⟨rfl, hF.stack⟩,
    hF.mem, hF.world⟩

theorem push (n : Fin 33) {v : Word} (hF : Fr k m pc st mem w)
    (hb : k.code[pc]? = some (0x5f + n.val).toUInt8)
    (hv : Bytes.toWord (readBytes k.code (pc + 1) n.val) = v) (hS : S m)
    (h : ∀ m', Fr k m' (pc + (1 + n.val)) (v :: st) mem w → Own S C m') : Own S C m := by
  apply of_wp (byte hF hb) hS
  rw [decode_push]
  simp only [exec, wp_bind, wp_charge, wp_getFrame, wp_push, wp_advance, wp_pure, Cont]
  intro _ _
  refine h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], ?_, hF.mem, hF.world⟩
  rw [hF.code, hF.pc] at *
  exact List.cons_eq_cons.2 ⟨hv, hF.stack⟩

theorem dup (n : Fin 16) (hF : Fr k m pc st mem w)
    (hb : k.code[pc]? = some (0x80 + n.val).toUInt8) (hx : st[n.val]? = some x) (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) (x :: st) mem w → Own S C m') : Own S C m := by
  apply of_wp (byte hF hb) hS
  rw [decode_dup]
  simp only [exec, wp_bind, wp_charge, wp_getFrame, hF.stack, hx, wp_push, wp_advance, wp_pure,
    Cont]
  intro _ _
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], by simp, hF.mem, hF.world⟩

theorem swap (n : Fin 16) (hF : Fr k m pc (y :: rest) mem w)
    (hb : k.code[pc]? = some (0x90 + n.val).toUInt8) (hx : (y :: rest)[n.val + 1]? = some x)
    (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) (((y :: rest).set 0 x).set (n.val + 1) y) mem w → Own S C m') :
    Own S C m := by
  apply of_wp (byte hF hb) hS
  rw [decode_swap]
  simp only [exec, wp_bind, wp_charge, wp_getFrame, hF.stack, hx, wp_modifyFrame, wp_advance,
    wp_pure, Cont]
  intro _
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], rfl, hF.mem, hF.world⟩

theorem pop (hF : Fr k m pc (x :: rest) mem w) (hb : k.code[pc]? = some 0x50) (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) rest mem w → Own S C m') : Own S C m := by
  apply of_wp (byte hF hb) hS
  rw [show Opcode.decode m.ctx.fork 0x50 = .pop by cases m.ctx.fork <;> rfl]
  simp only [exec, wp_bind, wp_pop, wp_charge, wp_advance, wp_pure, Cont]
  intro x' xs hx _
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], rfl, hF.mem, hF.world⟩

theorem jumpdest (hF : Fr k m pc st mem w) (hb : k.code[pc]? = some 0x5b) (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) st mem w → Own S C m') : Own S C m := by
  apply of_wp (byte hF hb) hS
  rw [show Opcode.decode m.ctx.fork 0x5b = .jumpdest by cases m.ctx.fork <;> rfl]
  simp only [exec, wp_bind, wp_charge, wp_advance, wp_pure, Cont]
  intro _
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], hF.stack, hF.mem, hF.world⟩

/-- `JUMP`: whether or not the destination is valid, the frame continues there if at all. -/
theorem jump (hF : Fr k m pc (x :: rest) mem w) (hb : k.code[pc]? = some 0x56) (hS : S m)
    (h : ∀ m', Fr k m' x.toNat rest mem w → Own S C m') : Own S C m := by
  apply of_wp (byte hF hb) hS
  rw [show Opcode.decode m.ctx.fork 0x56 = .jump by cases m.ctx.fork <;> rfl]
  simp only [exec, wp_bind, wp_popNat, wp_charge, wp_getFrame, wp_ite, wp_throw, wp_modifyFrame,
    wp_pure, Cont]
  intro x' xs hx _
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  exact ⟨fun _ => trivial, fun _ => h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, rfl, rfl, hF.mem,
    hF.world⟩⟩

theorem jumpi (hF : Fr k m pc (x :: y :: rest) mem w) (hb : k.code[pc]? = some 0x57) (hS : S m)
    (h0 : y = 0 → ∀ m', Fr k m' (pc + 1) rest mem w → Own S C m')
    (h1 : y ≠ 0 → ∀ m', Fr k m' x.toNat rest mem w → Own S C m') : Own S C m := by
  apply of_wp (byte hF hb) hS
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
      Own S C m') : Own S C m := by
  apply of_wp (byte hF hb) hS
  rw [show Opcode.decode m.ctx.fork 0x35 = .calldataload by cases m.ctx.fork <;> rfl]
  simp only [exec, wp_bind, wp_popNat, wp_charge, wp_getFrame, wp_push, wp_advance, wp_pure, Cont]
  intro x' xs hx _ _
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], by simp [hF.msg], hF.mem, hF.world⟩

theorem mload (hF : Fr k m pc (x :: rest) mem w) (hb : k.code[pc]? = some 0x51) (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) ((mem.expand x.toNat 32).loadWord x.toNat :: rest)
      (mem.expand x.toNat 32) w → Own S C m') : Own S C m := by
  apply of_wp (byte hF hb) hS
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
      Own S C m') : Own S C m := by
  apply of_wp (byte hF hb) hS
  rw [show Opcode.decode m.ctx.fork 0x52 = .mstore by cases m.ctx.fork <;> rfl]
  simp only [exec, memoryExpansion, expandMemory, List.foldl, wp_bind, wp_popNat, wp_pop,
    wp_getFrame, wp_charge, wp_modifyFrame, wp_advance, wp_pure, Cont]
  intro x' xs hx y' ys hy _
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hy
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], rfl, by simp [hF.mem], hF.world⟩

theorem sload (hF : Fr k m pc (x :: rest) mem w) (hb : k.code[pc]? = some 0x54) (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) (w.sload k.msg.currentTarget x :: rest) mem w → Own S C m') :
    Own S C m := by
  apply of_wp (byte hF hb) hS
  rw [show Opcode.decode m.ctx.fork 0x54 = .sload by cases m.ctx.fork <;> rfl]
  simp only [exec, accessStorageKey, wp_bind, wp_pop, wp_getFrame, wp_get, wp_charge, wp_push,
    wp_advance, wp_pure, Cont]
  intro x' xs hx
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  split <;> simp only [wp_bind, wp_pure, wp_modifySub] <;> intro _ _ <;>
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], by simp [hF.msg, hF.world], hF.mem,
    hF.world⟩

theorem sstore (hF : Fr k m pc (x :: y :: rest) mem w) (hb : k.code[pc]? = some 0x55)
    (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) rest mem (w.sstore k.msg.currentTarget x y) → Own S C m') :
    Own S C m := by
  apply of_wp (byte hF hb) hS
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
      m'.world = m.world.sstore m.frame.msg.currentTarget x y → Own S C m' := by
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
        rest) (mem.expand x.toNat y.toNat) w → Own S C m') : Own S C m := by
  apply of_wp (byte hF hb) hS
  rw [show Opcode.decode m.ctx.fork 0x20 = .keccak256 by cases m.ctx.fork <;> rfl]
  simp only [exec, memoryExpansion, expandMemory, readMemory, List.foldl, wp_bind, wp_popNat,
    wp_getFrame, wp_get, wp_charge, wp_modifyFrame, wp_push, wp_advance, wp_pure, Cont]
  intro x' xs hx y' ys hy _ _
  rw [hF.stack] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hy
  exact h _ ⟨hF.msg, hF.ctx, hF.pre, hF.code, by simp [hF.pc], by simp [hF.mem, hF.ctx],
    by simp [hF.mem], hF.world⟩

/-- Memory after copying `len` bytes `d` to `off` (expanded; empty copies write nothing). -/
def copyIn (mem : Memory) (off len : Nat) (d : ByteArray) : Memory :=
  if len = 0 then mem.expand off len else (mem.expand off len).write off d

theorem read_copyIn_of_disjoint (mem : Memory) (off len off' len' : Nat) (d : ByteArray)
    (hd : d.size = len) (h : off' + len' ≤ off ∨ off + len ≤ off') :
    (copyIn mem off len d).read off' len' = mem.read off' len' := by
  unfold copyIn
  split
  · exact Memory.read_expand _ _ _ _ _
  · rw [Memory.read_write_of_disjoint _ _ _ _ _ (by rw [hd]; exact h), Memory.read_expand]

theorem loadWord_copyIn_of_disjoint (mem : Memory) (off len off' : Nat) (d : ByteArray)
    (hd : d.size = len) (h : off' + 32 ≤ off ∨ off + len ≤ off') :
    (copyIn mem off len d).loadWord off' = mem.loadWord off' := by
  rw [Memory.loadWord, Memory.loadWord, read_copyIn_of_disjoint _ _ _ _ _ _ hd h]

theorem loadWord_copyIn_readBytes (mem : Memory) (off len off' o : Nat) (b : ByteArray)
    (h : off' + 32 ≤ off ∨ off + len ≤ off') :
    (copyIn mem off len (readBytes b o len)).loadWord off' = mem.loadWord off' :=
  loadWord_copyIn_of_disjoint _ _ _ _ _ (size_readBytes _ _ _) h

/-- `CALLDATACOPY`. -/
theorem calldatacopy (hF : Fr k m pc (x :: y :: z :: rest) mem w)
    (hb : k.code[pc]? = some 0x37) (hS : S m)
    (h : ∀ m', Fr k m' (pc + 1) rest
      (copyIn mem x.toNat z.toNat (readBytes k.msg.data y.toNat z.toNat)) w → Own S C m') :
    Own S C m := by
  apply of_wp (byte hF hb) hS
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
    show _ = copyIn _ _ _ _
    rw [copyIn, ite_eq_left h0, hF.mem]
  · rw [hF.msg, hsz] at h0
    show _ = copyIn _ _ _ _
    rw [copyIn, ite_eq_right h0, hF.mem, hF.msg]

/-- `RETURNDATACOPY`: the memory afterwards is left unknown. -/
theorem returndatacopy (hF : Fr k m pc (x :: y :: z :: rest) mem w)
    (hb : k.code[pc]? = some 0x3e) (hS : S m)
    (h : ∀ mem' m', Fr k m' (pc + 1) rest mem' w → Own S C m') : Own S C m := by
  apply of_wp (byte hF hb) hS
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

theorem decode_halts (fk : Fork) : Opcode.decode fk 0xf3 = .«return» ∧
    Opcode.decode fk 0xfd = .revert ∧ Opcode.decode fk 0x00 = .stop ∧
    Opcode.decode fk 0xfe = .invalid := by
  cases fk <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- `RETURN`, `REVERT`: the frame ends. -/
theorem halt (hF : Fr k m pc st mem w) (hb : k.code[pc]? = some b)
    (hop : Opcode.decode k.ctx.fork b = .«return» ∨ Opcode.decode k.ctx.fork b = .revert ∨
      Opcode.decode k.ctx.fork b = .stop ∨ Opcode.decode k.ctx.fork b = .invalid)
    (hS : S m) : Own S C m := by
  apply of_wp (byte hF hb) hS
  rw [fork hF]
  rcases hop with h | h | h | h <;> rw [h] <;>
    simp [exec, readOutput, memoryExpansion, expandMemory, readMemory, Cont]

/-- What a successful `STATICCALL` does to the frame, before any child runs: the world is
unchanged, the memory is expanded, and either the depth limit makes it push `0` and continue,
or it requests a static call of `to` with the memory's input and no value. -/
def StaticPost (m : Machine) (toW inOff inSize outOff outSize : Word) (rest : List Word) :
    Action → Machine → Prop := fun a m' =>
  m'.world = m.world ∧ m'.frame.msg = m.frame.msg ∧ m'.ctx = m.ctx ∧
    m'.precompiles = m.precompiles ∧ m'.frame.code = m.frame.code ∧
    m'.frame.memory = (m.frame.memory.expand inOff.toNat inSize.toNat).expand outOff.toNat
      outSize.toNat ∧
    ((a = .next ∧ m'.frame.stack = 0 :: rest ∧ m'.frame.pc = m.frame.pc + 1) ∨
     (∃ req, a = .call req ∧ m'.frame.stack = rest ∧ m'.frame.pc = m.frame.pc ∧
      req.msg.currentTarget = Word.toAddress toW ∧
      req.msg.codeAddress = some (Word.toAddress toW) ∧ req.msg.disablePrecompiles = false ∧
      req.msg.value = 0 ∧
      req.msg.data = readBytes ((m.frame.memory.expand inOff.toNat inSize.toNat).expand
        outOff.toNat outSize.toNat).bytes inOff.toNat inSize.toNat ∧
      req.retOffset = outOff.toNat ∧ req.retSize = outSize.toNat))

theorem exec_staticcall {g toW inOff inSize outOff outSize : Word}
    (hs : m.frame.stack = g :: toW :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none) :
    Wp (exec .staticcall) (StaticPost m toW inOff inSize outOff outSize rest) m := by
  simp only [exec, execCall, genericCall, memoryExpansion, expandMemory, readMemory,
    accessAddress, accessDelegation, setReturnData, List.foldl, wp_bind, wp_popNat, wp_popAddress,
    wp_getFrame, wp_get, wp_charge, wp_modifyFrame, wp_modifySub, wp_ite, wp_throw, wp_advance,
    wp_push, wp_refundGas, wp_pure, hs, List.cons.injEq, and_imp, forall_apply_eq_imp_iff,
    forall_eq', decide_false, Bool.false_and, Bool.false_eq_true, reduceCtorEq,
    not_false_eq_true, true_implies, implies_true]
  rcases hdel with hf | hd
  · simp [hf, StaticPost]
  · by_cases hf : m.ctx.fork < .prague
    · simp [hf, StaticPost]
    · simp [hf, hd, StaticPost]

/-- **`STATICCALL` of a precompile** (standard precompiles, not disabled by a delegation): the
frame continues at once with `0`, or with `1` and the precompile's output written back; the
world is unchanged. -/
theorem staticcallPre {g toW inOff inSize outOff outSize : Word}
    (hF : Fr k m pc (g :: toW :: inOff :: inSize :: outOff :: outSize :: rest) mem w)
    (hb : k.code[pc]? = some 0xfa) (hS : S m)
    (hpre : k.pre.isPrecompile (Word.toAddress toW) = true)
    (hdel : k.ctx.fork < .prague ∨ delegatedAddress? (w.code (Word.toAddress toW)) = none)
    (hC : ∀ req : CallRequest, req.msg.currentTarget = Word.toAddress toW → C m req)
    (h : ∀ m' res mem', Fr k m' (pc + 1) (res :: rest) mem' w →
      (res ≠ 0 → ∃ gas' : Nat,
        (k.pre.run (Word.toAddress toW) (readBytes ((mem.expand inOff.toNat inSize.toNat).expand
          outOff.toNat outSize.toNat).bytes inOff.toNat inSize.toNat) gas').success = true ∧
        mem' = EvmLogic.Program.returnMemory ((mem.expand inOff.toNat inSize.toNat).expand outOff.toNat outSize.toNat)
          outOff.toNat outSize.toNat (k.pre.run (Word.toAddress toW) (readBytes ((mem.expand
            inOff.toNat inSize.toNat).expand outOff.toNat outSize.toNat).bytes inOff.toNat
            inSize.toNat) gas').output) → Own S C m') :
    Own S C m := by
  have hdec : Opcode.decode m.ctx.fork 0xfa = .staticcall := by cases m.ctx.fork <;> rfl
  have hdel' : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none :=
    by rw [fork hF, hF.world]; exact hdel
  have hpost := exec_staticcall hF.stack hdel'
  have hb' := byte hF hb
  refine .intro hS ?_ ?_ ?_ ?_
  · intro b' m' hb'' he
    rw [hb'] at hb''; cases hb''
    rw [hdec] at he
    obtain ⟨hw, hmsg, hctx, hpr, hcode, hmem, hcase⟩ := hpost.of_run he
    rcases hcase with ⟨-, hst, hpc⟩ | ⟨req, hreq, -⟩
    · refine h m' 0 _ ⟨hmsg.trans hF.msg, hctx.trans hF.ctx, hpr.trans hF.pre,
        hcode.trans hF.code, by rw [hpc, hF.pc], hst, by rw [hmem, hF.mem], hw.trans hF.world⟩
        (fun h0 => absurd rfl h0)
    · cases hreq
  · intro b' req m' hb'' he
    rw [hb'] at hb''; cases hb''
    rw [hdec] at he
    obtain ⟨hw, hmsg, hctx, hpr, hcode, hmem, hcase⟩ := hpost.of_run he
    rcases hcase with ⟨hreq, -⟩ | ⟨req', hreq, hst, hpc, htgt, hca, hdis, -⟩
    · cases hreq
    · cases hreq
      refine ⟨?_, hC _ htgt⟩
      simp [precompileOf, hdis, hca, hpr, hF.pre, hpre]
  · intro b' req m' hb'' he
    rw [hb'] at hb''; cases hb''
    rw [hdec] at he
    obtain ⟨hw, hmsg, hctx, hpr, hcode, hmem, hcase⟩ := hpost.of_run he
    rcases hcase with ⟨hreq, -⟩ | ⟨req', hreq, hst, hpc, htgt, hca, hdis, hval, hdata, hro, hrs⟩
    · cases hreq
    · cases hreq
      have hpc' : precompileOf m'.precompiles req.msg = some (Word.toAddress toW) := by
        simp [precompileOf, hdis, hca, hpr, hF.pre, hpre]
      have htv : transferValue m'.world req.msg = m'.world := transferValue_zero _ _ hval
      simp only [launchCall, hpc', runPrecompile, htv]
      have hpr' : m'.precompiles = k.pre := hpr.trans hF.pre
      have hdata' : req.msg.data = readBytes ((mem.expand inOff.toNat inSize.toNat).expand
          outOff.toNat outSize.toNat).bytes inOff.toNat inSize.toNat := by rw [hdata, hF.mem]
      rw [hpr', hdata']
      split
      · rename_i hsucc
        refine h _ 1 _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ (fun _ => ⟨req.msg.gas, hsucc, rfl⟩) <;>
          simp [resume, ChildResult.success, EvmLogic.Program.returnMemory, hmsg, hF.msg, hctx, hF.ctx, hcode, hF.code, hpc, hF.pc, hst, hmem, hF.mem, hro, hrs, hw, hF.world]
      · refine h _ 0 _ ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩ (fun h0 => absurd rfl h0) <;>
          simp [resume, ChildResult.success, hmsg, hF.msg, hctx, hF.ctx, hcode, hF.code, hpc, hF.pc, hst, hw, hF.world]
  · intro b' msg m' hb'' he
    rw [hb'] at hb''; cases hb''
    rw [hdec] at he
    obtain ⟨-, -, -, -, -, -, hcase⟩ := hpost.of_run he
    rcases hcase with ⟨hreq, -⟩ | ⟨req', hreq, -⟩ <;> cases hreq

/-! ## Writing only allowed storage keys -/

/-- The instruction at `m`, if an `SSTORE`, writes a key satisfying `K`. -/
def SstoreOk (K : Word → Prop) (m : Machine) : Prop :=
  ∀ x rest, m.frame.code[m.frame.pc]? = some 0x55 → m.frame.stack = x :: rest → K x

theorem sstoreOk_of_ne {K : Word → Prop} (hF : Fr k m pc st mem w) (hb : k.code[pc]? = some b)
    (hne : b ≠ 0x55) : SstoreOk K m := by
  intro x rest h _
  rw [byte hF hb] at h
  exact absurd (Option.some.inj h) hne

theorem sstoreOk_of_key {K : Word → Prop} (hF : Fr k m pc (x :: rest) mem w) (hK : K x) :
    SstoreOk K m := by
  intro x' rest' _ hs
  rw [hF.stack] at hs
  cases hs
  exact hK

end Own

end EvmLogic.Program.Nested