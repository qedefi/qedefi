import EvmLeanProofs.Program.Call

/-!
# `CALL` without value: the callee-summary rule

`WP.call0` is `WP.staticcall` (`EvmLeanProofs.Program.Call`) for a `CALL` that sends no value,
as Solmate's `SafeTransferLib.safeTransferFrom` / `safeTransfer` do (`call(gas(), token, 0, …)`):
with value `0` there is no value transfer (`transferValue` is the identity), no
account-creation or value-transfer charge, no balance or static-context requirement, and the
child message is non-static exactly when the caller's is.

* `transferValue_zero`, `createCost_zero`, `transferCost_zero`: the value-dependent parts of
  `step_call` at value `0`.
* `step_call0`: `step_call` at value `0`.
* `WP.call0`: if the child frame, started fresh on the child message, `Halts` with `Hc`
  (typically a callee summary such as an ERC-20 `transferFrom` of the callee's code), the
  caller continues from `resumeAfter` of every outcome `Hc` allows.
-/

namespace EvmLean.Program

open Interpreter

/-- With value `0` the world is unchanged when the child starts. -/
theorem transferValue_zero (w : World) (msg : Message) (h : msg.value = 0) :
    transferValue w msg = w := by
  simp [transferValue, h]

/-- No account-creation charge without value. -/
theorem createCost_zero (w : World) (to : Address) : createCost w 0 to = 0 := by
  simp [createCost]

/-- No value-transfer charge without value. -/
theorem transferCost_zero : transferCost 0 = 0 := by
  simp [transferCost]

variable {m : Machine} {gas toW inOff inSize outOff outSize : Word} {rest : List Word}

/-- The child machine of a `CALL` without value (see `step_call`). -/
abbrev call0Child (m : Machine) (gas toW inOff inSize outOff outSize : Word)
    (rest : List Word) : Machine :=
  { m with
    frame := Frame.init
      (childMsg m m.frame.msg.currentTarget (Word.toAddress toW) (Word.toAddress toW) 0
        (callGas m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize).subCall true false
        inOff inSize outOff outSize)
      (.call outOff.toNat outSize.toNat) (m.world, m.transient)
    parents := callerFrame m rest (callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff
      outSize) (Word.toAddress toW) inOff inSize outOff outSize :: m.parents }

/-- The suspended caller frame of a `CALL` without value. -/
abbrev call0Caller (m : Machine) (gas toW inOff inSize outOff outSize : Word)
    (rest : List Word) : Frame :=
  callerFrame m rest (callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize)
    (Word.toAddress toW) inOff inSize outOff outSize

/-- **`CALL` without value to a non-precompile pushes the child frame**, on the unchanged
world. -/
theorem step_call0 (hcode : m.frame.code[m.frame.pc]? = some 0xf1)
    (hstk : m.frame.stack = gas :: toW :: 0 :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize ≤
      m.frame.gasLeft)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = false) :
    step m = .running (call0Child m gas toW inOff inSize outOff outSize rest) := by
  have h := step_call (value := 0) hcode hstk hdel
    (by rw [createCost_zero, transferCost_zero]; exact hgas) (.inr rfl) (by simp) hdepth hpre
  rw [createCost_zero, transferCost_zero, transferValue_zero _ _ rfl] at h
  exact h

/-- **Callee-summary rule for `CALL` without value** (see `step_call0`, `WP.call`): `Hc` is
what the callee's frame, started fresh on the child message, is known to do. -/
theorem WP.call0 {Q : Machine → Prop} {H Hc : Machine → Outcome → Prop}
    (hcode : m.frame.code[m.frame.pc]? = some 0xf1)
    (hstk : m.frame.stack = gas :: toW :: 0 :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize ≤
      m.frame.gasLeft)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = false)
    (hcallee : Halts (call0Child m gas toW inOff inSize outOff outSize rest) Hc)
    (k : ∀ mf o, Hc mf o → SameFrame (call0Child m gas toW inOff inSize outOff outSize rest) mf →
      WP (resumeAfter (call0Caller m gas toW inOff inSize outOff outSize rest) m.parents mf o)
        Q H) :
    WP m Q H :=
  WP.call (step_call0 hcode hstk hdel hgas hdepth hpre) rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hcallee
    (fun mf o hs hc => k mf o hc hs)

/-! ## Unknown return data in a one-word output window at `0`

After a failed call with output window `[0, 32)` the caller's memory is
`returnMemory (mem.expand 0 32) 0 32 out` for unknown revert data `out`: only the scratch word
at `0` is unknown; the size and every word from offset `32` on are those of `mem.expand 0 32`.
-/

/-- Writing at most 32 bytes at `0` into memory of at least one word does not grow it. -/
theorem size_returnMemory_zero (mem : Memory) (out : ByteArray) :
    (returnMemory (mem.expand 0 32) 0 32 out).size = (mem.expand 0 32).size := by
  unfold returnMemory
  split
  · rfl
  · rw [Memory.size_write, Memory.size_expand]
    have h32 : 32 ≤ (mem.expand 0 32).size := by
      rw [Memory.size_expand]
      simp only [Memory.wordsAfter, Memory.words, Nat.reduceEqDiff, ↓reduceIte]
      omega
    have hn : (out.extract 0 (min 32 out.size)).size ≤ 32 := by
      simp only [ByteArray.size_extract]; omega
    simp only [Memory.wordsAfter, Memory.words]
    split <;> omega

/-- Words from offset `32` on are unaffected by the copied return data. -/
theorem loadWord_returnMemory_zero (mem : Memory) (out : ByteArray) {off : Nat} (h : 32 ≤ off) :
    (returnMemory (mem.expand 0 32) 0 32 out).loadWord off = (mem.expand 0 32).loadWord off := by
  unfold returnMemory
  split
  · rfl
  · have hn : (out.extract 0 (min 32 out.size)).size ≤ 32 := by
      simp only [ByteArray.size_extract]; omega
    rw [Memory.loadWord, Memory.loadWord, Memory.read_write_of_disjoint _ _ _ _ _ (.inr (by omega))]

/-- `size_returnMemory_zero` and `loadWord_returnMemory_zero` for a name `M` of the memory
(after `generalize`). -/
theorem returnMemory_zero_facts {mem M : Memory} {out : ByteArray}
    (h : returnMemory (mem.expand 0 32) 0 32 out = M) :
    M.size = (mem.expand 0 32).size ∧
      ∀ off, 32 ≤ off → M.loadWord off = (mem.expand 0 32).loadWord off :=
  h ▸ ⟨size_returnMemory_zero mem out, fun _ h => loadWord_returnMemory_zero mem out h⟩

end EvmLean.Program
