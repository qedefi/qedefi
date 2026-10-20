import EvmLogic.Program.Call

/-!
# The callee-summary rule for a value-free `CALL`

`WP.callNoValue` is `WP.staticcall` (`EvmLeanProofs.Program.Call`) for `CALL` with value `0`,
the shape of every ERC-20 call a contract makes (`token.call(abi.encodeCall(transfer, …))`,
Solmate's `SafeTransferLib`): no value moves (`transferValue` is the identity), no
value-transfer or account-creation cost is charged, and the child frame is non-static iff the
caller's is. The child message is `childMsg … 0 … true false …` and the caller resumes from
`resumeAfter (callerFrame …)` after every end of the child that its summary allows.
-/

namespace EvmLean.Program

open Interpreter

variable {m : Machine} {gas toW inOff inSize outOff outSize : Word} {rest : List Word}

/-- A `CALL` without value: the account-creation cost is zero. -/
theorem createCost_zero (w : World) (a : Address) : createCost w 0 a = 0 := by
  simp [createCost]

/-- A `CALL` without value: the value-transfer cost is zero. -/
theorem transferCost_zero : transferCost 0 = 0 := by
  simp [transferCost]

/-- No value moves for a child message of value `0`. -/
theorem transferValue_childMsg_zero (m : Machine) (caller to : Address) (g : Nat)
    (isStatic : Bool) (inOff inSize outOff outSize : Word) :
    transferValue m.world (childMsg m caller to to 0 g true isStatic inOff inSize outOff outSize) =
      m.world := by
  simp [transferValue, childMsg]

/-- **`CALL` without value to a non-precompile pushes the child frame** (`step_call` with
`value = 0`). -/
theorem step_callNoValue (hcode : m.frame.code[m.frame.pc]? = some 0xf1)
    (hstk : m.frame.stack = gas :: toW :: 0 :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize ≤ m.frame.gasLeft)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = false) :
    step m = .running { m with
      frame := Frame.init
        (childMsg m m.frame.msg.currentTarget (Word.toAddress toW) (Word.toAddress toW) 0
          (callGas m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize).subCall true false
          inOff inSize outOff outSize)
        (.call outOff.toNat outSize.toNat) (m.world, m.transient)
      parents := callerFrame m rest (callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff
        outSize) (Word.toAddress toW) inOff inSize outOff outSize :: m.parents } := by
  have h := step_call (value := 0) hcode hstk hdel
    (by rw [createCost_zero, transferCost_zero]; exact hgas) (.inr rfl) (Nat.zero_le _) hdepth hpre
  rw [createCost_zero, transferCost_zero, transferValue_childMsg_zero] at h
  exact h

/-- **Callee-summary rule for a `CALL` without value** (see `step_callNoValue`, `WP.call`):
`Hc` is what the callee's frame, started fresh on the child message, is known to do. -/
theorem WP.callNoValue {Q : Machine → Prop} {H Hc : Machine → Outcome → Prop}
    (hcode : m.frame.code[m.frame.pc]? = some 0xf1)
    (hstk : m.frame.stack = gas :: toW :: 0 :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize ≤ m.frame.gasLeft)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = false)
    (hcallee : Halts { m with
      frame := Frame.init
        (childMsg m m.frame.msg.currentTarget (Word.toAddress toW) (Word.toAddress toW) 0
          (callGas m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize).subCall true false
          inOff inSize outOff outSize)
        (.call outOff.toNat outSize.toNat) (m.world, m.transient)
      parents := callerFrame m rest (callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff
        outSize) (Word.toAddress toW) inOff inSize outOff outSize :: m.parents } Hc)
    (k : ∀ mf o, Hc mf o → SameFrame { m with
      frame := Frame.init
        (childMsg m m.frame.msg.currentTarget (Word.toAddress toW) (Word.toAddress toW) 0
          (callGas m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize).subCall true false
          inOff inSize outOff outSize)
        (.call outOff.toNat outSize.toNat) (m.world, m.transient)
      parents := callerFrame m rest (callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff
        outSize) (Word.toAddress toW) inOff inSize outOff outSize :: m.parents } mf →
      WP (resumeAfter (callerFrame m rest (callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize
        outOff outSize) (Word.toAddress toW) inOff inSize outOff outSize) m.parents mf o) Q H) :
    WP m Q H :=
  WP.call (step_callNoValue hcode hstk hdel hgas hdepth hpre) rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hcallee
    (fun mf o hs hc => k mf o hc hs)

/-- Copying a child's output into a one-word output window at `0` (Solmate's `SafeTransferLib`
calls) changes neither the size of a memory of at least one word nor the word at `64` (the
free-memory pointer). -/
theorem returnMemory_zero_word (mem : Memory) (out : ByteArray) (h : 32 ≤ mem.size) :
    (returnMemory mem 0 32 out).loadWord 64 = mem.loadWord 64 ∧
      (returnMemory mem 0 32 out).size = mem.size := by
  unfold returnMemory
  split
  · exact ⟨rfl, rfl⟩
  · have hd : (out.extract 0 (min 32 out.size)).size ≤ 32 := by
      simp only [ByteArray.size_extract]; omega
    have hc : 32 * Memory.wordsAfter mem.words 0 (out.extract 0 (min 32 out.size)).size ≤
        mem.size := by
      unfold Memory.wordsAfter Memory.words
      have h1 : 1 ≤ mem.size / 32 := (Nat.le_div_iff_mul_le (by decide)).2 (by omega)
      have h2 : (0 + (out.extract 0 (min 32 out.size)).size + 31) / 32 < 2 :=
        (Nat.div_lt_iff_lt_mul (by decide)).2 (by omega)
      have h3 := Nat.mul_div_le mem.size 32
      split
      · omega
      · rw [Nat.max_eq_left (by omega)]; omega
    have he : mem.expand 0 (out.extract 0 (min 32 out.size)).size = mem := by
      simp only [Memory.expand, hc, ↓reduceIte]
    constructor
    · rw [Memory.loadWord, Memory.loadWord,
        Memory.read_write_of_disjoint _ _ _ _ _ (.inr (by omega))]
    · rw [Memory.size_write, he]

/-- `returnMemory_zero_word` for a memory named by an equation (as `generalize` leaves it). -/
theorem returnMemory_zero_word_eq {mem M : Memory} {out : ByteArray}
    (hM : returnMemory mem 0 32 out = M) (h : 32 ≤ mem.size) :
    M.loadWord 64 = mem.loadWord 64 ∧ M.size = mem.size :=
  hM ▸ returnMemory_zero_word mem out h

end EvmLean.Program
