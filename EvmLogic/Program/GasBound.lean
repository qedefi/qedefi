import EvmLogic.Program.Nested.Step

/-!
# A frame never ends with more gas than it started with

`Halts m H` says nothing about the gas the frame hands back, so after a call the caller's gas
`p.gasLeft + mf.frame.gasLeft` had no upper bound. Semantically there is one: every step keeps
the total gas of the frame stack from growing (`Nested.stepN_gas`), provided the machine's
precompiles return at most the gas they are given (`Nested.PrecompilesOk`, true of the standard
ones: `Nested.precompilesOk_standard`). Refunds do not interfere: they accrue in the substate
(`refundCounter`) and are paid at the end of the transaction, never into `gasLeft`.

* `returnedGas mf o`: the gas a finished frame hands to its parent (`mf.frame.gasLeft` after a
  `RETURN`/`STOP`/`REVERT` of a call frame, `0` after an exceptional halt);
* `Halts.gas_le`: every `Halts m H` also ends with `returnedGas mf o ≤ m.frame.gasLeft`;
* `WP.call_gas_le`, `WP.call0_gas`, `WP.staticcall_gas`, `WP.delegatecall_gas`: the callee-summary
  rules whose continuation also gets that the caller resumes with **at most the gas it had before
  the call** (`resumeAfter_gasLeft`, `gasLeft_resumeAfter_le`).
-/

namespace EvmLogic.Program
open EvmLean EvmLean.Interpreter
open Nested (PrecompilesOk gasSum resultGas)

/-- The gas a frame ended at `mf` with outcome `o` hands back to its parent (or to the
transaction): the frame's gas after `RETURN`/`STOP`/`REVERT` of a call, the gas after the code
deposit of a creation, `0` after an exceptional halt. -/
def returnedGas (mf : Machine) (o : Outcome) : Nat := (frameResult mf o).1.gasLeft

@[simp] theorem returnedGas_success_call {mf : Machine} {out : ByteArray} {a b : Nat}
    (hk : mf.frame.kind = .call a b) : returnedGas mf (.success out) = mf.frame.gasLeft := by
  simp [returnedGas, frameResult, hk]

@[simp] theorem returnedGas_revert (mf : Machine) (out : ByteArray) :
    returnedGas mf (.revert out) = mf.frame.gasLeft := rfl

@[simp] theorem returnedGas_halt (mf : Machine) (e : ExceptionalHalt) :
    returnedGas mf (.halt e) = 0 := rfl

/-- The caller's gas after the child of `mf` ended: what it kept plus what the child returned. -/
theorem resumeAfter_gasLeft (p : Frame) (ps : List Frame) (mf : Machine) (o : Outcome) :
    (resumeAfter p ps mf o).frame.gasLeft = p.gasLeft + returnedGas mf o := rfl

/-- The gas of a finished frame's step result: what it hands back plus the gas of its parents. -/
theorem resultGas_finishFrame (mf : Machine) (o : Outcome) :
    resultGas (finishFrame mf o) = returnedGas mf o + (mf.parents.map Frame.gasLeft).sum := by
  rw [finishFrame_eq]
  cases hp : mf.parents with
  | nil =>
    simp only [resultGas, List.map_nil, List.sum_nil, Nat.add_zero, returnedGas]
    unfold topLevelResult
    split <;> rfl
  | cons p ps =>
    simp only [resultGas, gasSum, resumeAfter_gasLeft, List.map_cons, List.sum_cons]
    simp only [resumeAfter, Nested.resume_parents]
    omega

/-- **A frame never ends with more gas than it started with**: the gas it hands back is at most
its gas at `m` (for machines whose precompiles do not create gas). -/
theorem Halts.gas_le {m : Machine} {H : Machine → Outcome → Prop}
    (hpre : PrecompilesOk m.precompiles) (h : Halts m H) :
    Halts m (fun mf o => H mf o ∧ returnedGas mf o ≤ m.frame.gasLeft) := by
  obtain ⟨n, mf, o, hn, hs, hH⟩ := h
  refine ⟨n, mf, o, hn, hs, hH, ?_⟩
  have hg := Nested.stepN_gas hpre n
  rw [hn, resultGas_finishFrame, hs.parents] at hg
  simp only [gasSum] at hg
  omega

/-- `Halts.gas_le` for a frame that ends by `RETURN`/`STOP`/`REVERT` of a call: its final gas. -/
theorem Halts.gasLeft_le {m : Machine} {H : Machine → Outcome → Prop}
    (hpre : PrecompilesOk m.precompiles) (h : Halts m H) {a b : Nat}
    (hk : m.frame.kind = .call a b) :
    Halts m (fun mf o => H mf o ∧ ((∃ out, o = .success out ∨ o = .revert out) →
      mf.frame.gasLeft ≤ m.frame.gasLeft)) := by
  refine (h.gas_le hpre).mono fun mf o hs ⟨hH, hg⟩ => ⟨hH, ?_⟩
  rintro ⟨out, rfl | rfl⟩
  · rwa [returnedGas_success_call (hs.kind.trans hk)] at hg
  · exact hg

/-- The caller's gas after a call is at most its gas before: what it kept plus what the child
started with is at most what it had (`step_gas`), and the child hands back at most what it
started with (`Halts.gas_le`). -/
theorem gasLeft_resumeAfter_le {m mc mf : Machine} {p : Frame} {o : Outcome}
    (hpre : PrecompilesOk m.precompiles) (hstep : step m = .running mc)
    (hpar : mc.parents = p :: m.parents) (hret : returnedGas mf o ≤ mc.frame.gasLeft) :
    (resumeAfter p m.parents mf o).frame.gasLeft ≤ m.frame.gasLeft := by
  have hg := Nested.step_gas hpre
  rw [hstep] at hg
  simp only [resultGas, gasSum, hpar, List.map_cons, List.sum_cons] at hg
  rw [resumeAfter_gasLeft]
  omega

/-- **Callee-summary rule with the gas bound**: `WP.call`, and the continuation also knows that
the caller resumes with at most the gas it had before the call. -/
theorem WP.call_gas_le {m mc : Machine} {p : Frame} {Q : Machine → Prop}
    {H Hc : Machine → Outcome → Prop} (hprec : PrecompilesOk m.precompiles)
    (hstep : step m = .running mc) (hpar : mc.parents = p :: m.parents)
    (hp : SameFrame m { mc with frame := p, parents := m.parents })
    (hcallee : Halts mc Hc)
    (k : ∀ mf o, SameFrame mc mf → Hc mf o →
      (resumeAfter p m.parents mf o).frame.gasLeft ≤ m.frame.gasLeft →
      WP (resumeAfter p m.parents mf o) Q H) :
    WP m Q H := by
  have hpc : PrecompilesOk mc.precompiles := by
    have : mc.precompiles = m.precompiles := hp.precompiles
    rw [this]; exact hprec
  exact WP.call hstep hpar hp (hcallee.gas_le hpc) fun mf o hs ⟨hc, hg⟩ =>
    k mf o hs hc (gasLeft_resumeAfter_le hprec hstep hpar hg)

variable {m : Machine} {gas toW inOff inSize outOff outSize : Word} {rest : List Word}

/-- `WP.call0` with the gas bound: the caller resumes with at most the gas it had. -/
theorem WP.call0_gas {Q : Machine → Prop} {H Hc : Machine → Outcome → Prop}
    (hprec : PrecompilesOk m.precompiles)
    (hcode : m.frame.code[m.frame.pc]? = some 0xf1)
    (hstk : m.frame.stack = gas :: toW :: 0 :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize ≤
      m.frame.gasLeft)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = false)
    (hcallee : Halts (call0Child m gas toW inOff inSize outOff outSize rest) Hc)
    (k : ∀ mf o, Hc mf o → SameFrame (call0Child m gas toW inOff inSize outOff outSize rest) mf →
      (resumeAfter (call0Caller m gas toW inOff inSize outOff outSize rest) m.parents mf o
        ).frame.gasLeft ≤ m.frame.gasLeft →
      WP (resumeAfter (call0Caller m gas toW inOff inSize outOff outSize rest) m.parents mf o)
        Q H) :
    WP m Q H :=
  WP.call_gas_le hprec (step_call0 hcode hstk hdel hgas hdepth hpre) rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hcallee
    (fun mf o hs hc hg => k mf o hc hs hg)

/-- `WP.delegatecall` with the gas bound: the caller resumes with at most the gas it had. -/
theorem WP.delegatecall_gas {Q : Machine → Prop} {H Hc : Machine → Outcome → Prop}
    (hprec : PrecompilesOk m.precompiles)
    (hcode : m.frame.code[m.frame.pc]? = some 0xf4)
    (hstk : m.frame.stack = gas :: toW :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize ≤
      m.frame.gasLeft)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = false)
    (hcallee : Halts (delegateChild m gas toW inOff inSize outOff outSize rest) Hc)
    (k : ∀ mf o, Hc mf o → SameFrame (delegateChild m gas toW inOff inSize outOff outSize rest) mf →
      (resumeAfter (delegateCaller m gas toW inOff inSize outOff outSize rest) m.parents mf o
        ).frame.gasLeft ≤ m.frame.gasLeft →
      WP (resumeAfter (delegateCaller m gas toW inOff inSize outOff outSize rest) m.parents mf o)
        Q H) :
    WP m Q H :=
  WP.call_gas_le hprec (step_delegatecall hcode hstk hdel hgas hdepth hpre) rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hcallee
    (fun mf o hs hc hg => k mf o hc hs hg)

/-- The child machine of a `STATICCALL` (see `step_staticcall`). -/
abbrev staticChild (m : Machine) (gas toW inOff inSize outOff outSize : Word)
    (rest : List Word) : Machine :=
  { m with
    frame := Frame.init
      (childMsg m m.frame.msg.currentTarget (Word.toAddress toW) (Word.toAddress toW) 0
        (callGas m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize).subCall true true
        inOff inSize outOff outSize)
      (.call outOff.toNat outSize.toNat) (m.world, m.transient)
    parents := callerFrame m rest (callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff
      outSize) (Word.toAddress toW) inOff inSize outOff outSize :: m.parents }

/-- `WP.staticcall` with the gas bound: the caller resumes with at most the gas it had. -/
theorem WP.staticcall_gas {Q : Machine → Prop} {H Hc : Machine → Outcome → Prop}
    (hprec : PrecompilesOk m.precompiles)
    (hcode : m.frame.code[m.frame.pc]? = some 0xfa)
    (hstk : m.frame.stack = gas :: toW :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize ≤
      m.frame.gasLeft)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = false)
    (hcallee : Halts (staticChild m gas toW inOff inSize outOff outSize rest) Hc)
    (k : ∀ mf o, Hc mf o → SameFrame (staticChild m gas toW inOff inSize outOff outSize rest) mf →
      (resumeAfter (call0Caller m gas toW inOff inSize outOff outSize rest) m.parents mf o
        ).frame.gasLeft ≤ m.frame.gasLeft →
      WP (resumeAfter (call0Caller m gas toW inOff inSize outOff outSize rest) m.parents mf o)
        Q H) :
    WP m Q H :=
  WP.call_gas_le hprec (step_staticcall hcode hstk hdel hgas hdepth hpre) rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hcallee
    (fun mf o hs hc hg => k mf o hc hs hg)

/-! ## What the caller keeps, for any requested gas

The gas argument of a `CALL*` is the word `GAS` pushed, `ofNat g` = `g mod 2²⁵⁶`: with no upper
bound on `g` the requested amount is unknown. What the caller keeps does not depend on it: the
all-but-1/64 rule caps the child's share, so the caller keeps at least 1/64 of what is left
after the access and memory charges. These lemmas give lower bounds on the caller's gas after
any call without value, whatever the requested gas, so no `g < 2^k` hypothesis is needed. -/

/-- The charge of a call without value is at most the access and memory charges plus
all-but-1/64 of the rest, whatever the requested gas word. -/
theorem callCost_le_max {m : Machine} {gas : Word} {to : Address}
    {inOff inSize outOff outSize : Word}
    (h : Gas.accessCost (m.frame.sub.accessedAddresses.contains to) +
      (callExt m inOff inSize outOff outSize).cost ≤ m.frame.gasLeft) :
    callCost m gas 0 to 0 0 inOff inSize outOff outSize +
        (m.frame.gasLeft - Gas.accessCost (m.frame.sub.accessedAddresses.contains to) -
          (callExt m inOff inSize outOff outSize).cost) / 64 ≤ m.frame.gasLeft := by
  unfold callCost callGas Gas.messageCallGas Gas.maxMessageCallGas
  have hlt : ¬ m.frame.gasLeft < Gas.accessCost (m.frame.sub.accessedAddresses.contains to) +
      0 + 0 + 0 + (callExt m inOff inSize outOff outSize).cost := by omega
  simp only [hlt, ite_false]
  have := Nat.min_le_right gas.toNat (m.frame.gasLeft -
    (callExt m inOff inSize outOff outSize).cost -
      (Gas.accessCost (m.frame.sub.accessedAddresses.contains to) + 0 + 0 + 0) -
    (m.frame.gasLeft - (callExt m inOff inSize outOff outSize).cost -
      (Gas.accessCost (m.frame.sub.accessedAddresses.contains to) + 0 + 0 + 0)) / 64)
  have h2 : (m.frame.gasLeft - (callExt m inOff inSize outOff outSize).cost -
      (Gas.accessCost (m.frame.sub.accessedAddresses.contains to) + 0 + 0 + 0)) =
      m.frame.gasLeft - Gas.accessCost (m.frame.sub.accessedAddresses.contains to) -
        (callExt m inOff inSize outOff outSize).cost := by omega
  rw [h2] at this ⊢
  have := Nat.div_le_self (m.frame.gasLeft -
    Gas.accessCost (m.frame.sub.accessedAddresses.contains to) -
      (callExt m inOff inSize outOff outSize).cost) 64
  omega

/-- **The caller keeps at least 1/64** of its gas after the access (≤ 2600) and memory charges,
for any requested gas word: a lower bound of the suspended caller's gas, hence of its gas
after the call returns (`resumeAfter_gasLeft`). -/
theorem le_gasLeft_callerFrame {m : Machine} {gas toW inOff inSize outOff outSize : Word}
    {rest : List Word} {c : Nat}
    (hc : (callExt m inOff inSize outOff outSize).cost ≤ c) (h : 2600 + c ≤ m.frame.gasLeft) :
    (m.frame.gasLeft - 2600 - c) / 64 ≤
      (callerFrame m rest (callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize)
        (Word.toAddress toW) inOff inSize outOff outSize).gasLeft := by
  have ha := accessCost_le (m.frame.sub.accessedAddresses.contains (Word.toAddress toW))
  have := callCost_le_max (gas := gas) (to := Word.toAddress toW) (m := m)
    (inOff := inOff) (inSize := inSize) (outOff := outOff) (outSize := outSize) (by omega)
  have h3 : (m.frame.gasLeft - 2600 - c) / 64 ≤ (m.frame.gasLeft -
      Gas.accessCost (m.frame.sub.accessedAddresses.contains (Word.toAddress toW)) -
        (callExt m inOff inSize outOff outSize).cost) / 64 :=
    Nat.div_le_div_right (by omega)
  simp only [callerFrame]
  omega

/-- The call is affordable when the access and memory charges are. -/
theorem callCost_le_gasLeft {m : Machine} {gas toW inOff inSize outOff outSize : Word} {c : Nat}
    (hc : (callExt m inOff inSize outOff outSize).cost ≤ c) (h : 2600 + c ≤ m.frame.gasLeft) :
    callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize ≤ m.frame.gasLeft := by
  have ha := accessCost_le (m.frame.sub.accessedAddresses.contains (Word.toAddress toW))
  have := callCost_le_max (gas := gas) (to := Word.toAddress toW) (m := m)
    (inOff := inOff) (inSize := inSize) (outOff := outOff) (outSize := outSize) (by omega)
  omega

end EvmLogic.Program
