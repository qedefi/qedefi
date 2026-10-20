import EvmLogic.Step.Basic
import EvmLogic.Step.Flow
import EvmLogic.Bytes
import EvmLogic.Program.Summary

/-!
# Calls: pushing the child frame, and callee summaries

`CALL`, `STATICCALL` and `DELEGATECALL` in the step semantics, for a call that does start a
child frame (enough gas, depth below 1024, for `CALL` an affordable value, a non-precompile
target without EIP-7702 delegation or a fork before Prague):

* `step_staticcall`, `step_call`, `step_delegatecall`: one `step` charges the caller
  (`callCost`: EIP-2929 access cost, EIP-150 all-but-1/64 forwarding via
  `Gas.messageCallGas`, value-transfer and new-account costs, memory expansion), warms the
  target, clears the return data, and pushes `Frame.init msg (.call outOff outSize) snapshot`
  for the child message `msg` (gas `(callGas …).subCall`, including the 2300 stipend when
  value moves; for `CALL` the value is transferred in the world first). The caller's frame,
  suspended, is `callerFrame …` (pc still at the `CALL*`).
* `WP.call`: the **callee-summary rule**. If the child's frame `Halts` with `H` (e.g. by a
  `FunctionSummary` of the callee's code applied to the fresh child machine), the caller
  continues from `resumeAfter p ps mf o` for every outcome the summary allows.
* `resumeAfter_success`, `resumeAfter_revert`, `resumeAfter_halt`: what the caller sees: the
  success flag pushed, the output copied to `[outOff, outOff + min outSize |output|)`,
  `RETURNDATA` set, unused child gas returned, the child's world (or the snapshot after a
  failure), the child's logs and warm sets merged on success, and the pc advanced.
* `step_staticcall_precompile`: a precompile runs to completion within the `step`.
-/

section

namespace EvmLean.Program

open Interpreter

/-! ## Warm sets -/

/-- Inserting an element that is already present changes nothing. -/
theorem AddressSet.insert_of_contains {s : AddressSet} {a : Address} (h : s.contains a = true) :
    s.insert a = s := by
  apply Std.ExtTreeSet.ext_contains
  intro x
  rw [Std.ExtTreeSet.contains_insert]
  by_cases hx : a = x
  · subst hx; simp [h]
  · simp [hx]

/-- The substate with `a` warm. -/
def _root_.EvmLean.Interpreter.Substate.warmAddr (sub : Substate) (a : Address) : Substate :=
  { sub with accessedAddresses := sub.accessedAddresses.insert a }

/-- `accessAddress` warms the address and reports whether it already was warm. -/
theorem run_accessAddress (m : Machine) (a : Address) :
    (accessAddress a).run m = pure (m.frame.sub.accessedAddresses.contains a,
      { m with frame := { m.frame with sub := m.frame.sub.warmAddr a } }) := by
  cases hw : m.frame.sub.accessedAddresses.contains a
  · simp only [accessAddress, getFrame, modifySub, modifyFrame, StateT.run_bind, hw,
      StateT.run_get, StateT.run_pure, pure_bind]
    rfl
  · simp only [accessAddress, getFrame, StateT.run_bind, hw, StateT.run_get, StateT.run_pure,
      pure_bind, Substate.warmAddr, AddressSet.insert_of_contains hw]
    rfl

/-- `accessDelegation` does nothing before Prague or for code without a designator. -/
theorem run_accessDelegation (m : Machine) (a : Address)
    (h : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code a) = none) :
    (accessDelegation a).run m = pure ((false, a, m.world.code a, 0), m) := by
  unfold accessDelegation
  by_cases hf : m.ctx.fork < .prague
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, hf, ite_true, StateT.run_pure]
  · have hd := h.resolve_left hf
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hf, ite_false, hd]
    rfl

/-! ## The charges of a call -/

/-- Memory expansion for a call's input and output windows. -/
def callExt (m : Machine) (inOff inSize outOff outSize : Word) : Gas.ExtendMemory :=
  Gas.extendMemory m.frame.memory.size [(inOff.toNat, inSize.toNat), (outOff.toNat, outSize.toNat)]

/-- Memory after expansion for a call's windows. -/
def callMemory (m : Machine) (inOff inSize outOff outSize : Word) : Memory :=
  (m.frame.memory.expand inOff.toNat inSize.toNat).expand outOff.toNat outSize.toNat

/-- `Gas.messageCallGas` for a call to `to` with `value`, requesting `gas`, with account
creation cost `create` and value-transfer cost `transfer` (both zero for `STATICCALL` and
`DELEGATECALL`; see `createCost`, `transferCost`). -/
def callGas (m : Machine) (gas value : Word) (to : Address) (create transfer : Nat)
    (inOff inSize outOff outSize : Word) : Gas.MessageCallGas :=
  Gas.messageCallGas value.toNat gas.toNat m.frame.gasLeft (callExt m inOff inSize outOff outSize).cost
    (Gas.accessCost (m.frame.sub.accessedAddresses.contains to) + 0 + create + transfer)

/-- Gas charged to the caller for the call (what the callee does not use comes back on
return). -/
def callCost (m : Machine) (gas value : Word) (to : Address) (create transfer : Nat)
    (inOff inSize outOff outSize : Word) : Nat :=
  (callGas m gas value to create transfer inOff inSize outOff outSize).cost +
    (callExt m inOff inSize outOff outSize).cost

/-- `CALL`'s account-creation cost: 25000 when value moves to a dead account. -/
def createCost (w : World) (value : Word) (to : Address) : Nat :=
  if value = 0 || isAccountAlive w to then 0 else Gas.newAccount

/-- `CALL`'s value-transfer cost: 9000 when value moves. -/
def transferCost (value : Word) : Nat := if value = 0 then 0 else Gas.callValue

/-- The caller's frame while the child runs: arguments popped, gas charged, memory expanded,
target warm, return data cleared. The pc still points at the `CALL*` (`resume` advances it). -/
def callerFrame (m : Machine) (rest : List Word) (cost : Nat) (to : Address)
    (inOff inSize outOff outSize : Word) : Frame :=
  { m.frame with
    stack := rest
    gasLeft := m.frame.gasLeft - cost
    memory := callMemory m inOff inSize outOff outSize
    returnData := .empty
    sub := m.frame.sub.warmAddr to }

/-- The child message of a call. -/
def childMsg (m : Machine) (caller to codeAddress : Address) (value : Word) (gas : Nat)
    (shouldTransferValue isStatic : Bool) (inOff inSize outOff outSize : Word) : Message where
  caller := caller
  target := some to
  currentTarget := to
  gas := gas
  value := value
  data := readBytes (callMemory m inOff inSize outOff outSize).bytes inOff.toNat inSize.toNat
  codeAddress := some codeAddress
  code := m.world.code codeAddress
  depth := m.frame.msg.depth + 1
  shouldTransferValue := shouldTransferValue
  isStatic := isStatic || m.frame.msg.isStatic
  accessedAddresses := (m.frame.sub.warmAddr codeAddress).accessedAddresses
  accessedStorageKeys := m.frame.sub.accessedStorageKeys
  disablePrecompiles := false

/-! ## `STATICCALL` -/

variable {m : Machine} {gas toW inOff inSize outOff outSize : Word} {rest : List Word}

/-- **`STATICCALL` to a non-precompile pushes the child frame.** The child runs
`m.world.code to` in a static context with gas `(callGas …).subCall` (EIP-150: at most all but
1/64 of what is left after the access and memory costs) and the input window as calldata. -/
theorem step_staticcall (hcode : m.frame.code[m.frame.pc]? = some 0xfa)
    (hstk : m.frame.stack = gas :: toW :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize ≤ m.frame.gasLeft)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = false) :
    step m = .running { m with
      frame := Frame.init
        (childMsg m m.frame.msg.currentTarget (Word.toAddress toW) (Word.toAddress toW) 0
          (callGas m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize).subCall true true
          inOff inSize outOff outSize)
        (.call outOff.toNat outSize.toNat) (m.world, m.transient)
      parents := callerFrame m rest (callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff
        outSize) (Word.toAddress toW) inOff inSize outOff outSize :: m.parents } := by
  have hg : ¬ m.frame.gasLeft < callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff
      outSize := Nat.not_lt.mpr hgas
  have hd : ¬ m.frame.msg.depth + 1 > Gas.stackDepthLimit := Nat.not_lt.mpr hdepth
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0xfa = .staticcall by
    cases m.ctx.fork <;> rfl]
  simp only [exec, execCall, popNat, popAddress, pop, getFrame, modifyFrame, StateT.run_bind,
    hstk, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, memoryExpansion]
  rw [run_accessAddress]
  simp only [pure_bind]
  rw [run_accessDelegation _ _ ?hd]
  case hd => exact hdel
  simp only [callCost, callGas, callExt, Nat.add_zero] at hg
  simp only [pure_bind, charge, getFrame, StateT.run_bind, StateT.run_get, StateT.run_pure,
    ite_true, Nat.add_zero, hg, ite_false, modifyFrame, StateT.run_modify,
    reduceCtorEq, decide_false, Bool.false_and, Bool.false_eq_true, expandMemory, genericCall,
    setReturnData, hd, List.foldl, readMemory]
  simp only [pure, Except.pure, launchCall, precompileOf, transferValue, hpre, Bool.false_eq_true,
    ite_false, ne_eq, not_true_eq_false, decide_false, Bool.and_false]
  rfl

/-! ## `CALL` -/

/-- **`CALL` to a non-precompile pushes the child frame.** The value moves from the caller to
`to` (`transferValue`) before the child starts; the snapshot for rollback is the world before
the transfer. Needs: not static or no value, an affordable value, enough gas, depth below the
limit. -/
theorem step_call {value : Word} (hcode : m.frame.code[m.frame.pc]? = some 0xf1)
    (hstk : m.frame.stack = gas :: toW :: value :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas value (Word.toAddress toW) (createCost m.world value (Word.toAddress toW))
      (transferCost value) inOff inSize outOff outSize ≤ m.frame.gasLeft)
    (hstatic : m.frame.msg.isStatic = false ∨ value = 0)
    (hbal : value.toNat ≤ (m.world.balance m.frame.msg.currentTarget).toNat)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = false) :
    step m = .running { m with
      world := transferValue m.world
        (childMsg m m.frame.msg.currentTarget (Word.toAddress toW) (Word.toAddress toW) value
          (callGas m gas value (Word.toAddress toW) (createCost m.world value (Word.toAddress toW))
            (transferCost value) inOff inSize outOff outSize).subCall true false
          inOff inSize outOff outSize)
      frame := Frame.init
        (childMsg m m.frame.msg.currentTarget (Word.toAddress toW) (Word.toAddress toW) value
          (callGas m gas value (Word.toAddress toW) (createCost m.world value (Word.toAddress toW))
            (transferCost value) inOff inSize outOff outSize).subCall true false
          inOff inSize outOff outSize)
        (.call outOff.toNat outSize.toNat) (m.world, m.transient)
      parents := callerFrame m rest (callCost m gas value (Word.toAddress toW)
        (createCost m.world value (Word.toAddress toW)) (transferCost value) inOff inSize outOff
        outSize) (Word.toAddress toW) inOff inSize outOff outSize :: m.parents } := by
  have hg : ¬ m.frame.gasLeft < callCost m gas value (Word.toAddress toW)
      (createCost m.world value (Word.toAddress toW)) (transferCost value) inOff inSize outOff
      outSize := Nat.not_lt.mpr hgas
  have hd : ¬ m.frame.msg.depth + 1 > Gas.stackDepthLimit := Nat.not_lt.mpr hdepth
  have hb : ¬ (m.world.balance m.frame.msg.currentTarget).toNat < value.toNat :=
    Nat.not_lt.mpr hbal
  have hs : (m.frame.msg.isStatic && decide (value ≠ 0)) = false := by
    rcases hstatic with h | h <;> simp [h]
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0xf1 = .call by
    cases m.ctx.fork <;> rfl]
  simp only [exec, execCall, popNat, popAddress, pop, getFrame, modifyFrame, StateT.run_bind,
    hstk, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, memoryExpansion]
  rw [run_accessAddress]
  simp only [pure_bind]
  rw [run_accessDelegation _ _ ?hd]
  case hd => exact hdel
  simp only [callCost, callGas, callExt, createCost, transferCost, Nat.add_zero] at hg
  simp only [pure_bind, charge, getFrame, StateT.run_bind, StateT.run_get, StateT.run_pure,
    Nat.add_zero, hg, ite_false, modifyFrame, StateT.run_modify, decide_true, Bool.true_and,
    hs, Bool.false_eq_true, expandMemory, genericCall, setReturnData, hd,
    List.foldl, readMemory, hb]
  simp only [pure, Except.pure, launchCall, precompileOf, transferValue, hpre, Bool.false_eq_true,
    ite_false]
  rfl

/-! ## `DELEGATECALL` -/

/-- **`DELEGATECALL` to a non-precompile pushes the child frame**, running the code of `to`
in the caller's context (same `ADDRESS`, `CALLER`, `CALLVALUE`; no value moves). -/
theorem step_delegatecall (hcode : m.frame.code[m.frame.pc]? = some 0xf4)
    (hstk : m.frame.stack = gas :: toW :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize ≤ m.frame.gasLeft)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = false) :
    step m = .running { m with
      frame := Frame.init
        (childMsg m m.frame.msg.caller m.frame.msg.currentTarget (Word.toAddress toW)
          m.frame.msg.value
          (callGas m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize).subCall false false
          inOff inSize outOff outSize)
        (.call outOff.toNat outSize.toNat) (m.world, m.transient)
      parents := callerFrame m rest (callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff
        outSize) (Word.toAddress toW) inOff inSize outOff outSize :: m.parents } := by
  have hg : ¬ m.frame.gasLeft < callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff
      outSize := Nat.not_lt.mpr hgas
  have hd : ¬ m.frame.msg.depth + 1 > Gas.stackDepthLimit := Nat.not_lt.mpr hdepth
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0xf4 = .delegatecall by
    cases m.ctx.fork <;> rfl]
  simp only [exec, execCall, popNat, popAddress, pop, getFrame, modifyFrame, StateT.run_bind,
    hstk, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, memoryExpansion]
  rw [run_accessAddress]
  simp only [pure_bind]
  rw [run_accessDelegation _ _ ?hd]
  case hd => exact hdel
  simp only [callCost, callGas, callExt, Nat.add_zero] at hg
  simp only [pure_bind, charge, getFrame, StateT.run_bind, StateT.run_get, StateT.run_pure,
    ite_true, Nat.add_zero, hg, ite_false, modifyFrame, StateT.run_modify, reduceCtorEq,
    decide_false, Bool.false_and, Bool.false_eq_true, expandMemory, genericCall, setReturnData, hd,
    List.foldl, readMemory]
  simp only [pure, Except.pure, launchCall, precompileOf, transferValue, hpre, Bool.false_eq_true,
    ite_false, Bool.false_and]
  rfl

/-! ## Returning to the caller -/

/-- `resume` keeps the machine constants and the parent's identity. -/
theorem sameFrame_resume (M : Machine) (r : ChildResult) : SameFrame M (resume M r) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The caller's substate after a successful child: logs, refunds, deletions and touched
accounts merged, warm sets taken from the child (`incorporate_child_on_success`). -/
def mergeSub (parent child : Substate) (w : World) (target : Address) : Substate :=
  let touched := parent.touchedAccounts.union child.touchedAccounts
  let touched := if accountExistsAndIsEmpty w target then touched.insert target else touched
  { logs := parent.logs ++ child.logs
    refundCounter := parent.refundCounter + child.refundCounter
    accountsToDelete := parent.accountsToDelete.union child.accountsToDelete
    touchedAccounts := touched
    accessedAddresses := child.accessedAddresses
    accessedStorageKeys := child.accessedStorageKeys }

/-- The caller's substate after a failed child: unchanged, except for the RIPEMD-160 touch
quirk (`incorporate_child_on_error`). -/
def failSub (parent child : Substate) (w : World) (target : Address) : Substate :=
  if child.touchedAccounts.contains ripemd160Address
      || (target == ripemd160Address && accountExistsAndIsEmpty w ripemd160Address) then
    { parent with touchedAccounts := parent.touchedAccounts.insert ripemd160Address }
  else parent

/-- Memory after copying a child's output into the caller's output window. -/
def returnMemory (mem : Memory) (outOff outSize : Nat) (out : ByteArray) : Memory :=
  if (out.extract 0 (min outSize out.size)).size = 0 then mem
  else mem.write outOff (out.extract 0 (min outSize out.size))

/-- **Return after success**: `1` pushed, output copied and kept as return data, unused gas
returned, the child's world, transient storage and accrued substate kept. -/
theorem resumeAfter_success {p : Frame} {ps : List Frame} {mf : Machine} {out : ByteArray}
    {o s : Nat} (hk : mf.frame.kind = .call o s) :
    resumeAfter p ps mf (.success out) =
      { mf with parents := ps, frame := { p with
        gasLeft := p.gasLeft + mf.frame.gasLeft
        sub := mergeSub p.sub mf.frame.sub mf.world mf.frame.msg.currentTarget
        returnData := out
        stack := 1 :: p.stack
        memory := returnMemory p.memory o s out
        pc := p.pc + 1 } } := by
  simp only [resumeAfter, frameResult, hk, resume, ChildResult.success, Option.isNone_none,
    Bool.not_false, Bool.and_self, ite_true]
  rfl

/-- **Return after `REVERT`**: `0` pushed, the revert data copied and kept as return data,
unused gas returned, world and transient storage rolled back to the child's snapshot. -/
theorem resumeAfter_revert {p : Frame} {ps : List Frame} {mf : Machine} {out : ByteArray}
    {o s : Nat} (hk : mf.frame.kind = .call o s) :
    resumeAfter p ps mf (.revert out) =
      { mf with
        parents := ps
        world := mf.frame.snapshot.1
        transient := mf.frame.snapshot.2
        frame :=
          { p with
            gasLeft := p.gasLeft + mf.frame.gasLeft
            sub := failSub p.sub mf.frame.sub mf.frame.snapshot.1 mf.frame.msg.currentTarget
            returnData := out
            stack := 0 :: p.stack
            memory := returnMemory p.memory o s out
            pc := p.pc + 1 } } := by
  simp only [resumeAfter, frameResult, hk, resume, ChildResult.success, Option.isNone_none,
    Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, failSub]
  rfl

/-- **Return after an exceptional halt**: `0` pushed, no gas returned, empty return data,
memory unchanged, world and transient storage rolled back. -/
theorem resumeAfter_halt {p : Frame} {ps : List Frame} {mf : Machine} {e : ExceptionalHalt}
    {o s : Nat} (hk : mf.frame.kind = .call o s) :
    resumeAfter p ps mf (.halt e) =
      { mf with
        parents := ps
        world := mf.frame.snapshot.1
        transient := mf.frame.snapshot.2
        frame :=
          { p with
            gasLeft := p.gasLeft
            sub := failSub p.sub mf.frame.sub mf.frame.snapshot.1 mf.frame.msg.currentTarget
            returnData := .empty
            stack := 0 :: p.stack
            pc := p.pc + 1 } } := by
  simp only [resumeAfter, frameResult, hk, resume, ChildResult.success, Option.isNone_some,
    Bool.false_and, Bool.false_eq_true, ite_false, failSub, Nat.add_zero]
  have : (ByteArray.empty.extract 0 (min s ByteArray.empty.size)).size = 0 := by
    simp
  simp only [this, ite_true]

/-- Returning one word into a 32-byte output window is an `MSTORE`. -/
theorem returnMemory_ofWord (mem : Memory) (off : Nat) (w : Word) :
    returnMemory mem off 32 (Bytes.ofWord w) = mem.storeWord off w := by
  have hs : (Bytes.ofWord w).size = 32 := Bytes.size_ofWord w
  have he : (Bytes.ofWord w).extract 0 (min 32 (Bytes.ofWord w).size) = Bytes.ofWord w := by
    rw [hs, Nat.min_self, ← hs, ByteArray.extract_zero_size]
  unfold returnMemory
  rw [he, hs]
  rfl

/-- The EIP-2929 address access cost is at most 2600. -/
theorem accessCost_le (warm : Bool) : Gas.accessCost warm ≤ 2600 := by
  cases warm <;> decide

/-- `Gas.messageCallGas` without value, when the extra and memory costs are affordable:
EIP-150 caps the forwarded gas at all but 1/64 of what is left, and the caller pays exactly the
forwarded gas plus the extra cost. -/
theorem messageCallGas_zero {g L mc extra : Nat} (h : extra + mc ≤ L) :
    Gas.messageCallGas (0 : Word).toNat g L mc extra =
      { cost := min g (Gas.maxMessageCallGas (L - mc - extra)) + extra,
        subCall := min g (Gas.maxMessageCallGas (L - mc - extra)) } := by
  have h0 : (0 : Word).toNat = 0 := rfl
  simp only [Gas.messageCallGas, h0, ite_true, Nat.not_lt.mpr h, ite_false, Nat.add_zero]

/-! ## The callee-summary rule -/

/-- **Callee-summary rule.** If the next step of `m` pushes a child frame (`mc`, whose parent
is the suspended caller frame `p`), and the child's frame `Halts` with `Hc` (for instance by a
summary of the callee's code), then `m` continues, in the same frame, from the caller resumed
after any end `(mf, o)` of the child that `Hc` allows. -/
theorem WP.call {m mc : Machine} {p : Frame} {Q : Machine → Prop}
    {H Hc : Machine → Outcome → Prop}
    (hstep : step m = .running mc) (hpar : mc.parents = p :: m.parents)
    (hp : SameFrame m { mc with frame := p, parents := m.parents })
    (hcallee : Halts mc Hc)
    (k : ∀ mf o, SameFrame mc mf → Hc mf o → WP (resumeAfter p m.parents mf o) Q H) :
    WP m Q H := by
  obtain ⟨n, mf, o, hH, hs, hn⟩ := hcallee.resume hpar
  have hsame : SameFrame m (resumeAfter p m.parents mf o) := by
    refine SameFrame.trans ?_ (sameFrame_resume _ _)
    exact ⟨hs.ctx.trans hp.ctx, hs.precompiles.trans hp.precompiles,
      hs.originalWorld.trans hp.originalWorld, rfl, hp.msg, hp.code, hp.jumpDests, hp.kind,
      hp.snapshot⟩
  refine WP.of_steps ⟨n + 1, ?_, hsame⟩ (k mf o hs hH)
  rw [show n + 1 = 1 + n by omega, stepN_add_of_running (by rw [stepN_one, hstep]), hn]

/-- The callee-summary rule for `STATICCALL` (see `step_staticcall`, `WP.call`): `Hc` is what
the callee's frame, started fresh on the child message, is known to do. -/
theorem WP.staticcall {Q : Machine → Prop} {H Hc : Machine → Outcome → Prop}
    (hcode : m.frame.code[m.frame.pc]? = some 0xfa)
    (hstk : m.frame.stack = gas :: toW :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize ≤ m.frame.gasLeft)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = false)
    (hcallee : Halts { m with
      frame := Frame.init
        (childMsg m m.frame.msg.currentTarget (Word.toAddress toW) (Word.toAddress toW) 0
          (callGas m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize).subCall true true
          inOff inSize outOff outSize)
        (.call outOff.toNat outSize.toNat) (m.world, m.transient)
      parents := callerFrame m rest (callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff
        outSize) (Word.toAddress toW) inOff inSize outOff outSize :: m.parents } Hc)
    (k : ∀ mf o, Hc mf o → SameFrame { m with
      frame := Frame.init
        (childMsg m m.frame.msg.currentTarget (Word.toAddress toW) (Word.toAddress toW) 0
          (callGas m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize).subCall true true
          inOff inSize outOff outSize)
        (.call outOff.toNat outSize.toNat) (m.world, m.transient)
      parents := callerFrame m rest (callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff
        outSize) (Word.toAddress toW) inOff inSize outOff outSize :: m.parents } mf →
      WP (resumeAfter (callerFrame m rest (callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize
        outOff outSize) (Word.toAddress toW) inOff inSize outOff outSize) m.parents mf o) Q H) :
    WP m Q H :=
  WP.call (step_staticcall hcode hstk hdel hgas hdepth hpre) rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hcallee
    (fun mf o hs hc => k mf o hc hs)

end EvmLean.Program

end

section

/-!
## The callee-summary rule for a value-free `CALL`

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

end

section

/-!
## `CALL` without value: the callee-summary rule

`WP.call0` is `WP.staticcall` (`EvmLeanProofs.Program.Call`) for a `CALL` that sends no value,
as Solmate's `SafeTransferLib.safeTransferFrom` / `safeTransfer` do (`call(gas(), token, 0, …)`):
with value `0` there is no value transfer (`transferValue` is the identity), no
account-creation or value-transfer charge, no balance or static-context requirement, and the
child message is non-static exactly when the caller's is.

* `transferValue_zero` (and `createCost_zero`, `transferCost_zero` of `OutExtraCall`): the
  value-dependent parts of `step_call` at value `0`.
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

end
