import EvmLogic.Tactic.SolStep
import EvmLogic.Solidity.Call

/-!
# Selector dispatch

solc 0.8.28 (legacy pipeline, optimizer on) starts every contract with the same dispatcher:

```
PUSH1 0x80 PUSH1 0x40 MSTORE              free-memory pointer := 0x80
CALLVALUE DUP1 ISZERO PUSH2 a JUMPI       (only if no function is payable)
  PUSH0 PUSH0 REVERT                        revert if value was sent
a: JUMPDEST POP
PUSH1 0x04 CALLDATASIZE LT PUSH2 f JUMPI  calldata shorter than a selector: fallback f
PUSH0 CALLDATALOAD PUSH1 0xe0 SHR         sel := calldata[0:4]
DUP1 PUSH4 s GT PUSH2 b JUMPI             binary split on the sorted selectors (> 4 functions)
DUP1 PUSH4 s₁ EQ PUSH2 e₁ JUMPI           linear EQ chain within each half
DUP1 PUSH4 s₂ EQ PUSH2 e₂ JUMPI
…
f: PUSH0 PUSH0 REVERT                     no match (no fallback function)
```

and enters the function's ABI decoder at `eᵢ` with the selector still on the stack.

`Reaches code sel entry n cost` packages the outcome as a reusable rewrite rule: from the
start of a call frame running `code` with calldata whose selector is `sel` (and zero call
value), `n` steps lead to `pc = entry` with stack `[sel]`, memory `initMemory` and `cost` gas
spent; nothing else in the machine changes. It quantifies over *every* machine (context,
world, caller, calldata beyond the selector, warm sets, gas), so one proof per selector
serves every theorem about that function. Instances are proved by `sol_dispatch`, which runs
the dispatcher symbolically for an arbitrary machine (e.g.
`Examples.Erc20.reaches_transfer`).
-/

section

namespace EvmLean.Solidity.Dispatch

open Interpreter

/-- **Dispatch reaches the entry of a function.** Running `code` from the start of a call
frame whose calldata has selector `sel` (at least four bytes, value zero, `cost` gas
available) takes `n` steps to `entry`, with the selector on the stack, the free-memory
pointer initialised and exactly `cost` gas charged. -/
def Reaches (code : ByteArray) (sel entry n cost : Nat) : Prop :=
  ∀ (m : Machine) (k : Nat), m.frame.code = code → m.frame.jumpDests = validJumpDests code →
    m.frame.pc = 0 → m.frame.stack = [] → m.frame.memory = {} → m.frame.msg.value = 0 →
    Abi.selectorOf m.frame.msg.data = sel → 4 ≤ m.frame.msg.data.size →
    m.frame.msg.data.size < 2 ^ 256 → cost ≤ m.frame.gasLeft →
    run (k + n) m = run k { m with frame := { m.frame with
      pc := entry, stack := [BitVec.ofNat 256 sel], memory := initMemory,
      gasLeft := m.frame.gasLeft - cost } }

/-- The calldata-size check `CALLDATASIZE < 4` is false for calldata with a selector. -/
theorem lt_calldatasize_four {n : Nat} (h₁ : 4 ≤ n) (h₂ : n < 2 ^ 256) :
    Word.lt (BitVec.ofNat 256 n) (BitVec.ofNat 256 4) = BitVec.ofNat 256 0 := by
  simp only [Word.lt, Word.ofBool, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h₂]
  have : ¬ n < 4 % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt (by decide)]; omega
  simp [this]

/-- The selector as the dispatcher sees it. -/
theorem selector_eq {data : ByteArray} {sel : Nat} (h : Abi.selectorOf data = sel) :
    BitVec.ofNat 256 (Abi.selectorOf data) = BitVec.ofNat 256 sel := by rw [h]

/-- `Reaches` for a machine at the start of a call frame (`Frame.init`), the form produced by
`initMachine`: the hypotheses are about the message only. (Applying `Reaches` with `rfl` for
the code and jump-destination hypotheses would make the elaborator unfold `validJumpDests`
of a literal code; this lemma keeps them symbolic.) -/
theorem Reaches.run_eq {code : ByteArray} {sel entry n cost : Nat}
    (h : Reaches code sel entry n cost) {m : Machine} {msg : Message} {kind : FrameKind}
    {snap : World × TransientStorage} (hfr : m.frame = Frame.init msg kind snap)
    (hcode : msg.code = code) (hval : msg.value = 0) (hsel : Abi.selectorOf msg.data = sel)
    (hsz : 4 ≤ msg.data.size) (hsz' : msg.data.size < 2 ^ 256) (hgas : cost ≤ msg.gas)
    (k : Nat) :
    run (k + n) m = run k { m with frame := { m.frame with
      pc := entry, stack := [BitVec.ofNat 256 sel], memory := initMemory,
      gasLeft := m.frame.gasLeft - cost } } :=
  h m k (by rw [hfr, ← hcode]; rfl) (by rw [hfr, ← hcode]; rfl) (by rw [hfr]; rfl)
    (by rw [hfr]; rfl) (by rw [hfr]; rfl) (by rw [hfr]; exact hval) (by rw [hfr]; exact hsel)
    (by rw [hfr]; exact hsz) (by rw [hfr]; exact hsz') (by rw [hfr]; exact hgas)

/-- Prove `Reaches code sel entry n cost` for literal `code` (all numbers explicit) by
running the dispatcher on an arbitrary machine. -/
macro "sol_dispatch" : tactic => `(tactic| (
  intro m k hcode hjd hpc hstk hmem hval hsel hsz hsz' hgas
  obtain ⟨ctx, pre, w, tr, ow, ca,
    ⟨msg, c, jd, pc, stk, mem, gas, rd, sub, snap, kind⟩, parents⟩ := m
  simp only at hcode hjd hpc hstk hmem hval hsel hsz hsz' hgas ⊢
  subst hpc hstk hmem
  subst c
  subst jd
  have hlt := lt_calldatasize_four hsz hsz'
  have hsel' := selector_eq hsel
  -- Hide the target machine: normalization would otherwise try to close the final goal
  -- `run k m = run k m'` by unfolding the gas arithmetic of both sides.
  generalize hR : run k _ = R
  sol_steps [hval, hlt, hsel']
  subst hR
  simp only [initMemory, BitVec.ofNat_eq_ofNat, Nat.sub_sub, Nat.reduceAdd]))

end EvmLean.Solidity.Dispatch

end

section

/-!
## Dispatch from the start of a top-level call

`Dispatch.Reaches.run_start` instantiates a dispatch lemma (`Dispatch.Reaches`) at the machine
`start ctx w tr (callMsg code …)` of a top-level call (`EvmLeanProofs.Solidity.Call`), for any
calldata with the right selector: the hypotheses are about the calldata only. Every
per-function theorem about a compiled contract starts with it.
-/

namespace EvmLean.Solidity.Dispatch

open Interpreter

/-- **Dispatch of a top-level call.** -/
theorem Reaches.run_start {code : ByteArray} {sel entry n cost : Nat}
    (h : Reaches code sel entry n cost) {ctx : Context} {w : World} {tr : TransientStorage}
    {token caller : Address} {data : ByteArray} {gas : Nat} {warmAddrs : AddressSet}
    {warmKeys : StorageKeySet} (hsel : Abi.selectorOf data = sel) (hsz : 4 ≤ data.size)
    (hsz' : data.size < 2 ^ 256) (hgas : cost ≤ gas) (k : Nat) :
    run (k + n) (start ctx w tr (callMsg code token caller data gas warmAddrs warmKeys)) =
      run k { start ctx w tr (callMsg code token caller data gas warmAddrs warmKeys) with
        frame := { (start ctx w tr (callMsg code token caller data gas warmAddrs warmKeys)).frame with
          pc := entry, stack := [BitVec.ofNat 256 sel], memory := initMemory,
          gasLeft := gas - cost } } :=
  h.run_eq (msg := callMsg code token caller data gas warmAddrs warmKeys) rfl rfl rfl hsel hsz
    hsz' hgas k

end EvmLean.Solidity.Dispatch

end
