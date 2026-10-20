import EvmLogic.Tactic.SolStep
import EvmLogic.Solidity.Call

/-!
# Selector dispatch

`Reaches code sel entry n cost` packages solc's dispatcher (callvalue check, selector
extraction, `PUSH4 sel EQ` chain) as a rewrite rule over *every* machine: `n` steps from the
frame start reach `entry` with stack `[sel]`, so one proof per selector (by `sol_dispatch`)
serves every theorem about that function.
-/

section

namespace EvmLogic.Solidity.Dispatch
open EvmLean EvmLogic.Tactic EvmLean.Interpreter

/-- **Dispatch reaches the entry of a function**: from the frame start with selector `sel`
(≥ 4 calldata bytes, value zero), `n` steps reach `entry` with `[sel]` and `cost` gas spent. -/
def Reaches (code : ByteArray) (sel entry n cost : Nat) : Prop :=
  ∀ (m : Machine) (k : Nat), m.frame.code = code → m.frame.jumpDests = validJumpDests code →
    m.frame.pc = 0 → m.frame.stack = [] → m.frame.memory = {} → m.frame.msg.value = 0 →
    Abi.selectorOf m.frame.msg.data = sel → 4 ≤ m.frame.msg.data.size →
    m.frame.msg.data.size < 2 ^ 256 → cost ≤ m.frame.gasLeft →
    run (k + n) m = run k { m with frame := { m.frame with
      pc := entry, stack := [BitVec.ofNat 256 sel], memory := initMemory,
      gasLeft := m.frame.gasLeft - cost } }

theorem lt_calldatasize_four {n : Nat} (h₁ : 4 ≤ n) (h₂ : n < 2 ^ 256) :
    Word.lt (BitVec.ofNat 256 n) (BitVec.ofNat 256 4) = BitVec.ofNat 256 0 := by
  simp only [Word.lt, Word.ofBool, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h₂]
  have : ¬ n < 4 % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt (by decide)]; omega
  simp [this]

theorem selector_eq {data : ByteArray} {sel : Nat} (h : Abi.selectorOf data = sel) :
    BitVec.ofNat 256 (Abi.selectorOf data) = BitVec.ofNat 256 sel := by rw [h]

/-- `Reaches` at a `Frame.init` machine. Use this rather than `Reaches` with `rfl`, which
makes the elaborator unfold `validJumpDests` of a literal code. -/
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

end EvmLogic.Solidity.Dispatch

end

section

/-! ## Dispatch from the start of a top-level call -/

namespace EvmLogic.Solidity.Dispatch
open EvmLean EvmLogic.Tactic EvmLean.Interpreter

/-- **Dispatch of a top-level call** (`start … (callMsg …)`). -/
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

end EvmLogic.Solidity.Dispatch

end
