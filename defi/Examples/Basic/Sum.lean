import EvmLogic.Tactic.WpStep
import EvmLogic.Program.Summary
import EvmLogic.Program.Block

/-!
# Demo: a solc loop, proved with the loop rule

`Sum.sol` (solc 0.8.28, `--optimize --optimize-runs 200 --evm-version cancun`):

```solidity
function sum(uint256 n) external pure returns (uint256 s) {
    unchecked { for (uint256 i = 0; i < n; ++i) { s += i; } }
}
```

* `loop`: the loop at pc `0x4e` (head `DUP3 DUP2 LT ISZERO PUSH1 0x60 JUMPI`, body back to the
  head), by induction on the iterations left: from the head with counter `k` and accumulator
  `sumTo k`, the loop exits at `0x60` with `sumTo n`, having used exactly `55 (n - k) + 26` gas.
  Each iteration is one `wp_run_to 0x4e`.
* `sum_halts`: the whole frame (dispatcher, ABI decoding, loop via `WP.bind`, return), for any
  parents; `sum_processMessageCall`: the top-level statement.
-/

namespace EvmLean.Program.Examples.Sum

open Interpreter

/-- Runtime code of `Sum` (solc output, including the metadata trailer). -/
def code : ByteArray := ⟨#[
  0x60, 0x80, 0x60, 0x40, 0x52, 0x34, 0x80, 0x15, 0x60, 0x0e, 0x57, 0x5f, 0x5f, 0xfd, 0x5b, 0x50,
  0x60, 0x04, 0x36, 0x10, 0x60, 0x26, 0x57, 0x5f, 0x35, 0x60, 0xe0, 0x1c, 0x80, 0x63, 0x18, 0x8b,
  0x85, 0xb4, 0x14, 0x60, 0x2a, 0x57, 0x5b, 0x5f, 0x5f, 0xfd, 0x5b, 0x60, 0x39, 0x60, 0x35, 0x36,
  0x60, 0x04, 0x60, 0x66, 0x56, 0x5b, 0x60, 0x4b, 0x56, 0x5b, 0x60, 0x40, 0x51, 0x90, 0x81, 0x52,
  0x60, 0x20, 0x01, 0x60, 0x40, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3, 0x5b, 0x5f, 0x80, 0x5b, 0x82,
  0x81, 0x10, 0x15, 0x60, 0x60, 0x57, 0x90, 0x81, 0x01, 0x90, 0x60, 0x01, 0x01, 0x60, 0x4e, 0x56,
  0x5b, 0x50, 0x91, 0x90, 0x50, 0x56, 0x5b, 0x5f, 0x60, 0x20, 0x82, 0x84, 0x03, 0x12, 0x15, 0x60,
  0x75, 0x57, 0x5f, 0x5f, 0xfd, 0x5b, 0x50, 0x35, 0x91, 0x90, 0x50, 0x56, 0xfe, 0xa2, 0x64, 0x69,
  0x70, 0x66, 0x73, 0x58, 0x22, 0x12, 0x20, 0x40, 0x6b, 0x65, 0xaa, 0x68, 0x61, 0x62, 0x24, 0xcf,
  0x2a, 0xc0, 0xb5, 0x7d, 0xf0, 0xe8, 0x37, 0xf1, 0xaf, 0x84, 0x58, 0x18, 0x59, 0x2f, 0x04, 0x19,
  0x76, 0xa4, 0x95, 0x63, 0x20, 0x61, 0xd8, 0x64, 0x73, 0x6f, 0x6c, 0x63, 0x43, 0x00, 0x08, 0x1c,
  0x00, 0x33]⟩

-- The basic blocks of the function code (the rest is solc's metadata).
#guard (blockStarts .cancun code).take 17 =
  [0x00, 0x0b, 0x0e, 0x17, 0x26, 0x2a, 0x35, 0x39, 0x4b, 0x4e, 0x56, 0x60, 0x66, 0x72, 0x75, 0x7c,
   0x7d]
#guard ((basicBlocks .cancun code).find? (·.start = 0x4e)).map (·.next) = some 0x56

/-- `∑_{i<k} i` in 256-bit arithmetic. -/
def sumTo : Nat → Word
  | 0 => 0
  | k + 1 => sumTo k + BitVec.ofNat 256 k

/-- Incrementing the counter. -/
theorem ofNat_succ' (k : Nat) : 1#256 + BitVec.ofNat 256 k = BitVec.ofNat 256 (k + 1) := by
  apply BitVec.eq_of_toNat_eq; simp; omega

/-- One loop step of the accumulator. -/
theorem sumTo_succ' (k : Nat) : BitVec.ofNat 256 k + sumTo k = sumTo (k + 1) := by
  simp only [sumTo]; exact BitVec.add_comm _ _

/-- The loop condition holds while `k < n`. -/
theorem lt_ofNat {k n : Nat} (hk : k < n) (hn : n < 2 ^ 256) :
    Word.lt (BitVec.ofNat 256 k) (BitVec.ofNat 256 n) = 1 := by
  rw [Word.lt_eq_one_iff]; simp; omega

/-- The loop condition fails at `k = n`. -/
theorem lt_ofNat_self (n : Nat) : Word.lt (BitVec.ofNat 256 n) (BitVec.ofNat 256 n) = 0 := by
  rw [Word.lt_eq_zero_iff]; exact Nat.le_refl _

/-- The machine at the loop exit (`pc = 0x60`), from the loop head with counter `k`. -/
def loopExit (m : Machine) (n k : Nat) (rest : List Word) : Machine :=
  { m with frame :=
    { m.frame with
      pc := 0x60
      stack := BitVec.ofNat 256 n :: sumTo n :: BitVec.ofNat 256 n :: rest
      gasLeft := m.frame.gasLeft - (55 * (n - k) + 26) } }

set_option maxHeartbeats 0 in
/-- **The loop** (see the module docstring), by induction on `d = n - k`. -/
theorem loop (n : Nat) (rest : List Word) (hn : n < 2 ^ 256) (hlen : rest.length < 1000) (Q H) :
    ∀ d k (m : Machine), n - k = d → k ≤ n →
    m.frame.code = code → m.frame.jumpDests = validJumpDests code → m.frame.pc = 0x4e →
    m.frame.stack = BitVec.ofNat 256 k :: sumTo k :: BitVec.ofNat 256 n :: rest →
    55 * (n - k) + 26 ≤ m.frame.gasLeft →
    Q (loopExit m n k rest) →
    WP m Q H := by
  intro d
  induction d with
  | zero =>
    intro k m hd hk hc hj hpc hs hg hQ
    have hkn : k = n := by omega
    subst hkn
    simp only [loopExit] at hQ
    wp_intro m
    wp_run_to 0x60 [lt_ofNat_self]
    refine WP.ret_of_eq ?_ hQ
    simp only [Machine.mk.injEq, Frame.mk.injEq, true_and, and_true]
    omega
  | succ d ih =>
    intro k m hd hk hc hj hpc hs hg hQ
    have hkn : k < n := by omega
    simp only [loopExit] at hQ
    wp_intro m
    wp_run_to 0x4e [lt_ofNat hkn hn, ofNat_succ', sumTo_succ']
    refine ih (k + 1) _ (by omega) (by omega) (by dsimp only) (by dsimp only) (by dsimp only)
      (by dsimp only) (by dsimp only; omega) ?_
    simp only [loopExit]
    refine (congrArg Q ?_).mp hQ
    simp only [Machine.mk.injEq, Frame.mk.injEq, true_and, and_true]
    omega

/-- What a successful `sum(n)` frame leaves behind. -/
def SumPost (m₀ : Machine) (n : Nat) (mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord (sumTo n)) ∧ mf.world = m₀.world ∧ mf.transient = m₀.transient ∧
    mf.createdAccounts = m₀.createdAccounts ∧ mf.frame.sub = m₀.frame.sub

set_option maxHeartbeats 0 in
/-- The whole frame of `sum(n)`: prologue to the loop head, the loop, the return. -/
theorem sum_halts (m : Machine) (n : Nat) (hn : n < 2 ^ 256)
    (hc : m.frame.code = code) (hj : m.frame.jumpDests = validJumpDests code)
    (hpc : m.frame.pc = 0) (hs : m.frame.stack = []) (hmem : m.frame.memory = {})
    (hval : m.frame.msg.value = 0) (hsize : m.frame.msg.data.size = 36)
    (hsel : selectorOf m.frame.msg.data = 0x188b85b4#256)
    (harg : Bytes.toWord (readBytes m.frame.msg.data 4 32) = BitVec.ofNat 256 n)
    (hg : 55 * n + 500 ≤ m.frame.gasLeft) :
    Halts m (SumPost m n) := by
  apply WP.halts_of_false
  simp only [selectorOf] at hsel
  wp_intro m
  wp_run_to 0x4e [hval, hsize, hsel, harg]
  refine WP.bind (loop n [57#256, 411796916#256] hn (by decide) (· = loopExit _ n 0 _) _ n 0 _
    (by omega) (Nat.zero_le _) (by dsimp only) (by dsimp only) (by dsimp only)
    (by dsimp only [sumTo]; rfl) (by dsimp only; omega) rfl) ?_
  rintro _ - rfl
  simp only [loopExit]
  wp_steps
  simp only [SumPost, outputMachine, and_self]

/-- The runtime code is not an EIP-7702 delegation designator. -/
theorem delegatedAddress?_code : delegatedAddress? code = none := by decide +kernel

/-- **`sum(n)` returns `∑_{i<n} i`** (modulo `2²⁵⁶`): a top-level call of the solc-compiled
`Sum` contract with calldata selecting `sum` and encoding `n`, for every `Crypto`, context
without EIP-7702 authorizations (or before Prague), world, transient storage, caller, warm
sets, and gas at least `55 n + 500`, succeeds with output `sumTo n` and leaves the world
unchanged, for all large enough fuel. -/
theorem sum_processMessageCall {ctx : Context} {w : World} {tr : TransientStorage}
    {msg : Message} {a : Address} {n : Nat}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork a = false) (htarget : msg.target = some a)
    (hca : msg.codeAddress = some a) (hcode : msg.code = code) (hval : msg.value = 0)
    (hdepth : msg.depth = 0) (hsize : msg.data.size = 36)
    (hsel : selectorOf msg.data = 0x188b85b4#256)
    (harg : Bytes.toWord (readBytes msg.data 4 32) = BitVec.ofNat 256 n) (hn : n < 2 ^ 256)
    (hgas : 55 * n + 500 ≤ msg.gas) :
    ∃ N, ∀ fuel, N ≤ fuel → ∃ r, processMessageCall fuel ctx w tr msg = .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord (sumTo n) ∧ r.world = w := by
  have hf := fresh_startMachine ctx w tr msg
  rw [hcode] at hf
  obtain ⟨hc, hj, hpc, hs, hmem, hg, -⟩ := hf.frame
  obtain ⟨N, hN⟩ := processMessageCall_of_halts hdeleg (hcode ▸ delegatedAddress?_code) htarget
    hca hpre hval hdepth (sum_halts _ n hn hc hj hpc hs hmem hval hsize hsel harg (hg ▸ hgas))
  refine ⟨N, fun fuel hle => ?_⟩
  obtain ⟨mf, o, ⟨rfl, hw, -⟩, hsame, hrun⟩ := hN fuel hle
  have hk : mf.frame.kind = .call 0 0 := hsame.kind
  obtain ⟨h1, h2, h3, -⟩ := topLevelResult_success_call (t := msg.target)
    (out := Bytes.ofWord (sumTo n)) hk
  exact ⟨_, hrun, h1, h2, h3.trans hw⟩
