import Verified.AaveV3.AToken.Code
import Verified.Solmate.ERC20.BalanceOf
import EvmLogic.Solidity.ERC20Oz

/-!
# Aave V3 `AToken` bytecode: shared vocabulary

Every theorem about the deployed AToken implementation (`AToken.runtimeCode`) is stated for an
arbitrary fresh frame `m` running it (`Fresh AToken.runtimeCode m`): any executing address (on
mainnet the aToken proxy, which reaches the implementation by `DELEGATECALL`, so the frame's
storage is the proxy's), any caller, any world, any `Crypto`, any depth. Such a `Halts` statement
is a top-level fact and a callee summary at once (`WP.call`, `WP.delegatecall`-style rules).

The immutables are concrete in the code (`POOL` = the Pool proxy `pool`, the rewards controller,
the treasury), so the literal-code executors apply (`pwp_steps` with the kernel code table of
`Code.lean`). This file fixes:

* `pool`, its word as pushed by the code, and `poolWord_eq_caller` (a non-Pool caller fails the
  `onlyPool` comparison);
* `callerMustBePool`: the 4-byte revert data of the custom error `CallerMustBePool()`;
* `Unchanged`, `RevertsWith`, `NoEffect`, `NoEffectOut`: postconditions of a frame that reverts
  having changed nothing (world, transient storage, created accounts, logs), with a gas bound
  (and, for `NoEffectOut`, a bound on the revert data);
* calldata facts for the ABI decoder's size checks and address validation.
-/

namespace Verified.AaveV3.AToken
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open Verified.AaveV3.Contracts

/-! ## The Pool -/

/-- The Pool proxy, the value of the immutable `POOL` in the deployed code. -/
def pool : Address := 0x87870Bca3F3fD6335C3F4ce8392D69350B4fA4E2

/-- The word the code pushes for `POOL` (after solc's address mask). -/
theorem ofAddress_pool :
    Word.ofAddress pool = 773725381719276160229242488166406195640368342242#256 := by decide

/-- The `onlyPool` comparison `POOL == msg.sender` fails for any other caller. -/
theorem poolWord_eq_caller {c : Address} (h : c ≠ pool) :
    Word.eq 773725381719276160229242488166406195640368342242#256 (Word.ofAddress c) = 0#256 := by
  rw [← ofAddress_pool]
  exact eq_of_ne fun e => h (Word.ofAddress_injective e).symm

/-- The `onlyPool` comparison succeeds for the Pool. -/
theorem poolWord_eq_pool :
    Word.eq 773725381719276160229242488166406195640368342242#256 (Word.ofAddress pool) = 1#256 := by
  rw [← ofAddress_pool]; exact eq_self _

/-! ## Revert data -/

/-- The revert data of `CallerMustBePool()`: its 4-byte selector `0x54b39ce2`. -/
def callerMustBePool : ByteArray := ⟨#[0x54, 0xb3, 0x9c, 0xe2]⟩

theorem callerMustBePool_mem : ("CallerMustBePool()", (0x54b39ce2 : UInt32)) ∈ AToken.errors := by
  decide

theorem callerMustBePool_eq : callerMustBePool = Abi.selectorBytes 0x54b39ce2 := by decide +kernel

/-- The word solc stores for the error (`0x54b39ce2 << 224`): its first 4 bytes are the selector
(`reduceErrorSelector`, for any custom error). -/
theorem read_callerMustBePool (mem : Memory) (off : Nat) :
    (mem.storeWord off
        38311627670967753522350073125268627061094447950948343943422773345822703616000#256).read
      off 4 = callerMustBePool := by
  simp only [reduceErrorSelector]; exact callerMustBePool_eq.symm

/-! ## Postconditions -/

/-- The frame changed nothing observable: world, transient storage, created accounts, logs. -/
def Unchanged (m mf : Machine) : Prop :=
  mf.world = m.world ∧ mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs

/-- The frame reverts with data `out`, having changed nothing, using at most `g` gas. -/
def RevertsWith (out : ByteArray) (g : Nat) (m mf : Machine) (o : Outcome) : Prop :=
  o = .revert out ∧ Unchanged m mf ∧ m.frame.gasLeft ≤ mf.frame.gasLeft + g

/-- The frame reverts (with some data), having changed nothing, using at most `g` gas. -/
def NoEffect (g : Nat) (m mf : Machine) (o : Outcome) : Prop :=
  (∃ out, o = .revert out) ∧ Unchanged m mf ∧ m.frame.gasLeft ≤ mf.frame.gasLeft + g

theorem RevertsWith.noEffect {out : ByteArray} {g : Nat} {m mf : Machine} {o : Outcome}
    (h : RevertsWith out g m mf o) : NoEffect g m mf o :=
  ⟨⟨out, h.1⟩, h.2⟩

/-- `NoEffect` with revert data of at most `n` bytes (what a caller copying the data back, such
as the aToken proxy, needs to bound its gas). -/
def NoEffectOut (g n : Nat) (m mf : Machine) (o : Outcome) : Prop :=
  (∃ out, o = .revert out ∧ out.size ≤ n) ∧ Unchanged m mf ∧
    m.frame.gasLeft ≤ mf.frame.gasLeft + g

theorem NoEffectOut.noEffect {g n : Nat} {m mf : Machine} {o : Outcome}
    (h : NoEffectOut g n m mf o) : NoEffect g m mf o :=
  ⟨let ⟨out, ho, _⟩ := h.1; ⟨out, ho⟩, h.2⟩

theorem RevertsWith.noEffectOut {out : ByteArray} {g n : Nat} {m mf : Machine} {o : Outcome}
    (h : RevertsWith out g m mf o) (hn : out.size ≤ n) : NoEffectOut g n m mf o :=
  ⟨⟨out, h.1, hn⟩, h.2⟩

/-! ## Calldata -/

/-- The calldata word at `off` is a clean address (what solc's ABI decoder accepts). -/
def IsAddressArg (data : ByteArray) (off : Nat) : Prop :=
  ∃ a : Address, Bytes.toWord (readBytes data off 32) = Word.ofAddress a

/-- solc's address validation (`x == x & (2^160 - 1)`) fails on a word that is no address. -/
theorem eq_and_addressMask_of_not {x : Word} (h : ¬ ∃ a : Address, x = Word.ofAddress a) :
    Word.eq x (x &&& 1461501637330902918203684832716283019655932542975#256) = 0#256 := by
  apply eq_of_ne
  intro e
  apply h
  refine ⟨x.setWidth 160, ?_⟩
  apply BitVec.eq_of_toNat_eq
  have he := congrArg BitVec.toNat e
  rw [BitVec.toNat_and] at he
  simp only [Word.ofAddress, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by have := Nat.mod_lt x.toNat (show 0 < 2 ^ 160 by decide); omega)]
  rw [show (1461501637330902918203684832716283019655932542975#256).toNat = 2 ^ 160 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod] at he
  exact he

theorem lt_size_four_one {n : Nat} (h : n < 4) : Word.lt (ofNat n) (BitVec.ofNat 256 4) = 1 := by
  rw [Word.lt_eq_one_iff]; simp only [ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact h

theorem iszero_slt_calldatasize_short {size n : Nat} (h1 : 4 ≤ size) (h2 : size < 4 + n)
    (h3 : n < 2 ^ 255) :
    Word.iszero (Word.slt (BitVec.ofNat 256 size - 4#256) (BitVec.ofNat 256 n)) = 0 := by
  have hx : (BitVec.ofNat 256 size - 4#256).toNat = size - 4 := by
    rw [BitVec.toNat_sub_of_le] <;> simp [BitVec.le_def] <;> omega
  simp only [Word.iszero, Word.slt, Word.ofBool, BitVec.slt_eq_ult, BitVec.msb_eq_decide, hx,
    BitVec.ult, BitVec.toNat_ofNat]
  simp (disch := omega) [Nat.mod_eq_of_lt]
  rw [decide_eq_false (by omega), decide_eq_false (by omega), decide_eq_true (by omega)]
  decide

end Verified.AaveV3.AToken
