import Verified.WeirdERC20.USDT.Spec.MalformedCert
import Verified.WeirdERC20.USDT.Spec.Basic
import Verified.WeirdERC20.BNB.Spec.Views
import Verified.WeirdERC20.STA.Spec.MalformedPrefix
import Verified.WeirdERC20.Common.Entry

/-!
# USDT's dispatcher, modifiers and deprecation branch with any calldata

Symbolic runs of the mainnet USDT code (solc 0.4.18) from a fresh frame, for a token that is not
deprecated (`hdep`, from `Live`):

* `getter_dispatch`: to the dispatch target of a getter, nothing written;
* `X_view` (`totalSupply`, `balanceOf`, `allowance`): through the deprecation branch to the
  view's body, nothing written;
* `X_dirty` (`transfer`, `approve`, `transferFrom`), at any gas, any value, any calldata: the
  frame fails (value, a pause, a blacklisted payer, too few argument words for
  `onlyPayloadSize`, or no gas), or it reaches the body past the last calldata read (`entryS`:
  the arguments decoded, the storage keys read warm); `X_clean`: exactly so, with enough gas;
* `op_value`: an operation's stub, which rejects value.
-/

set_option linter.unusedSimpArgs false

namespace Verified.WeirdERC20.USDT.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.USDT.Contracts
open Verified.WeirdERC20.Common Verified.Solady.Spec.AnyGas
open Verified.WeirdERC20.BNB.Spec (div_selector)
open Verified.WeirdERC20.STA.Spec.Malformed (and_mask_lit mask_lit_and)
open Verified.Common.Malformed (Unchanged)
open EvmLogic.AbsInt

/-! ## Words and states -/

/-- The `i`-th argument word (zero-padded). -/
abbrev aw (d : ByteArray) (i : Nat) : Word := Bytes.toWord (readBytes d (4 + 32 * i) 32)

/-- The `i`-th argument as a masked address word. -/
abbrev aa (d : ByteArray) (i : Nat) : Word := Word.ofAddress (Word.toAddress (aw d i))

/-- `deprecated`, `paused` as the code reads them (byte 20 of slots 10 and 0). -/
abbrev byte20 (w : World) (t : Address) (k : Word) : Word :=
  255#256 &&& (w.sload t k).div 1461501637330902918203684832716283019655932542976#256

/-- `isBlackListed[a]` as the code reads it. -/
abbrev blackB (crypto : Crypto) (w : World) (t : Address) (a : Word) : Word :=
  255#256 &&& (w.sload t (crypto.keccak256 (Bytes.ofWord a ++ Bytes.ofWord 6#256))).div 1#256

/-- The memory after the blacklist lookup of `a`. -/
def memB (a : Word) : Memory :=
  ((((((({} : Memory).expand 64 32).storeWord 64 96#256).expand 0 32).storeWord 0 a).expand
    32 32).storeWord 32 6#256).expand 0 64

/-- The memory after solc 0.4's prologue. -/
def mem60 : Memory := (({} : Memory).expand 64 32).storeWord 64 96#256

/-- The substate after reading `paused`, the blacklist row of `a` and `deprecated`. -/
def subB (m : Machine) (a : Word) : Substate :=
  ((m.frame.sub.warmKey m.frame.msg.currentTarget 0#256).warmKey m.frame.msg.currentTarget
    (m.ctx.crypto.keccak256 (Bytes.ofWord a ++ Bytes.ofWord 6#256))).warmKey
      m.frame.msg.currentTarget 10#256

/-- The substate after reading `deprecated`. -/
def subD (m : Machine) : Substate := m.frame.sub.warmKey m.frame.msg.currentTarget 10#256

/-- `transfer`'s stack past `onlyPayloadSize`. -/
def stT (d : ByteArray) : List Word :=
  [64#256, 0#256, 0#256, aw d 1, aa d 0, 5785#256, aw d 1, aa d 0, 1930#256, 2835717307#256]

/-- `approve`'s stack past `onlyPayloadSize`. -/
def stA (d : ByteArray) : List Word :=
  [64#256, aw d 1, aa d 0, 3259#256, 64#256, aw d 1, aa d 0, 674#256, 157198259#256]

/-- `transferFrom`'s stack past `onlyPayloadSize`. -/
def stF (d : ByteArray) : List Word :=
  [96#256, 0#256, 0#256, 0#256, aw d 2, aa d 1, aa d 0, 4247#256, aw d 2, aa d 1, aa d 0, 914#256,
    599290589#256]

theorem iszero3 {x : Word} (h : x.iszero.iszero.iszero ≠ 0) : x = 0 := by
  by_contra hx
  apply h
  have h1 : x.iszero = 0 := iszero_of_ne hx
  rw [h1]; decide

theorem size_of_lt3 {n k : Nat} (hn : n < 2 ^ 64) (hk : k < 2 ^ 64)
    (h : ((ofNat n).lt (BitVec.ofNat 256 k)).iszero.iszero.iszero ≠ 0) : k ≤ n := by
  have h0 := iszero3 h
  by_contra hc
  have : (ofNat n : Word).lt (BitVec.ofNat 256 k) = 1 := by
    simp only [Word.lt, Word.ofBool, ofNat, BitVec.ult, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp; omega
  rw [this] at h0
  exact absurd h0 (by decide)

theorem lt_size_zero {n k : Nat} (h : k ≤ n) (hn : n < 2 ^ 64) (hk : k < 2 ^ 64) :
    (ofNat n : Word).lt (BitVec.ofNat 256 k) = 0 := by
  simp only [Word.lt, Word.ofBool, ofNat, BitVec.ult, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  simp; omega

/-! ## Getters and views -/

/-- The dispatcher's run to a getter's dispatch target. -/
def AtGetter (m : Machine) (q : Nat) (sel : Nat) (s : Machine) : Prop :=
  s.frame.pc = q ∧ s.frame.stack = [BitVec.ofNat 256 sel] ∧ s.frame.code = USDT.runtimeCode ∧
    Unchanged m s

set_option maxHeartbeats 0 in
theorem getter_dispatch {sel q : Nat} (hge : (sel, q) ∈ getterEntries) (m : Machine)
    (hf : Fresh USDT.runtimeCode m) (hsel : Abi.selectorOf m.frame.msg.data = sel)
    (h4 : 4 ≤ m.frame.msg.data.size) (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (AtGetter m q sel) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  simp only [getterEntries, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hge
  rcases hge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    solady_fresh_intro
    hwp_steps stop_at [0x019b, 0x02a4, 0x0394, 0x03e9, 0x0436, 0x045f, 0x0488, 0x04c6, 0x0517,
      0x0583, 0x0612, 0x0667, 0x06bc, 0x086a, 0x0893, 0x091d] [hsel', hz]
    exact WP.ret ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A view's run to its body past the deprecation branch: a machine of the getters' region. -/
def AtView (m : Machine) (s : Machine) : Prop :=
  InCert (fun _ => 0) usdtGetters s ∧ s.frame.code = USDT.runtimeCode ∧ Unchanged m s

set_option maxHeartbeats 0 in
/-- `totalSupply`'s dispatcher and deprecation branch, at any gas, with any value and calldata. -/
theorem totalSupply_view (m : Machine) (hf : Fresh USDT.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x18160ddd) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hdep : byte20 m.world m.frame.msg.currentTarget 10#256 = 0) :
    WP m (AtView m) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  solady_fresh_intro
  hwp_steps stop_at [0x0eb4] [hsel', hz, hdep, and_mask_lit, mask_lit_and, Word.toAddress_ofAddress]
  exact WP.ret ⟨⟨[.top, .const 797, .top], usdtGetters_seed (by simp [getterSeeds, viewSeeds]), ⟨trivial, rfl, trivial, trivial⟩⟩, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 0 in
/-- `balanceOf`'s dispatcher and deprecation branch, at any gas, with any value and calldata. -/
theorem balanceOf_view (m : Machine) (hf : Fresh USDT.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x70a08231) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hdep : byte20 m.world m.frame.msg.currentTarget 10#256 = 0) :
    WP m (AtView m) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  solady_fresh_intro
  hwp_steps stop_at [0x1337] [hsel', hz, hdep, and_mask_lit, mask_lit_and, Word.toAddress_ofAddress]
  exact WP.ret ⟨⟨[.top, .top, .const 1511, .top], usdtGetters_seed (by simp [getterSeeds, viewSeeds]), ⟨trivial, trivial, rfl, trivial, trivial⟩⟩, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 0 in
/-- `allowance`'s dispatcher and deprecation branch, at any gas, with any value and calldata. -/
theorem allowance_view (m : Machine) (hf : Fresh USDT.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xdd62ed3e) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hdep : byte20 m.world m.frame.msg.currentTarget 10#256 = 0) :
    WP m (AtView m) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  solady_fresh_intro
  hwp_steps stop_at [0x1c3f] [hsel', hz, hdep, and_mask_lit, mask_lit_and, Word.toAddress_ofAddress]
  exact WP.ret ⟨⟨[.top, .top, .top, .const 2132, .top], usdtGetters_seed (by simp [getterSeeds, viewSeeds]), ⟨trivial, trivial, trivial, rfl, trivial, trivial⟩⟩, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 0 in
/-- `transfer`'s dispatcher, modifiers and deprecation branch, at any gas, with any value and
calldata. -/
theorem transfer_dirty (m : Machine) (hf : Fresh USDT.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xa9059cbb) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hdep : byte20 m.world m.frame.msg.currentTarget 10#256 = 0) :
    WP m (fun s => s = entryS (subB m (Word.ofAddress m.frame.msg.caller)) (memB (Word.ofAddress m.frame.msg.caller)) m 0x26b6 (stT m.frame.msg.data) s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0 ∧
      68 ≤ m.frame.msg.data.size ∧
      byte20 m.world m.frame.msg.currentTarget 0#256 = 0 ∧
      blackB m.ctx.crypto m.world m.frame.msg.currentTarget (Word.ofAddress m.frame.msg.caller) = 0) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [0x26b6] [hsel', hz, hdep, and_mask_lit, mask_lit_and, Word.toAddress_ofAddress]
  refine WP.ret ⟨by simp only [entryS, subB, subD, memB, mem60, stT], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›,
    size_of_lt3 (k := 68) hsz (by norm_num) ‹_›, iszero3 ‹_›, iszero3 ‹_›⟩

set_option maxHeartbeats 0 in
/-- `transfer`'s dispatcher, modifiers and deprecation branch, exactly. -/
theorem transfer_clean (m : Machine) (hf : Fresh USDT.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xa9059cbb) (hsize : 68 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft)
    (hdep : byte20 m.world m.frame.msg.currentTarget 10#256 = 0) (hpause : byte20 m.world m.frame.msg.currentTarget 0#256 = 0)
    (hblack : blackB m.ctx.crypto m.world m.frame.msg.currentTarget (Word.ofAddress m.frame.msg.caller) = 0) :
    WP m (fun s => s = entryS (subB m (Word.ofAddress m.frame.msg.caller)) (memB (Word.ofAddress m.frame.msg.caller)) m 0x26b6 (stT m.frame.msg.data) s.frame.gasLeft ∧
      m.frame.gasLeft - 10000 ≤ s.frame.gasLeft) (fun _ _ => False) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := lt_size_zero (n := m.frame.msg.data.size) (k := 68) hsize hsz (by norm_num)
  solady_fresh_intro
  pwp_run_to 0x26b6 [hval, hsel', hz, hl, hdep, hpause, hblack, and_mask_lit, mask_lit_and, Memory.read_64,
    Word.toAddress_ofAddress]
  refine WP.ret ⟨by simp only [entryS, subB, subD, memB, mem60, stT], ?_⟩
  evm_gas

set_option maxHeartbeats 0 in
/-- `approve`'s dispatcher, modifiers and deprecation branch, at any gas, with any value and
calldata. -/
theorem approve_dirty (m : Machine) (hf : Fresh USDT.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x095ea7b3) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hdep : byte20 m.world m.frame.msg.currentTarget 10#256 = 0) :
    WP m (fun s => s = entryS (subD m) (mem60) m 0x2026 (stA m.frame.msg.data) s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0 ∧
      68 ≤ m.frame.msg.data.size) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [0x2026] [hsel', hz, hdep, and_mask_lit, mask_lit_and, Word.toAddress_ofAddress]
  refine WP.ret ⟨by simp only [entryS, subB, subD, memB, mem60, stA], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›,
    size_of_lt3 (k := 68) hsz (by norm_num) ‹_›⟩

set_option maxHeartbeats 0 in
/-- `approve`'s dispatcher, modifiers and deprecation branch, exactly. -/
theorem approve_clean (m : Machine) (hf : Fresh USDT.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x095ea7b3) (hsize : 68 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft)
    (hdep : byte20 m.world m.frame.msg.currentTarget 10#256 = 0) :
    WP m (fun s => s = entryS (subD m) (mem60) m 0x2026 (stA m.frame.msg.data) s.frame.gasLeft ∧
      m.frame.gasLeft - 10000 ≤ s.frame.gasLeft) (fun _ _ => False) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := lt_size_zero (n := m.frame.msg.data.size) (k := 68) hsize hsz (by norm_num)
  solady_fresh_intro
  pwp_run_to 0x2026 [hval, hsel', hz, hl, hdep, and_mask_lit, mask_lit_and, Memory.read_64,
    Word.toAddress_ofAddress]
  refine WP.ret ⟨by simp only [entryS, subB, subD, memB, mem60, stA], ?_⟩
  evm_gas

set_option maxHeartbeats 0 in
/-- `transferFrom`'s dispatcher, modifiers and deprecation branch, at any gas, with any value and
calldata. -/
theorem transferFrom_dirty (m : Machine) (hf : Fresh USDT.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x23b872dd) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hdep : byte20 m.world m.frame.msg.currentTarget 10#256 = 0) :
    WP m (fun s => s = entryS (subB m (aa m.frame.msg.data 0)) (memB (aa m.frame.msg.data 0)) m 0x21c8 (stF m.frame.msg.data) s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0 ∧
      100 ≤ m.frame.msg.data.size ∧
      byte20 m.world m.frame.msg.currentTarget 0#256 = 0 ∧
      blackB m.ctx.crypto m.world m.frame.msg.currentTarget (aa m.frame.msg.data 0) = 0) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [0x21c8] [hsel', hz, hdep, and_mask_lit, mask_lit_and, Word.toAddress_ofAddress]
  refine WP.ret ⟨by simp only [entryS, subB, subD, memB, mem60, stF], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›,
    size_of_lt3 (k := 100) hsz (by norm_num) ‹_›, iszero3 ‹_›, iszero3 ‹_›⟩

set_option maxHeartbeats 0 in
/-- `transferFrom`'s dispatcher, modifiers and deprecation branch, exactly. -/
theorem transferFrom_clean (m : Machine) (hf : Fresh USDT.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x23b872dd) (hsize : 100 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft)
    (hdep : byte20 m.world m.frame.msg.currentTarget 10#256 = 0) (hpause : byte20 m.world m.frame.msg.currentTarget 0#256 = 0)
    (hblack : blackB m.ctx.crypto m.world m.frame.msg.currentTarget (aa m.frame.msg.data 0) = 0) :
    WP m (fun s => s = entryS (subB m (aa m.frame.msg.data 0)) (memB (aa m.frame.msg.data 0)) m 0x21c8 (stF m.frame.msg.data) s.frame.gasLeft ∧
      m.frame.gasLeft - 10000 ≤ s.frame.gasLeft) (fun _ _ => False) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := lt_size_zero (n := m.frame.msg.data.size) (k := 100) hsize hsz (by norm_num)
  solady_fresh_intro
  pwp_run_to 0x21c8 [hval, hsel', hz, hl, hdep, hpause, hblack, and_mask_lit, mask_lit_and, Memory.read_64,
    Word.toAddress_ofAddress]
  refine WP.ret ⟨by simp only [entryS, subB, subD, memB, mem60, stF], ?_⟩
  evm_gas

/-- The operations' selectors with their stubs' targets past the value check. -/
def opEntries : List (Nat × Nat) :=
  [(0x0ecb93c0, 0x02dc), (0x3f4ba83a, 0x04bc), (0x8456cb59, 0x0608), (0xc0324c77, 0x0797),
    (0xcc872b66, 0x07c3), (0xdb006a75, 0x07e6), (0xe4997dc5, 0x08ef), (0xf3bdc228, 0x098a)]

set_option maxHeartbeats 0 in
/-- An operation's stub rejects value: the frame fails, or it has no value. -/
theorem op_value {sel q : Nat} (hge : (sel, q) ∈ opEntries) (m : Machine)
    (hf : Fresh USDT.runtimeCode m) (hsel : Abi.selectorOf m.frame.msg.data = sel)
    (h4 : 4 ≤ m.frame.msg.data.size) (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun _ => m.frame.msg.value = 0) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  simp only [opEntries, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hge
  rcases hge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    solady_fresh_intro
    hwp_steps stop_at [0x02dc, 0x04bc, 0x0608, 0x0797, 0x07c3, 0x07e6, 0x08ef, 0x098a]
      [hsel', hz]
    exact WP.ret (Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›)

end Verified.WeirdERC20.USDT.Spec.Malformed
