import Verified.AaveV3.AToken.Basic

/-!
# `AToken`: the scaled ledger in storage, the address immutables

What the views return, as functions of the executing account's storage (the proxy's, under
`DELEGATECALL`): `userStateSlot`, `scaledBalance` (low 120 bits of `_userState[a]`),
`previousIndex` (its high 128 bits), `scaledTotalSupply` (slot 54), `underlyingAsset` (slot 61);
the immutables `treasury`, `rewardsController`; the postcondition `Returns`; and the word
identities that turn solc's masks into these forms.
-/

namespace Verified.AaveV3.AToken
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Verified.AaveV3.Contracts
open Verified.Solmate.ERC20 (lt_size_four)

/-! ## Storage reads -/

/-- The slot of `_userState[a]`: `keccak(pad(a) ‖ pad(52))`. -/
def userStateSlot (crypto : Crypto) (a : Address) : Word :=
  crypto.keccak256 (Bytes.ofWord (Word.ofAddress a) ++ Bytes.ofWord 52#256)

/-- `a`'s scaled balance at `token`: the low 120 bits of `_userState[a]` (`uint120 balance`). -/
def scaledBalance (crypto : Crypto) (w : World) (token a : Address) : Word :=
  BitVec.ofNat 256 ((w.sload token (userStateSlot crypto a)).toNat % 2 ^ 120)

/-- `a`'s previous index at `token`: the high 128 bits of `_userState[a]`
(`uint128 additionalData`). -/
def previousIndex (crypto : Crypto) (w : World) (token a : Address) : Word :=
  BitVec.ofNat 256 ((w.sload token (userStateSlot crypto a)).toNat / 2 ^ 128)

/-- The scaled total supply at `token`: slot 54 (`_totalSupply`). -/
def scaledTotalSupply (w : World) (token : Address) : Word := w.sload token 54#256

/-- The underlying asset of `token`: the low 160 bits of slot 61 (`_underlyingAsset`). -/
def underlyingAsset (w : World) (token : Address) : Word :=
  BitVec.ofNat 256 ((w.sload token 61#256).toNat % 2 ^ 160)

/-- The treasury, the immutable `TREASURY`. -/
def treasury : Address := 0x464C71f6c2F760DdA6093dCB91C24c39e5d6e18c

/-- The rewards controller, the immutable `REWARDS_CONTROLLER`. -/
def rewardsController : Address := 0x8164Cc65827dcFe994AB23944CBC90e0aa80bFcb

/-! ## The packed `_userState` word as bit fields

`_userState[a]` packs `uint120 balance` (bits 0–119), a delegation byte (bits 120–127) and
`uint128 additionalData` (the previous index, bits 128–255): the bit fields `balanceField`,
`delegationField`, `indexField` (`EvmLogic.Solidity.BitField`). -/

/-- `_userState[a].balance`: the low 120 bits. -/
def balanceField : BitField := ⟨0, 120⟩

/-- The delegation-state byte above the balance (bits 120–127). -/
def delegationField : BitField := ⟨120, 8⟩

/-- `_userState[a].additionalData` (the previous index): the high 128 bits. -/
def indexField : BitField := ⟨128, 128⟩

theorem balanceField_valid : balanceField.Valid := by decide
theorem indexField_valid : indexField.Valid := by decide
theorem balance_index_disjoint : BitField.Disjoint balanceField indexField := by decide
theorem balance_delegation_disjoint : BitField.Disjoint balanceField delegationField := by decide
theorem index_balance_disjoint : BitField.Disjoint indexField balanceField := by decide
theorem index_delegation_disjoint : BitField.Disjoint indexField delegationField := by decide

/-- `1329…575 &&& v` (solc's `uint120` mask) is `balanceField.get v`. -/
theorem mask120_and_eq_get (v : Word) :
    1329227995784915872903807060280344575#256 &&& v = balanceField.get v := by
  simp only [BitField.get, balanceField, BitField.mask, BitVec.ushiftRight_zero]
  rw [BitVec.and_comm]

theorem mask120_and (x : Word) :
    1329227995784915872903807060280344575#256 &&& x = BitVec.ofNat 256 (x.toNat % 2 ^ 120) := by
  rw [mask120_and_eq_get, BitField.get_eq_ofNat _ (by decide)]
  simp [balanceField]

theorem mask128_and_div (x : Word) :
    340282366920938463463374607431768211455#256 &&&
        x.div 340282366920938463463374607431768211456#256 =
      BitVec.ofNat 256 (x.toNat / 2 ^ 128) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  rw [BitVec.toNat_and, Nat.and_comm,
    show (340282366920938463463374607431768211455#256).toNat = 2 ^ 128 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Word.div, BitVec.toNat_udiv,
    show (340282366920938463463374607431768211456#256).toNat = 2 ^ 128 from rfl,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem mask160_and_and (x : Word) :
    1461501637330902918203684832716283019655932542975#256 &&& x &&&
        1461501637330902918203684832716283019655932542975#256 =
      BitVec.ofNat 256 (x.toNat % 2 ^ 160) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_and,
    show (1461501637330902918203684832716283019655932542975#256).toNat = 2 ^ 160 - 1 from rfl,
    Nat.and_comm (2 ^ 160 - 1), Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod, BitVec.toNat_ofNat]
  omega

/-- The view selectors are those of the verified ABI. -/
theorem viewSelectors_abi :
    ("scaledBalanceOf(address)", (0x1da24f3e : UInt32)) ∈ AToken.selectors ∧
    ("scaledTotalSupply()", (0xb1bf962d : UInt32)) ∈ AToken.selectors ∧
    ("getScaledUserBalanceAndSupply(address)", (0x0afbcdc9 : UInt32)) ∈ AToken.selectors ∧
    ("getPreviousIndex(address)", (0xe0753986 : UInt32)) ∈ AToken.selectors ∧
    ("POOL()", (0x7535d246 : UInt32)) ∈ AToken.selectors ∧
    ("TREASURY()", (0x2d2c5565 : UInt32)) ∈ AToken.selectors ∧
    ("RESERVE_TREASURY_ADDRESS()", (0xae167335 : UInt32)) ∈ AToken.selectors ∧
    ("REWARDS_CONTROLLER()", (0xcd086d45 : UInt32)) ∈ AToken.selectors ∧
    ("UNDERLYING_ASSET_ADDRESS()", (0xb16a19de : UInt32)) ∈ AToken.selectors := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The immutables as recorded for the deployment. -/
theorem immutables_eq :
    ("TREASURY", Word.ofAddress treasury) ∈ AToken.immutableValues ∧
    ("POOL", Word.ofAddress pool) ∈ AToken.immutableValues ∧
    ("REWARDS_CONTROLLER", Word.ofAddress rewardsController) ∈ AToken.immutableValues := by
  decide

/-! ## Postconditions -/

/-- The frame returns `out`, having changed nothing, using at most `g` gas. -/
def Returns (out : ByteArray) (g : Nat) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success out ∧ Unchanged m mf ∧ m.frame.gasLeft ≤ mf.frame.gasLeft + g

end Verified.AaveV3.AToken
