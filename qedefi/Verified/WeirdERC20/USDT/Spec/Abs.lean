import QEDefi.ERC20.Spec.Storage
import QEDefi.ERC20.Spec.Instances.USDT
import Verified.WeirdERC20.USDT.Contracts.USDT

/-!
# USDT: the bytecode spec statement

The data `ERC20Spec` is applied to for mainnet `TetherToken` (`contracts/mainnet/USDT/`): the
storage abstraction `usdtAbs`, the dispatcher's selectors `sel`, the decoder `ops` of the admin
entry points and the accounts they name (`opAddrs`), the gas bound `g₀`, and `usdtSpec`, the
statement the bytecode proofs target. The model is `QEDefi.ERC20.Spec.USDT.usdtModel`.

**Layout** (`storageLayout.json`, checked against mainnet in `layout-check.txt`): slot 0 packs
`owner` (bytes 0–19, `ownerField`) and `paused` (byte 20, `pausedField`); `_totalSupply` is slot
1, `balances` slot 2, `basisPointsRate` slot 3, `maximumFee` slot 4, `allowed` slot 5,
`isBlackListed` slot 6 (a `bool` in the low byte of each row, `rowBool`), `name`/`symbol` slots
7/8 (never read by the ERC-20 entry points), `decimals` slot 9, and slot 10 packs
`upgradedAddress` (bytes 0–19) and `deprecated` (byte 20, `deprecatedField`).

**Scope: a live, six-decimal token whose owner is an actor** (`Live`). The abstraction reads the
real state only when `deprecated` is false, `decimals` is `6` and the owner is one of the
actors; otherwise it reads a state with supply `2²⁵⁶`, which no `wf` state has, so every
obligation is vacuous there (`Start.wf`). Why:

* once `deprecate(a)` ran, every entry point forwards to the token at `a`: that is a
  two-contract system (`QEDefi.ERC20.VariantDeprecation`), not this model;
* `setParams` scales the maximum fee by `10 ^ decimals`, the model by `Variant.usdt.feeUnit =
  10⁶` (mainnet USDT has 6 decimals);
* the fee is credited to the owner and `issue`/`redeem` change the owner's balance, so the
  owner's row must be among the rows the abstraction reads and whose distinctness `Sound`
  assumes.

`Sound crypto Act`: the actors' rows of `balances`, `isBlackListed` and `allowed` are pairwise
distinct and none is a fixed slot (`ActorRows`).
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLogic EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.Math

/-! ## Layout -/

/-- `owner`: bytes 0–19 of slot 0. -/
def ownerField : Field := ⟨0#256, 0, 20⟩
/-- `paused`: byte 20 of slot 0. -/
def pausedField : Field := ⟨0#256, 20, 1⟩
/-- `deprecated`: byte 20 of slot 10 (bytes 0–19 hold `upgradedAddress`). -/
def deprecatedField : Field := ⟨10#256, 20, 1⟩
/-- A `bool` mapping value: the low byte of its row. -/
def rowBool : BitField := ⟨0, 8⟩

/-- The slot of `_totalSupply`. -/
def supplySlot : Word := 1
/-- The slot of `balances`. -/
def balancesSlot : Word := 2
/-- The slot of `basisPointsRate`. -/
def bpsSlot : Word := 3
/-- The slot of `maximumFee`. -/
def maxFeeSlot : Word := 4
/-- The slot of `allowed`. -/
def allowedSlot : Word := 5
/-- The slot of `isBlackListed`. -/
def blackSlot : Word := 6
/-- The slot of `decimals`. -/
def decimalsSlot : Word := 9

/-- The fixed slots the abstraction reads. -/
def fixedSlots : List Word := [0, supplySlot, bpsSlot, maxFeeSlot, decimalsSlot, 10]

/-- The owner of the token at `token`. -/
def ownerOf (w : World) (token : Address) : Address :=
  Word.toAddress (ownerField.get (w.sload token 0))

/-- Whether the token is paused. -/
def pausedOf (w : World) (token : Address) : Bool := pausedField.get (w.sload token 0) != 0

/-- Whether `a` is blacklisted, as the actors see it (`false` for other accounts). -/
def blacklistedOf (crypto : Crypto) (Act : Finset Address) (w : World) (token a : Address) :
    Bool :=
  decide (a ∈ Act) &&
    (rowBool.get (w.sload token (mappingSlot crypto (Word.ofAddress a) blackSlot)) != 0)

/-- **The scope of the abstraction**: not deprecated, six decimals, the owner an actor. -/
def Live (Act : Finset Address) (w : World) (token : Address) : Prop :=
  deprecatedField.get (w.sload token 10) = 0 ∧ w.sload token decimalsSlot = 6 ∧
    ownerOf w token ∈ Act

instance (Act : Finset Address) (w : World) (token : Address) : Decidable (Live Act w token) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The token at `token` as the actors see it, in the layout of `TetherToken`. -/
noncomputable def readState (crypto : Crypto) (Act : Finset Address) (w : World)
    (token : Address) : VState Address where
  self := token
  bal := readMap crypto Act w token balancesSlot
  supply := readSlot w token supplySlot
  allowance := readMap2 crypto Act w token allowedSlot
  scale := 1
  admin := ownerOf w token
  paused := pausedOf w token
  blacklisted := blacklistedOf crypto Act w token
  feeBps := readSlot w token bpsSlot
  feeMax := readSlot w token maxFeeSlot
  ether := (w.balance token).toNat
  frozen := 0
  nonces := 0

/-- **USDT as the actors see it**: `readState` when `Live`, otherwise a state outside the
model's invariant (supply `2²⁵⁶`). -/
noncomputable def read (crypto : Crypto) (Act : Finset Address) (w : World) (token : Address) :
    VState Address :=
  if Live Act w token then readState crypto Act w token
  else { readState crypto Act w token with supply := U256 }

/-- The slots `read` depends on: the fixed slots and the actors' rows of the three mappings. -/
def footprint (crypto : Crypto) (Act : Finset Address) (k : Word) : Prop :=
  k ∈ fixedSlots ∨ MapSlots crypto Act balancesSlot k ∨ Map2Slots crypto Act allowedSlot k ∨
    MapSlots crypto Act blackSlot k

theorem readState_congr {crypto : Crypto} {Act : Finset Address} {w w' : World}
    {token : Address} (h : ∀ k, footprint crypto Act k → w'.sload token k = w.sload token k)
    (hb : w'.balance token = w.balance token) :
    readState crypto Act w' token = readState crypto Act w token := by
  have hf : ∀ k ∈ fixedSlots, w'.sload token k = w.sload token k := fun k hk => h k (.inl hk)
  have h0 := hf 0 (by simp [fixedSlots])
  have hblack : blacklistedOf crypto Act w' token = blacklistedOf crypto Act w token := by
    funext a
    simp only [blacklistedOf]
    by_cases ha : a ∈ Act
    · rw [h _ (.inr (.inr (.inr ⟨a, ha, rfl⟩)))]
    · simp [ha]
  simp only [readState, ownerOf, pausedOf, h0, hblack, hb,
    readMap_congr (fun k hk => h k (.inr (.inl hk))),
    readMap2_congr (fun k hk => h k (.inr (.inr (.inl hk)))),
    readSlot_congr (hf supplySlot (by simp [fixedSlots])),
    readSlot_congr (hf bpsSlot (by simp [fixedSlots])),
    readSlot_congr (hf maxFeeSlot (by simp [fixedSlots]))]

theorem live_congr {Act : Finset Address} {w w' : World} {token : Address}
    (h : ∀ k ∈ fixedSlots, w'.sload token k = w.sload token k) :
    Live Act w' token ↔ Live Act w token := by
  simp only [Live, ownerOf, h 0 (by simp [fixedSlots]), h 10 (by simp [fixedSlots]),
    h decimalsSlot (by simp [fixedSlots])]

/-- **USDT's storage abstraction.** -/
noncomputable def usdtAbs : TokenAbs (VState Address) where
  read := read
  footprint := footprint
  read_congr := by
    intro crypto Act w w' token h hb
    simp only [read, live_congr (Act := Act) (fun k hk => h k (.inl hk)), readState_congr h hb]
  Sound crypto Act := ActorRows crypto Act [balancesSlot, blackSlot] [allowedSlot] fixedSlots

/-! ## Selectors, other entry points, gas -/

/-- The dispatcher's selectors (the verified ABI). -/
def sel : List Nat := Contracts.USDT.selectors.map (·.2.toNat)

/-- The `i`-th argument word of the calldata (zero-padded, as `CALLDATALOAD` reads it). -/
def argWord (data : ByteArray) (i : Nat) : Word := Bytes.toWord (Interpreter.readBytes data (4 + 32 * i) 32)

/-- The `i`-th argument as an address (solc 0.4 masks it to its low 160 bits). -/
def argAddr (data : ByteArray) (i : Nat) : Address := Word.toAddress (argWord data i)

/-- **The admin entry points** the model has, decoded as solc 0.4.18's dispatcher does (no
length check: missing argument bytes read as zero; addresses masked): `addBlackList(u)`,
`removeBlackList(u)`, `destroyBlackFunds(u)`, `setParams(bps, max)`, `issue(v)` (a mint to the
caller, which succeeds only for the owner) and `redeem(v)` (a burn from the caller), without
value (they are not payable).

Not decoded: `pause()`/`unpause()` (the model's `setPaused` succeeds for the owner whatever the
current flag, the code reverts on `pause()` when paused and on `unpause()` when not, so they
are not this model's operation), `deprecate`, `transferOwnership` (not in the model), and the
getters. -/
def ops (caller : Address) (data : ByteArray) (value : ℕ) : Option (Variant.Op Address) :=
  if value ≠ 0 ∨ data.size < 4 then none
  else
    let s := Abi.selectorOf data
    if s = 0x0ecb93c0 then some (.setBlacklisted caller (argAddr data 0) true)
    else if s = 0xe4997dc5 then some (.setBlacklisted caller (argAddr data 0) false)
    else if s = 0xf3bdc228 then some (.destroyBlackFunds caller (argAddr data 0))
    else if s = 0xc0324c77 then
      some (.setParams caller (argWord data 0).toNat (argWord data 1).toNat)
    else if s = 0xcc872b66 then some (.mint caller caller (argWord data 0).toNat)
    else if s = 0xdb006a75 then some (.burn caller caller (argWord data 0).toNat)
    else none

/-- The accounts an operation names (besides its caller). -/
def opAddrs : Variant.Op Address → List Address
  | .setBlacklisted _ u _ => [u]
  | .destroyBlackFunds _ u => [u]
  | _ => []

/-- The gas from which every outcome is exact. A `transferFrom` writes up to four rows
(allowance, payer, recipient, owner: at most `4 · 22100` gas) and two logs; `200000` covers it
with room for the unoptimised code. -/
def g₀ : Nat := 200000

/-- **The bytecode spec of USDT**: the deployed runtime code is the USDT model through
`usdtAbs`. -/
abbrev usdtSpec : Prop :=
  ERC20Spec Contracts.USDT.runtimeCode usdtAbs
    (QEDefi.ERC20.Spec.USDT.usdtModel : TokenModel (VState Address) Address (Variant.Op Address))
    g₀ sel ops opAddrs

end Verified.WeirdERC20.USDT.Spec
