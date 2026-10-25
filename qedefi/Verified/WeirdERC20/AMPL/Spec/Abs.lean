import QEDefi.ERC20.Spec.Storage
import QEDefi.ERC20.Spec.Instances.AMPL
import Verified.WeirdERC20.AMPL.Contracts.AMPL

/-!
# AMPL (`UFragments`) under the ERC-20 spec: the abstraction and the statement

`amplSpec : Prop` is `ERC20Spec` for the `UFragments` implementation code (solc 0.7.6,
`Verified.WeirdERC20.AMPL.Contracts.AMPL.runtimeCode`) against `amplModel`
(`QEDefi.ERC20.Spec.Instances.AMPL`), through `amplAbs`.

**Behind the proxy.** AMPL's address holds the zos `AdminUpgradeabilityProxy`
(`…Contracts.AMPLProxy`), whose fallback `DELEGATECALL`s the implementation. The spec is stated
for the *implementation code running in any fresh frame*: `ERC20Spec` quantifies over every
frame whose code is `AMPL.runtimeCode`, at any executing address, and a `DELEGATECALL` child
(`delegateChild`) is such a frame, executing at the proxy's address with the proxy's storage,
the original `CALLER` and `CALLVALUE`, and no value transfer of its own (so `Start.launched`
holds). `token` in `amplAbs.read` is therefore the proxy's address and the slots below are the
proxy's storage. What the proxy's dispatch theorem must add to make this a theorem about calls
to AMPL's address: for every caller other than the proxy admin (the admin's calls are answered
by the proxy itself and never reach the token), the proxy frame `DELEGATECALL`s the address in
its implementation slot (pre-EIP-1967 zos slot
`keccak256("org.zeppelinos.proxy.implementation")`) with its whole calldata and all but the
proxy's own gas costs, that address holds `AMPL.runtimeCode`, and the proxy returns or reverts
with exactly the child's output, keeping the child's world, logs and transient storage. With
that, `ERC20Spec` of the implementation is the token's behaviour at the proxy (as Aave's aToken
proxy, `forward_halts`). The proxy's own slots (admin, implementation) are outside the
implementation's footprint and are never written by it.

**Storage** (`contracts/mainnet/AMPL/storageLayout.json`, the proxy's storage): `initialized`
… 0–154, `monetaryPolicy` 155 (an address in the low 160 bits; two deprecated flags above it),
`_totalSupply` 156, `_gonsPerFragment` 157, `_gonBalances` 158, `_allowedFragments` 159,
`_nonces` 160. The model state, for the actors `Act`: their gon balances (`bal`, with
`balanceOf = gons / scale`), the allowances between them (in fragments), their nonces, the
supply, `_gonsPerFragment` as `scale`, the monetary policy as the privileged account (`admin`,
who alone may `rebase`); `ether` is the balance of the executing address.

`amplSound crypto Act`: the actors' rows of `_gonBalances`, `_nonces` and `_allowedFragments`
are pairwise distinct and avoid slots 155–157 (`ActorRows`).

**Other entry points** (`amplOps`): `transferAll(to)`, `transferAllFrom(from, to)`,
`increaseAllowance(sp, x)`, `decreaseAllowance(sp, x)`, with clean address arguments and no
value. Not decoded: `rebase(epoch, supplyDelta)` (the model's `rebase` takes the new supply,
while the call carries a signed delta from the current one, which a decoder of the calldata
alone cannot turn into it; a decoder over the state would be needed), and the owner's
`setMonetaryPolicy`/`transferOwnership`/`renounceOwnership` and `initialize`, which change
state the model does not have (the owner) or the monetary policy without a model operation.
-/

namespace Verified.WeirdERC20.AMPL.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec
open QEDefi.ERC20.Spec.AMPL Verified.WeirdERC20.AMPL.Contracts

/-- The model state of AMPL in the storage of `token` (the proxy) in `w`, for the actors
`Act`. -/
noncomputable def amplRead (crypto : Crypto) (Act : Finset Address) (w : World)
    (token : Address) : VState Address where
  self := token
  bal := readMap crypto Act w token 158#256
  supply := readSlot w token 156#256
  allowance := readMap2 crypto Act w token 159#256
  scale := readSlot w token 157#256
  admin := (w.sload token 155#256).toAddress
  paused := false
  blacklisted := fun _ => false
  feeBps := 0
  feeMax := 0
  ether := (w.balance token).toNat
  frozen := 0
  nonces := readMap crypto Act w token 160#256

/-- The slots `amplRead` reads: the monetary policy, supply, gons per fragment and the actors'
rows. -/
def amplFootprint (crypto : Crypto) (Act : Finset Address) (k : Word) : Prop :=
  k = 155#256 ∨ k = 156#256 ∨ k = 157#256 ∨ MapSlots crypto Act 158#256 k ∨
    Map2Slots crypto Act 159#256 k ∨ MapSlots crypto Act 160#256 k

/-- The hash hypotheses: the actors' rows are distinct and avoid the fixed slots. -/
def amplSound (crypto : Crypto) (Act : Finset Address) : Prop :=
  ActorRows crypto Act [158#256, 160#256] [159#256] [155#256, 156#256, 157#256]

theorem amplRead_congr (crypto : Crypto) (Act : Finset Address) (w w' : World) (token : Address)
    (h : ∀ k, amplFootprint crypto Act k → w'.sload token k = w.sload token k)
    (hb : w'.balance token = w.balance token) :
    amplRead crypto Act w' token = amplRead crypto Act w token := by
  unfold amplRead
  rw [readMap_congr (fun k hk => h k (.inr (.inr (.inr (.inl hk))))),
    readMap2_congr (fun k hk => h k (.inr (.inr (.inr (.inr (.inl hk)))))),
    readMap_congr (fun k hk => h k (.inr (.inr (.inr (.inr (.inr hk)))))),
    readSlot_congr (h _ (.inr (.inl rfl))), readSlot_congr (h _ (.inr (.inr (.inl rfl)))),
    h _ (.inl rfl), hb]

/-- **The storage abstraction of AMPL** (in the proxy's storage). -/
noncomputable def amplAbs : TokenAbs (VState Address) where
  read := amplRead
  footprint := amplFootprint
  read_congr := amplRead_congr
  Sound := amplSound

/-! ## The statement -/

/-- The model. -/
noncomputable abbrev M : TokenModel (VState Address) Address (Variant.Op Address) := amplModel

/-- The gas from which every obligation is exact. -/
def g₀ : Nat := 100000

/-- The dispatcher's selectors (`AMPL.selectors`). -/
def sel : List Nat := AMPL.selectors.map (·.2.toNat)

/-- The `i`-th argument word of `data`. -/
def argWord (data : ByteArray) (i : Nat) : Word := Bytes.toWord (readBytes data (4 + 32 * i) 32)

/-- An address argument word, if it is clean (solc 0.7 reverts on dirty ones). -/
def addrArg (x : Word) : Option Address := if x.toNat < 2 ^ 160 then some x.toAddress else none

/-- **The other entry points**: `transferAll(to)`, `transferAllFrom(from, to)`,
`increaseAllowance(sp, x)`, `decreaseAllowance(sp, x)`, well-formed arguments, no value. -/
def amplOps (caller : Address) (data : ByteArray) (value : ℕ) : Option (Variant.Op Address) :=
  if value ≠ 0 ∨ data.size < 36 then none
  else if Abi.selectorOf data = 0xa3a7e7f3 then
    (addrArg (argWord data 0)).map fun a => .transferAll caller a
  else if data.size < 68 then none
  else if Abi.selectorOf data = 0x84d4b410 then
    (addrArg (argWord data 0)).bind fun a =>
      (addrArg (argWord data 1)).map fun b => .transferAllFrom caller a b
  else if Abi.selectorOf data = 0x39509351 then
    (addrArg (argWord data 0)).map fun a => .adjustAllowance caller a true (argWord data 1).toNat
  else if Abi.selectorOf data = 0xa457c2d7 then
    (addrArg (argWord data 0)).map fun a => .adjustAllowance caller a false (argWord data 1).toNat
  else none

/-- The accounts an operation names. -/
def amplOpAddrs : Variant.Op Address → List Address
  | .transferAll _ a => [a]
  | .transferAllFrom _ a b => [a, b]
  | .adjustAllowance _ a _ _ => [a]
  | _ => []

/-- **The bytecode spec of AMPL's implementation**, running in the proxy's storage. -/
abbrev amplSpec : Prop := ERC20Spec AMPL.runtimeCode amplAbs M g₀ sel amplOps amplOpAddrs

end Verified.WeirdERC20.AMPL.Spec
