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
(byte 0) and `initializing` (byte 1) in slot 0, `_name`/`_symbol`/`_decimals` 51–53, the owner
104 (`Ownable._owner`), `monetaryPolicy` 155 (an address in the low 160 bits; two deprecated
flags above it), `_totalSupply` 156, `_gonsPerFragment` 157, `_gonBalances` 158,
`_allowedFragments` 159, `_nonces` 160. The model state (`AState`), for the actors `Act`: their
gon balances (`bal`, with `balanceOf = gons / scale`), the allowances between them (in
fragments), their nonces, the supply, `_gonsPerFragment` as `scale`, the monetary policy as the
privileged account (`admin`, who alone may `rebase`), the owner (who alone may set the monetary
policy and pass ownership on); `ether` is the balance of the executing address.

**Scope: an initialized instance** (`Live`: `initialized` set, `initializing` clear). The
abstraction reads the real supply only when `Live`; otherwise it reads supply `0`, which no
`wf` state has, so every obligation is vacuous there (`Start.wf`), as USDT's `Live`. Why: the
two `initializer` functions (`initialize(address)`, `initialize(string,string,uint8)`) run
while `initialized` is clear (or `initializing` set, or the executing address has no code) and
write the name, symbol, decimals, owner, supply and the owner's whole `TOTAL_GONS`; on a deployed
instance they always revert, and they are no operation of the model.

`amplSound crypto Act`: the actors' rows of `_gonBalances`, `_nonces` and `_allowedFragments`
are pairwise distinct and avoid slots 0, 104 and 155–157 (`ActorRows`).

**Other entry points** (`amplOps`): `transferAll(to)`, `transferAllFrom(from, to)`,
`increaseAllowance(sp, x)`, `decreaseAllowance(sp, x)` (operations of `Variant.ampl`, `.base`),
`setMonetaryPolicy(p)`, `transferOwnership(o)`, `renounceOwnership()` and `rebase(epoch, Δ)` (the
signed delta `Δ` read as an `int256`), with clean address arguments and no value. Not decoded:
the two `initialize` functions (out of the scope above).
-/

namespace Verified.WeirdERC20.AMPL.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec
open QEDefi.ERC20.Spec.AMPL Verified.WeirdERC20.AMPL.Contracts

/-- **The scope**: an initialized instance (slot 0: `initialized` byte `1`, `initializing`
byte `0`). -/
def Live (w : World) (token : Address) : Prop := w.sload token 0#256 &&& 0xffff#256 = 1#256

instance (w : World) (token : Address) : Decidable (Live w token) :=
  inferInstanceAs (Decidable (_ = _))

/-- The model state of AMPL in the storage of `token` (the proxy) in `w`, for the actors
`Act` (supply `0` outside the scope `Live`). -/
noncomputable def amplRead (crypto : Crypto) (Act : Finset Address) (w : World)
    (token : Address) : AState Address where
  self := token
  bal := readMap crypto Act w token 158#256
  supply := if Live w token then readSlot w token 156#256 else 0
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
  owner := (w.sload token 104#256).toAddress

/-- The slots `amplRead` reads: the monetary policy, supply, gons per fragment, the actors'
rows, the initialization flags and the owner. -/
def amplFootprint (crypto : Crypto) (Act : Finset Address) (k : Word) : Prop :=
  k = 155#256 ∨ k = 156#256 ∨ k = 157#256 ∨ MapSlots crypto Act 158#256 k ∨
    Map2Slots crypto Act 159#256 k ∨ MapSlots crypto Act 160#256 k ∨ k = 0#256 ∨ k = 104#256

/-- The hash hypotheses: the actors' rows are distinct and avoid the fixed slots. -/
def amplSound (crypto : Crypto) (Act : Finset Address) : Prop :=
  ActorRows crypto Act [158#256, 160#256] [159#256] [155#256, 156#256, 157#256, 0#256, 104#256]

theorem amplRead_congr (crypto : Crypto) (Act : Finset Address) (w w' : World) (token : Address)
    (h : ∀ k, amplFootprint crypto Act k → w'.sload token k = w.sload token k)
    (hb : w'.balance token = w.balance token) :
    amplRead crypto Act w' token = amplRead crypto Act w token := by
  have h0 := h _ (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))))
  have h104 := h _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl)))))))
  unfold amplRead
  rw [readMap_congr (fun k hk => h k (.inr (.inr (.inr (.inl hk))))),
    readMap2_congr (fun k hk => h k (.inr (.inr (.inr (.inr (.inl hk)))))),
    readMap_congr (fun k hk => h k (.inr (.inr (.inr (.inr (.inr (.inl hk))))))),
    readSlot_congr (h _ (.inr (.inl rfl))), readSlot_congr (h _ (.inr (.inr (.inl rfl)))),
    h _ (.inl rfl)]
  simp only [Live, h0, h104, hb]
  congr 1

/-- **The storage abstraction of AMPL** (in the proxy's storage). -/
noncomputable def amplAbs : TokenAbs (AState Address) where
  read := amplRead
  footprint := amplFootprint
  read_congr := amplRead_congr
  Sound := amplSound

/-! ## The statement -/

/-- The model. -/
noncomputable abbrev M : TokenModel (AState Address) Address (AmplOp Address) := amplModel

/-- The gas from which every obligation is exact. -/
def g₀ : Nat := 100000

/-- The dispatcher's selectors (`AMPL.selectors`). -/
def sel : List Nat := AMPL.selectors.map (·.2.toNat)

/-- The `i`-th argument word of `data`. -/
def argWord (data : ByteArray) (i : Nat) : Word := Bytes.toWord (readBytes data (4 + 32 * i) 32)

/-- An address argument word, if it is clean (solc 0.7 reverts on dirty ones). -/
def addrArg (x : Word) : Option Address := if x.toNat < 2 ^ 160 then some x.toAddress else none

/-- **The other entry points**: `renounceOwnership()`, `transferAll(to)`,
`setMonetaryPolicy(p)`, `transferOwnership(o)`, `transferAllFrom(from, to)`,
`increaseAllowance(sp, x)`, `decreaseAllowance(sp, x)`, `rebase(epoch, Δ)`, well-formed
arguments, no value. -/
def amplOps (caller : Address) (data : ByteArray) (value : ℕ) : Option (AmplOp Address) :=
  if value ≠ 0 ∨ data.size < 4 then none
  else if Abi.selectorOf data = 0x715018a6 then some (.renounceOwnership caller)
  else if data.size < 36 then none
  else if Abi.selectorOf data = 0xa3a7e7f3 then
    (addrArg (argWord data 0)).map fun a => .base (.transferAll caller a)
  else if Abi.selectorOf data = 0x8b5a6a08 then
    (addrArg (argWord data 0)).map fun p => .setMonetaryPolicy caller p
  else if Abi.selectorOf data = 0xf2fde38b then
    (addrArg (argWord data 0)).map fun o => .transferOwnership caller o
  else if data.size < 68 then none
  else if Abi.selectorOf data = 0x84d4b410 then
    (addrArg (argWord data 0)).bind fun a =>
      (addrArg (argWord data 1)).map fun b => .base (.transferAllFrom caller a b)
  else if Abi.selectorOf data = 0x39509351 then
    (addrArg (argWord data 0)).map fun a =>
      .base (.adjustAllowance caller a true (argWord data 1).toNat)
  else if Abi.selectorOf data = 0xa457c2d7 then
    (addrArg (argWord data 0)).map fun a =>
      .base (.adjustAllowance caller a false (argWord data 1).toNat)
  else if Abi.selectorOf data = 0x7a43e23f then some (.rebase caller (argWord data 1).toInt)
  else none

/-- The accounts an operation names (whose rows it changes). -/
def amplOpAddrs : AmplOp Address → List Address
  | .base (.transferAll _ a) => [a]
  | .base (.transferAllFrom _ a b) => [a, b]
  | .base (.adjustAllowance _ a _ _) => [a]
  | _ => []

/-- **The bytecode spec of AMPL's implementation**, running in the proxy's storage. -/
abbrev amplSpec : Prop := ERC20Spec AMPL.runtimeCode amplAbs M g₀ sel amplOps amplOpAddrs

end Verified.WeirdERC20.AMPL.Spec
