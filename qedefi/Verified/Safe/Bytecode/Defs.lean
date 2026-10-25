import Verified.Safe.Bytecode.Code
import Verified.OpenZeppelin.Proxy.Guard
import EvmLogic.Program.Nested.Sandbox
import EvmLogic.Tactic.OwnStep
import QEDefi.Actor.Derive

/-!
# Safe v1.5.0 owning a ProxyAdmin: definitions

The deployment of the upgrade guard with a real Safe: the OpenZeppelin v5.7.0
`TransparentUpgradeableProxy` at `px`, its `ProxyAdmin` at `pa`, the implementation `ActorImpl`
at `ia`, and the owner of the ProxyAdmin, a `SafeProxy` at `sf` running the Safe v1.5.0 singleton
deployed at `sg` (both byte-for-byte the mainnet code, reproduced from the v1.5.0 sources by
`scripts/build-contracts.sh`).

- **Storage layout** of Safe v1.5.0 (`ownerSlot`, `moduleSlot`, `approvalSlot`, the guard,
  module-guard and fallback-handler slots) and its **digests** (`safeDigest`: the EIP-712 hash
  `keccak256(0x1901 ‖ domainSeparator ‖ structHash)` of this Safe on this chain;
  `ethSignDigest`: its `eth_sign` wrapping).
- `Signers`: every owner `ecrecover` recovers from a digest of this Safe (plain or `eth_sign`)
  is in `T` (in the style of `SigUnforgeable`).
- `G`: the protected state. The implementation slot, the ProxyAdmin's owner, and the Safe's
  configuration: singleton, threshold, owners (every set owner slot is an owner's), modules (only
  the sentinel), no guard, no module guard, the fallback handler `h₀` (unset or not a relay), and
  no approval by an owner outside `T` of any digest of this Safe.
- `Protected`, `Rw`: the run-level hypothesis on hashing. Whenever the singleton, at the Safe,
  writes its nonce or an approval (keys `5` and `approvalSlot a h`), the key is not protected.
  Only a keccak collision can make it fail; no injectivity or disjointness of keccak is assumed.
- `Iss`: the Safe issues static calls, calls to non-relays (its fallback handler), and, from the
  proxy, the `DELEGATECALL` of the singleton's code; the proxy runs only the implementation's
  code; the singleton account is unconstrained (its frames act only as `sg`).
-/

namespace Verified.Safe.Guard

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested
open EvmLogic.AbsInt EvmLogic.AbsInt.Guard Verified.OpenZeppelin.Contracts EvmLogic.Solidity
open Verified.OpenZeppelin.Proxy Verified.Safe.Contracts

/-! ## Storage layout -/

/-- The sentinel of Safe's linked lists. -/
def sentinel : Address := 1

/-- `GUARD_STORAGE_SLOT`. -/
def guardSlot : Word := 0x4a204f620c8c5ccdca3fd54d003badd85ba500436a431f0cbda4f558c93c34c8
/-- `MODULE_GUARD_STORAGE_SLOT`. -/
def moduleGuardSlot : Word := 0xb104e0b93118902c651344349b610029d694cfdec91c589c91ebafbcd0289947
/-- `FALLBACK_HANDLER_STORAGE_SLOT`. -/
def handlerSlot : Word := 0x6c9a6c4a39284e37ed1cf53d337577d14212a4870fb976a4366c693b939918d5

/-- The slot of `key` in the mapping at `slot` (`keccak256(key ‖ slot)`). -/
def mapSlot (crypto : Crypto) (key slot : Word) : Word :=
  crypto.keccak256 (Bytes.ofWord key ++ Bytes.ofWord slot)

/-- `owners[a]` (slot `2`). -/
def ownerSlot (crypto : Crypto) (a : Address) : Word := mapSlot crypto (Word.ofAddress a) 2
/-- `modules[a]` (slot `1`). -/
def moduleSlot (crypto : Crypto) (a : Address) : Word := mapSlot crypto (Word.ofAddress a) 1
/-- `approvedHashes[a][h]` (slot `8`). -/
def approvalSlot (crypto : Crypto) (a : Address) (h : Word) : Word :=
  mapSlot crypto h (mapSlot crypto (Word.ofAddress a) 8)

/-! ## Digests -/

/-- `DOMAIN_SEPARATOR_TYPEHASH`. -/
def domainTypehash : Word := 0x47e79534a245952e8b16893a336b85a3d9ea9fa8c573f3d803afb92a79469218

/-- `domainSeparator()` of the Safe `sf` on chain `chainId`. -/
def domainSeparator (crypto : Crypto) (chainId : Nat) (sf : Address) : Word :=
  crypto.keccak256 (Bytes.ofWord domainTypehash ++ Bytes.ofWord (ofNat chainId) ++
    Bytes.ofWord (Word.ofAddress sf))

/-- The EIP-712 digest of the struct hash `sh` (32 bytes) for the Safe `sf` on chain
`chainId`. -/
def safeDigest (crypto : Crypto) (chainId : Nat) (sf : Address) (sh : ByteArray) : Word :=
  crypto.keccak256 (⟨#[0x19, 0x01]⟩ ++ Bytes.ofWord (domainSeparator crypto chainId sf) ++ sh)

/-- `"\x19Ethereum Signed Message:\n32"`. -/
def ethSignPrefix : ByteArray :=
  ⟨#[0x19, 0x45, 0x74, 0x68, 0x65, 0x72, 0x65, 0x75, 0x6d, 0x20, 0x53, 0x69, 0x67, 0x6e, 0x65,
    0x64, 0x20, 0x4d, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65, 0x3a, 0x0a, 0x33, 0x32]⟩

/-- The `eth_sign` digest of `d`. -/
def ethSignDigest (crypto : Crypto) (d : Word) : Word :=
  crypto.keccak256 (ethSignPrefix ++ Bytes.ofWord d)

/-- **The signers** (in the style of `SigUnforgeable`): every owner that `ecrecover` recovers
from a digest of this Safe on this chain, directly or `eth_sign`-wrapped, is in `T`. Owners
outside `T` signed nothing for this Safe on this chain. -/
structure Signers (crypto : Crypto) (chainId : Nat) (sf : Address) (O T : Finset Address) :
    Prop where
  ecdsa : ∀ sh v r s a, sh.size = 32 →
    ecrecoverAddress? crypto (safeDigest crypto chainId sf sh) v r s = some a → a ∈ O → a ∈ T
  ethSign : ∀ sh v r s a, sh.size = 32 →
    ecrecoverAddress? crypto (ethSignDigest crypto (safeDigest crypto chainId sf sh)) v r s =
      some a → a ∈ O → a ∈ T

/-! ## The deployment -/

/-- A deployment: proxy, ProxyAdmin, implementation, Safe and singleton (distinct, the
ProxyAdmin and the Safe not at the `ecrecover` precompile `1`). -/
structure Dep where
  px : Address
  pa : Address
  ia : Address
  sf : Address
  sg : Address
  px_pa : px ≠ pa
  px_ia : px ≠ ia
  pa_ia : pa ≠ ia
  sf_px : sf ≠ px
  sf_pa : sf ≠ pa
  sf_ia : sf ≠ ia
  sg_px : sg ≠ px
  sg_pa : sg ≠ pa
  sg_ia : sg ≠ ia
  sg_sf : sg ≠ sf
  pa_one : pa ≠ 1
  sf_one : sf ≠ 1

namespace Dep

variable (D : Dep)

/-- The code of each relay. -/
def code (a : Address) : ByteArray :=
  if a = D.px then OzTransparentProxy.runtimeCodeWith ⟨D.pa⟩
  else if a = D.pa then OzProxyAdmin.runtimeCode
  else if a = D.sf then SafeProxy.runtimeCode
  else if a = D.sg then SafeSingleton.runtimeCode else ActorImpl.runtimeCode

def Rl (a : Address) : Prop := a = D.px ∨ a = D.pa ∨ a = D.ia ∨ a = D.sf ∨ a = D.sg

/-- **Idle principals**: the owners outside `T` (externally owned accounts that send nothing),
and, from Prague on, the `ecrecover` address. -/
def X (fork : Fork) (O T : Finset Address) (a : Address) : Prop :=
  (a = 1 ∧ .prague ≤ fork) ∨ (a ∈ O ∧ a ∉ T)

/-- **The Safe's protected configuration** (its storage `s`): singleton, threshold, owners within
`O`, only the sentinel module, no guard, no module guard, the fallback handler `h₀`, and no
approval of a digest of this Safe by an owner outside `T`. -/
structure SafeOk (crypto : Crypto) (chainId : Nat) (O T : Finset Address) (thr : Nat) (h₀ : Word)
    (s : Word → Word) : Prop where
  singleton : s 0 = Word.ofAddress D.sg
  threshold : s 4 = BitVec.ofNat 256 thr
  owners : ∀ a, s (ownerSlot crypto a) ≠ 0 → a ∈ O
  sentinelModule : s (moduleSlot crypto sentinel) = Word.ofAddress sentinel
  modules : ∀ a, a ≠ sentinel → s (moduleSlot crypto a) = 0
  guard : s guardSlot = 0
  moduleGuard : s moduleGuardSlot = 0
  handler : s handlerSlot = h₀
  approvals : ∀ a ∈ O, a ∉ T → ∀ sh, sh.size = 32 →
    s (approvalSlot crypto a (safeDigest crypto chainId D.sf sh)) = 0

/-- **The protected state**: the implementation, the ProxyAdmin's owner, the Safe's
configuration. -/
def G (crypto : Crypto) (chainId : Nat) (O T : Finset Address) (thr : Nat) (h₀ : Word)
    (w : World) : Prop :=
  w.sload D.px implSlot = Word.ofAddress D.ia ∧ w.sload D.pa 0 = Word.ofAddress D.sf ∧
    D.SafeOk crypto chainId O T thr h₀ (w.sload D.sf)

/-- The keys `G` reads in the Safe's storage. -/
def Protected (crypto : Crypto) (chainId : Nat) (O T : Finset Address) (sf : Address) (k : Word) :
    Prop :=
  k = 0 ∨ k = 4 ∨ k = guardSlot ∨ k = moduleGuardSlot ∨ k = handlerSlot ∨
    (∃ a, k = ownerSlot crypto a) ∨ (∃ a, k = moduleSlot crypto a) ∨
    (∃ a sh, a ∈ O ∧ a ∉ T ∧ sh.size = 32 ∧
      k = approvalSlot crypto a (safeDigest crypto chainId sf sh))

/-- The keys the singleton writes outside doomed regions: the nonce, approvals. -/
def Kw (crypto : Crypto) (k : Word) : Prop := k = 5 ∨ ∃ a h, k = approvalSlot crypto a h

/-- **The run-level hypothesis on hashing**: an `SSTORE` of the singleton's code at the Safe
to its nonce or an approval key does not write a protected key. -/
def Rw (crypto : Crypto) (chainId : Nat) (O T : Finset Address) (m : Machine) : Prop :=
  m.frame.msg.currentTarget = D.sf → m.frame.code = SafeSingleton.runtimeCode →
    ∀ k rest, m.frame.code[m.frame.pc]? = some 0x55 → m.frame.stack = k :: rest →
      Kw crypto k → ¬ Protected crypto chainId O T D.sf k

/-- What relays issue. The proxy runs only the implementation's code; the Safe issues static
calls, calls to accounts that are not relays, and the `DELEGATECALL` of the singleton's code,
for a sender other than itself; the singleton account is unconstrained. -/
def Iss (r : Address) (_ : Machine) (c : Message) : Prop :=
  (r = D.px ∧ c.code = ActorImpl.runtimeCode) ∨
    (r = D.sf ∧ (c.isStatic = true ∨ ¬ D.Rl c.currentTarget ∨
      (c.currentTarget = D.sf ∧ c.code = SafeSingleton.runtimeCode ∧ c.caller ≠ D.sf))) ∨
    r = D.sg

/-- The doom point: `simulateAndRevert`'s `DELEGATECALL` (pc `11184`). -/
def Dsim (m : Machine) : Prop := m.frame.pc = 11184

/-- What a frame of the Safe may assume at each step (supplied by the simulation). -/
def Rsf (crypto : Crypto) (chainId : Nat) (O T : Finset Address) (thr : Nat) (h₀ : Word)
    (fork : Fork) (m : Machine) : Prop :=
  D.G crypto chainId O T thr h₀ m.world ∧ IdleW (X fork O T) m.world ∧
    RelayCode D.Rl D.code m.world ∧ D.Rw crypto chainId O T m

theorem code_sg : D.code D.sg = SafeSingleton.runtimeCode := by
  simp [code, D.sg_px, D.sg_pa, D.sg_sf]

theorem code_sf : D.code D.sf = SafeProxy.runtimeCode := by
  simp [code, D.sf_px, D.sf_pa]

theorem deleg_sg : delegatedAddress? SafeSingleton.runtimeCode = none :=
  Verified.OpenZeppelin.Proxy.Dep.deleg_none (by rw [SafeSingleton.size_runtimeCode]; decide)

theorem deleg_sf : delegatedAddress? SafeProxy.runtimeCode = none :=
  Verified.OpenZeppelin.Proxy.Dep.deleg_none (by rw [SafeProxy.size_runtimeCode]; decide)

/-- The Safe's issuance, for `OwnG`. -/
def Csf (m : Machine) (req : CallRequest) : Prop := D.Iss D.sf m req.msg

end Dep

end Verified.Safe.Guard
