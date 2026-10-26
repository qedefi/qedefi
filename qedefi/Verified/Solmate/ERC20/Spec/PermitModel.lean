import Verified.Solmate.ERC20.Spec.Normal
import Verified.Solmate.ERC20.Permit
import EvmLogic.Solidity.Strings
import Verified.Solmate.ERC4626.UnknownSelectors

/-!
# Solmate's `permit`: the signature recovery and the gas bound

What the deployed asset's `permit(owner, spender, value, deadline, v, r, s)` recovers, read off
the compiled code (solc 0.8.28):

* the domain separator (`DOMAIN_SEPARATOR()`, entry `0x0424`) is the `INITIAL_DOMAIN_SEPARATOR`
  immutable on the deployment chain (`chainid() = INITIAL_CHAIN_ID`); off it,
  `computeDomainSeparator()` (`0x0749`) hashes `name` with the in-place packed encoder `0x0a66`
  (no memory allocation, so no `Panic(0x41)`; an inconsistent slot word, a short form of 32
  bytes or more or a long form below 32, is `Panic(0x22)`: `nameBytes` is `none`);
* the signer is `ecrecover` (precompile `0x01`) of the EIP-712 digest at the owner's nonce:
  `Permit.digest`, `Permit.structHash`; a failed recovery, a `v` outside `27`/`28` (the ABI
  decoder rejects `v ≥ 256` first), and a frame at the call-depth limit (the `STATICCALL` to
  `0x01` then fails at once and `permit` reverts) all give `0`, which never passes
  (`recoveredAddress != address(0)`).

`solmateRec ia m n` is that address for the frame `m` and nonce `n`; `solmateGp ia m` is the
gas from which `permit` is exact: a fixed 100000, plus, off the deployment chain, the cost of
hashing `name` (`Str.getterGas` of its length).
-/

namespace Verified.Solmate.ERC20.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.Solmate QEDefi.Math Finsupp
open Verified.Solmate.Contracts Verified.Solmate.ERC20 Verified.Solmate.ERC4626

/-- `computeDomainSeparator()` for the name bytes `name`. -/
def dsOfName (crypto : Crypto) (name : ByteArray) (chainId : Word) (self : Address) : Word :=
  crypto.keccak256 (Bytes.ofWord Permit.DOMAIN_TYPEHASH ++
    (Bytes.ofWord (crypto.keccak256 name) ++ (Bytes.ofWord Permit.VERSION_HASH ++
      (Bytes.ofWord chainId ++ Bytes.ofWord (Word.ofAddress self)))))

/-- **The bytes the packed encoder `0x0a66` hashes for `name`** (slot 0 of `sload`): a short
string (low bit clear) is the slot word's first `(S >> 1) & 127` bytes, a long one (low bit
set) the `S >> 1` bytes from `keccak256(0)`; `none` when the slot word is inconsistent
(`Panic(0x22)`). -/
def nameBytes (crypto : Crypto) (sload : Word → Word) : Option ByteArray :=
  let S := sload 0#256
  if S &&& 1#256 = 0#256 then
    if (Permit.shortLength S).toNat < 32 then some (Permit.shortStringBytes S) else none
  else if 32 ≤ (Word.shr 1#256 S).toNat then
    some (Str.longData sload (arrayDataSlot crypto 0#256) (Word.shr 1#256 S).toNat)
  else none

/-- **The domain separator of the frame `m`**: the immutable on the deployment chain, else
computed from `name` (slot 0); `none` when computing it panics. -/
def solmateDs (ia : SolmateAsset.Immutables) (m : Machine) : Option Word :=
  if ofNat m.ctx.block.chainId = ia.initialChainId then some ia.initialDomainSeparator
  else (nameBytes m.ctx.crypto (m.world.sload m.frame.msg.currentTarget)).map fun name =>
    dsOfName m.ctx.crypto name (ofNat m.ctx.block.chainId) m.frame.msg.currentTarget

/-- **Solmate's signature recovery**: the address `ecrecover` returns for the `permit` calldata
of `m` at nonce `n`; `0` when recovery fails, at the call-depth limit, or when the domain
separator panics. -/
def solmateRec (ia : SolmateAsset.Immutables) (m : Machine) (n : ℕ) : Address :=
  let d := m.frame.msg.data
  if Gas.stackDepthLimit < m.frame.msg.depth + 1 then 0
  else match solmateDs ia m with
    | none => 0
    | some ds =>
      (ecrecoverAddress? m.ctx.crypto
        (Permit.digest m.ctx.crypto ds (Permit.structHash m.ctx.crypto
          (Word.toAddress (argWord d 0)) (Word.toAddress (argWord d 1)) (argWord d 2) (word n)
          (argWord d 3))) (argWord d 4) (argWord d 5) (argWord d 6)).getD 0

/-- **The gas from which Solmate's `permit` is exact.** -/
def solmateGp (ia : SolmateAsset.Immutables) (m : Machine) : Nat :=
  100000 + (if ofNat m.ctx.block.chainId = ia.initialChainId then 0
    else Str.getterGas (Str.slotLen (m.world.sload m.frame.msg.currentTarget 0#256)))

/-! ## The model's `permit` -/

theorem call_permit (s : VState Address) (c o sp : Address) (v : ℕ) (live : Bool)
    (rec : ℕ → Address) :
    V.call s c (.permit o sp v live rec) =
      if live = true ∧ rec (s.nonces o) = o ∧ o ≠ 0 then
        .ok { s.setAllowance o sp v with
          nonces := s.nonces.update o ((s.nonces o + 1) % U256) } .empty
      else .halt .revert := by
  unfold Variant.call
  rw [failKind_standard]
  by_cases h : live = true ∧ rec (s.nonces o) = o ∧ o ≠ 0
  · obtain ⟨h1, h2, h3⟩ := h
    have h3' : o ≠ 0#160 := h3
    simp [h3', Variant.step, Variant.permit, Variant.permitOk, Variant.standard, h1, h2,
      Variant.retData]
  · rw [if_neg' h]
    have : Variant.permitOk V s o sp v live rec = false := by
      simp only [Variant.permitOk, Variant.standard]
      by_cases h1 : live = true <;> by_cases h2 : rec (s.nonces o) = o <;> by_cases h3 : o = 0 <;>
        simp_all
    have hr : (Variant.standard : Variant Address).permitRule = .eip2612 true true := rfl
    simp [Variant.step, Variant.permit, hr, this, Variant.failWith]

end Verified.Solmate.ERC20.Spec
