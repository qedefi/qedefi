import EvmLogic.Program.PrecompileCall
import EvmLogic.Solidity.ERC20
import Verified.Solmate.ERC20.BalanceOf
import EvmLogic.Tactic.WpStep
import EvmLogic.Program.Summary
import EvmLogic.Tactic.Patched
import EvmLogic.Solidity.Memory
import EvmLogic.Tactic.Mcopy
import EvmLogic.Solidity.Word
import EvmLogic.Solidity.Events
import QEDefi.ERC4626.Logs
import Verified.MathlibDeps
import QEDefi.Math.Arith

/-!
# EIP-2612 as the bytecode computes it

The specification of `permit`, `DOMAIN_SEPARATOR()` and `nonces(owner)` as explicit expressions
in the context's `Crypto` (nothing assumed about it), and the asset's bytecode theorems:
`asset_permit_halts` succeeds exactly when `PermitValid` holds. A long `name` (over 31 bytes)
off the deployment chain is not covered (`DomainCase`). `docs/erc4626/details.md` §7.
-/

section

namespace Verified.Solmate.ERC20.Permit
open QEDefi.ERC4626

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic

/-! ## Constants of the bytecode -/

/-- `keccak256("Permit(…)")` as a literal of the code, *not* `crypto.keccak256` of the string:
for an arbitrary `Crypto` the code still uses this word (agreement with Keccak: `difftest`). -/
def PERMIT_TYPEHASH : Word :=
  0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9#256

/-- `keccak256("EIP712Domain(…)")`, a literal of the code. -/
def DOMAIN_TYPEHASH : Word :=
  0x8b73c3c69bb8fe3d512ecc4cf759cc79239f7b179b0ffacaa9a75d522b39400f#256

/-- `keccak256("1")`, a literal of the code. -/
def VERSION_HASH : Word :=
  0xc89efdaa54c0f20c7adf612882df0950f5a951637e0307cdcb4c672f298b8bc6#256

def eip712Prefix : ByteArray := ⟨#[0x19, 0x01]⟩

/-! ## The EIP-712 message -/

/-- `keccak256(abi.encode(PERMIT_TYPEHASH, owner, spender, value, nonce, deadline))`. -/
def structHash (crypto : Crypto) (owner spender : Address) (value nonce deadline : Word) : Word :=
  crypto.keccak256 (Bytes.ofWord PERMIT_TYPEHASH ++ (Bytes.ofWord (Word.ofAddress owner) ++
    (Bytes.ofWord (Word.ofAddress spender) ++ (Bytes.ofWord value ++ (Bytes.ofWord nonce ++
      Bytes.ofWord deadline)))))

/-- `keccak256(abi.encodePacked("\x19\x01", domainSeparator, structHash))`. -/
def digest (crypto : Crypto) (domainSep sh : Word) : Word :=
  crypto.keccak256 (eip712Prefix ++ (Bytes.ofWord domainSep ++ Bytes.ofWord sh))

/-- **The signature check of `permit`**: `owner ≠ 0` and `ecrecover` (precompile `0x01`) of the
permit digest at `nonce` under `domainSep` recovers `owner`. -/
def SigOk (crypto : Crypto) (domainSep : Word) (owner spender : Address)
    (value nonce deadline v r s : Word) : Prop :=
  owner ≠ 0 ∧
    ecrecoverAddress? crypto (digest crypto domainSep (structHash crypto owner spender value nonce
      deadline)) v r s = some owner

/-! ## The domain separator -/

def shortLength (slot : Word) : Word := Word.shr 1#256 slot &&& 127#256

/-- A `string` slot word in Solidity's short form (low bit clear, length below 32). -/
def ShortString (slot : Word) : Prop := slot &&& 1#256 = 0#256 ∧ (shortLength slot).toNat < 32

def shortStringBytes (slot : Word) : ByteArray :=
  (Bytes.ofWord (slot &&& ~~~255#256)).extract 0 (shortLength slot).toNat

/-- `computeDomainSeparator()` for a short `name` stored as `nameSlot`. -/
def computedDomainSeparator (crypto : Crypto) (nameSlot chainId : Word) (self : Address) : Word :=
  crypto.keccak256 (Bytes.ofWord DOMAIN_TYPEHASH ++
    (Bytes.ofWord (crypto.keccak256 (shortStringBytes nameSlot)) ++ (Bytes.ofWord VERSION_HASH ++
      (Bytes.ofWord chainId ++ Bytes.ofWord (Word.ofAddress self)))))

/-- **`DOMAIN_SEPARATOR()`**: the immutable on the deployment chain, else recomputed from the
name in slot 0. -/
def domainSeparator (crypto : Crypto) (initialChainId initialDomainSeparator chainId nameSlot : Word)
    (self : Address) : Word :=
  if chainId = initialChainId then initialDomainSeparator
  else computedDomainSeparator crypto nameSlot chainId self

/-- The covered cases of `DOMAIN_SEPARATOR()`: the deployment chain, or a short name. -/
def DomainCase (initialChainId chainId nameSlot : Word) : Prop :=
  chainId = initialChainId ∨ ShortString nameSlot

/-! ## `permit` -/

/-- The slot of `nonces[a]` (slot 5 of Solmate's `ERC20`). -/
def nonceSlot (crypto : Crypto) (a : Address) : Word := mappingSlot crypto (Word.ofAddress a) 5#256

/-- **When `permit` succeeds**, at the owner's current nonce: `v < 256`, the deadline not passed,
and `SigOk`. -/
def PermitValid (crypto : Crypto) (domainSep : Word) (timestamp : Nat) (owner spender : Address)
    (value deadline v r s nonce : Word) : Prop :=
  v.toNat < 256 ∧ (ofNat timestamp).toNat ≤ deadline.toNat ∧
    SigOk crypto domainSep owner spender value nonce deadline v r s

/-- The world after `permit`: `nonces[owner]++` (wrapping), then the allowance write. -/
def permitWorld (crypto : Crypto) (w : World) (token owner spender : Address) (value : Word) :
    World :=
  (w.sstore token (nonceSlot crypto owner) (w.sload token (nonceSlot crypto owner) + 1#256)).sstore
    token (ERC20.allowanceSlot crypto ERC20.Layout.solmate owner spender) value

/-- Calldata of `permit(owner, spender, value, deadline, v, r, s)`, as the ABI decoder reads it
(covers `Abi.encodeCall` and calldata assembled by a caller). -/
structure PermitCall (data : ByteArray) (owner spender : Address) (value deadline v r s : Word) :
    Prop where
  selector : Abi.selectorOf data = 0xd505accf
  size : 228 ≤ data.size
  arg0 : Bytes.toWord (readBytes data 4 32) = Word.ofAddress owner
  arg1 : Bytes.toWord (readBytes data 36 32) = Word.ofAddress spender
  arg2 : Bytes.toWord (readBytes data 68 32) = value
  arg3 : Bytes.toWord (readBytes data 100 32) = deadline
  arg4 : Bytes.toWord (readBytes data 132 32) = v
  arg5 : Bytes.toWord (readBytes data 164 32) = r
  arg6 : Bytes.toWord (readBytes data 196 32) = s

def permitData (owner spender : Address) (value deadline v r s : Word) : ByteArray :=
  Abi.encodeCall 0xd505accf [Word.ofAddress owner, Word.ofAddress spender, value, deadline, v, r, s]

theorem permitCall_encodeCall (owner spender : Address) (value deadline v r s : Word) :
    PermitCall (permitData owner spender value deadline v r s) owner spender value deadline v r s :=
  ⟨by rw [permitData, Abi.selectorOf_encodeCall],
   by rw [permitData, Abi.size_encodeCall]; simp,
   Abi.calldataload_encodeCall _ _ 0 (by simp), Abi.calldataload_encodeCall _ _ 1 (by simp),
   Abi.calldataload_encodeCall _ _ 2 (by simp), Abi.calldataload_encodeCall _ _ 3 (by simp),
   Abi.calldataload_encodeCall _ _ 4 (by simp), Abi.calldataload_encodeCall _ _ 5 (by simp),
   Abi.calldataload_encodeCall _ _ 6 (by simp)⟩

/-! ## What is *not* assumed -/

/-- **ECDSA unforgeability (documentation only; no theorem uses it)**: every signature recovering
to `owner` is for a digest in `Signed owner`. Add it as a hypothesis to conclude "only the
owner can grant an allowance by `permit`". -/
def SigUnforgeable (crypto : Crypto) (Signed : Address → Word → Prop) : Prop :=
  ∀ owner hash v r s, ecrecoverAddress? crypto hash v r s = some owner → Signed owner hash

theorem signed_of_sigOk {crypto : Crypto} {Signed : Address → Word → Prop}
    (hu : SigUnforgeable crypto Signed) {ds : Word} {owner spender : Address}
    {value nonce deadline v r s : Word}
    (h : SigOk crypto ds owner spender value nonce deadline v r s) :
    Signed owner (digest crypto ds (structHash crypto owner spender value nonce deadline)) :=
  hu _ _ _ _ _ h.2

end Verified.Solmate.ERC20.Permit

end

section

/-!
## The asset's `DOMAIN_SEPARATOR()`

Internal function at `0x0424` (called by `permit` and the external getter); off the deployment
chain it calls `computeDomainSeparator()` (`0x0749`), which encodes `name` (`0x0a66`).
-/

namespace Verified.Solmate.ERC20.Permit
open QEDefi.ERC4626

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts

/-- The `INITIAL_CHAIN_ID` immutable, as the `PUSH32` at `0x0426` reads it. -/
theorem readBytes_asset_chainId (ia : SolmateAsset.Immutables) :
    readBytes (SolmateAsset.runtimeCodeWith ia) 1063 32 = Bytes.ofWord ia.initialChainId := by
  have hp : ia.patches = [] ++ (1063, ia.initialChainId) ::
      [(1116, ia.initialDomainSeparator), (345, ia.decimals)] := rfl
  simp only [SolmateAsset.runtimeCodeWith, hp]
  exact readBytes_patchWords_last _ _ _ _ _ (by rw [SolmateAsset.size_runtimeCode]; decide)
    (by simp)

/-- The `INITIAL_DOMAIN_SEPARATOR` immutable, as the `PUSH32` at `0x045b` reads it. -/
theorem readBytes_asset_ds (ia : SolmateAsset.Immutables) :
    readBytes (SolmateAsset.runtimeCodeWith ia) 1116 32 = Bytes.ofWord ia.initialDomainSeparator := by
  have hp : ia.patches = [(1063, ia.initialChainId)] ++ (1116, ia.initialDomainSeparator) ::
      [(345, ia.decimals)] := rfl
  simp only [SolmateAsset.runtimeCodeWith, hp]
  exact readBytes_patchWords_last _ _ _ _ _ (by rw [SolmateAsset.size_runtimeCode]; decide)
    (by simp)

/-- Memory after `DOMAIN_SEPARATOR()`: unchanged (free pointer `0x80`), or free pointer `0x140`
after `computeDomainSeparator()`. -/
def DsMem (mem : Memory) : Prop :=
  (mem.loadWord 64 = 128#256 ∧ mem.size = 96) ∨ (mem.loadWord 64 = 320#256 ∧ mem.size = 320)

theorem not_255 : (~~~255#256 : Word) =
    115792089237316195423570985008687907853269984665640564039457584007913129639680#256 := by
  decide

/-- The domain separator the code of a frame computes. -/
def dsOf (initialChainId initialDomainSeparator : Word) (m : Machine) : Word :=
  domainSeparator m.ctx.crypto initialChainId initialDomainSeparator (ofNat m.ctx.block.chainId)
    (m.world.sload m.frame.msg.currentTarget 0#256) m.frame.msg.currentTarget

set_option maxHeartbeats 0 in
/-- The internal `DOMAIN_SEPARATOR()` (entry `0x0424`, stack `r :: rest`) returns to `r` with
`Permit.domainSeparator …`, memory as in `DsMem`, at most 6000 gas. -/
theorem asset_ds_wp {ia : SolmateAsset.Immutables} (m : Machine) {r : Word} {rest : List Word}
    (hc : m.frame.code = SolmateAsset.runtimeCodeWith ia)
    (hj : JumpTable m.frame.jumpDests (SolmateAsset.runtimeCodeWith ia))
    (hpc : m.frame.pc = 1060) (hs : m.frame.stack = r :: rest) (hlen : rest.length ≤ 1000)
    (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hfmp : m.frame.memory.loadWord 64 = 128#256) (hsize : m.frame.memory.size = 96)
    (hcase : DomainCase ia.initialChainId (ofNat m.ctx.block.chainId)
      (m.world.sload m.frame.msg.currentTarget 0#256))
    (hg : 10000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun m' => ∃ mem g sub, m' = m.resumeWith r.toNat
        (dsOf ia.initialChainId ia.initialDomainSeparator m :: rest) mem g m.frame.returnData sub ∧
        DsMem mem ∧ m.frame.gasLeft ≤ g + 6000 ∧ g ≤ m.frame.gasLeft ∧
        sub.logs = m.frame.sub.logs)
      (fun _ _ => False) := by
  have hagree := assetJumpDestsAgree ia
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hc hpc hs
  simp only [dsOf, domainSeparator]
  by_cases hceq : ofNat m_ctx.block.chainId = ia.initialChainId
  · -- the deployment chain: the immutable
    have he : Word.eq (ofNat m_ctx.block.chainId) ia.initialChainId = 1#256 := by
      rw [hceq]; exact Solidity.eq_self _
    simp only [hceq, ↓reduceIte]
    pwp_steps [he, readBytes_asset_chainId, readBytes_asset_ds]
    apply WP.ret
    exact ⟨_, _, _, rfl, .inl ⟨hfmp, hsize⟩, by omega, by omega, rfl⟩
  · -- another chain: `computeDomainSeparator()`
    have hne : Word.eq (ofNat m_ctx.block.chainId) ia.initialChainId = 0#256 := eq_of_ne hceq
    have hshort := hcase.resolve_left hceq
    simp only [hceq, ↓reduceIte, computedDomainSeparator, shortStringBytes]
    generalize hns : m_world.sload m_msg.currentTarget 0#256 = ns at hshort ⊢
    obtain ⟨h1, hl⟩ := hshort
    have hl1 : (shortLength ns).lt 32#256 = 1#256 := (Word.lt_eq_one_iff _ _).2 hl
    simp only [shortLength] at hl1 hl ⊢
    have hle : (Word.shr 1#256 ns &&& 127#256).toNat ≤ 32 := by omega
    pwp_steps [hne, readBytes_asset_chainId, readBytes_asset_ds, hfmp, hsize, permit_norm, hns, h1,
      hl1, Word.mul_iszero_iszero, Word.add_sub_cancel_left']
    generalize hL : (Word.shr (1#256) ns &&& 127#256) = L at hle ⊢
    wp_generalize_mem M hM
    have hMs : M.size = 160 := by subst hM; simp only [permit_norm, hsize]
    have hMr : M.read 128 L.toNat = (Bytes.ofWord (ns &&& ~~~255#256)).extract 0 L.toNat := by
      subst hM; simp only [Memory.read_expand, Memory.read_storeWord_prefix _ _ _ _ hle, not_255]
    have hM64 : M.loadWord 64 = 128#256 := by
      subst hM
      simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord_of_disjoint,
        hfmp]
    clear hM
    refine WP.of_step (step_keccak256 (by pcode_fact) rfl (by simp; omega) ?hg) (by same_frame) ?hw
    case hg =>
      dsimp only
      rw [hMs, BitVec.toNat_ofNat, show 128 % 2 ^ 256 = 128 by decide,
        Gas.extendMemory_one_of_le (by omega) (by decide)]
      simp only [Gas.keccak256Cost, Gas.keccak256Base, Gas.keccak256PerWord, Gas.words]
      evm_gas
    dsimp only
    rw [BitVec.toNat_ofNat, show 128 % 2 ^ 256 = 128 by decide,
      Memory.expand_eq_self_of_le (by omega) (by rw [hMs]), readBytes_bytes, hMr, hMs,
      Gas.extendMemory_one_of_le (by omega) (by decide)]
    wp_generalize_gas g1 hg1
    have hg1' : m_gasLeft ≤ g1 + 3000 := by subst hg1; evm_gas
    have hg1'' : 5000 ≤ g1 := by subst hg1; evm_gas
    have hg1u : g1 ≤ m_gasLeft := by subst hg1; omega
    clear hg1
    pwp_steps [hM64, hMs, permit_norm, Memory.read_160]
    apply WP.ret
    refine ⟨_, _, _, rfl, .inr ⟨?_, ?_⟩, by omega, by omega, rfl⟩
    · simp only [Memory.loadWord_expand, Memory.loadWord_storeWord]
    · simp only [permit_norm, hMs]

end Verified.Solmate.ERC20.Permit

namespace Verified.Solmate.ERC20.Permit
open QEDefi.ERC4626

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts

set_option maxHeartbeats 0 in
/-- **`DOMAIN_SEPARATOR()` of the asset**, in any fresh frame; the world is unchanged. -/
theorem asset_domainSeparator_halts {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x3644e515)
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hcase : DomainCase ia.initialChainId (ofNat m.ctx.block.chainId)
      (m.world.sload m.frame.msg.currentTarget 0#256))
    (hg : 20000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    Halts m (fun mf o =>
      o = .success (Bytes.ofWord (dsOf ia.initialChainId ia.initialDomainSeparator m)) ∧
      mf.world = m.world ∧ m.frame.gasLeft ≤ mf.frame.gasLeft + 10000) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_run_to 1060 [hval, hsel', hlt, Abi.shr_calldataload_zero]
  refine WP.bind_mono (asset_ds_wp _ rfl hj rfl rfl (by simp) (by pjumpdest_disch)
    (Memory.loadWord_storeWord _ _ _) (by simp [Memory.size_storeWord, Memory.size_expand,
      Memory.wordsAfter, Memory.words]) hcase (by dsimp only; omega) (by dsimp only; omega))
    (fun _ _ _ h => h.elim) ?_
  rintro _ - ⟨mem, g, sub, rfl, hmem, hgb, -, -⟩
  dsimp only [Machine.resumeWith] at hgb ⊢
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  simp only [dsOf]
  rcases hmem with ⟨h64, hs⟩ | ⟨h64, hs⟩
  · pwp_steps [h64, hs, permit_norm]
    refine ⟨trivial, by dsimp only [outputMachine], ?_⟩
    dsimp only [outputMachine]; evm_gas
  · pwp_steps [h64, hs, permit_norm]
    refine ⟨trivial, by dsimp only [outputMachine], ?_⟩
    dsimp only [outputMachine]; evm_gas

end Verified.Solmate.ERC20.Permit

namespace Verified.Solmate.ERC20.Permit
open QEDefi.ERC4626

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts

theorem nonceSlot_eq (crypto : Crypto) (a : Address) :
    nonceSlot crypto a = crypto.keccak256 (Bytes.ofWord (Word.ofAddress a) ++ Bytes.ofWord 5#256) :=
  rfl

set_option maxHeartbeats 0 in
/-- **`nonces(owner)` of the asset**, in any fresh frame; the world is unchanged. -/
theorem asset_nonces_halts {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (owner : Address)
    (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x7ecebe00)
    (hsize : 36 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (harg : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress owner)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (fun mf o =>
      o = .success (Bytes.ofWord (m.world.sload m.frame.msg.currentTarget
        (nonceSlot m.ctx.crypto owner))) ∧
      mf.world = m.world ∧ m.frame.gasLeft ≤ mf.frame.gasLeft + 3000) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg,
    ofAddress_and_addressMask, Solidity.eq_self, Memory.read_64]
  refine ⟨rfl, by dsimp only [outputMachine], ?_⟩
  dsimp only [outputMachine]
  evm_gas

end Verified.Solmate.ERC20.Permit

end

section

/-!
## The asset's `permit`: from the `ECRECOVER` call (`0x065f`) to the end

Memory holds `digest ‖ v ‖ r ‖ s`, a zero output word and the free pointer `F` (`0x80`, or
`0x140` after `computeDomainSeparator()`); every offset is `F` plus a constant.
-/

namespace Verified.Solmate.ERC20.Permit
open QEDefi.ERC4626

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts

def RecoversTo (crypto : Crypto) (dg v r s : Word) (owner : Address) : Prop :=
  owner ≠ 0 ∧ ecrecoverAddress? crypto dg v r s = some owner

def TailPost (owner spender : Address) (value dg v r s : Word) (m mf : Machine) (o : Outcome) :
    Prop :=
  (RecoversTo m.ctx.crypto dg v r s owner →
    o = .success .empty ∧
    mf.world = m.world.sstore m.frame.msg.currentTarget
      (ERC20.allowanceSlot m.ctx.crypto ERC20.Layout.solmate owner spender) value ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs.push
      (approvalLog m.frame.msg.currentTarget owner spender value)) ∧
  (¬ RecoversTo m.ctx.crypto dg v r s owner → ∃ out, o = .revert out) ∧
  m.frame.gasLeft ≤ mf.frame.gasLeft + 40000

theorem iszero_ofAddress {a : Address} (h : a ≠ 0) : Word.iszero (Word.ofAddress a) = 0#256 := by
  apply iszero_of_ne
  intro he; apply h
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat he
  simp only [Word.ofAddress, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
  have hlt := a.isLt
  rw [Nat.mod_eq_of_lt (by omega)] at this
  exact this

theorem eq_ofAddress_ne {a b : Address} (h : a ≠ b) :
    Word.eq (Word.ofAddress a) (Word.ofAddress b) = 0#256 :=
  eq_of_ne fun he => h (Word.ofAddress_injective he)

set_option maxHeartbeats 0 in
theorem asset_permit_tail {ia : SolmateAsset.Immutables} (m : Machine) {M : Memory} {F : Nat}
    {dg v r s deadline value : Word} {owner spender : Address}
    (hF : F = 128 ∨ F = 320)
    (hc : m.frame.code = SolmateAsset.runtimeCodeWith ia)
    (hj : JumpTable m.frame.jumpDests (SolmateAsset.runtimeCodeWith ia))
    (hpc : m.frame.pc = 1631)
    (hs : m.frame.stack = [ofNat m.frame.gasLeft, 1#256, BitVec.ofNat 256 (F + 354), 128#256,
      BitVec.ofNat 256 (F + 322), 32#256, BitVec.ofNat 256 (F + 482), 1#256, 0#256,
      s, r, v, deadline, value, Word.ofAddress spender, Word.ofAddress owner, 424#256,
      3573918927#256])
    (hmem : m.frame.memory = M) (hM64 : M.loadWord 64 = BitVec.ofNat 256 (F + 354))
    (hMout : M.loadWord (F + 322) = 0#256)
    (hMin : M.read (F + 354) 128 =
      Bytes.ofWord dg ++ (Bytes.ofWord v ++ (Bytes.ofWord r ++ Bytes.ofWord s)))
    (hMs : M.size = F + 512)
    (hg : 40000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel1 : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hstatic : m.frame.msg.isStatic = false) :
    WP m (fun _ => False) (TailPost owner spender value dg v r s m) := by
  have hagree := assetJumpDestsAgree ia
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hc hpc hs hmem hstd
  have hmod : m_gasLeft % 2 ^ 256 = m_gasLeft := Nat.mod_eq_of_lt (by omega)
  have hacc := accessCost_le (m_sub.accessedAddresses.contains 1)
  rcases hF with rfl | rfl <;>
  · simp only [Nat.reduceAdd] at hM64 hMout hMin hMs ⊢
    refine WP.staticcall_ecrecover (hash := dg) (v := v) (r := r) (s := s) (by pcode_fact) rfl rfl
      hdel1 ?_ hdepth hMin ?_ ?_
    · simp only [callCost, callGas, callExt, ofNat, BitVec.toNat_ofNat, Nat.reducePow,
        Nat.reduceMod]
      rw [messageCallGas_zero (by evm_gas)]
      simp only [Gas.maxMessageCallGas]
      evm_gas
    · simp only [callGas, callExt, ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      rw [messageCallGas_zero (by evm_gas)]
      simp only [Gas.maxMessageCallGas]
      evm_gas
    simp only [returnMemory_ecrecoverOutput, callMemory, callCost, callGas, callExt, ofNat,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, callerFrame]
    rw [messageCallGas_zero (by evm_gas)]
    simp only [Gas.maxMessageCallGas]
    wp_generalize_gas g1 hg1
    have hg1' : m_gasLeft ≤ g1 + 6000 := by
      subst hg1
      generalize Gas.accessCost (Std.ExtTreeSet.contains m_sub.accessedAddresses 1) = acc at hacc ⊢
      evm_gas
    have hg1'' : 30000 ≤ g1 := by
      subst hg1
      generalize Gas.accessCost (Std.ExtTreeSet.contains m_sub.accessedAddresses 1) = acc at hacc ⊢
      evm_gas
    clear hg1
    generalize ecrecoverOutput m_ctx.crypto dg v r s = rd
    cases hrec : ecrecoverAddress? m_ctx.crypto dg v r s with
    | none =>
      -- invalid signature: the pre-stored zero is read back
      pwp_steps [hM64, hMout, ofAddress_and_addressMask, addressMask_and_ofAddress,
        Solidity.eq_self, iszero_zero, iszero_one, permit_norm, hMs, Memory.read_64, hstatic]
      unfold TailPost RecoversTo
      refine ⟨fun h => absurd h.2 (by rw [hrec]; simp), fun _ => ⟨_, rfl⟩, ?_⟩
      dsimp only [outputMachine]; evm_gas
    | some a =>
      by_cases ha0 : a = 0
      · subst ha0
        pwp_steps [hM64, hMout, ofAddress_and_addressMask, addressMask_and_ofAddress,
          Solidity.eq_self, iszero_zero, iszero_one, permit_norm, hMs, Memory.read_64, hstatic]
        unfold TailPost RecoversTo
        refine ⟨fun h => (h.1 (Option.some.inj (h.2.symm.trans hrec))).elim, fun _ => ⟨_, rfl⟩,
          ?_⟩
        dsimp only [outputMachine]; evm_gas
      · have hz := iszero_ofAddress ha0
        by_cases hao : a = owner
        · subst hao
          pwp_steps [hM64, hz, ofAddress_and_addressMask, addressMask_and_ofAddress,
            Solidity.eq_self, iszero_zero, iszero_one, permit_norm, hMs, Memory.read_64, hstatic]
          apply WP.halt_of_step (step_stop (by pcode_fact)) (SameFrame.refl _)
          unfold TailPost RecoversTo
          refine ⟨fun _ => ⟨rfl, ?_, rfl, rfl, ?_⟩, fun h => absurd ⟨ha0, hrec⟩ h, ?_⟩
          · rfl
          · dsimp only
            logs_simp []
            event_log [value]
          · evm_gas
        · have hne := eq_ofAddress_ne hao
          pwp_steps [hM64, hz, hne, ofAddress_and_addressMask, addressMask_and_ofAddress,
            Solidity.eq_self, iszero_zero, iszero_one, permit_norm, hMs, Memory.read_64, hstatic]
          unfold TailPost RecoversTo
          refine ⟨fun h => (hao (Option.some.inj (hrec.symm.trans h.2))).elim, fun _ => ⟨_, rfl⟩,
            ?_⟩
          dsimp only [outputMachine]; evm_gas

end Verified.Solmate.ERC20.Permit

end

section

/-! ## The asset's `permit`: the body after `DOMAIN_SEPARATOR()` (`0x0566` to the end) -/

namespace Verified.Solmate.ERC20.Permit
open QEDefi.ERC4626

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts

def BodyPost (ds : Word) (owner spender : Address) (value deadline v r s : Word) (m mf : Machine)
    (o : Outcome) : Prop :=
  (RecoversTo m.ctx.crypto (digest m.ctx.crypto ds (structHash m.ctx.crypto owner spender value
      (m.world.sload m.frame.msg.currentTarget (nonceSlot m.ctx.crypto owner)) deadline)) v r s
      owner →
    o = .success .empty ∧
    mf.world = permitWorld m.ctx.crypto m.world m.frame.msg.currentTarget owner spender value ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs.push
      (approvalLog m.frame.msg.currentTarget owner spender value)) ∧
  (¬ RecoversTo m.ctx.crypto (digest m.ctx.crypto ds (structHash m.ctx.crypto owner spender value
      (m.world.sload m.frame.msg.currentTarget (nonceSlot m.ctx.crypto owner)) deadline)) v r s
      owner → ∃ out, o = .revert out) ∧
  m.frame.gasLeft ≤ mf.frame.gasLeft + 80000

theorem prefix_eq :
    (Bytes.ofWord 11309588061646438093662687302255421419811724423900836950936401294474059186176#256).extract
      0 2 = eip712Prefix := by
  kernel_decide

set_option maxHeartbeats 0 in
theorem asset_permit_body {ia : SolmateAsset.Immutables} (m : Machine) {M : Memory} {F S : Nat}
    {ds deadline value v r s : Word} {owner spender : Address}
    (hFS : (F = 128 ∧ S = 96) ∨ (F = 320 ∧ S = 320))
    (hc : m.frame.code = SolmateAsset.runtimeCodeWith ia)
    (hj : JumpTable m.frame.jumpDests (SolmateAsset.runtimeCodeWith ia))
    (hpc : m.frame.pc = 1382)
    (hs : m.frame.stack = [ds, 1#256, 0#256, s, r, v, deadline, value, Word.ofAddress spender,
      Word.ofAddress owner, 424#256, 3573918927#256])
    (hmem : m.frame.memory = M) (hM64 : M.loadWord 64 = BitVec.ofNat 256 F) (hMs : M.size = S)
    (hv : v &&& 255#256 = v)
    (hg : 90000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel1 : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hstatic : m.frame.msg.isStatic = false) :
    WP m (fun _ => False) (BodyPost ds owner spender value deadline v r s m) := by
  have hagree := assetJumpDestsAgree ia
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hc hpc hs hmem hstd
  rcases hFS with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · pwp_run_to 1420 [hM64, hMs, permit_norm, ofAddress_and_addressMask, addressMask_and_ofAddress,
      Memory.read_64, hstatic]
    generalize hN : m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress owner) ++ Bytes.ofWord 5#256)) = nonce
    wp_generalize_gas g1 hg1
    have hg1' : m_gasLeft ≤ g1 + 30000 := by subst hg1; evm_gas
    have hg1'' : 60000 ≤ g1 := by subst hg1; evm_gas
    have hg1u : g1 ≤ m_gasLeft := by subst hg1; omega
    clear hg1
    -- the struct hash
    wp_generalize_mem M1 hM1
    have hM1a := congrArg (Memory.loadWord · 64) hM1
    have hM1b := congrArg Memory.size hM1
    simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord_of_disjoint,
      hM64] at hM1a
    simp only [permit_norm, hMs] at hM1b
    clear hM1
    replace hM1a := hM1a.symm
    replace hM1b := hM1b.symm
    pwp_run_to 1522 [hM1a, hM1b, permit_norm, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_192]
    -- the digest
    wp_generalize_mem M2 hM2
    have hM2a := congrArg (Memory.loadWord · 64) hM2
    have hM2b := congrArg Memory.size hM2
    simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord] at hM2a
    simp only [permit_norm, hM1b] at hM2b
    clear hM2
    replace hM2a := hM2a.symm
    replace hM2b := hM2b.symm
    pwp_run_to 1580 [hM2a, hM2b, permit_norm, Memory.read_66, Memory.read_storeWord_two,
      prefix_eq]
    -- the input of `ecrecover`
    wp_generalize_mem M3 hM3
    have hM3a := congrArg (Memory.loadWord · 64) hM3
    have hM3b := congrArg Memory.size hM3
    simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord] at hM3a
    simp only [permit_norm, hM2b] at hM3b
    clear hM3
    replace hM3a := hM3a.symm
    replace hM3b := hM3b.symm
    pwp_run_to 1631 [hM3a, hM3b, permit_norm, hv]
    refine WP.mono (asset_permit_tail _
      (dg := digest m_ctx.crypto ds (structHash m_ctx.crypto owner spender value nonce deadline))
      (by decide) rfl hj rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ rfl
      (by dsimp only; rw [World.code_sstore]; exact hdel1) hdepth hstatic) (fun _ _ h => h) ?_
    · simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord_of_disjoint,
        Memory.loadWord_storeWord]
    · simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord_of_disjoint,
        Memory.loadWord_storeWord]
    · simp (disch := decide) only [Memory.read_128, Memory.read_expand, Memory.read_storeWord,
        Memory.read_storeWord_of_disjoint]
      rfl
    · simp only [permit_norm, hM3b]
    · dsimp only; omega
    · dsimp only; omega
    intro mf o _ ht
    obtain ⟨h1, h2, h3⟩ := ht
    subst hN
    refine ⟨fun hr => ?_, fun hr => h2 hr, ?_⟩
    · obtain ⟨ho, hw, ht, hc, hl⟩ := h1 hr
      exact ⟨ho, hw, ht, hc, hl⟩
    dsimp only at h3 ⊢
    omega

end Verified.Solmate.ERC20.Permit

end

section

/-! ## The asset's `permit`, in any frame -/

namespace Verified.Solmate.ERC20.Permit
open QEDefi.ERC4626

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts

/-- A `permit` result for separator `ds`: success with `permitWorld` and one `Approval` log
exactly when `PermitValid` at the owner's current nonce, else a revert; ≤ 100000 gas. -/
def PermitPost (ds : Word) (owner spender : Address) (value deadline v r s : Word) (m mf : Machine)
    (o : Outcome) : Prop :=
  (PermitValid m.ctx.crypto ds m.ctx.block.timestamp owner spender value deadline v r s
      (m.world.sload m.frame.msg.currentTarget (nonceSlot m.ctx.crypto owner)) →
    o = .success .empty ∧
    mf.world = permitWorld m.ctx.crypto m.world m.frame.msg.currentTarget owner spender value ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs.push
      (approvalLog m.frame.msg.currentTarget owner spender value)) ∧
  (¬ PermitValid m.ctx.crypto ds m.ctx.block.timestamp owner spender value deadline v r s
      (m.world.sload m.frame.msg.currentTarget (nonceSlot m.ctx.crypto owner)) →
    ∃ out, o = .revert out) ∧
  m.frame.gasLeft ≤ mf.frame.gasLeft + 100000

theorem and_255_of_lt {x : Word} (h : x.toNat < 256) : x &&& 255#256 = x := by
  apply BitVec.eq_of_toNat_eq
  have h255 : (255#256).toNat = 2 ^ 8 - 1 := by simp
  rw [BitVec.toNat_and, h255, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by simpa using h)]

theorem and_255_ne {x : Word} (h : 256 ≤ x.toNat) : x &&& 255#256 ≠ x := by
  intro he
  have := congrArg BitVec.toNat he
  have h255 : (255#256).toNat = 2 ^ 8 - 1 := by simp
  rw [BitVec.toNat_and, h255, Nat.and_two_pow_sub_one_eq_mod] at this
  have := Nat.mod_lt x.toNat (show 2 ^ 8 > 0 by decide)
  omega

set_option maxHeartbeats 0 in
/-- **`permit` of the asset, in any fresh non-static frame**, for every `Crypto`: `PermitPost`
under the domain separator `dsOf …`. Assumes the standard precompiles (`hstd`), `0x01` not
delegated, room for one more frame, `100000 ≤ gas < 2⁶⁴`, and `DomainCase`. -/
theorem asset_permit_halts {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false)
    {owner spender : Address} {value deadline v r s : Word}
    (hd : PermitCall m.frame.msg.data owner spender value deadline v r s)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hcase : DomainCase ia.initialChainId (ofNat m.ctx.block.chainId)
      (m.world.sload m.frame.msg.currentTarget 0#256))
    (hg : 100000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel1 : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit) :
    Halts m (PermitPost (dsOf ia.initialChainId ia.initialDomainSeparator m) owner spender value
      deadline v r s m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1, harg2, harg3, harg4, harg5, harg6⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 224))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  subst hstd
  unfold PermitPost PermitValid
  by_cases hv : v.toNat < 256
  swap
  · -- `v` is not a `uint8`: the decoder reverts
    have hne := eq_of_ne (Ne.symm (and_255_ne (x := v) (by omega)))
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, harg4,
      harg5, harg6, hne, ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self]
    refine ⟨fun h => absurd h.1 hv, fun _ => ⟨_, rfl⟩, ?_⟩
    dsimp only [outputMachine]; evm_gas
  have hv' := and_255_of_lt hv
  by_cases hdl : (ofNat m_ctx.block.timestamp).toNat ≤ deadline.toNat
  swap
  · -- the deadline has passed
    have hlt' : Word.lt deadline (ofNat m_ctx.block.timestamp) = 1 :=
      (Word.lt_eq_one_iff _ _).2 (by omega)
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, harg4,
      harg5, harg6, hv', hlt', ofAddress_and_addressMask, addressMask_and_ofAddress,
      Solidity.eq_self, iszero_one]
    refine ⟨fun h => absurd h.2.1 hdl, fun _ => ⟨_, rfl⟩, ?_⟩
    dsimp only [outputMachine]; evm_gas
  have hge : Word.lt deadline (ofNat m_ctx.block.timestamp) = 0 := (Word.lt_eq_zero_iff _ _).2 hdl
  pwp_run_to 1060 [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3,
    harg4, harg5, harg6, hv', hge, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Solidity.eq_self, iszero_zero]
  refine WP.bind_mono (asset_ds_wp _ rfl hj rfl rfl (by simp) (by pjumpdest_disch)
    (Memory.loadWord_storeWord _ _ _) (by simp [Memory.size_storeWord, Memory.size_expand,
      Memory.wordsAfter, Memory.words]) hcase (by dsimp only; omega) (by dsimp only; omega))
    (fun _ _ _ h => h.elim) ?_
  rintro _ - ⟨mem, g, sub, rfl, hmem, hgb, hgu, hlog⟩
  dsimp only [Machine.resumeWith] at hgb hgu hlog ⊢
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, dsOf]
  generalize domainSeparator m_ctx.crypto _ _ _ _ _ = ds
  rcases hmem with ⟨h64, hs⟩ | ⟨h64, hs⟩
  · refine WP.mono (asset_permit_body _ (F := 128) (S := 96) (.inl ⟨rfl, rfl⟩) rfl hj rfl rfl rfl
      h64 hs hv' (by dsimp only; omega) (by dsimp only; omega) rfl hdel1 hdepth hstatic)
      (fun _ _ h => h) ?_
    intro mf o _ ⟨h1, h2, h3⟩
    refine ⟨fun h => ?_, fun h => h2 fun h' => h ⟨hv, hdl, h'⟩, ?_⟩
    · obtain ⟨ho, hw, ht, hc, hl⟩ := h1 h.2.2
      exact ⟨ho, hw, ht, hc, hl.trans (by rw [hlog])⟩
    dsimp only at h3 ⊢
    omega
  · refine WP.mono (asset_permit_body _ (F := 320) (S := 320) (.inr ⟨rfl, rfl⟩) rfl hj rfl rfl rfl
      h64 hs hv' (by dsimp only; omega) (by dsimp only; omega) rfl hdel1 hdepth hstatic)
      (fun _ _ h => h) ?_
    intro mf o _ ⟨h1, h2, h3⟩
    refine ⟨fun h => ?_, fun h => h2 fun h' => h ⟨hv, hdl, h'⟩, ?_⟩
    · obtain ⟨ho, hw, ht, hc, hl⟩ := h1 h.2.2
      exact ⟨ho, hw, ht, hc, hl.trans (by rw [hlog])⟩
    dsimp only at h3 ⊢
    omega

end Verified.Solmate.ERC20.Permit

end
