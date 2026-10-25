import Verified.AaveV3.AToken.Havoc.Run

/-!
# `initialize` reverts, `rescueTokens` writes nothing

`initialize(…)` runs `VersionedInitializable.initializer`: with `initializing = false`, the
executing account holding code (`isConstructor()` is false) and `lastInitializedRevision ≥ 5`
(all part of `Good`), it reverts before any write. `rescueTokens(token, to, amount)` asks the ACL
manager (two static calls of untrusted code) and calls `token` (any account, also a protected
one: `pwp_call_any`); it writes nothing.
-/

namespace Verified.AaveV3.AToken.Havoc
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
  EvmLogic.Program.Reentrancy EvmLogic.Solidity Verified.AaveV3.Contracts

theorem init_byte {crypto : Crypto} {w : World} {t : Address} (h : TokenOk crypto w t) :
    255#256 &&& w.sload t 1#256 = 0#256 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, Nat.and_comm,
    show (255#256 : Word).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact h.init

theorem rev_gt {crypto : Crypto} {w : World} {t : Address} (h : TokenOk crypto w t) :
    Word.gt 5#256 (w.sload t 0#256) = 0#256 :=
  (gt_eq_zero_iff _ _).2 h.rev

theorem codesize_iszero {crypto : Crypto} {w : World} {t : Address} (h : Good crypto w)
    (ht : Prot t) : (ofNat (w.code t).size : Word).iszero = 0#256 := by
  refine (iszero_eq_zero_iff _).2 ?_
  have hs := h.code_size t ht
  have hlt : (w.code t).size < 2 ^ 256 := by
    rcases ht with rfl | rfl
    · rw [h.proxyCode, ATokenProxy.size_runtimeCode]; decide
    · rw [h.implCode, AToken.size_runtimeCode]; decide
  simp only [ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]; exact hs

theorem Good.tokenOk {crypto : Crypto} {w : World} {t : Address} (h : Good crypto w)
    (ht : Prot t) : TokenOk crypto w t := by
  rcases ht with rfl | rfl
  · exact h.proxyOk
  · exact h.implOk

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
-- `initialize` reverts before any external call, so the shared call handler never runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- `initialize(…)`: reverts. -/
theorem body_initialize : BodyOk 1053 := by
  intro G ctx w tr ow created msg jd sel g sub snap ko ks parents hK hcov hg hsnap hw hst ht
  have h1 := init_byte (hw.tokenOk ht)
  have h2 := codesize_iszero hw ht
  have h3 := rev_gt (hw.tokenOk ht)
  apwp_run [mask_and_eq, and_mask_eq, Word.toAddress_ofAddress, keccak_mappingSlot,
    EvmLogic.Solidity.eq_self, addressMask_and_ofAddress, h1, h2, h3] using atok_handle

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `rescueTokens(token, to, amount)`: writes nothing. -/
theorem body_rescueTokens : BodyOk 1277 := by
  atok_run

end Verified.AaveV3.AToken.Havoc
