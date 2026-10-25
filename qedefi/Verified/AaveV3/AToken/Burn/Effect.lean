import Verified.AaveV3.AToken.Burn.Success
import Verified.AaveV3.AToken.Mint.Effect

/-!
# `AToken.burn` by the Pool: the effect on the scaled ledger

Reading `burnWorld` back through the views: the user's scaled balance and the scaled total
supply both shrink by the scaled amount (the ledger stays balanced), the user's previous index
becomes `index`, the delegation byte and every other slot are unchanged.
-/

namespace Verified.AaveV3.AToken
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open Verified.AaveV3.Contracts

variable {crypto : Crypto} {w : World} {t u : Address} {amt idx : Word}

theorem sload_burnWorld_user :
    (burnWorld crypto w t u amt idx).sload t (userStateSlot crypto u) =
      userWordMinted (scaledBalance crypto w t u - amt) (w.sload t (userStateSlot crypto u)) idx := by
  simp only [burnWorld, World.sload_sstore_self]

theorem sload_burnWorld_supply (hslot : userStateSlot crypto u ≠ 54#256) :
    (burnWorld crypto w t u amt idx).sload t 54#256 = w.sload t 54#256 - amt := by
  simp only [burnWorld]
  rw [World.sload_sstore_ne_key _ _ _ (fun e => hslot e.symm), World.sload_sstore_self]

theorem sload_burnWorld_other {k : Word} (hk : k ≠ userStateSlot crypto u) (hk' : k ≠ 54#256) :
    (burnWorld crypto w t u amt idx).sload t k = w.sload t k := by
  simp only [burnWorld]
  rw [World.sload_sstore_ne_key _ _ _ hk, World.sload_sstore_ne_key _ _ _ hk',
    World.sload_sstore_ne_key _ _ _ hk]

/-- The new scaled balance is the old one minus the scaled amount. -/
theorem scaledBalance_burnWorld (hle : amt.toNat ≤ (scaledBalance crypto w t u).toNat) :
    (scaledBalance crypto (burnWorld crypto w t u amt idx) t u).toNat =
      (scaledBalance crypto w t u).toNat - amt.toNat := by
  have hlt : (scaledBalance crypto w t u).toNat < 2 ^ 120 := by
    rw [toNat_scaledBalance]; exact Nat.mod_lt _ (by decide)
  rw [toNat_scaledBalance, sload_burnWorld_user, toNat_userWordMinted_mod,
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle), Nat.mod_eq_of_lt (by omega)]

/-- The new previous index is `index`. -/
theorem previousIndex_burnWorld (hidx : idx.toNat < 2 ^ 128) :
    previousIndex crypto (burnWorld crypto w t u amt idx) t u = idx := by
  simp only [previousIndex]
  rw [sload_burnWorld_user, toNat_userWordMinted_div, Nat.mod_eq_of_lt hidx, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

/-- The delegation byte is unchanged. -/
theorem delegation_burnWorld :
    ((burnWorld crypto w t u amt idx).sload t (userStateSlot crypto u)).toNat / 2 ^ 120 % 2 ^ 8 =
      (w.sload t (userStateSlot crypto u)).toNat / 2 ^ 120 % 2 ^ 8 := by
  rw [sload_burnWorld_user, toNat_userWordMinted_deleg]

/-- The new scaled total supply is the old one minus the scaled amount. -/
theorem scaledTotalSupply_burnWorld (hslot : userStateSlot crypto u ≠ 54#256)
    (hsup : amt.toNat ≤ (scaledTotalSupply w t).toNat) :
    (scaledTotalSupply (burnWorld crypto w t u amt idx) t).toNat =
      (scaledTotalSupply w t).toNat - amt.toNat := by
  simp only [scaledTotalSupply] at hsup ⊢
  rw [sload_burnWorld_supply hslot, BitVec.toNat_sub_of_le (BitVec.le_def.mpr hsup)]

/-- **The scaled ledger stays balanced** under `burn`. -/
theorem burnWorld_ledger (hslot : userStateSlot crypto u ≠ 54#256)
    (hle : amt.toNat ≤ (scaledBalance crypto w t u).toNat)
    (hsup : amt.toNat ≤ (scaledTotalSupply w t).toNat) :
    (scaledBalance crypto (burnWorld crypto w t u amt idx) t u).toNat +
        (scaledTotalSupply w t).toNat =
      (scaledBalance crypto w t u).toNat +
        (scaledTotalSupply (burnWorld crypto w t u amt idx) t).toNat := by
  rw [scaledBalance_burnWorld hle, scaledTotalSupply_burnWorld hslot hsup]; omega

/-- What `burn(u, _, _, amt, idx)` does to the scaled ledger, read through the views. -/
def BurnEffect (u : Address) (amt idx : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord (Word.iszero
    (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u - amt))) ∧
  (scaledBalance m.ctx.crypto mf.world m.frame.msg.currentTarget u).toNat =
    (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat - amt.toNat ∧
  (scaledTotalSupply mf.world m.frame.msg.currentTarget).toNat =
    (scaledTotalSupply m.world m.frame.msg.currentTarget).toNat - amt.toNat ∧
  previousIndex m.ctx.crypto mf.world m.frame.msg.currentTarget u = idx ∧
  (mf.world.sload m.frame.msg.currentTarget (userStateSlot m.ctx.crypto u)).toNat / 2 ^ 120 %
      2 ^ 8 =
    (m.world.sload m.frame.msg.currentTarget (userStateSlot m.ctx.crypto u)).toNat / 2 ^ 120 %
      2 ^ 8 ∧
  ∀ k, k ≠ userStateSlot m.ctx.crypto u → k ≠ 54#256 →
    mf.world.sload m.frame.msg.currentTarget k = m.world.sload m.frame.msg.currentTarget k

theorem BurnOk.effect {u : Address} {amt idx : Word} {m mf : Machine} {o : Outcome}
    (h : BurnOk u amt idx m mf o) (hslot : userStateSlot m.ctx.crypto u ≠ 54#256)
    (hle : amt.toNat ≤ (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat)
    (hidx : idx.toNat < 2 ^ 128)
    (hsup : amt.toNat ≤ (scaledTotalSupply m.world m.frame.msg.currentTarget).toNat) :
    BurnEffect u amt idx m mf o := by
  obtain ⟨ho, hw⟩ := h
  refine ⟨ho, ?_, ?_, ?_, ?_, fun k hk hk' => by rw [hw, sload_burnWorld_other hk hk']⟩
  · simp only [scaledBalance] at hle ⊢
    rw [hw]
    exact scaledBalance_burnWorld hle
  · simp only [scaledTotalSupply]
    rw [hw]
    exact scaledTotalSupply_burnWorld hslot hsup
  · simp only [previousIndex]
    rw [hw]
    exact previousIndex_burnWorld hidx
  · rw [hw]; exact delegation_burnWorld

/-- **`burn` by the Pool, on the scaled ledger** (hypotheses of `burn_halts_ok`): `u`'s scaled
balance and the scaled total supply both shrink by `amt`, `u`'s previous index becomes `idx`, its
delegation byte and every other slot of the executing account are unchanged. -/
theorem burn_halts_effect (m : Machine) (hf : Fresh AToken.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xb18d6afd)
    (hsize : 164 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    {u r : Address} {amount amt idx : Word}
    (harg0 : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress u)
    (harg1 : Bytes.toWord (readBytes m.frame.msg.data 36 32) = Word.ofAddress r)
    (harg2 : Bytes.toWord (readBytes m.frame.msg.data 68 32) = amount)
    (harg3 : Bytes.toWord (readBytes m.frame.msg.data 100 32) = amt)
    (harg4 : Bytes.toWord (readBytes m.frame.msg.data 132 32) = idx)
    (hc : m.frame.msg.caller = pool)
    (hg : 5000000 ≤ m.frame.gasLeft)
    (hrcOk : HandleActionOkCode (m.world.code rewardsController) m.frame.msg.currentTarget)
    (hcs : (m.world.code rewardsController).size ≠ 0)
    (hcs2 : (m.world.code rewardsController).size < 2 ^ 256)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code rewardsController) = none)
    (hpre : m.precompiles.isPrecompile rewardsController = false)
    (hdepth : m.frame.msg.depth < 1024)
    (hr : r ≠ m.frame.msg.currentTarget)
    (hslot61 : userStateSlot m.ctx.crypto u ≠ 61#256)
    (hTok : TransferOk (underlyingAddress m.world m.frame.msg.currentTarget)
      m.frame.msg.currentTarget)
    (hdelU : m.ctx.fork < .prague ∨ delegatedAddress?
      (m.world.code (underlyingAddress m.world m.frame.msg.currentTarget)) = none)
    (hpreU : m.precompiles.isPrecompile (underlyingAddress m.world m.frame.msg.currentTarget) =
      false)
    (hamt : amt ≠ 0) (hslot : userStateSlot m.ctx.crypto u ≠ 54#256)
    (hle : amt.toNat ≤ (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat)
    (hsupLe : amt.toNat ≤ (scaledTotalSupply m.world m.frame.msg.currentTarget).toNat)
    (hidx : idx.toNat < 2 ^ 128)
    (hmul : (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat * idx.toNat <
      2 ^ 256)
    (hinc : (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat *
        (previousIndex m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat /
          1000000000000000000000000000 ≤
      (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat * idx.toNat /
        1000000000000000000000000000) :
    Halts m (BurnEffect u amt idx m) :=
  (burn_halts_ok m hf hval hstatic hsel hsize hsize' harg0 harg1 harg2 harg3 harg4 hc hg
    hrcOk hcs hcs2 hdel hpre hdepth hr hslot61 hTok hdelU hpreU hamt hslot hle hsupLe hidx hmul
    hinc).mono
    fun _ _ _ h => h.effect hslot hle hidx hsupLe

end Verified.AaveV3.AToken
