import Verified.AaveV3.AToken.Mint.Success

/-!
# `AToken.mint` by the Pool: the effect on the scaled ledger

Reading `mintWorld` back through the views of `State.lean`: the user's scaled balance grows by
the scaled amount, the scaled total supply by the same amount (the ledger invariant
"Σ scaled balances = `_totalSupply`" is preserved), the user's previous index becomes `index`,
the delegation byte and every other slot are unchanged. `mint_halts_effect` packages these
with `mint_halts_ok`.
-/

namespace Verified.AaveV3.AToken
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open Verified.AaveV3.Contracts

variable {crypto : Crypto} {w : World} {t u : Address} {amt idx : Word}

theorem sload_mintWorld_user :
    (mintWorld crypto w t u amt idx).sload t (userStateSlot crypto u) =
      userWordMinted (amt + scaledBalance crypto w t u) (w.sload t (userStateSlot crypto u)) idx := by
  simp only [mintWorld, World.sload_sstore_self]

theorem sload_mintWorld_supply (hslot : userStateSlot crypto u ≠ 54#256) :
    (mintWorld crypto w t u amt idx).sload t 54#256 = amt + w.sload t 54#256 := by
  simp only [mintWorld]
  rw [World.sload_sstore_ne_key _ _ _ (fun e => hslot e.symm), World.sload_sstore_self]

theorem sload_mintWorld_other {k : Word} (hk : k ≠ userStateSlot crypto u) (hk' : k ≠ 54#256) :
    (mintWorld crypto w t u amt idx).sload t k = w.sload t k := by
  simp only [mintWorld]
  rw [World.sload_sstore_ne_key _ _ _ hk, World.sload_sstore_ne_key _ _ _ hk',
    World.sload_sstore_ne_key _ _ _ hk]

theorem sload_mintWorld_account {a : Address} (ha : a ≠ t) (k : Word) :
    (mintWorld crypto w t u amt idx).sload a k = w.sload a k := by
  simp only [mintWorld]
  rw [World.sload_sstore_ne_addr _ _ _ _ ha, World.sload_sstore_ne_addr _ _ _ _ ha,
    World.sload_sstore_ne_addr _ _ _ _ ha]

theorem toNat_scaledBalance (crypto : Crypto) (w : World) (t u : Address) :
    (scaledBalance crypto w t u).toNat =
      (w.sload t (userStateSlot crypto u)).toNat % 2 ^ 120 := by
  simp only [scaledBalance, BitVec.toNat_ofNat]; omega

/-- The new scaled balance is the old one plus the scaled amount. -/
theorem scaledBalance_mintWorld
    (hnb : (scaledBalance crypto w t u).toNat + amt.toNat < 2 ^ 120) :
    (scaledBalance crypto (mintWorld crypto w t u amt idx) t u).toNat =
      (scaledBalance crypto w t u).toNat + amt.toNat := by
  rw [toNat_scaledBalance, sload_mintWorld_user, toNat_userWordMinted_mod, BitVec.toNat_add,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.add_comm]

/-- The new previous index is `index`. -/
theorem previousIndex_mintWorld (hidx : idx.toNat < 2 ^ 128) :
    previousIndex crypto (mintWorld crypto w t u amt idx) t u = idx := by
  simp only [previousIndex]
  rw [sload_mintWorld_user, toNat_userWordMinted_div, Nat.mod_eq_of_lt hidx, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

/-- The delegation byte (byte 15 of `_userState[u]`) is unchanged. -/
theorem delegation_mintWorld :
    ((mintWorld crypto w t u amt idx).sload t (userStateSlot crypto u)).toNat / 2 ^ 120 % 2 ^ 8 =
      (w.sload t (userStateSlot crypto u)).toNat / 2 ^ 120 % 2 ^ 8 := by
  rw [sload_mintWorld_user, toNat_userWordMinted_deleg]

/-- The new scaled total supply is the old one plus the scaled amount. -/
theorem scaledTotalSupply_mintWorld (hslot : userStateSlot crypto u ≠ 54#256)
    (hsup : (scaledTotalSupply w t).toNat + amt.toNat < 2 ^ 256) :
    (scaledTotalSupply (mintWorld crypto w t u amt idx) t).toNat =
      (scaledTotalSupply w t).toNat + amt.toNat := by
  simp only [scaledTotalSupply] at hsup ⊢
  rw [sload_mintWorld_supply hslot, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega), Nat.add_comm]

/-- **The scaled ledger stays balanced**: `u`'s scaled balance and the scaled total supply grow
by the same amount. -/
theorem mintWorld_ledger (hslot : userStateSlot crypto u ≠ 54#256)
    (hnb : (scaledBalance crypto w t u).toNat + amt.toNat < 2 ^ 120)
    (hsup : (scaledTotalSupply w t).toNat + amt.toNat < 2 ^ 256) :
    (scaledBalance crypto (mintWorld crypto w t u amt idx) t u).toNat +
        (scaledTotalSupply w t).toNat =
      (scaledBalance crypto w t u).toNat +
        (scaledTotalSupply (mintWorld crypto w t u amt idx) t).toNat := by
  rw [scaledBalance_mintWorld hnb, scaledTotalSupply_mintWorld hslot hsup]; omega

/-- What `mint(_, u, amt, idx)` does to the scaled ledger, read through the views. -/
def MintEffect (u : Address) (amt idx : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord (Word.iszero
    (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u))) ∧
  (scaledBalance m.ctx.crypto mf.world m.frame.msg.currentTarget u).toNat =
    (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat + amt.toNat ∧
  (scaledTotalSupply mf.world m.frame.msg.currentTarget).toNat =
    (scaledTotalSupply m.world m.frame.msg.currentTarget).toNat + amt.toNat ∧
  previousIndex m.ctx.crypto mf.world m.frame.msg.currentTarget u = idx ∧
  (mf.world.sload m.frame.msg.currentTarget (userStateSlot m.ctx.crypto u)).toNat / 2 ^ 120 %
      2 ^ 8 =
    (m.world.sload m.frame.msg.currentTarget (userStateSlot m.ctx.crypto u)).toNat / 2 ^ 120 %
      2 ^ 8 ∧
  ∀ k, k ≠ userStateSlot m.ctx.crypto u → k ≠ 54#256 →
    mf.world.sload m.frame.msg.currentTarget k = m.world.sload m.frame.msg.currentTarget k

theorem MintOk.effect {u : Address} {amt idx : Word} {m mf : Machine} {o : Outcome}
    (h : MintOk u amt idx m mf o) (hslot : userStateSlot m.ctx.crypto u ≠ 54#256)
    (hnb : (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat + amt.toNat <
      2 ^ 120)
    (hidx : idx.toNat < 2 ^ 128)
    (hsup : (scaledTotalSupply m.world m.frame.msg.currentTarget).toNat + amt.toNat < 2 ^ 256) :
    MintEffect u amt idx m mf o := by
  obtain ⟨ho, hw⟩ := h
  refine ⟨ho, ?_, ?_, ?_, ?_, fun k hk hk' => by rw [hw, sload_mintWorld_other hk hk']⟩
  · simp only [scaledBalance] at hnb ⊢
    rw [hw]
    exact scaledBalance_mintWorld hnb
  · simp only [scaledTotalSupply]
    rw [hw]
    exact scaledTotalSupply_mintWorld hslot hsup
  · simp only [previousIndex]
    rw [hw]
    exact previousIndex_mintWorld hidx
  · rw [hw]; exact delegation_mintWorld

/-- **`mint` by the Pool, on the scaled ledger** (hypotheses of `mint_halts_ok`): returns
whether `u` held nothing, `u`'s scaled balance and the scaled total supply both grow by `amt`,
`u`'s previous index becomes `idx`, its delegation byte and every other slot of the executing
account are unchanged. -/
theorem mint_halts_effect (m : Machine) (hf : Fresh AToken.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xb3f1c93d)
    (hsize : 132 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    {c u : Address} {amt idx : Word}
    (harg0 : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress c)
    (harg1 : Bytes.toWord (readBytes m.frame.msg.data 36 32) = Word.ofAddress u)
    (harg2 : Bytes.toWord (readBytes m.frame.msg.data 68 32) = amt)
    (harg3 : Bytes.toWord (readBytes m.frame.msg.data 100 32) = idx)
    (hc : m.frame.msg.caller = pool)
    (hg : 1000000 ≤ m.frame.gasLeft)
    (hslot : userStateSlot m.ctx.crypto u ≠ 54#256)
    (hamt : amt ≠ 0)
    (hnb : (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat + amt.toNat <
      2 ^ 120)
    (hidx : idx.toNat < 2 ^ 128)
    (hmul : ((scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat + amt.toNat) *
      idx.toNat < 2 ^ 256)
    (hinc : (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat *
        (previousIndex m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat /
          1000000000000000000000000000 ≤
      (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat * idx.toNat /
        1000000000000000000000000000)
    (hsup : (scaledTotalSupply m.world m.frame.msg.currentTarget).toNat + amt.toNat < 2 ^ 256)
    (hrcOk : HandleActionOk (m.world.code rewardsController) m.frame.msg.currentTarget)
    (hcs : (m.world.code rewardsController).size ≠ 0)
    (hcs2 : (m.world.code rewardsController).size < 2 ^ 256)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code rewardsController) = none)
    (hpre : m.precompiles.isPrecompile rewardsController = false)
    (hdepth : m.frame.msg.depth < 1024) :
    Halts m (MintEffect u amt idx m) :=
  (mint_halts_ok m hf hval hstatic hsel hsize hsize' harg0 harg1 harg2 harg3 hc hg hslot hamt
    hnb hidx hmul hinc hsup hrcOk hcs hcs2 hdel hpre hdepth).mono
    fun _ _ _ h => h.effect hslot hnb hidx hsup

end Verified.AaveV3.AToken
