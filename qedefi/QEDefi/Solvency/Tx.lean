import QEDefi.Solvency.Bank
import EvmLogic.Tx.Lift

/-!
# Ether across a transaction

All ether in the world (`supply`) never grows over a successful transaction
(`process_supply_le`): the prefix debits the upfront fee from the sender, the top-level message
call creates no ether (`processMessageCall_supply_le`, the ether-aware havoc theorem with no
protected account), and the suffix credits back at most the execution part of the fee (refund to
the sender, priority fee to the coinbase; the base fee and the blob fee are burned), then only
erases accounts.

`process_keeps_ether`: the lifting theorem of `EvmLogic.Tx.Lift` for invariants about ether,
such as bank solvency (`Solvent`): the invariant need only be kept by changes that keep storage
and code of the protected accounts, do not decrease their balances, and keep all ether below
`2²⁵⁶`. The coinbase reward cannot wrap a protected account's balance, because all ether stays
below `2²⁵⁶`.
-/

namespace QEDefi.Solvency
open EvmLean EvmLean.Interpreter EvmLean.Tx EvmLogic EvmLogic.Program EvmLogic.Program.Nested
  EvmLogic.Program.Reentrancy EvmLogic.Tx

/-! ## Changing one balance -/

/-- Changing one balance changes all ether by the difference. -/
theorem supply_add_of_balances {w w' : World} {a : Address}
    (h : ∀ b, b ≠ a → w'.balance b = w.balance b) :
    supply w' + (w.balance a).toNat = supply w + (w'.balance a).toNat := by
  let f : Address → Nat := fun b => (w.balance b).toNat
  have hb : ∀ b, (w'.balance b).toNat = Function.update f a (w'.balance a).toNat b := by
    intro b
    by_cases hba : b = a
    · subst hba; simp
    · simp [hba, f, h b hba]
  have e := sum_update_add f a (w'.balance a).toNat
  have : supply w' = ∑ b, Function.update f a (w'.balance a).toNat b :=
    Finset.sum_congr rfl fun b _ => hb b
  rw [this]; simp only [supply]; simp only [f] at e ⊢; omega

theorem balance_le_supply (w : World) (a : Address) : (w.balance a).toNat ≤ supply w :=
  le_sum (fun b => (w.balance b).toNat) a

/-! ## The prefix -/

/-- **The prefix debits the fee**: when the sender can pay `fee`, all ether drops by `fee`. -/
theorem supply_prefixWorld {w : World} {s : Address} {fee : Nat}
    (hfee : fee ≤ (w.account s).balance.toNat) :
    supply (prefixWorld w s (BitVec.ofNat 256 ((w.account s).balance.toNat - fee))) + fee =
      supply w := by
  have h := supply_add_of_balances (w := w)
    (w' := prefixWorld w s (BitVec.ofNat 256 ((w.account s).balance.toNat - fee))) (a := s)
    (fun b hb => by rw [balance_prefixWorld]; simp [hb])
  rw [balance_prefixWorld] at h
  simp only [ite_true, BitVec.toNat_ofNat] at h
  have hlt := ((w.account s).balance).isLt
  rw [Nat.mod_eq_of_lt (by omega)] at h
  simp only [World.balance] at h
  omega

/-! ## The suffix -/

/-- A credit that keeps all ether below `2²⁵⁶` adds to all ether and to the credited balance. -/
theorem supply_creditBalance {w : World} {a : Address} {k : Nat} (h : supply w + k < 2 ^ 256) :
    supply (creditBalance w a k) = supply w + k ∧
      ∀ b, (w.balance b).toNat ≤ ((creditBalance w a k).balance b).toNat := by
  have hle := balance_le_supply w a
  have hca := toNat_balance_creditBalance_self (w := w) (a := a) (k := k) (by omega)
  have e := supply_add_of_balances (w := w) (w' := creditBalance w a k) (a := a)
    (fun b hb => by rw [balance_creditBalance]; simp [hb])
  refine ⟨by omega, fun b => ?_⟩
  by_cases hb : b = a
  · subst hb; omega
  · rw [balance_creditBalance]; simp [hb]

theorem supply_foldl_erase_le (s : AddressSet) (w : World) :
    supply (s.foldl (fun w a => w.erase a) w) ≤ supply w := by
  refine Finset.sum_le_sum fun b _ => ?_
  simp only [World.balance]
  rw [account_foldl_erase]
  split
  · simp
  · exact Nat.le_refl _

theorem supply_destroyTouchedEmpty (w : World) (t : AddressSet) :
    supply (destroyTouchedEmpty w t) = supply w := by
  simp [supply, destroyTouchedEmpty_balance]

/-- **The suffix credits at most the two amounts**, and keeps or raises every balance outside
`accountsToDelete`, when all ether stays below `2²⁵⁶`. -/
theorem supply_suffixWorld {r : MessageResult} {sender coinbase : Address} {refund reward : Nat}
    (h : supply r.world + refund + reward < 2 ^ 256) :
    supply (suffixWorld r sender coinbase refund reward) ≤ supply r.world + refund + reward ∧
      ∀ p, p ∉ r.accountsToDelete → (r.world.balance p).toNat ≤
        ((suffixWorld r sender coinbase refund reward).balance p).toNat := by
  obtain ⟨e1, b1⟩ := supply_creditBalance (w := r.world) (a := sender) (k := refund) (by omega)
  obtain ⟨e2, b2⟩ := supply_creditBalance (w := creditBalance r.world sender refund)
    (a := coinbase) (k := reward) (by omega)
  refine ⟨?_, fun p hp => ?_⟩
  · unfold suffixWorld
    rw [supply_destroyTouchedEmpty]
    exact Nat.le_trans (supply_foldl_erase_le _ _) (by omega)
  · rw [balance_suffixWorld _ _ _ _ _ hp]
    exact Nat.le_trans (b1 p) (b2 p)

/-! ## The top-level message call creates no ether -/

/-- "All ether is at most `S`" is closed under everything code can do, when `S < 2²⁵⁶`. -/
theorem goodOps_supply_le {S : Nat} (hS : S < 2 ^ 256) :
    GoodOps (fun _ => False) (fun w => supply w ≤ S) where
  code _ _ _ h := h.elim
  deleg _ _ _ h := h.elim
  sstore w a k v h _ := by rw [supply_sstore]; exact h
  nonce w a h := by rw [supply_incrementNonce]; exact h
  move w src dst v h hv _ := by rw [supply_moveEther hv (by omega)]; exact h
  burn w a h _ := Nat.le_trans (supply_setAccountBalance_zero w a) h
  setCode w a c h _ := by rw [supply_setCode]; exact h

/-- **A top-level message call creates no ether**: from a world whose ether is below `2²⁵⁶`, any
top-level message that moves its value (any caller, code, calldata), before Prague or without
EIP-7702 authorizations, ends with at most as much ether. -/
theorem processMessageCall_supply_le {fuel : Nat} {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} {r : MessageResult} (hs : supply w < 2 ^ 256)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hdepth : msg.depth = 0)
    (htarget : msg.target = some msg.currentTarget ∨ msg.target = none)
    (hv : msg.shouldTransferValue = true)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) : supply r.world ≤ supply w :=
  processMessageCall_good_v (C := fun _ => True) (goodOps_supply_le hs) (Nat.le_refl _) hdeleg
    ⟨hdepth, id, htarget, fun h => h.elim⟩ hv trivial (fun _ hd => hd.danger.1.elim) hr

/-! ## Transactions -/

theorem credits_le {gas gu p b : Nat} (hgu : gu ≤ gas) :
    (gas - gu) * p + gu * (p - b) ≤ gas * p := by
  have h1 : gu * (p - b) ≤ gu * p := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h2 : (gas - gu) * p + gu * p = gas * p := by rw [← Nat.add_mul, Nat.sub_add_cancel hgu]
  omega

/-- **An ether invariant of top-level message calls is an invariant of transactions.** If `Inv`
holds only in worlds where the protected accounts (`P`) hold real code (`hP`) and all ether is
below `2²⁵⁶` (`hcap`), is kept by every top-level message call with the `TopMsg` facts (`hmsg`),
and is kept by every change that keeps storage and code of the protected accounts, does not
decrease their balances and keeps all ether below `2²⁵⁶` (`hframe`), then every successful
transaction before Prague or without EIP-7702 authorizations (`hdeleg`, for
`processMessageCall_supply_le`) keeps it, and all ether does not grow. -/
theorem process_keeps_ether {P : Address → Prop} {Inv : World → Prop} {fuel : Nat}
    {crypto : Crypto} {fork : Fork} {env : BlockEnv} {gasAvail blobAvail : Nat} {w : World}
    {tx : Transaction} {hint : Option Address} {out : TxOutput}
    (hP : ∀ w, Inv w → ∀ p, P p → RealCode (w.code p))
    (hcap : ∀ w, Inv w → supply w < 2 ^ 256)
    (hmsg : ∀ (ctx : Context) (w₁ : World) (msg : Message) (r : MessageResult), Inv w₁ →
      TopMsg P crypto fork env tx w₁ ctx msg → processMessageCall fuel ctx w₁ ∅ msg = .ok r →
      Inv r.world)
    (hframe : ∀ w w', Inv w →
      (∀ p, P p → Keep p w w' ∧ (w.balance p).toNat ≤ (w'.balance p).toNat) →
      supply w' < 2 ^ 256 → Inv w')
    (hdeleg : fork < .prague ∨ tx.authorizations = [])
    (hw : Inv w) (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    Inv out.world ∧ supply out.world ≤ supply w := by
  obtain ⟨c, ctx, msg, r, gu, hc, hm, hr, hgu, hout⟩ := process_split (hP w hw) h
  have hchk := check_ok hc
  have hfee : upfrontFee fork env tx c ≤ (w.account c.sender).balance.toNat := by
    have := hchk.2.2.2.1; omega
  have hs1 := supply_prefixWorld hfee
  have hsw := hcap w hw
  have hsender : ∀ p, P p → p ≠ c.sender := fun p hp he =>
    not_realCode_sender hc (he ▸ hP w hw p hp)
  have h1 := hframe w (prefixWorld w c.sender
    (BitVec.ofNat 256 ((w.account c.sender).balance.toNat - upfrontFee fork env tx c))) hw
    (fun p hp => ⟨keep_prefixWorld w c.sender _ p, by
    rw [balance_prefixWorld]; simp [hsender p hp]⟩) (by omega)
  have h2 := hmsg ctx _ msg r h1 hm hr
  have hs2 := processMessageCall_supply_le (by omega) (hm.deleg hdeleg) hm.top.depth
    hm.top.target hm.transfers hr
  have hcr := credits_le (p := c.effectiveGasPrice) (b := env.baseFee) hgu
  have hfee' : tx.gas * c.effectiveGasPrice ≤ upfrontFee fork env tx c := by
    unfold upfrontFee; omega
  have hsum : supply r.world + (tx.gas - gu) * c.effectiveGasPrice +
      gu * (c.effectiveGasPrice - env.baseFee) ≤ supply w := by
    generalize supply (prefixWorld w c.sender _) = S1 at hs1 hs2
    generalize (tx.gas - gu) * c.effectiveGasPrice = R at hcr ⊢
    generalize gu * (c.effectiveGasPrice - env.baseFee) = W at hcr ⊢
    generalize tx.gas * c.effectiveGasPrice = T at hcr hfee'
    generalize upfrontFee fork env tx c = F at hfee' hs1
    omega
  obtain ⟨hs3, hb3⟩ := supply_suffixWorld (r := r) (sender := c.sender) (coinbase := env.coinbase)
    (refund := (tx.gas - gu) * c.effectiveGasPrice)
    (reward := gu * (c.effectiveGasPrice - env.baseFee)) (by omega)
  rw [hout]
  refine ⟨hframe _ _ h2 (fun p hp => ?_) (by omega), by omega⟩
  obtain ⟨hd, hsz⟩ := processMessageCall_realCode hr (hm.real p hp)
  exact ⟨keep_suffixWorld hsz hd _ _ _ _, hb3 p hd⟩

end QEDefi.Solvency
