import Verified.WETH9.Rows
import Verified.WETH9.Tx7702

/-!
# WETH9's ether backs its tokens after any transaction, with hash hypotheses on finitely many rows

`weth9_solvent_7702`, `weth9_backed_7702` (`Verified.WETH9.Backed7702`) and their transaction
versions (`Verified.WETH9.Tx7702`) carry the global hash hypotheses of `weth9_backed`, almost
surely false for Keccak (`Verified.WETH9.Rows`). Here they are replaced by hypotheses about the
rows the execution uses:

* **`FramesOk_rows`** (a message call), **`TxFramesOk_rows`** (a transaction): every non-static
  WETH9 frame the top-level message call reaches (`Reaches`; `TxReaches`: the machines `process`
  runs) has the two allowance rows its message may write outside the `balanceOf` rows
  (`AllowOk_rows`);
* for the sum over holders, distinct `balanceOf` rows on the finite set of holders summed over.

The message-level theorems, **`weth9_solvent_rows`** and **`weth9_backed_rows`**, use the
ether-aware havoc theorem restricted to reached frames
(`QEDefi.ERC20.Spec.Invariant.processMessageCall_good_reach`): the frame summary
(`weth_halts_rows`) is only needed for the WETH9 frames the call reaches, where the hypothesis
gives `AllowOk_rows`.

`process_keeps_ether_rows` is `QEDefi.Solvency.process_keeps_ether_of` whose message-level
premise also receives that the message call's machines are the transaction's, so that a
hypothesis about the transaction's frames reaches the message-level theorem
(`weth9_solvent_rows`).

**`weth9_solvent_tx_rows`**, **`weth9_backed_tx_rows`**: from a world in which WETH9 is solvent,
every successful transaction (any type, sender, recipient, value, calldata, gas limit, fees and
EIP-7702 authorizations; any fork, block and coinbase) whose WETH9 frames write no allowance row
that is a `balanceOf` row leaves `Σ_{a ∈ A} balanceOf[a]` at most WETH9's ether and below
`2²⁵⁶`, for every finite set `A` of holders with distinct `balanceOf` rows.
-/

namespace Verified.WETH9
open EvmLean EvmLean.Interpreter EvmLean.Tx EvmLogic EvmLogic.Program EvmLogic.Program.Nested
  EvmLogic.Program.Reentrancy EvmLogic.Tx QEDefi.Solvency Verified.WETH9.Contracts

/-! ## Any frame, any message call -/

/-- **A dangerous WETH9 frame** (`DStartV`) whose message satisfies `AllowOk_rows` ends in a
world in which WETH9 is solvent. `weth_covers` for one frame, with `AllowOk_rows` of its message
for `hK`. -/
theorem weth_halts_rows {crypto : Crypto} {weth : Address} {G : Nat} {m : Machine}
    (hd : DStartV (· = weth) (Good crypto weth) (Ctx crypto) G m)
    (hA : AllowOk_rows crypto m.frame.msg) :
    Halts m (fun mf o => Good crypto weth (frameResult mf o).2.1) := by
  obtain ⟨⟨⟨⟨ko, ks, hfr⟩, ⟨hP, hst⟩, hsnap, hkeep, hcode, -, -, hcaller, -, -, hpre⟩,
    hweq, haff⟩, hstv, hctx⟩ := hd
  obtain ⟨ctx, pre, world, tr, ow, created, ⟨msg, code, jd, pc, stack, mem, gas, rd, sub, snap,
    kind⟩, parents⟩ := m
  dsimp only at hfr hP hst hsnap hkeep hcode hcaller hpre hweq haff hstv hctx hA ⊢
  simp only [Frame.init, Frame.mk.injEq] at hfr
  obtain ⟨-, rfl, -, rfl, rfl, rfl, rfl, rfl, -, -, rfl⟩ := hfr
  have hc : msg.code = WETH9.runtimeCode := by
    rw [hcode, hP, (hkeep weth rfl).code]; exact hsnap.code
  rw [hc]
  subst hweq hpre hP
  apply WP.halts_of_false
  exact weth_frame_rows ctx tr ow created msg jd sub snap ko ks parents msg.gas hA hsnap hst
    hcaller hstv (haff hstv) hctx

/-- **Every WETH9 frame a message call reaches writes no `balanceOf` row as an allowance**: each
non-static frame at `weth` that the top-level message call reaches (`Reaches`) satisfies
`AllowOk_rows`. A hypothesis about the finitely many frames of one execution; see
`AllowOk_rows` for why each holds for Keccak. -/
def FramesOk_rows (crypto : Crypto) (weth : Address) (ctx : Context) (w : World)
    (tr : TransientStorage) (msg : Message) : Prop :=
  ∀ m, Reaches ctx w tr msg m → m.frame.msg.currentTarget = weth →
    m.frame.msg.isStatic = false → AllowOk_rows crypto m.frame.msg

/-- **WETH9 stays solvent after any message call whose WETH9 frames write no `balanceOf` row
as an allowance**: from a world in which it is solvent, any top-level message call (any fork,
any EIP-7702 authorizations; any target, code, value, calldata; an unprotected sender; any
callees, including ones that call WETH9 at any depth) that moves its value, hashing with
`crypto`, ends in a world in which it is solvent — provided every WETH9 frame it reaches has the
two allowance rows its message may write outside the `balanceOf` rows (`FramesOk_rows`).
`weth9_solvent_7702` with a hypothesis about this execution's rows for its global `hK`. -/
theorem weth9_solvent_rows {crypto : Crypto} {weth : Address} {fuel : Nat}
    {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message} {r : MessageResult}
    (hw : Good crypto weth w) (hctx : ctx.crypto = crypto)
    (hmsg : TopOk (· = weth) w msg) (hv : msg.shouldTransferValue = true)
    (hrows : FramesOk_rows crypto weth ctx w tr msg)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) : Good crypto weth r.world :=
  QEDefi.ERC20.Spec.Invariant.processMessageCall_good_reach (C := Ctx crypto)
    (goodOps_solvent size_code deleg_code) hw hmsg hv hctx
    (fun _ hm hd => weth_halts_rows hd (hrows _ hm hd.danger.1 hd.danger.2)) hr

/-- **What a finite set of holders is owed is at most what WETH9 owes**, when their `balanceOf`
rows are distinct. -/
theorem sum_le_owed_rows {crypto : Crypto} {weth : Address} (w : World) {A : Finset Address}
    (hA : Set.InjOn (balSlot crypto) A) :
    ∑ a ∈ A, (w.sload weth (balSlot crypto a)).toNat ≤ owed crypto 3#256 weth w := by
  unfold owed
  rw [← Finset.sum_image (f := fun s => (w.sload weth s).toNat) hA]
  refine Finset.sum_le_sum_of_subset fun s hs => ?_
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hs
  exact mem_balanceSlots crypto 3#256 a

/-- **WETH9's ether backs its tokens after any message call whose WETH9 frames write no
`balanceOf` row as an allowance**: under the hypotheses of `weth9_solvent_rows`, for every finite
set `A` of holders whose `balanceOf` rows are distinct, `Σ_{a ∈ A} balanceOf[a] ≤
address(weth).balance` and the sum is below `2²⁵⁶`. `A` may be every account holding WETH (the
nonzero rows are finitely many); `n` holders have colliding rows with probability at most
`n²/2²⁵⁷` for a random 256-bit function, so distinct rows on `A` is plausible for Keccak where
injectivity on all `2¹⁶⁰` addresses (`weth9_backed`'s `hinj`) is not. -/
theorem weth9_backed_rows {crypto : Crypto} {weth : Address} {fuel : Nat}
    {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message} {r : MessageResult}
    (hw : Good crypto weth w) (hctx : ctx.crypto = crypto)
    (hmsg : TopOk (· = weth) w msg) (hv : msg.shouldTransferValue = true)
    (hrows : FramesOk_rows crypto weth ctx w tr msg)
    (hr : processMessageCall fuel ctx w tr msg = .ok r)
    {A : Finset Address} (hA : Set.InjOn (balSlot crypto) A) :
    ∑ a ∈ A, (r.world.sload weth (balSlot crypto a)).toNat ≤ (r.world.balance weth).toNat ∧
      ∑ a ∈ A, (r.world.sload weth (balSlot crypto a)).toNat < 2 ^ 256 := by
  have h := weth9_solvent_rows hw hctx hmsg hv hrows hr
  have hs := sum_le_owed_rows (weth := weth) r.world hA
  exact ⟨Nat.le_trans hs h.backed, Nat.lt_of_le_of_lt hs h.bounded⟩

/-! ## Transactions -/

/-- **The decomposition of a transaction**, as `process_split`, with in addition that the
machines of its top-level message call are the transaction's (`TxReaches`). -/
theorem process_split_rows {P : Address → Prop} {fuel : Nat} {crypto : Crypto} {fork : Fork}
    {env : BlockEnv} {gasAvail blobAvail : Nat} {w : World} {tx : Transaction}
    {hint : Option Address} {out : TxOutput} (hP : ∀ p, P p → RealCode (w.code p))
    (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    ∃ (c : Checked) (ctx : Context) (msg : Message) (r : MessageResult) (gasUsed : Nat),
      check crypto fork env gasAvail blobAvail w tx hint = .ok c ∧
      TopMsg P crypto fork env tx (msgWorld fork env w tx c) ctx msg ∧
      (∀ m, Reaches ctx (msgWorld fork env w tx c) ∅ msg m →
        TxReaches crypto fork env gasAvail blobAvail w tx hint m) ∧
      processMessageCall fuel ctx (msgWorld fork env w tx c) ∅ msg = .ok r ∧
      gasUsed ≤ tx.gas ∧
      out.world = suffixWorld r c.sender env.coinbase ((tx.gas - gasUsed) * c.effectiveGasPrice)
        (gasUsed * (c.effectiveGasPrice - env.baseFee)) := by
  obtain ⟨i, c, r, gu, hv, hc, hr, hgu, hout, -, -⟩ := process_ok h
  have hval := validate_ok hv
  refine ⟨c, _, _, r, gu, hc, ⟨topOk_prepareMessage hP hc _ _ _,
    prepareMessage_shouldTransferValue .., prepareMessage_isStatic .., by simp, rfl, rfl, rfl, rfl,
    ?_, fun ho => ?_, fun p hp => ?_⟩, fun m hm => ⟨c, hc, ?_⟩, hr, hgu, hout⟩
  · simp only [prepareMessage_gas]; omega
  · simp only [prepareMessage_gas]; have := hval.2.2.2 ho; omega
  · unfold msgWorld; rw [code_prefixWorld]; exact hP p hp
  · rw [← hval.1]; exact hm

/-- **An ether invariant of top-level message calls is an invariant of transactions**:
`QEDefi.Solvency.process_keeps_ether_of`, whose message-level premise (`hmsg`) also receives
that the message call's machines are the transaction's (`TxReaches`), so that it may use a
hypothesis about the transaction's execution. -/
theorem process_keeps_ether_rows {P : Address → Prop} {Inv : World → Prop} {fuel : Nat}
    {crypto : Crypto} {fork : Fork} {env : BlockEnv} {gasAvail blobAvail : Nat} {w : World}
    {tx : Transaction} {hint : Option Address} {out : TxOutput}
    (hP : ∀ w, Inv w → ∀ p, P p → RealCode (w.code p))
    (hcap : ∀ w, Inv w → supply w < 2 ^ 256)
    (hmsg : ∀ (ctx : Context) (w₁ : World) (msg : Message) (r : MessageResult), Inv w₁ →
      TopMsg P crypto fork env tx w₁ ctx msg →
      (∀ m, Reaches ctx w₁ ∅ msg m → TxReaches crypto fork env gasAvail blobAvail w tx hint m) →
      processMessageCall fuel ctx w₁ ∅ msg = .ok r → Inv r.world)
    (hframe : ∀ w w', Inv w →
      (∀ p, P p → Keep p w w' ∧ (w.balance p).toNat ≤ (w'.balance p).toNat) →
      supply w' < 2 ^ 256 → Inv w')
    (hsup : ∀ (ctx : Context) (w₁ : World) (msg : Message) (r : MessageResult),
      supply w₁ < 2 ^ 256 → TopMsg P crypto fork env tx w₁ ctx msg →
      processMessageCall fuel ctx w₁ ∅ msg = .ok r → supply r.world ≤ supply w₁)
    (hw : Inv w) (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    Inv out.world ∧ supply out.world ≤ supply w := by
  obtain ⟨c, ctx, msg, r, gu, hc, hm, hreach, hr, hgu, hout⟩ := process_split_rows (hP w hw) h
  unfold msgWorld at hm hreach hr
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
  have h2 := hmsg ctx _ msg r h1 hm hreach hr
  have hs2 := hsup ctx _ msg r (by omega) hm hr
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

/-- **Every WETH9 frame a transaction reaches writes no `balanceOf` row as an allowance**: each
non-static frame at `weth` among the machines of the transaction's top-level message call
(`TxReaches`) satisfies `AllowOk_rows`. `FramesOk_rows` for the message call `process` runs; a
hypothesis about the finitely many frames of this transaction, see `AllowOk_rows` for why each
holds for Keccak. -/
def TxFramesOk_rows (crypto : Crypto) (weth : Address) (fork : Fork) (env : BlockEnv)
    (gasAvail blobAvail : Nat) (w : World) (tx : Transaction) (hint : Option Address) : Prop :=
  ∀ m, TxReaches crypto fork env gasAvail blobAvail w tx hint m →
    m.frame.msg.currentTarget = weth → m.frame.msg.isStatic = false →
    AllowOk_rows crypto m.frame.msg

/-- **WETH9 stays solvent after any transaction whose WETH9 frames write no `balanceOf` row as
an allowance**: from a world in which it is solvent, every successful transaction (any type,
sender, recipient, value, calldata, gas limit, fees and EIP-7702 authorizations; any fork, block
and coinbase; hashing with `crypto`) ends in a world in which it is solvent, provided every
WETH9 frame it runs has the two allowance rows its message may write outside the `balanceOf` rows
(`TxFramesOk_rows`). `weth9_solvent_tx_7702` with a hypothesis about this transaction's rows for
its global `hK`. -/
theorem weth9_solvent_tx_rows {crypto : Crypto} {weth : Address} {fuel : Nat} {fork : Fork}
    {env : BlockEnv} {gasAvail blobAvail : Nat} {w : World} {tx : Transaction}
    {hint : Option Address} {out : TxOutput} (hw : Good crypto weth w)
    (hrows : TxFramesOk_rows crypto weth fork env gasAvail blobAvail w tx hint)
    (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    Good crypto weth out.world :=
  (process_keeps_ether_rows (P := (· = weth)) (Inv := Good crypto weth)
    (fun _ hw _ hp => hp ▸ realCode_good hw) (fun _ hw => hw.capped)
    (fun _ _ _ _ h1 hm hreach hr => weth9_solvent_rows h1 hm.ctxCrypto hm.top hm.transfers
      (fun m hm' ht hs => hrows m (hreach m hm') ht hs) hr)
    (fun _ _ hw hk hs => good_of_frame hw (hk weth rfl).1 (hk weth rfl).2 hs)
    (fun _ _ _ _ hs hm hr => processMessageCall_supply_le_7702 hs hm.top.depth hm.top.target
      hm.transfers hr) hw h).1

/-- **WETH9's ether backs its tokens, after any transaction whose WETH9 frames write no
`balanceOf` row as an allowance**: under the hypotheses of `weth9_solvent_tx_rows`, for every
finite set `A` of holders whose `balanceOf` rows are distinct (see `weth9_backed_rows`),
`Σ_{a ∈ A} balanceOf[a] ≤ address(weth).balance` and the sum is below `2²⁵⁶`.
`weth9_backed_tx_7702` with hypotheses about finitely many rows for its global `hK` and
`hinj`. -/
theorem weth9_backed_tx_rows {crypto : Crypto} {weth : Address} {fuel : Nat} {fork : Fork}
    {env : BlockEnv} {gasAvail blobAvail : Nat} {w : World} {tx : Transaction}
    {hint : Option Address} {out : TxOutput} (hw : Good crypto weth w)
    (hrows : TxFramesOk_rows crypto weth fork env gasAvail blobAvail w tx hint)
    (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out)
    {A : Finset Address} (hA : Set.InjOn (balSlot crypto) A) :
    ∑ a ∈ A, (out.world.sload weth (balSlot crypto a)).toNat ≤
        (out.world.balance weth).toNat ∧
      ∑ a ∈ A, (out.world.sload weth (balSlot crypto a)).toNat < 2 ^ 256 := by
  have hg := weth9_solvent_tx_rows hw hrows h
  have hs := sum_le_owed_rows (weth := weth) out.world hA
  exact ⟨Nat.le_trans hs hg.backed, Nat.lt_of_le_of_lt hs hg.bounded⟩

end Verified.WETH9
