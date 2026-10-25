import QEDefi.Solvency.Bank
import Examples.Reentrancy.Contracts.GuardedBank
import EvmLogic.Tactic.PrefixStep
import EvmLogic.Program.Reentrancy.PrefixCall

/-!
# `GuardedBank` is solvent after any transaction

`GuardedBank` (`contracts/src/reentrancy/Banks.sol`) sends **before** it debits, like the
vulnerable bank, but both state-changing functions hold OpenZeppelin's `ReentrancyGuard` lock: a
status word at the ERC-7201 slot `statusSlot` is set to `2` on entry (a function entered while it
is `2` reverts) and reset to `1` on exit. Proved on the compiled bytecode, for any gas:

* `locked_covers`: while the lock is held, every frame of the bank reverts or (the view
  `balances(a)`) returns without writing: the bank's storage and code stay frozen, and its ether
  can only grow (`Locked`, a `GoodOps` invariant). No induction: callbacks never reach a call.
* `guarded_frame`: every frame of the bank keeps it solvent. `withdraw()` takes the lock, reaches
  its `CALL` with the debt still recorded; `pwp_call_v` with the call-site invariant `Locked`
  (the callee and its callbacks cannot touch the bank's storage nor take its ether) resumes in a
  world holding at least the ether minus the amount sent; the tail then zeroes the entry and
  releases the lock (`solvent_unlock`), run by `apwp_steps` from the resumed machine.
* **`guarded_solvent`**: any top-level message call from a solvent world leaves the bank solvent,
  provided the status slot is none of the balance entries' slots (a Keccak hypothesis about one
  target, `statusSlot ∉ balanceSlots crypto 0`).
-/

namespace Examples.Reentrancy.Solvency.Guarded
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
open QEDefi.Solvency
  EvmLogic.Program.Reentrancy EvmLogic.Solidity Examples.Reentrancy.Contracts

/-- The bank is solvent (`balances` at slot `0`, the code `GuardedBank.runtimeCode`). -/
abbrev Good (crypto : Crypto) (bank : Address) : World → Prop :=
  Solvent crypto 0 GuardedBank.runtimeCode bank

/-- The transaction hashes with `crypto`. -/
abbrev Ctx (crypto : Crypto) : Context → Prop := fun c => c.crypto = crypto

/-- OpenZeppelin's `ReentrancyGuard` status slot (ERC-7201 namespace
`openzeppelin.storage.ReentrancyGuard`), loaded by `CODECOPY` from the code. -/
abbrev statusSlot : Word :=
  0x9b779b17422d0df92223018b32b4d1fa46e071723d6817e2486d003becc55f00#256

theorem size_code : GuardedBank.runtimeCode.size ≠ 0 := by
  rw [GuardedBank.size_runtimeCode]; decide

theorem deleg_code : delegatedAddress? GuardedBank.runtimeCode = none := by decide +kernel

variable {crypto : Crypto} {bank : Address}

/-! ## While the lock is held -/

set_option maxHeartbeats 1000000 in
/-- **A frame of the bank while the lock is held** keeps `Locked`: the guarded functions revert,
the view returns without writing. -/
theorem locked_frame {w₀ : World} {L : Nat} (hcode0 : w₀.code bank = GuardedBank.runtimeCode)
    (hst0 : w₀.sload bank statusSlot = 2#256)
    (ctx : Context) (tr : TransientStorage) (ow : World) (created : AddressSet) (msg : Message)
    (jd : Array Bool) (sub : Substate) (snap : World × TransientStorage) (ko ks : Nat)
    (parents : List Frame) (g0 : Nat)
    (hsnap : Locked bank w₀ L snap.1)
    (htgt : msg.currentTarget = bank) (hcaller : msg.caller ≠ bank)
    (haff : msg.value ≠ 0 → msg.value.toNat ≤ (snap.1.balance msg.caller).toNat) :
    WP (Machine.mk ctx (PrecompileImpl.standard ctx) (transferValue snap.1 msg) tr ow created
      (Frame.mk msg GuardedBank.runtimeCode jd 0 [] {} g0 .empty sub snap (.call ko ks)) parents)
      (fun _ => False) (FailOk (Locked bank w₀ L)) := by
  have S := goodOps_locked (bank := bank) (w₀ := w₀) (L := L)
    (by rw [hcode0]; exact size_code) (by rw [hcode0]; exact deleg_code)
  have hT : Locked bank w₀ L (transferValue snap.1 msg) :=
    S.transfer hsnap fun _ h2 => ⟨haff h2, .inl hcaller⟩
  have hK : (transferValue snap.1 msg).sload msg.currentTarget
      70319816728846589445362000750570655803700195216363692647688146666176345628416#256 =
      2#256 := by
    rw [htgt, hT.keep.sload]; exact hst0
  apwp_steps [hK]
  -- `balances(a)`: `RETURN` without writing
  exact pwp_return ‹_› (by code_fact) rfl rfl hT

/-- **The summaries while the lock is held**, for every gas. -/
theorem locked_covers {w₀ : World} {L : Nat} (hcode0 : w₀.code bank = GuardedBank.runtimeCode)
    (hst0 : w₀.sload bank statusSlot = 2#256) (C : Context → Prop) (G : Nat) :
    CoversV (· = bank) (Locked bank w₀ L) C G := by
  intro m hd
  obtain ⟨⟨⟨⟨ko, ks, hfr⟩, ⟨hP, -⟩, hsnap, hkeep, hcode, -, -, hcaller, -, -, hpre⟩,
    hweq, haff⟩, hstv, -⟩ := hd
  obtain ⟨ctx, pre, world, tr, ow, created, ⟨msg, code, jd, pc, stack, mem, gas, rd, sub, snap,
    kind⟩, parents⟩ := m
  dsimp only at hfr hP hsnap hkeep hcode hcaller hpre hweq haff hstv ⊢
  simp only [Frame.init, Frame.mk.injEq] at hfr
  obtain ⟨-, rfl, -, rfl, rfl, rfl, rfl, rfl, -, -, rfl⟩ := hfr
  have hc : msg.code = GuardedBank.runtimeCode := by
    rw [hcode, hP, (hkeep bank rfl).code, hsnap.keep.code]; exact hcode0
  rw [hc]
  subst hweq hpre
  apply WP.halts_of_false
  exact locked_frame hcode0 hst0 ctx tr ow created msg jd sub snap ko ks parents msg.gas hsnap
    hP hcaller (haff hstv)

/-! ## One frame of the bank -/

set_option maxHeartbeats 4000000 in
/-- **Every frame of the bank keeps it solvent**, for any gas. -/
theorem guarded_frame (hK : statusSlot ∉ balanceSlots crypto 0)
    (ctx : Context) (tr : TransientStorage) (ow : World) (created : AddressSet) (msg : Message)
    (jd : Array Bool) (sub : Substate) (snap : World × TransientStorage) (ko ks : Nat)
    (parents : List Frame) (g0 : Nat)
    (hsnap : Good crypto bank snap.1) (hst : msg.isStatic = false)
    (htgt : msg.currentTarget = bank) (hcaller : msg.caller ≠ bank)
    (hstv : msg.shouldTransferValue = true)
    (haff : msg.value ≠ 0 → msg.value.toNat ≤ (snap.1.balance msg.caller).toNat)
    (hctx : ctx.crypto = crypto) :
    WP (Machine.mk ctx (PrecompileImpl.standard ctx) (transferValue snap.1 msg) tr ow created
      (Frame.mk msg GuardedBank.runtimeCode jd 0 [] {} g0 .empty sub snap (.call ko ks)) parents)
      (fun _ => False) (FailOk (Good crypto bank)) := by
  have S := goodOps_solvent (crypto := crypto) (base := 0) (bank := bank) size_code deleg_code
  have hT : Good crypto bank (transferValue snap.1 msg) :=
    S.transfer hsnap fun _ h2 => ⟨haff h2, .inl hcaller⟩
  have hB := backed_transferValue (base := 0) size_code hsnap htgt hcaller hstv haff
  subst hctx htgt
  apwp_steps
  -- `deposit()`: `STOP` after taking the lock, crediting `msg.value`, releasing the lock
  · have hno : _ := ‹Word.iszero (Word.gt _ _) ≠ 0›
    refine pwp_stop (by code_fact) rfl ((solvent_credit ?_ ?_ ?_ hno).sstore_other hK _)
    · rw [World.code_sstore]; exact hT.code
    · rw [supply_sstore]; exact hT.capped
    · rw [owed_sstore_other _ (show statusSlot ∉ balanceSlots ctx.crypto 0#256 from hK),
        World.balance_sstore]; exact hB
  -- `withdraw()`: the `CALL` under the lock, with the debt still recorded
  · have hval : _ := ‹Word.iszero msg.value ≠ 0›
    have hK' : statusSlot ∉ balanceSlots ctx.crypto 0#256 := hK
    have hcodec : ((transferValue snap.1 msg).sstore msg.currentTarget statusSlot 2#256).code
        msg.currentTarget = GuardedBank.runtimeCode := by rw [World.code_sstore]; exact hT.code
    have hstc : ((transferValue snap.1 msg).sstore msg.currentTarget statusSlot 2#256).sload
        msg.currentTarget statusSlot = 2#256 := World.sload_sstore_self _ _ _ _
    have h0 : owed ctx.crypto 0#256 msg.currentTarget ((transferValue snap.1 msg).sstore
        msg.currentTarget statusSlot 2#256) ≤ (((transferValue snap.1 msg).sstore
          msg.currentTarget statusSlot 2#256).balance msg.currentTarget).toNat := by
      rw [owed_sstore_other _ hK', World.balance_sstore]; exact hT.backed
    have SL := goodOps_locked (bank := msg.currentTarget)
      (w₀ := (transferValue snap.1 msg).sstore msg.currentTarget statusSlot 2#256)
      (L := (((transferValue snap.1 msg).sstore msg.currentTarget statusSlot 2#256).balance
          msg.currentTarget).toNat - (((transferValue snap.1 msg).sstore msg.currentTarget
            statusSlot 2#256).sload msg.currentTarget
              (mappingSlot ctx.crypto (Word.ofAddress msg.caller) 0#256)).toNat)
      (by rw [hcodec]; exact size_code) (by rw [hcodec]; exact deleg_code)
    refine pwp_call_v SL (C := Ctx ctx.crypto) rfl
      (fun g _ => locked_covers hcodec hstc _ g) ‹_› (by code_fact) rfl rfl
      (by simpa using hcaller) ⟨keep_refl _ _, Nat.sub_le _ _, by rw [supply_sstore]; exact hT.capped⟩
      (fun _ hb => ?_) ?_
    · dsimp only at hb
      rw [Word.toAddress_ofAddress]
      refine ⟨keep_moveEther (by rw [hcodec]; exact size_code), ?_,
        by rw [supply_moveEther hb (by rw [supply_sstore]; exact hT.capped), supply_sstore];
           exact hT.capped⟩
      rw [balance_moveEther _ _ (Ne.symm hcaller)]
      simp only [ite_true]
      rw [toNat_sub_of_le hb]
      rfl
    · intro m'' hsf hpc ⟨x, hx⟩ hgood
      obtain ⟨c'', p'', w'', t'', o'', cr'', ⟨msg'', code'', jd'', pc'', st'', mem'', g'', rd'',
        sub'', snap'', kind''⟩, par''⟩ := m''
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hsf
      dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 hpc hx hgood
      subst h1 h2 h3 h4 h5 h6 h7 h8 h9 hpc hx
      apwp_steps
      all_goals refine pwp_stop ?_ rfl ?_
      all_goals try code_fact
      all_goals
        dsimp only
        exact (solvent_unlock hcodec h0 hgood).sstore_other hK' _
  -- `balances(a)`: `RETURN` without writing
  · exact pwp_return ‹_› (by code_fact) rfl rfl hT

/-! ## Any frame, any transaction -/

/-- **The bank's summaries**, for every gas (no induction: callbacks under the lock never reach
a call). -/
theorem guarded_covers (hK : statusSlot ∉ balanceSlots crypto 0) (G : Nat) :
    CoversV (· = bank) (Good crypto bank) (Ctx crypto) G := by
  intro m hd
  obtain ⟨⟨⟨⟨ko, ks, hfr⟩, ⟨hP, hst⟩, hsnap, hkeep, hcode, -, -, hcaller, -, -, hpre⟩,
    hweq, haff⟩, hstv, hctx⟩ := hd
  obtain ⟨ctx, pre, world, tr, ow, created, ⟨msg, code, jd, pc, stack, mem, gas, rd, sub, snap,
    kind⟩, parents⟩ := m
  dsimp only at hfr hP hst hsnap hkeep hcode hcaller hpre hweq haff hstv hctx ⊢
  simp only [Frame.init, Frame.mk.injEq] at hfr
  obtain ⟨-, rfl, -, rfl, rfl, rfl, rfl, rfl, -, -, rfl⟩ := hfr
  have hc : msg.code = GuardedBank.runtimeCode := by
    rw [hcode, hP, (hkeep bank rfl).code]; exact hsnap.code
  rw [hc]
  subst hweq hpre
  apply WP.halts_of_false
  exact guarded_frame hK ctx tr ow created msg jd sub snap ko ks parents msg.gas hsnap hst hP
    hcaller hstv (haff hstv) hctx

/-- **`GuardedBank` stays solvent after any transaction**: from a world in which it is solvent,
any top-level message call (any target, code, value, calldata; an unprotected sender; callees
that call back into the bank at any depth) that moves its value, hashing with the world's
`crypto`, before Prague or without EIP-7702 authorizations, ends in a world in which it is
solvent — provided the guard's status slot is none of the balance entries' slots. -/
theorem guarded_solvent (hK : statusSlot ∉ balanceSlots crypto 0) {fuel : Nat} {ctx : Context}
    {w : World} {tr : TransientStorage} {msg : Message} {r : MessageResult}
    (hw : Good crypto bank w) (hctx : ctx.crypto = crypto)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : TopOk (· = bank) w msg) (hv : msg.shouldTransferValue = true)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) : Good crypto bank r.world :=
  processMessageCall_good_v (goodOps_solvent size_code deleg_code) hw hdeleg hmsg hv hctx
    (guarded_covers hK _) hr

/-- **Solvency over addresses**: when the slots of `balances[a]` do not collide, after any
transaction `Σ_a balances[a] ≤ address(bank).balance`. -/
theorem guarded_backed (hK : statusSlot ∉ balanceSlots crypto 0) {fuel : Nat} {ctx : Context}
    {w : World} {tr : TransientStorage} {msg : Message} {r : MessageResult}
    (hw : Good crypto bank w) (hctx : ctx.crypto = crypto)
    (hinj : Function.Injective fun a : Address => mappingSlot crypto (Word.ofAddress a) 0)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : TopOk (· = bank) w msg) (hv : msg.shouldTransferValue = true)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    ∑ a : Address, (r.world.sload bank (mappingSlot crypto (Word.ofAddress a) 0)).toNat ≤
      (r.world.balance bank).toNat := by
  rw [← owed_eq_sum_addresses _ hinj]
  exact (guarded_solvent hK hw hctx hdeleg hmsg hv hr).backed

end Examples.Reentrancy.Solvency.Guarded
