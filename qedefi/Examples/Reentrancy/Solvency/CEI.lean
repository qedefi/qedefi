import Examples.Reentrancy.Solvency.Model
import Examples.Reentrancy.Contracts.CEIBank
import EvmLogic.Tactic.PrefixStep
import EvmLogic.Program.Reentrancy.PrefixCall
import EvmLogic.Program.Reentrancy.Tail

/-!
# `CEIBank` is solvent after any transaction

`CEIBank` (`contracts/src/reentrancy/Banks.sol`) debits before it sends: `withdraw()` zeroes
`balances[msg.sender]`, then sends the old balance with a plain `call` that forwards all gas, so
the recipient may call back into the bank at any depth. Proved on the compiled bytecode:

* `cei_frame`: every frame of the bank, started by a value-moving message from an unprotected
  caller in a solvent world, ends in a solvent world, for **any gas**. The dispatcher and each
  function body run under symbolic gas with the prefix calculus (`apwp_steps`): `deposit()` stops
  after crediting `msg.value` (`solvent_deposit`), `balances(a)` returns without writing,
  `withdraw()` reaches its `CALL` with the entry zeroed; there `pwp_call_v` (the untrusted call
  with any outcome) needs solvency before and after the transfer (`solvent_withdraw`) and the
  bank's summaries for less gas; after the call, the tail is certified world-safe from its pc
  (`tail_check`, `noWrite_halts_tail`), so whatever the callee did, the frame ends solvent.
* `cei_covers`: the summaries, by induction on gas (`coversV_of_lt`): a callback has less gas.
* **`cei_solvent`**: any top-level message call (any code, value, calldata, callee behaviour,
  reentrancy at any depth) from a solvent world leaves the bank solvent.
* `cei_backed`: the same as `Σ_a balances[a] ≤ address(bank).balance` over all addresses, when
  the entries' slots do not collide.
-/

namespace Examples.Reentrancy.Solvency.CEI
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
  EvmLogic.Program.Reentrancy EvmLogic.Solidity EvmLogic.AbsInt Examples.Reentrancy.Contracts

/-- The bank is solvent (`balances` at slot `0`, the bank's code `CEIBank.runtimeCode`). -/
abbrev Good (crypto : Crypto) (bank : Address) : World → Prop :=
  Solvent crypto 0 CEIBank.runtimeCode bank

/-- The transaction hashes with `crypto`. -/
abbrev Ctx (crypto : Crypto) : Context → Prop := fun c => c.crypto = crypto

theorem size_code : CEIBank.runtimeCode.size ≠ 0 := by rw [CEIBank.size_runtimeCode]; decide

theorem deleg_code : delegatedAddress? CEIBank.runtimeCode = none := by decide +kernel

/-! ## The tail after the call -/

/-- The abstract stack after `withdraw()`'s `CALL` (the success flag, the call's leftovers, the
return address `0x88` of the body, the selector). -/
def tailInit : AStack := [.top, .top, .top, .top, .top, .top, .const 0x88, .top]

/-- **The tail after `withdraw()`'s call is world-safe** (kernel evaluation of the abstract
interpreter from pc `0xb7`). -/
theorem tail_check :
    tailCheck (fun _ => false) CEIBank.runtimeCode [] 0xb7 tailInit 10000 = true := by
  decide +kernel

/-! ## One frame of the bank -/

variable {crypto : Crypto} {bank : Address}

set_option maxHeartbeats 1000000 in
/-- **Every frame of the bank keeps it solvent**, for any gas, given the summaries of frames
with less gas (`hcov`). -/
theorem cei_frame {G : Nat} (hcov : ∀ g < G, CoversV (· = bank) (Good crypto bank) (Ctx crypto) g)
    (ctx : Context) (tr : TransientStorage) (ow : World) (created : AddressSet) (msg : Message)
    (jd : Array Bool) (sub : Substate) (snap : World × TransientStorage) (ko ks : Nat)
    (parents : List Frame) (g0 : Nat) (hg0 : g0 ≤ G)
    (hsnap : Good crypto bank snap.1) (hst : msg.isStatic = false)
    (htgt : msg.currentTarget = bank) (hcaller : msg.caller ≠ bank)
    (hstv : msg.shouldTransferValue = true)
    (haff : msg.value ≠ 0 → msg.value.toNat ≤ (snap.1.balance msg.caller).toNat)
    (hctx : ctx.crypto = crypto) :
    WP (Machine.mk ctx (PrecompileImpl.standard ctx) (transferValue snap.1 msg) tr ow created
      (Frame.mk msg CEIBank.runtimeCode jd 0 [] {} g0 .empty sub snap (.call ko ks)) parents)
      (fun _ => False) (FailOk (Good crypto bank)) := by
  have S := goodOps_solvent (crypto := crypto) (base := 0) (bank := bank) size_code deleg_code
  have hT : Good crypto bank (transferValue snap.1 msg) :=
    S.transfer hsnap fun _ h2 => ⟨haff h2, .inl hcaller⟩
  obtain ⟨t, hcert, hsafe⟩ := tailCheck_sound (ρ := fun _ => 0) tail_check
    (fun _ _ h => by cases h)
  subst hctx htgt
  apwp_steps
  -- `deposit()`: `STOP` after crediting `msg.value`
  · rename_i hno _ _ _
    exact pwp_stop (by code_fact) rfl
      (solvent_deposit size_code hsnap rfl hcaller hstv haff hno)
  -- `withdraw()`: the `CALL` with the caller's entry zeroed
  · rename_i hval _ _ hgas
    have hv0 := iszero_ne_zero hval
    have hW := solvent_withdraw (base := 0) size_code hT hcaller
    refine pwp_call_v S (C := Ctx ctx.crypto) rfl (fun g hg => hcov g (Nat.lt_of_lt_of_le hg hgas)) hsnap
      (by code_fact) rfl rfl (by simpa using hcaller) hW.1 (fun _ hb => ?_) ?_
    · rw [Word.toAddress_ofAddress]; exact hW.2 hb
    · intro m'' hsf hpc ⟨x, hx⟩ hgood
      refine WP.halts (Halts.failOk (ko := ko) (ks := ks) hsf.kind (by rw [hsf.snapshot]; exact hsnap)
        hgood (noWrite_halts_tail hcert hsafe (hsf.code) (inCert_of_entry hcert hpc ?_)))
      rw [hx]
      simp only [tailInit, StackOk, AVal.Holds, true_and, and_true]
      rfl
  -- `balances(a)`: `RETURN` without writing
  · exact pwp_return ‹_› (by code_fact) rfl rfl hT

/-! ## Any frame, any transaction -/

/-- **The bank's summaries**, for every gas (by induction on gas: a callback has less gas than
the frame that made the call). -/
theorem cei_covers (G : Nat) : CoversV (· = bank) (Good crypto bank) (Ctx crypto) G := by
  refine coversV_of_lt (fun G ih => ?_) G
  intro m hd
  obtain ⟨⟨⟨⟨ko, ks, hfr⟩, ⟨hP, hst⟩, hsnap, hkeep, hcode, -, -, hcaller, hgas, -, hpre⟩,
    hweq, haff⟩, hstv, hctx⟩ := hd
  obtain ⟨ctx, pre, world, tr, ow, created, ⟨msg, code, jd, pc, stack, mem, gas, rd, sub, snap,
    kind⟩, parents⟩ := m
  dsimp only at hfr hP hst hsnap hkeep hcode hcaller hgas hpre hweq haff hstv hctx ⊢
  simp only [Frame.init, Frame.mk.injEq] at hfr
  obtain ⟨-, rfl, -, rfl, rfl, rfl, rfl, rfl, -, -, rfl⟩ := hfr
  have hc : msg.code = CEIBank.runtimeCode := by
    rw [hcode, hP, (hkeep bank rfl).code]; exact hsnap.code
  rw [hc]
  subst hweq hpre
  apply WP.halts_of_false
  exact cei_frame ih ctx tr ow created msg jd sub snap ko ks parents msg.gas hgas hsnap hst hP
    hcaller hstv (haff hstv) hctx

/-- **`CEIBank` stays solvent after any transaction**: from a world in which it is solvent, any
top-level message call (any target, code, value, calldata; an unprotected sender; callees that
call back into the bank at any depth) that moves its value, hashing with the world's `crypto`,
before Prague or without EIP-7702 authorizations, ends in a world in which it is solvent. -/
theorem cei_solvent {fuel : Nat} {ctx : Context} {w : World} {tr : TransientStorage}
    {msg : Message} {r : MessageResult} (hw : Good crypto bank w) (hctx : ctx.crypto = crypto)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : TopOk (· = bank) w msg) (hv : msg.shouldTransferValue = true)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) : Good crypto bank r.world :=
  processMessageCall_good_v (goodOps_solvent size_code deleg_code) hw hdeleg hmsg hv hctx
    (cei_covers _) hr

/-- **Solvency over addresses**: when the slots of `balances[a]` do not collide, after any
transaction `Σ_a balances[a] ≤ address(bank).balance`. -/
theorem cei_backed {fuel : Nat} {ctx : Context} {w : World} {tr : TransientStorage}
    {msg : Message} {r : MessageResult} (hw : Good crypto bank w) (hctx : ctx.crypto = crypto)
    (hinj : Function.Injective fun a : Address => mappingSlot crypto (Word.ofAddress a) 0)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : TopOk (· = bank) w msg) (hv : msg.shouldTransferValue = true)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    ∑ a : Address, (r.world.sload bank (mappingSlot crypto (Word.ofAddress a) 0)).toNat ≤
      (r.world.balance bank).toNat := by
  rw [← owed_eq_sum_addresses _ hinj]
  exact (cei_solvent hw hctx hdeleg hmsg hv hr).backed

end Examples.Reentrancy.Solvency.CEI
