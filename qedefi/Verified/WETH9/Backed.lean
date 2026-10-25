import Verified.WETH9.Solvency

/-!
# WETH9's ether backs its tokens after any transaction

Mainnet WETH9 (`Verified.WETH9.Contracts.WETH9`, solc 0.4.19) keeps `balanceOf` at slot `3` and
`allowance` at slot `4`. `Good crypto weth` is `Solvent` for the `balanceOf` entries
(`QEDefi.Solvency.Bank`): what WETH9 owes, summed over the entries' slots, is at
most its ether and below `2²⁵⁶`, and all ether is below `2²⁵⁶`. Proved on the deployed bytecode,
for any gas:

* `weth_frame`: **every function** keeps WETH9 solvent. `apwp_steps` runs the dispatcher and
  the bodies of `deposit()` (and the fallback, which calls it), `withdraw`, `transfer`,
  `transferFrom` (with and without the allowance debit), `approve`, `balanceOf` and
  `allowance`; the string and `decimals`/`totalSupply` views, whose code loops or uses `EXP`/
  `BALANCE`, are stopped at their entries (`apwp_steps stop_at`) and closed by certified
  world-safe tails (`view_wp`). The writes are solc 0.4's unchecked arithmetic:
  `solvent_credit_unchecked` (a credit backed by the ether cannot wrap, since an entry is at
  most what WETH9 owes), `solvent_move` (debit then credit, `transferFrom`), `solvent_debit` and
  `solvent_send` (`withdraw`, whose send has the 2300-gas stipend: `pwp_call_stipend`).
* `weth_covers`: the summaries, with no induction (nothing can call back into WETH9).
* **`weth9_solvent`**, **`weth9_backed`**: any top-level message call from a solvent world leaves
  WETH9 solvent; with non-colliding `balanceOf` slots, `Σₐ balanceOf[a] ≤ address(weth).balance`
  and the sum is below `2²⁵⁶`, over all addresses.

The only Keccak hypothesis is `Disjoint (allowanceSlots crypto) (balanceSlots crypto 3)`: no
`allowance[a][b]` entry (the slots `approve` and `transferFrom` write) shares its slot with a
`balanceOf` entry. It is about two finite families of slots, not injectivity of Keccak.
-/

namespace Verified.WETH9
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
open QEDefi.Solvency
  EvmLogic.Program.Reentrancy EvmLogic.Solidity EvmLogic.AbsInt Verified.WETH9.Contracts

/-! ## Normal forms -/

/-- solc's address mask of any word is an address. -/
theorem mask_and_eq (x : Word) :
    1461501637330902918203684832716283019655932542975#256 &&& x =
      Word.ofAddress (Word.toAddress x) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Word.ofAddress, Word.toAddress, BitVec.toNat_and, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by decide : 1461501637330902918203684832716283019655932542975 < 2 ^ 256),
    show (1461501637330902918203684832716283019655932542975 : Nat) = 2 ^ 160 - 1 by decide,
    Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]

/-- A Keccak of two words is a mapping slot. -/
theorem keccak_mappingSlot (crypto : Crypto) (k b : Word) :
    crypto.keccak256 (Bytes.ofWord k ++ Bytes.ofWord b) = mappingSlot crypto k b := rfl

/-! ## Allowances -/

/-- The slots of `allowance[a][b]` (nested mapping at slot `4`), for all addresses `a`, `b`. -/
def allowanceSlots (crypto : Crypto) : Finset Word :=
  Finset.univ.image fun p : Address × Address =>
    mappingSlot crypto (Word.ofAddress p.2) (mappingSlot crypto (Word.ofAddress p.1) 4#256)

/-- Under the disjointness hypothesis, no allowance entry is a balance entry. -/
theorem allowance_not_mem {crypto : Crypto}
    (hK : Disjoint (allowanceSlots crypto) (balanceSlots crypto 3#256)) (a b : Address) :
    mappingSlot crypto (Word.ofAddress b) (mappingSlot crypto (Word.ofAddress a) 4#256) ∉
      balanceSlots crypto 3#256 :=
  Finset.disjoint_left.1 hK (Finset.mem_image.2 ⟨(a, b), Finset.mem_univ _, rfl⟩)

/-- A write to an allowance entry leaves every balance entry. -/
theorem sload_allowance_sstore {crypto : Crypto}
    (hK : Disjoint (allowanceSlots crypto) (balanceSlots crypto 3#256)) (w : World) (bank : Address)
    (a b c : Address) (v : Word) :
    (w.sstore bank
      (mappingSlot crypto (Word.ofAddress b) (mappingSlot crypto (Word.ofAddress a) 4#256)) v).sload
      bank (mappingSlot crypto (Word.ofAddress c) 3#256) =
      w.sload bank (mappingSlot crypto (Word.ofAddress c) 3#256) :=
  World.sload_sstore_ne_key _ _ _ fun h =>
    allowance_not_mem hK a b (h ▸ mem_balanceSlots crypto 3#256 c)

/-! ## Debits, credits, transfers, sends -/

section
variable {crypto : Crypto} {base : Word} {code : ByteArray} {bank : Address}

/-- **Debiting `v` from an entry holding at least `v`** keeps the bank solvent, and lowers what
it owes by `v`. -/
theorem solvent_debit {w : World} {a : Address} {v : Word} (h : Solvent crypto base code bank w)
    (hv : v.toNat ≤ (w.sload bank (mappingSlot crypto (Word.ofAddress a) base)).toNat) :
    Solvent crypto base code bank (w.sstore bank (mappingSlot crypto (Word.ofAddress a) base)
        (w.sload bank (mappingSlot crypto (Word.ofAddress a) base) - v)) ∧
      owed crypto base bank (w.sstore bank (mappingSlot crypto (Word.ofAddress a) base)
        (w.sload bank (mappingSlot crypto (Word.ofAddress a) base) - v)) + v.toNat =
        owed crypto base bank w := by
  have ho := owed_sstore (crypto := crypto) (base := base) (bank := bank) w a
    (w.sload bank (mappingSlot crypto (Word.ofAddress a) base) - v)
  rw [toNat_sub_of_le hv] at ho
  have hle := sload_le_owed (crypto := crypto) (base := base) (bank := bank) w a
  refine ⟨⟨?_, ?_, ?_, ?_⟩, by omega⟩
  · rw [World.code_sstore, h.code]
  · rw [World.balance_sstore]; have := h.backed; omega
  · have := h.bounded; omega
  · rw [supply_sstore]; exact h.capped

/-- **Crediting `v` to an entry**, unchecked (solc 0.4), keeps the bank solvent when its ether
covers what it owes plus `v`: the entry is at most what it owes, so the sum does not wrap. -/
theorem solvent_credit_unchecked {w : World} {a : Address} {v : Word} (hcode : w.code bank = code)
    (hcap : supply w < 2 ^ 256)
    (hb : owed crypto base bank w + v.toNat ≤ (w.balance bank).toNat) :
    Solvent crypto base code bank (w.sstore bank (mappingSlot crypto (Word.ofAddress a) base)
      (w.sload bank (mappingSlot crypto (Word.ofAddress a) base) + v)) := by
  have hle := sload_le_owed (crypto := crypto) (base := base) (bank := bank) w a
  have hbal := (w.balance bank).isLt
  have hadd := QEDefi.Solvency.toNat_add_of_lt
    (x := w.sload bank (mappingSlot crypto (Word.ofAddress a) base))
    (y := v) (by omega)
  have ho := owed_sstore (crypto := crypto) (base := base) (bank := bank) w a
    (w.sload bank (mappingSlot crypto (Word.ofAddress a) base) + v)
  rw [hadd] at ho
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [World.code_sstore, hcode]
  · rw [World.balance_sstore]; omega
  · omega
  · rw [supply_sstore]; exact hcap

/-- **Moving `v` between two entries** (debit `src`, then credit `dst`, as WETH9's
`transferFrom`) keeps the bank solvent when `src` holds at least `v`. -/
theorem solvent_move {w : World} {src dst : Address} {v : Word}
    (h : Solvent crypto base code bank w)
    (hv : v.toNat ≤ (w.sload bank (mappingSlot crypto (Word.ofAddress src) base)).toNat) :
    Solvent crypto base code bank
      ((w.sstore bank (mappingSlot crypto (Word.ofAddress src) base)
          (w.sload bank (mappingSlot crypto (Word.ofAddress src) base) - v)).sstore bank
        (mappingSlot crypto (Word.ofAddress dst) base)
        ((w.sstore bank (mappingSlot crypto (Word.ofAddress src) base)
          (w.sload bank (mappingSlot crypto (Word.ofAddress src) base) - v)).sload bank
            (mappingSlot crypto (Word.ofAddress dst) base) + v)) := by
  obtain ⟨h1, ho⟩ := solvent_debit h hv
  refine solvent_credit_unchecked h1.code h1.capped ?_
  rw [ho, World.balance_sstore]; exact h.backed

/-- **Sending `v` wei out of the bank** keeps it solvent when what it owes plus `v` is backed. -/
theorem solvent_send {w : World} {c : Address} {v : Word} (hsize : code.size ≠ 0)
    (hcode : w.code bank = code) (hcap : supply w < 2 ^ 256) (hc : c ≠ bank)
    (hb : owed crypto base bank w + v.toNat ≤ (w.balance bank).toNat)
    (hv : v.toNat ≤ (w.balance bank).toNat) :
    Solvent crypto base code bank (moveEther w bank c v) := by
  have hk : Keep bank w (moveEther w bank c v) := keep_moveEther (by rw [hcode]; exact hsize)
  refine ⟨by rw [hk.code]; exact hcode, ?_, ?_, by rw [supply_moveEther hv hcap]; exact hcap⟩
  · rw [owed_keep hk, balance_moveEther _ _ (Ne.symm hc)]
    simp only [ite_true]
    rw [toNat_sub_of_le hv]
    omega
  · rw [owed_keep hk]; have := (w.balance bank).isLt; omega

end

/-! ## Views: certified world-safe tails -/

/-- The tail of `name()` from its entry is world-safe (kernel evaluation). -/
theorem view_check_name :
    tailCheck (fun _ => false) WETH9.runtimeCode [] 0xb9 [.top] 10000 = true := by
  decide +kernel

/-- The tail of `totalSupply()` from its entry is world-safe. -/
theorem view_check_totalSupply :
    tailCheck (fun _ => false) WETH9.runtimeCode [] 0x1a1 [.top] 10000 = true := by
  decide +kernel

/-- The tail of `decimals()` from its entry is world-safe. -/
theorem view_check_decimals :
    tailCheck (fun _ => false) WETH9.runtimeCode [] 0x266 [.top] 10000 = true := by
  decide +kernel

/-- The tail of `symbol()` from its entry is world-safe. -/
theorem view_check_symbol :
    tailCheck (fun _ => false) WETH9.runtimeCode [] 0x2e2 [.top] 10000 = true := by
  decide +kernel



/-- The views' entries: `name()`, `totalSupply()`, `decimals()`, `symbol()`. -/
theorem view_checks {q : Nat} (hq : q ∈ [0xb9, 0x1a1, 0x266, 0x2e2]) :
    tailCheck (fun _ => false) WETH9.runtimeCode [] q [.top] 10000 = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  exacts [view_check_name, view_check_totalSupply, view_check_decimals, view_check_symbol]

/-- **A view of WETH9 entered at `q`** (its tail from `q` certified world-safe) ends in a `Good`
world when the frame starts in one. -/
theorem view_wp {Good : World → Prop} {Q : Machine → Prop} {m : Machine} {ko ks : Nat}
    (hq : m.frame.pc ∈ [0xb9, 0x1a1, 0x266, 0x2e2])
    (hcode : m.frame.code = WETH9.runtimeCode) {x : Word}
    (hstk : m.frame.stack = [x]) (hk : m.frame.kind = .call ko ks)
    (hsnap : Good m.frame.snapshot.1) (hw : Good m.world) : WP m Q (FailOk Good) := by
  obtain ⟨t, hcert, hsafe⟩ := tailCheck_sound (ρ := fun _ => 0) (view_checks hq)
    (fun _ _ h => by cases h)
  refine WP.halts (Halts.failOk hk hsnap hw (noWrite_halts_tail hcert hsafe hcode
    (inCert_of_entry hcert rfl ?_)))
  rw [hstk]
  simp only [StackOk, AVal.Holds, and_true]

/-! ## Any frame of WETH9 -/

/-- WETH9 is solvent (`balanceOf` at slot `3`, the deployed code). -/
abbrev Good (crypto : Crypto) (weth : Address) : World → Prop :=
  Solvent crypto 3#256 WETH9.runtimeCode weth

/-- The transaction hashes with `crypto`. -/
abbrev Ctx (crypto : Crypto) : Context → Prop := fun c => c.crypto = crypto

theorem size_code : WETH9.runtimeCode.size ≠ 0 := by rw [WETH9.size_runtimeCode]; decide

theorem deleg_code : delegatedAddress? WETH9.runtimeCode = none := by decide +kernel

set_option hygiene false in
/-- A `LOG` at which the world is `Good` (by `g`), then the steps to `STOP`. -/
local macro "log_stop " b:num p:num g:term : tactic => `(tactic| (
  refine pwp_safe (b := $b) (p := $p) ‹_› ?_ rfl (by code_fact) (by decide) (by decide) ?_
  · dsimp only; exact $g
  · intro _ _ _ _ _ _
    dsimp only
    apwp_steps
    exact pwp_stop (by code_fact) rfl (by dsimp only; exact $g)))

set_option hygiene false in
/-- A `LOG` at which the world is `Good` (by `g`), then the steps to `RETURN`. -/
local macro "log_return " b:num p:num g:term : tactic => `(tactic| (
  refine pwp_safe (b := $b) (p := $p) ‹_› ?_ rfl (by code_fact) (by decide) (by decide) ?_
  · dsimp only; exact $g
  · intro _ _ _ _ _ _
    dsimp only
    apwp_steps
    exact pwp_return ‹_› (by code_fact) rfl rfl (by dsimp only; exact $g)))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
/-- **Every frame of WETH9 keeps it solvent**, for any gas and any calldata. -/
theorem weth_frame {crypto : Crypto}
    (hK : Disjoint (allowanceSlots crypto) (balanceSlots crypto 3#256))
    (ctx : Context) (tr : TransientStorage) (ow : World) (created : AddressSet) (msg : Message)
    (jd : Array Bool) (sub : Substate) (snap : World × TransientStorage) (ko ks : Nat)
    (parents : List Frame) (g0 : Nat)
    (hsnap : Good crypto msg.currentTarget snap.1) (hst : msg.isStatic = false)
    (hcaller : msg.caller ≠ msg.currentTarget)
    (hstv : msg.shouldTransferValue = true)
    (haff : msg.value ≠ 0 → msg.value.toNat ≤ (snap.1.balance msg.caller).toNat)
    (hctx : ctx.crypto = crypto) :
    WP (Machine.mk ctx (PrecompileImpl.standard ctx) (transferValue snap.1 msg) tr ow created
      (Frame.mk msg WETH9.runtimeCode jd 0 [] {} g0 .empty sub snap (.call ko ks)) parents)
      (fun _ => False) (FailOk (Good crypto msg.currentTarget)) := by
  subst hctx
  have S := goodOps_solvent (crypto := ctx.crypto) (base := 3#256) (bank := msg.currentTarget)
    size_code deleg_code
  have hT : Good ctx.crypto msg.currentTarget (transferValue snap.1 msg) :=
    S.transfer hsnap fun _ h2 => ⟨haff h2, .inl hcaller⟩
  have hB := backed_transferValue (base := 3#256) size_code hsnap rfl hcaller hstv haff
  apwp_steps stop_at [0xb9, 0x1a1, 0x266, 0x2e2] [addressMask_and_ofAddress, mask_and_eq,
    Word.toAddress_ofAddress, keccak_mappingSlot, EvmLogic.Solidity.eq_self]
  -- the fallback (no selector matched): `deposit()`
  · log_stop 0xa2 4 (solvent_credit_unchecked hT.code hT.capped hB)
  -- `allowance(a, b)`
  · exact pwp_return ‹_› (by code_fact) rfl rfl hT
  -- `deposit()`
  · log_stop 0xa2 4 (solvent_credit_unchecked hT.code hT.capped hB)
  -- `transfer(dst, wad)`
  · log_return 0xa3 5 (solvent_move hT (le_of_iszero3 (by with_reducible assumption)))
  -- `symbol()`
  · exact view_wp (by simp) rfl rfl rfl hsnap hT
  -- `balanceOf(a)`
  · exact pwp_return ‹_› (by code_fact) rfl rfl hT
  -- `decimals()`
  · exact view_wp (by simp) rfl rfl rfl hsnap hT
  -- `withdraw(wad)`: the send with the stipend, the caller's entry already debited
  · have hbal := le_of_iszero3 ‹(Word.lt _ _).iszero.iszero.iszero ≠ 0›
    obtain ⟨hW1, howed⟩ := solvent_debit hT hbal
    refine pwp_call_stipend ‹_› (by code_fact) rfl rfl ?_ ?_
    · by_cases hw0 : Bytes.toWord (readBytes msg.data 4 32) = 0
      · rw [hw0]; decide
      · have hz : (Bytes.toWord (readBytes msg.data 4 32)).iszero = 0 := iszero_of_ne hw0
        have hn : (Bytes.toWord (readBytes msg.data 4 32)).toNat ≠ 0 := fun h =>
          hw0 (BitVec.eq_of_toNat_eq (by simpa using h))
        rw [hz]; simp [hn, Gas.callStipend]
    · intro m'' x hsf hpc hx hW
      obtain ⟨c'', p'', w'', t'', o'', cr'', ⟨msg'', code'', jd'', pc'', st'', mem'', g'', rd'',
        sub'', snap'', kind''⟩, par''⟩ := m''
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hsf
      dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 hpc hx hW
      subst c'' p'' o'' par'' msg'' code'' jd'' kind'' snap'' pc'' st''
      apwp_steps
      -- the recipient accepted: the debit and the send keep WETH9 solvent
      have hx0 := iszero_eq_zero (iszero_ne_zero ‹Word.iszero (Word.iszero x) ≠ 0›)
      obtain ⟨haff', hworld⟩ := hW.2 hx0
      have hgood : Good ctx.crypto msg.currentTarget w'' := by
        rw [hworld, Word.toAddress_ofAddress]
        split
        · exact hW1
        · refine solvent_send size_code hW1.code hW1.capped hcaller ?_ haff'
          rw [howed, World.balance_sstore]; exact hT.backed
      refine pwp_safe (b := 0xa2) (p := 4) ‹_› hgood rfl (by code_fact) (by decide) (by decide) ?_
      intro _ _ _ _ _ _
      dsimp only
      apwp_steps
      exact pwp_stop (by code_fact) rfl hgood
  -- `transferFrom(src, dst, wad)`, debiting the allowance
  · log_return 0xa3 5 (solvent_move (hT.sstore_other (allowance_not_mem hK _ _) _)
      (by rw [sload_allowance_sstore hK]; exact le_of_iszero3 (by with_reducible assumption)))
  -- `transferFrom(src, dst, wad)`, unlimited allowance
  · log_return 0xa3 5 (solvent_move hT (le_of_iszero3 (by with_reducible assumption)))
  -- `transferFrom(src, dst, wad)`, debiting the allowance
  · log_return 0xa3 5 (solvent_move (hT.sstore_other (allowance_not_mem hK _ _) _)
      (by rw [sload_allowance_sstore hK]; exact le_of_iszero3 (by with_reducible assumption)))
  -- `transferFrom(src, dst, wad)` by `src` itself
  · log_return 0xa3 5 (solvent_move hT (le_of_iszero3 (by with_reducible assumption)))
  -- `totalSupply()`
  · exact view_wp (by simp) rfl rfl rfl hsnap hT
  -- `approve(guy, wad)`
  · log_return 0xa3 5 (hT.sstore_other (allowance_not_mem hK _ _) _)
  -- `name()`
  · exact view_wp (by simp) rfl rfl rfl hsnap hT
  -- calldata shorter than a selector: `deposit()`
  · log_stop 0xa2 4 (solvent_credit_unchecked hT.code hT.capped hB)

/-! ## Any frame, any transaction -/

/-- **WETH9's summaries**, for every gas (no induction: its only call, in `withdraw`, has the
2300-gas stipend, so nothing calls back into it). -/
theorem weth_covers {crypto : Crypto} {weth : Address}
    (hK : Disjoint (allowanceSlots crypto) (balanceSlots crypto 3#256)) (G : Nat) :
    CoversV (· = weth) (Good crypto weth) (Ctx crypto) G := by
  intro m hd
  obtain ⟨⟨⟨⟨ko, ks, hfr⟩, ⟨hP, hst⟩, hsnap, hkeep, hcode, -, -, hcaller, -, -, hpre⟩,
    hweq, haff⟩, hstv, hctx⟩ := hd
  obtain ⟨ctx, pre, world, tr, ow, created, ⟨msg, code, jd, pc, stack, mem, gas, rd, sub, snap,
    kind⟩, parents⟩ := m
  dsimp only at hfr hP hst hsnap hkeep hcode hcaller hpre hweq haff hstv hctx ⊢
  simp only [Frame.init, Frame.mk.injEq] at hfr
  obtain ⟨-, rfl, -, rfl, rfl, rfl, rfl, rfl, -, -, rfl⟩ := hfr
  have hc : msg.code = WETH9.runtimeCode := by
    rw [hcode, hP, (hkeep weth rfl).code]; exact hsnap.code
  rw [hc]
  subst hweq hpre hP
  apply WP.halts_of_false
  exact weth_frame hK ctx tr ow created msg jd sub snap ko ks parents msg.gas hsnap hst hcaller
    hstv (haff hstv) hctx

/-- **WETH9 stays solvent after any transaction**: from a world in which it is solvent, any
top-level message call (any target, code, value, calldata; an unprotected sender; any callees,
including ones that call WETH9 at any depth) that moves its value, hashing with the world's
`crypto`, before Prague or without EIP-7702 authorizations, ends in a world in which it is
solvent — provided no `allowance` entry shares its slot with a `balanceOf` entry. -/
theorem weth9_solvent {crypto : Crypto} {weth : Address}
    (hK : Disjoint (allowanceSlots crypto) (balanceSlots crypto 3#256)) {fuel : Nat}
    {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message} {r : MessageResult}
    (hw : Good crypto weth w) (hctx : ctx.crypto = crypto)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : TopOk (· = weth) w msg) (hv : msg.shouldTransferValue = true)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) : Good crypto weth r.world :=
  processMessageCall_good_v (goodOps_solvent size_code deleg_code) hw hdeleg hmsg hv hctx
    (weth_covers hK _) hr

/-- **WETH9's ether backs its tokens, after any transaction**: when the slots of
`balanceOf[a]` do not collide, `Σₐ balanceOf[a] ≤ address(weth).balance` and the sum is below
`2²⁵⁶`, over all addresses. -/
theorem weth9_backed {crypto : Crypto} {weth : Address}
    (hK : Disjoint (allowanceSlots crypto) (balanceSlots crypto 3#256))
    (hinj : Function.Injective (balSlot crypto)) {fuel : Nat} {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} {r : MessageResult}
    (hw : Good crypto weth w) (hctx : ctx.crypto = crypto)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : TopOk (· = weth) w msg) (hv : msg.shouldTransferValue = true)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    ∑ a : Address, (r.world.sload weth (balSlot crypto a)).toNat ≤
        (r.world.balance weth).toNat ∧
      ∑ a : Address, (r.world.sload weth (balSlot crypto a)).toNat < 2 ^ 256 := by
  have h := weth9_solvent hK hw hctx hdeleg hmsg hv hr
  have he := owed_eq_sum_addresses (crypto := crypto) (base := 3#256) (bank := weth) r.world hinj
  exact ⟨he ▸ h.backed, he ▸ h.bounded⟩

end Verified.WETH9
