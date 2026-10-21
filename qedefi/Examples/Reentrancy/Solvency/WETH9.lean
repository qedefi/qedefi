import Examples.Reentrancy.Solvency.Model
import Examples.WETH9.Contracts.WETH9
import EvmLogic.Tactic.PrefixStep
import EvmLogic.Program.Reentrancy.PrefixCall
import EvmLogic.Program.Reentrancy.Tail
import EvmLogic.Solidity.Abi
import EvmLogic.Solidity.Word
import QEDefi.ERC20.Variant
import Examples.Reentrancy.Solvency.Deps

/-!
# WETH9's `withdraw` is atomic, whatever the recipient

Mainnet WETH9 (`Examples.WETH9.Contracts.WETH9`, solc 0.4.19) debits `balanceOf[msg.sender]`
(`SSTORE` at `0x0a73`) before it sends the ether with `msg.sender.transfer(wad)`: a `CALL` at
`0x0aa4` with gas argument `2300 · [wad = 0]`, so the recipient runs with at most the 2300-gas
stipend. Proved on the deployed bytecode, for **any gas** and **any recipient code**:

* `withdraw_frame`: a frame of WETH9 with calldata `withdraw(wad)` ends with the world it started
  from (it reverted, ran out of gas, or the recipient refused), or with exactly
  `withdrawWorld`: the caller's entry debited by `wad` and `wad` wei moved to the caller, after
  checking `wad ≤ balanceOf[caller]` and `wad ≤` the contract's ether. The dispatcher and body run
  under symbolic gas with `apwp_steps`; the send is `pwp_call_stipend` (the stipend lemma: the
  recipient, and everything it starts, changes no world state); the tail checks the flag, emits
  `Withdrawal` (`pwp_safe`) and stops.
* `withdraw_refines`, **`withdraw_halts_refines`**: such a frame refines the WETH model of
  `QEDefi.ERC20.Variant`: the world is unchanged, or its balances and ether are those of
  `weth9.withdraw s caller wad true` (the recipient accepted), for any abstract state `s`
  matching the world before.

The any-transaction ether backing of WETH9 (`Σ balanceOf ≤ ether`, every function) is
`Examples.Reentrancy.Solvency.WETH9Backed`.
-/

namespace Examples.Reentrancy.Solvency.WETH
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
  EvmLogic.Program.Reentrancy EvmLogic.Solidity Examples.WETH9.Contracts

/-! Kernel lookup table of the deployed code (bytes and jump destinations). -/
code_table WETH9.runtimeCode

/-! ## The withdrawal -/

/-- The slot of `balanceOf[a]` (mapping at slot `3`). -/
abbrev balSlot (crypto : Crypto) (a : Address) : Word := mappingSlot crypto (Word.ofAddress a) 3

/-- The world after `c` withdraws `wad` from `weth`: the entry debited, then (for `wad ≠ 0`)
`wad` wei moved from `weth` to `c`. -/
def withdrawWorld (crypto : Crypto) (weth c : Address) (wad : Word) (w : World) : World :=
  if wad = 0 then w.sstore weth (balSlot crypto c) (w.sload weth (balSlot crypto c) - wad)
  else moveEther (w.sstore weth (balSlot crypto c) (w.sload weth (balSlot crypto c) - wad))
    weth c wad

/-- How a frame running `withdraw(wad)` ends: in the world it started from, or after a checked
withdrawal. -/
def WithdrawPost (crypto : Crypto) (weth c : Address) (wad : Word) (w₀ w : World) : Prop :=
  w = w₀ ∨ (wad.toNat ≤ (w₀.sload weth (balSlot crypto c)).toNat ∧
    wad.toNat ≤ (w₀.balance weth).toNat ∧ w = withdrawWorld crypto weth c wad w₀)

/-! ## Words -/

/-- solc 0.4's selector extraction (`CALLDATALOAD 0 / 2²²⁴ & 0xffffffff`). -/
theorem div_selector (data : ByteArray) :
    (4294967295#256 &&& Word.div (Bytes.toWord (readBytes data 0 32))
      26959946667150639794667015087019630673637144422540572481103610249216#256) =
      BitVec.ofNat 256 (Abi.selectorOf data) := by
  have hs := Abi.shr_calldataload_zero data
  have hsel : Abi.selectorOf data < 2 ^ 32 := by
    have := Bytes.toNat_lt (readBytes data 0 4)
    rw [size_readBytes] at this
    unfold Abi.selectorOf; simpa using this
  have hdiv : Word.div (Bytes.toWord (readBytes data 0 32))
      26959946667150639794667015087019630673637144422540572481103610249216#256 =
      Word.shr (BitVec.ofNat 256 224) (Bytes.toWord (readBytes data 0 32)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [Word.div, Word.shr, BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight,
      BitVec.toNat_udiv, BitVec.toNat_ofNat]
    rw [Nat.shiftRight_eq_div_pow]
  rw [hdiv, hs]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : Abi.selectorOf data < 2 ^ 256),
    show (4294967295 : Nat) % 2 ^ 256 = 2 ^ 32 - 1 by decide, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hsel]

theorem lt_size_four {n : Nat} (h₁ : 4 ≤ n) (h₂ : n < 2 ^ 256) :
    Word.lt (ofNat n) (BitVec.ofNat 256 4) = 0 := by
  rw [Word.lt_eq_zero_iff]; simp only [ofNat, BitVec.toNat_ofNat]; omega

theorem le_of_iszero3 {x y : Word} (h : (Word.lt x y).iszero.iszero.iszero ≠ 0) :
    y.toNat ≤ x.toNat :=
  (Word.lt_eq_zero_iff x y).1 (iszero_ne_zero (iszero_eq_zero (iszero_ne_zero h)))

/-! ## The frame -/

set_option maxHeartbeats 4000000 in
/-- **A WETH9 frame running `withdraw(wad)` is atomic**, for any gas and any recipient: it ends
in the world it started from, or after the checked withdrawal `withdrawWorld`. -/
theorem withdraw_frame (ctx : Context) (tr : TransientStorage) (ow : World)
    (created : AddressSet) (msg : Message) (jd : Array Bool) (sub : Substate)
    (snap : World × TransientStorage) (ko ks : Nat) (parents : List Frame) (g0 : Nat)
    (hsel : Abi.selectorOf msg.data = 0x2e1a7d4d) (hsize : 4 ≤ msg.data.size)
    (hsize' : msg.data.size < 2 ^ 256) (hst : msg.isStatic = false) :
    WP (Machine.mk ctx (PrecompileImpl.standard ctx) (transferValue snap.1 msg) tr ow created
      (Frame.mk msg WETH9.runtimeCode jd 0 [] {} g0 .empty sub snap (.call ko ks)) parents)
      (fun _ => False) (FailOk (WithdrawPost ctx.crypto msg.currentTarget msg.caller
        (Bytes.toWord (readBytes msg.data 4 32)) snap.1)) := by
  have hsel' := div_selector msg.data
  rw [hsel] at hsel'
  have hlt := lt_size_four hsize hsize'
  have hsnap : WithdrawPost ctx.crypto msg.currentTarget msg.caller
      (Bytes.toWord (readBytes msg.data 4 32)) snap.1 snap.1 := .inl rfl
  apwp_steps [hsel', hlt, addressMask_and_ofAddress]
  -- the send: `CALL` with the stipend, the entry already debited
  have hv0 := iszero_ne_zero ‹Word.iszero msg.value ≠ 0›
  have hbal := le_of_iszero3 ‹(Word.lt _ _).iszero.iszero.iszero ≠ 0›
  rw [transferValue_zero _ _ hv0] at hbal ⊢
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
    -- the recipient accepted: the world is the withdrawal's
    have hx0 := iszero_eq_zero (iszero_ne_zero ‹Word.iszero (Word.iszero x) ≠ 0›)
    obtain ⟨haff, hworld⟩ := hW.2 hx0
    have hgood : WithdrawPost ctx.crypto msg.currentTarget msg.caller
        (Bytes.toWord (readBytes msg.data 4 32)) snap.1 w'' := by
      refine .inr ⟨hbal, ?_, ?_⟩
      · simpa [World.balance_sstore] using haff
      · rw [hworld, Word.toAddress_ofAddress]; rfl
    refine pwp_safe (b := 0xa2) (p := 4) ‹_› hgood rfl (by code_fact) (by decide) (by decide) ?_
    intro _ _ _ _ _ _
    dsimp only
    apwp_steps
    exact pwp_stop (by code_fact) rfl hgood

/-- **Any WETH9 frame running `withdraw(wad)` is atomic** (top level or a callee at any depth,
any gas, any recipient): it hands back the world it started from, or the checked withdrawal. -/
theorem withdraw_halts {m : Machine} {msg : Message} {ko ks : Nat}
    {snap : World × TransientStorage}
    (hfr : m.frame = Frame.init msg (.call ko ks) snap) (hcode : msg.code = WETH9.runtimeCode)
    (hworld : m.world = transferValue snap.1 msg)
    (hpre : m.precompiles = PrecompileImpl.standard m.ctx)
    (hsel : Abi.selectorOf msg.data = 0x2e1a7d4d) (hsize : 4 ≤ msg.data.size)
    (hsize' : msg.data.size < 2 ^ 256) (hst : msg.isStatic = false) :
    Halts m (fun mf o => WithdrawPost m.ctx.crypto msg.currentTarget msg.caller
      (Bytes.toWord (readBytes msg.data 4 32)) snap.1 (frameResult mf o).2.1) := by
  obtain ⟨ctx, pre, world, tr, ow, created, ⟨msg', code, jd, pc, stack, mem, gas, rd, sub, snap',
    kind⟩, parents⟩ := m
  dsimp only at hfr hworld hpre ⊢
  simp only [Frame.init, Frame.mk.injEq] at hfr
  obtain ⟨h1, h2, -, h4, h5, h6, h7, h8, -, h10, h11⟩ := hfr
  subst msg' code pc stack mem gas rd snap' kind
  rw [hcode]
  subst hworld hpre
  exact WP.halts_of_false (withdraw_frame ctx tr ow created msg jd sub snap ko ks parents
    msg.gas hsel hsize hsize' hst)

/-! ## Refinement of the WETH model -/

open QEDefi.ERC20

/-- WETH9's `balanceOf` mapping in a world, as a finitely supported function. -/
noncomputable def balOf (crypto : Crypto) (weth : Address) (w : World) : Address →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun a => (w.sload weth (balSlot crypto a)).toNat

/-- A model state describes a world's WETH9 balances and ether. -/
def Describes (crypto : Crypto) (weth : Address) (s : VState Address) (w : World) : Prop :=
  s.bal = balOf crypto weth w ∧ s.ether = (w.balance weth).toNat

/-- **The bytecode's withdrawal refines the model's**: a frame that ends as `WithdrawPost` says
leaves the world unchanged, or ends in a world described by `weth9.withdraw s c wad true` (the
recipient accepted), for any model state `s` describing the world before. The entry of `c` must
not share its slot with another address's (one Keccak target, `hfresh`). -/
theorem withdraw_refines {crypto : Crypto} {weth c : Address} {wad : Word} {w₀ w : World}
    {s : VState Address} (hd : Describes crypto weth s w₀) (hc : c ≠ weth)
    (hcode : (w₀.code weth).size ≠ 0)
    (hfresh : ∀ a, balSlot crypto a = balSlot crypto c → a = c)
    (h : WithdrawPost crypto weth c wad w₀ w) :
    w = w₀ ∨ ∃ s', (Variant.weth9 : Variant Address).withdraw s c wad.toNat true = some s' ∧
      Describes crypto weth s' w := by
  rcases h with h | ⟨hb, he, rfl⟩
  · exact .inl h
  right
  have hbc : s.bal c = (w₀.sload weth (balSlot crypto c)).toNat := by
    rw [hd.1]; simp [balOf]
  refine ⟨{ s with bal := s.bal - Finsupp.single c wad.toNat, ether := s.ether - wad.toNat },
    ?_, ?_, ?_⟩
  · simp [Variant.withdraw, Variant.weth9, Variant.standard, hbc, hd.2, Nat.not_lt.2 hb,
      Nat.not_lt.2 he]
  · -- the balances
    ext a
    have hk1 : ∀ v, (w₀.sstore weth (balSlot crypto c) v).sload weth (balSlot crypto a) =
        if a = c then v else w₀.sload weth (balSlot crypto a) := by
      intro v
      by_cases ha : a = c
      · subst ha; simp
      · rw [World.sload_sstore_ne_key _ _ _ (fun h => ha (hfresh a h))]; simp [ha]
    have hw : (withdrawWorld crypto weth c wad w₀).sload weth (balSlot crypto a) =
        if a = c then w₀.sload weth (balSlot crypto c) - wad
        else w₀.sload weth (balSlot crypto a) := by
      unfold withdrawWorld
      split
      · exact hk1 _
      · rw [(keep_moveEther (src := weth) (dst := c) (v := wad)
          (by rw [World.code_sstore]; exact hcode)).sload]
        exact hk1 _
    simp only [balOf, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply,
      Finsupp.coe_equivFunOnFinite_symm]
    rw [hd.1, hw]
    simp only [balOf, Finsupp.coe_equivFunOnFinite_symm]
    by_cases ha : a = c
    · subst ha; simp [toNat_sub_of_le hb]
    · simp [ha, Ne.symm ha]
  · -- the ether
    show s.ether - wad.toNat = ((withdrawWorld crypto weth c wad w₀).balance weth).toNat
    rw [hd.2]
    unfold withdrawWorld
    split
    · rename_i h0; subst h0; simp
    · rw [balance_moveEther _ _ (Ne.symm hc)]
      simp only [ite_true, World.balance_sstore]
      rw [toNat_sub_of_le he]

/-- **WETH9's `withdraw` refines the model atomically, whatever the recipient**: any frame of
the deployed bytecode running `withdraw(wad)` (any gas, any depth, any recipient code) hands back
the world it started from, or a world described by `weth9.withdraw s caller wad true`. -/
theorem withdraw_halts_refines {m : Machine} {msg : Message} {ko ks : Nat}
    {snap : World × TransientStorage} {s : VState Address}
    (hfr : m.frame = Frame.init msg (.call ko ks) snap) (hcode : msg.code = WETH9.runtimeCode)
    (hworld : m.world = transferValue snap.1 msg)
    (hpre : m.precompiles = PrecompileImpl.standard m.ctx)
    (hsel : Abi.selectorOf msg.data = 0x2e1a7d4d) (hsize : 4 ≤ msg.data.size)
    (hsize' : msg.data.size < 2 ^ 256) (hst : msg.isStatic = false)
    (hd : Describes m.ctx.crypto msg.currentTarget s snap.1)
    (hc : msg.caller ≠ msg.currentTarget) (hcw : (snap.1.code msg.currentTarget).size ≠ 0)
    (hfresh : ∀ a, balSlot m.ctx.crypto a = balSlot m.ctx.crypto msg.caller → a = msg.caller) :
    Halts m (fun mf o => (frameResult mf o).2.1 = snap.1 ∨
      ∃ s', (Variant.weth9 : Variant Address).withdraw s msg.caller
        (Bytes.toWord (readBytes msg.data 4 32)).toNat true = some s' ∧
        Describes m.ctx.crypto msg.currentTarget s' (frameResult mf o).2.1) :=
  (withdraw_halts hfr hcode hworld hpre hsel hsize hsize' hst).mono
    fun _ _ _ h => withdraw_refines hd hc hcw hfresh h

end Examples.Reentrancy.Solvency.WETH
