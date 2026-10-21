import Examples.Solmate.ERC20.SpecView

/-!
# The asset's `mint` and `burn`

`MockERC20.mint`/`burn` (public, unrestricted Solmate `_mint`/`_burn`) in any non-static frame:
`*_halts_ok`/`*_halts_revert` (checked `totalSupply +=` / `balanceOf[from] -=`) and
`assetMint_refines`/`assetBurn_refines` against `Token.mint`/`Token.burn`. The refinements need
`KeccakAvoids crypto (AddressKeyed [3]) [2]`: a balance slot equal to the supply slot 2 would
make the view double-count, so the theorem is false without it.
-/

section

namespace Examples.Solmate.ERC20
open Examples.Solmate.ERC4626 QEDefi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open QEDefi.Math QEDefi.ERC20 Examples.Solmate.ERC4626.Shares

/-! ## Word lemmas: the checked addition -/

theorem gt_add_self_of_lt {x y : Word} (h : x.toNat + y.toNat < 2 ^ 256) :
    Word.gt x (y + x) = 0#256 := by
  simp only [Word.gt, Word.ofBool, BitVec.ult, decide_eq_true_eq]
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  simp

theorem gt_add_self_of_le {x y : Word} (h : 2 ^ 256 ≤ x.toNat + y.toNat) :
    Word.gt x (y + x) = 1#256 := by
  simp only [Word.gt, Word.ofBool, BitVec.ult, decide_eq_true_eq]
  have hx := x.isLt
  have hy := y.isLt
  rw [BitVec.toNat_add, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  simp only [show y.toNat + x.toNat - 2 ^ 256 < x.toNat by omega, ]
  rfl

/-! ## The world -/

/-- The world after `mint`: `totalSupply += amount`, then `balanceOf[dst] += amount`. -/
def mintWorld (crypto : Crypto) (w : World) (token dst : Address) (amount : Word) : World :=
  let st := ERC20.balanceSlot crypto ERC20.Layout.solmate dst
  let w₁ := w.sstore token 2#256 (amount + w.sload token 2#256)
  w₁.sstore token st (amount + w₁.sload token st)

theorem sload_mintWorld {crypto : Crypto} {w : World} {token dst b : Address} {amount k : Word}
    (h : b ≠ token ∨ (k ≠ 2#256 ∧ k ≠ ERC20.balanceSlot crypto ERC20.Layout.solmate dst)) :
    (mintWorld crypto w token dst amount).sload b k = w.sload b k := by
  simp only [mintWorld]
  rw [sload_sstore_frame (by rcases h with h | h; exact .inl h; exact .inr h.2),
    sload_sstore_frame (by rcases h with h | h; exact .inl h; exact .inr h.1)]

theorem code_mintWorld (crypto : Crypto) (w : World) (token dst : Address) (amount : Word)
    (b : Address) : (mintWorld crypto w token dst amount).code b = w.code b := by
  simp [mintWorld]

/-- A successful asset `mint`: empty output, world `mintWorld`, ≤ 55000 gas. -/
def MintOk (dst : Address) (amount : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success .empty ∧
  mf.world = mintWorld m.ctx.crypto m.world m.frame.msg.currentTarget dst amount ∧
  mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
  m.frame.gasLeft ≤ mf.frame.gasLeft + 55000

/-! ## Bytecode -/

set_option maxHeartbeats 0 in
/-- **The asset's `mint`, success**: when `totalSupply + amount` does not overflow. -/
theorem mint_halts_ok {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {dst : Address}
    {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x40c10f19 (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    (hov : (m.world.sload m.frame.msg.currentTarget 2#256).toNat + amount.toNat < 2 ^ 256) :
    Halts m (MintOk dst amount m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  simp only [gt_add_self_of_lt hov, iszero_zero]
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  pwp_codecopy
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  refine WP.halt_of_step (step_stop ?_) (by same_frame) ⟨rfl, ?_, rfl, rfl, ?_⟩
  · pcode_fact
  · simp only [mintWorld, balanceSlot_solmate]
  · evm_gas

set_option maxHeartbeats 0 in
/-- **The asset's `mint`, overflow**, in any frame: `Panic(0x11)`. -/
theorem mint_halts_revert {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) {dst : Address} {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x40c10f19 (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 10000 ≤ m.frame.gasLeft)
    (hov : 2 ^ 256 ≤ (m.world.sload m.frame.msg.currentTarget 2#256).toNat + amount.toNat) :
    Halts m (Reverts 10000 m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  simp only [gt_add_self_of_le hov, iszero_one]
  pwp_steps
  refine ⟨⟨_, rfl⟩, ?_⟩
  dsimp only [outputMachine]
  evm_gas

/-! ## Against the model -/

theorem balanceSlot_ne_two {crypto : Crypto}
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256]) (a : Address) :
    ERC20.balanceSlot crypto ERC20.Layout.solmate a ≠ 2#256 :=
  mappingSlot_ne_of_avoids hk ⟨a, 3#256, by simp, rfl⟩ (by simp)

/-- Allowance entries represented after `mint`/`burn`: those in neither written slot. -/
def MintAllowances (crypto : Crypto) (dst : Address) (o sp : Address) : Prop :=
  ERC20.allowanceSlot crypto ERC20.Layout.solmate o sp ≠ 2#256 ∧
    ERC20.allowanceSlot crypto ERC20.Layout.solmate o sp ≠
      ERC20.balanceSlot crypto ERC20.Layout.solmate dst

theorem repOn_mintWorld {crypto : Crypto} {w : World} {token dst : Address} {amount : Word}
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256])
    (hd : ERC20.BalanceSlotOk crypto ERC20.Layout.solmate dst)
    {t t' : Token Address} (hr : Rep (ERC20.view crypto ERC20.Layout.solmate w token) t)
    (hw : t.WF) (ht : t.mint dst amount.toNat = some t') :
    RepOn (MintAllowances crypto dst)
      (ERC20.view crypto ERC20.Layout.solmate (mintWorld crypto w token dst amount) token) t' := by
  obtain ⟨hov, rfl⟩ := Token.mint_eq_some.1 ht
  have hd2 := balanceSlot_ne_two hk dst
  have hts : (w.sload token 2#256).toNat = t.totalSupply := hr.totalSupply
  have hbal : (w.sload token (ERC20.balanceSlot crypto ERC20.Layout.solmate dst)).toNat =
      t.balanceOf dst := hr.balanceOf dst
  have hle := Token.balanceOf_le_totalSupply hw dst
  have hM : MAX < 2 ^ 256 := by unfold MAX; omega
  refine ⟨?_, fun a => ?_, fun o sp hp => ?_⟩
  · show ((mintWorld crypto w token dst amount).sload token 2#256).toNat = _
    simp only [mintWorld]
    rw [World.sload_sstore_ne_key _ _ _ (fun e => hd2 e.symm), World.sload_sstore_self,
      BitVec.toNat_add, hts, Nat.mod_eq_of_lt (by omega)]
    omega
  · show ((mintWorld crypto w token dst amount).sload token
      (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat = _
    dsimp only
    rw [Token.add_single_apply]
    by_cases ha : dst = a
    · subst ha
      simp only [mintWorld, World.sload_sstore_self, ↓reduceIte]
      rw [World.sload_sstore_ne_key _ _ _ hd2, BitVec.toNat_add, hbal,
        Nat.mod_eq_of_lt (by omega)]
      omega
    · simp only [ha, ↓reduceIte]
      rw [sload_mintWorld (.inr ⟨balanceSlot_ne_two hk a,
        ERC20.balanceSlot_ne hd (Ne.symm ha)⟩)]
      exact hr.balanceOf a
  · show ((mintWorld crypto w token dst amount).sload token
      (ERC20.allowanceSlot crypto ERC20.Layout.solmate o sp)).toNat = _
    rw [sload_mintWorld (.inr hp)]
    exact hr.allowance o sp trivial

/-- **The asset's `mint` refines `Token.mint`**, in any non-static frame. -/
theorem assetMint_refines {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hstatic : m.frame.msg.isStatic = false) {dst : Address} {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x40c10f19 (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    (hk : KeccakAvoids m.ctx.crypto (AddressKeyed [3#256]) [2#256])
    (hdst : ERC20.BalanceSlotOk m.ctx.crypto ERC20.Layout.solmate dst)
    {t : Token Address} (hr : Rep (assetView m) t) (hw : t.WF) :
    match t.mint dst amount.toNat with
    | some t' => Halts m (fun mf o => MintOk dst amount m mf o ∧
        RepOn (MintAllowances m.ctx.crypto dst)
          (ERC20.view m.ctx.crypto ERC20.Layout.solmate mf.world m.frame.msg.currentTarget) t')
    | none => Halts m (Reverts 10000 m) := by
  have hts : (m.world.sload m.frame.msg.currentTarget 2#256).toNat = t.totalSupply :=
    hr.totalSupply
  split
  · rename_i t' hT
    have hov := (Token.mint_eq_some.1 hT).1
    have hrep := repOn_mintWorld hk hdst hr hw hT
    refine (mint_halts_ok m hf hval hstatic hd hsz hg (by rw [hts]; unfold MAX at hov; omega)).mono
      fun mf o _ hok => ⟨hok, ?_⟩
    rw [hok.2.1]
    exact hrep
  · rename_i hT
    have hov : MAX < t.totalSupply + amount.toNat := by
      unfold Token.mint at hT
      split at hT
      · assumption
      · cases hT
    exact mint_halts_revert m hf hval hd hsz (by omega) (by rw [hts]; unfold MAX at hov; omega)

end Examples.Solmate.ERC20

end

section

/-! ## `burn` (anyone can burn anyone's tokens; the model's "loss" when `from` is the vault) -/

namespace Examples.Solmate.ERC20
open Examples.Solmate.ERC4626 QEDefi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open QEDefi.Math QEDefi.ERC20 Examples.Solmate.ERC4626.Shares

/-! ## The world -/

/-- The world after `burn`: `balanceOf[src] -= amount`, then `totalSupply -= amount`. -/
def burnWorld (crypto : Crypto) (w : World) (token src : Address) (amount : Word) : World :=
  let ss := ERC20.balanceSlot crypto ERC20.Layout.solmate src
  let w₁ := w.sstore token ss (w.sload token ss - amount)
  w₁.sstore token 2#256 (w₁.sload token 2#256 - amount)

theorem sload_burnWorld {crypto : Crypto} {w : World} {token src b : Address} {amount k : Word}
    (h : b ≠ token ∨ (k ≠ 2#256 ∧ k ≠ ERC20.balanceSlot crypto ERC20.Layout.solmate src)) :
    (burnWorld crypto w token src amount).sload b k = w.sload b k := by
  simp only [burnWorld]
  rw [sload_sstore_frame (by rcases h with h | h; exact .inl h; exact .inr h.1),
    sload_sstore_frame (by rcases h with h | h; exact .inl h; exact .inr h.2)]

theorem code_burnWorld (crypto : Crypto) (w : World) (token src : Address) (amount : Word)
    (b : Address) : (burnWorld crypto w token src amount).code b = w.code b := by
  simp [burnWorld]

/-- A successful asset `burn`: empty output, world `burnWorld`, ≤ 55000 gas. -/
def BurnOk (src : Address) (amount : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success .empty ∧
  mf.world = burnWorld m.ctx.crypto m.world m.frame.msg.currentTarget src amount ∧
  mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
  m.frame.gasLeft ≤ mf.frame.gasLeft + 55000

/-! ## Bytecode -/

set_option maxHeartbeats 0 in
/-- **The asset's `burn`, success**: when `src`'s balance covers `amount`. -/
theorem burn_halts_ok {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {src : Address}
    {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x9dc29fac (Word.ofAddress src) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    (hbal : amount.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate src)).toNat) :
    Halts m (BurnOk src amount m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [balanceSlot_solmate] at hbal
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  simp only [gt_sub_self_of_le hbal, iszero_zero]
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  pwp_codecopy
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  refine WP.halt_of_step (step_stop ?_) (by same_frame) ⟨rfl, ?_, rfl, rfl, ?_⟩
  · pcode_fact
  · simp only [burnWorld, balanceSlot_solmate]
  · evm_gas

set_option maxHeartbeats 0 in
/-- **The asset's `burn`, insufficient balance**, in any frame: `Panic(0x11)`. -/
theorem burn_halts_revert {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) {src : Address} {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x9dc29fac (Word.ofAddress src) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 10000 ≤ m.frame.gasLeft)
    (hbal : (m.world.sload m.frame.msg.currentTarget
      (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate src)).toNat < amount.toNat) :
    Halts m (Reverts 10000 m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [balanceSlot_solmate] at hbal
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  simp only [gt_sub_self_of_lt hbal, iszero_one]
  pwp_steps
  refine ⟨⟨_, rfl⟩, ?_⟩
  dsimp only [outputMachine]
  evm_gas

/-! ## Against the model -/

/-- Allowance entries represented after `burn` (as for `mint`). -/
abbrev BurnAllowances (crypto : Crypto) (src : Address) : Address → Address → Prop :=
  MintAllowances crypto src

theorem repOn_burnWorld {crypto : Crypto} {w : World} {token src : Address} {amount : Word}
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256])
    (hs : ERC20.BalanceSlotOk crypto ERC20.Layout.solmate src)
    {t t' : Token Address} (hr : Rep (ERC20.view crypto ERC20.Layout.solmate w token) t)
    (hw : t.WF) (ht : t.burn src amount.toNat = some t') :
    RepOn (BurnAllowances crypto src)
      (ERC20.view crypto ERC20.Layout.solmate (burnWorld crypto w token src amount) token) t' := by
  obtain ⟨hv, rfl⟩ := Token.burn_eq_some.1 ht
  have hs2 := balanceSlot_ne_two hk src
  have hts : (w.sload token 2#256).toNat = t.totalSupply := hr.totalSupply
  have hbal : (w.sload token (ERC20.balanceSlot crypto ERC20.Layout.solmate src)).toNat =
      t.balanceOf src := hr.balanceOf src
  have hle := Token.balanceOf_le_totalSupply hw src
  refine ⟨?_, fun a => ?_, fun o sp hp => ?_⟩
  · show ((burnWorld crypto w token src amount).sload token 2#256).toNat = _
    simp only [burnWorld]
    rw [World.sload_sstore_self, World.sload_sstore_ne_key _ _ _ (fun e => hs2 e.symm),
      BitVec.toNat_sub_of_le (BitVec.le_def.2 (by rw [hts]; omega)), hts]
  · show ((burnWorld crypto w token src amount).sload token
      (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat = _
    dsimp only
    rw [Token.sub_single_apply]
    by_cases ha : src = a
    · subst ha
      simp only [burnWorld, ↓reduceIte]
      rw [World.sload_sstore_ne_key _ _ _ hs2, World.sload_sstore_self,
        BitVec.toNat_sub_of_le (BitVec.le_def.2 (by rw [hbal]; exact hv)), hbal]
    · simp only [ha, ↓reduceIte]
      rw [sload_burnWorld (.inr ⟨balanceSlot_ne_two hk a,
        ERC20.balanceSlot_ne hs (Ne.symm ha)⟩)]
      exact hr.balanceOf a
  · show ((burnWorld crypto w token src amount).sload token
      (ERC20.allowanceSlot crypto ERC20.Layout.solmate o sp)).toNat = _
    rw [sload_burnWorld (.inr hp)]
    exact hr.allowance o sp trivial

/-- **The asset's `burn` refines `Token.burn`**, in any non-static frame. -/
theorem assetBurn_refines {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hstatic : m.frame.msg.isStatic = false) {src : Address} {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x9dc29fac (Word.ofAddress src) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    (hk : KeccakAvoids m.ctx.crypto (AddressKeyed [3#256]) [2#256])
    (hs : ERC20.BalanceSlotOk m.ctx.crypto ERC20.Layout.solmate src)
    {t : Token Address} (hr : Rep (assetView m) t) (hw : t.WF) :
    match t.burn src amount.toNat with
    | some t' => Halts m (fun mf o => BurnOk src amount m mf o ∧
        RepOn (BurnAllowances m.ctx.crypto src)
          (ERC20.view m.ctx.crypto ERC20.Layout.solmate mf.world m.frame.msg.currentTarget) t')
    | none => Halts m (Reverts 10000 m) := by
  have hbal : (m.world.sload m.frame.msg.currentTarget
      (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate src)).toNat = t.balanceOf src :=
    hr.balanceOf src
  split
  · rename_i t' hT
    have hv := (Token.burn_eq_some.1 hT).1
    have hrep := repOn_burnWorld hk hs hr hw hT
    refine (burn_halts_ok m hf hval hstatic hd hsz hg (by rw [hbal]; exact hv)).mono
      fun mf o _ hok => ⟨hok, ?_⟩
    rw [hok.2.1]
    exact hrep
  · rename_i hT
    have hlt : t.balanceOf src < amount.toNat := by
      unfold Token.burn at hT
      split at hT
      · assumption
      · cases hT
    exact burn_halts_revert m hf hval hd hsz (by omega) (by rw [hbal]; exact hlt)

end Examples.Solmate.ERC20

end
