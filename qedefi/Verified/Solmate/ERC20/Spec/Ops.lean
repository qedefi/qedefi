import Verified.Solmate.ERC20.Spec.Normal

/-!
# Solmate's `MockERC20`: `mint` and `burn` as operations

`solmateOps` decodes the two entry points of `MockERC20` outside the ERC-20 interface:
`mint(to, amount)` and `burn(from, amount)`, open to every caller, from well-formed calldata
(selector, two argument words, a clean address) without value; `solmateOpAddrs` names the
account each one touches. `mint_normal`/`burn_normal`: in a frame with enough gas, not static,
they end as `Variant.standard.stepOp` says.
-/

namespace Verified.Solmate.ERC20.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.Solmate QEDefi.Math Finsupp
open Verified.Solmate.Contracts Verified.Solmate.ERC20 Verified.Solmate.ERC4626 QEDefi.ERC4626

/-- The address in a clean argument word. -/
theorem ofAddress_toAddress_clean {d : ByteArray} {j : Nat} (h : CleanAddr d j) :
    Word.ofAddress (Word.toAddress (argWord d j)) = argWord d j := by
  have h' := congrArg BitVec.toNat h
  simp only [addressMask, BitVec.toNat_and, BitVec.toNat_ofNat] at h'
  rw [Nat.mod_eq_of_lt (by decide : 2 ^ 160 - 1 < 2 ^ 256), Nat.and_two_pow_sub_one_eq_mod] at h'
  apply BitVec.eq_of_toNat_eq
  simp only [Word.ofAddress, Word.toAddress, BitVec.toNat_setWidth]
  rw [h', Nat.mod_eq_of_lt (argWord d j).isLt]

/-- Well-formed calldata of a function `(address, uint256)` with selector `sel`. -/
def AddrAmount (d : ByteArray) (sel : Nat) : Prop :=
  Abi.selectorOf d = sel ∧ 68 ≤ d.size ∧ CleanAddr d 0

instance (d : ByteArray) (sel : Nat) : Decidable (AddrAmount d sel) := by
  unfold AddrAmount CleanAddr; infer_instance

/-- **The decoder of `mint` and `burn`** (calldata without value). -/
noncomputable def solmateOps (caller : Address) (d : ByteArray) (value : ℕ) :
    Option (Variant.Op Address) :=
  if value ≠ 0 then none
  else if AddrAmount d 0x40c10f19 then
    some (.mint caller (Word.toAddress (argWord d 0)) (argWord d 1).toNat)
  else if AddrAmount d 0x9dc29fac then
    some (.burn caller (Word.toAddress (argWord d 0)) (argWord d 1).toNat)
  else none

/-- The accounts an operation names: the receiver of `mint`, the holder of `burn`. -/
def solmateOpAddrs : Variant.Op Address → List Address
  | .mint _ d _ => [d]
  | .burn _ s _ => [s]
  | _ => []

theorem solmateOps_some {caller : Address} {d : ByteArray} {value : ℕ}
    {e : Variant.Op Address} (h : solmateOps caller d value = some e) :
    value = 0 ∧
      ((AddrAmount d 0x40c10f19 ∧
          e = .mint caller (Word.toAddress (argWord d 0)) (argWord d 1).toNat) ∨
        (AddrAmount d 0x9dc29fac ∧
          e = .burn caller (Word.toAddress (argWord d 0)) (argWord d 1).toNat)) := by
  unfold solmateOps at h
  split_ifs at h with h0 h1 h2
  · cases h; exact ⟨by omega, .inl ⟨h1, rfl⟩⟩
  · cases h; exact ⟨by omega, .inr ⟨h2, rfl⟩⟩

theorem twoWordCall_of_addrAmount {d : ByteArray} {sel : Nat} (h : AddrAmount d sel) :
    TwoWordCall d sel (Word.ofAddress (Word.toAddress (argWord d 0)))
      (word (argWord d 1).toNat) := by
  obtain ⟨hs, hz, hc⟩ := h
  refine ⟨hs, hz, ?_, ?_⟩
  · rw [ofAddress_toAddress_clean hc]; rfl
  · simp [word, argWord]

variable {ia : SolmateAsset.Immutables} {Act : Finset Address} {m : Machine}

/-! ## The worlds read back -/

theorem read_mintWorld {crypto : Crypto} {w : World} {token d : Address} {v : ℕ}
    (hS : SolmateSound crypto Act) (hd : d ∈ Act) (hv : v < 2 ^ 256)
    (hov : (solmateRead crypto Act w token).supply + v ≤ MAX)
    (hb : (solmateRead crypto Act w token).bal d ≤ (solmateRead crypto Act w token).supply) :
    solmateRead crypto Act (mintWorld crypto w token d (word v)) token =
      { solmateRead crypto Act w token with
        supply := (solmateRead crypto Act w token).supply + v,
        bal := (solmateRead crypto Act w token).bal + single d v } ∧
    FrameKeeps solmateAbs crypto Act token w (mintWorld crypto w token d (word v)) := by
  have hbd : (w.sload token (mappingSlot crypto (Word.ofAddress d) 3#256)).toNat =
      (solmateRead crypto Act w token).bal d := (readMap_of_mem hd w token 3#256).symm
  have hsup : (w.sload token 2#256).toNat = (solmateRead crypto Act w token).supply := rfl
  have hne : mappingSlot crypto (Word.ofAddress d) 3#256 ≠ 2#256 :=
    fun e => hS.fixed1 3#256 (by simp) d hd (by simp [e])
  unfold MAX at hov
  refine ⟨?_, ?_⟩
  · simp only [mintWorld, ERC20.balanceSlot, layout_balances]
    rw [read_sstore_bal hS hd, read_sstore_supply hS]
    simp only [VState.mk.injEq, true_and, and_true]
    refine ⟨?_, ?_⟩
    · ext a
      simp only [update_apply, coe_add, Pi.add_apply, single_apply]
      by_cases had : d = a
      · subst had
        simp only [↓reduceIte, sload_sstore_token, hne]
        rw [BitVec.toNat_add, toNat_word hv, hbd, Nat.mod_eq_of_lt (by omega)]
        omega
      · simp [had, Ne.symm had]
    · rw [BitVec.toNat_add, toNat_word hv, hsup, Nat.mod_eq_of_lt (by omega)]
      omega
  · simp only [mintWorld, ERC20.balanceSlot, layout_balances]
    exact frameKeeps_sstore (frameKeeps_sstore (frameKeeps_refl _ _ _ _) footprint_supply)
      (footprint_bal hd)

theorem read_burnWorld {crypto : Crypto} {w : World} {token src : Address} {v : ℕ}
    (hS : SolmateSound crypto Act) (hs : src ∈ Act) (hv : v < 2 ^ 256)
    (hle : v ≤ (solmateRead crypto Act w token).bal src)
    (hb : (solmateRead crypto Act w token).bal src ≤ (solmateRead crypto Act w token).supply) :
    solmateRead crypto Act (burnWorld crypto w token src (word v)) token =
      { solmateRead crypto Act w token with
        supply := (solmateRead crypto Act w token).supply - v,
        bal := (solmateRead crypto Act w token).bal - single src v } ∧
    FrameKeeps solmateAbs crypto Act token w (burnWorld crypto w token src (word v)) := by
  have hbs : (w.sload token (mappingSlot crypto (Word.ofAddress src) 3#256)).toNat =
      (solmateRead crypto Act w token).bal src := (readMap_of_mem hs w token 3#256).symm
  have hsup : (w.sload token 2#256).toNat = (solmateRead crypto Act w token).supply := rfl
  have hne : mappingSlot crypto (Word.ofAddress src) 3#256 ≠ 2#256 :=
    fun e => hS.fixed1 3#256 (by simp) src hs (by simp [e])
  refine ⟨?_, ?_⟩
  · simp only [burnWorld, ERC20.balanceSlot, layout_balances]
    rw [read_sstore_supply hS, read_sstore_bal hS hs]
    simp only [VState.mk.injEq, true_and, and_true]
    refine ⟨?_, ?_⟩
    · ext a
      simp only [update_apply, coe_tsub, Pi.sub_apply, single_apply]
      by_cases had : src = a
      · subst had
        simp only [↓reduceIte]
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_word hv, hbs]; omega),
          toNat_word hv, hbs]
      · simp [had, Ne.symm had]
    · rw [sload_sstore_token, if_neg' (Ne.symm hne),
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_word hv, hsup]; omega),
        toNat_word hv, hsup]
  · simp only [burnWorld, ERC20.balanceSlot, layout_balances]
    exact frameKeeps_sstore (frameKeeps_sstore (frameKeeps_refl _ _ _ _) (footprint_bal hs))
      footprint_supply

theorem bal_le_supply (hS : Start (code ia) solmateAbs M Act m) (a : Address) :
    (pre solmateAbs Act m).bal a ≤ (pre solmateAbs Act m).supply := by
  obtain ⟨h1, -⟩ := wf_total hS
  rw [← h1]; exact Token.le_total _ a

/-! ## The operations in normal frames -/

set_option maxHeartbeats 1000000 in
/-- **`mint(dst, v)` in a normal frame** ends as `stepOp` says. -/
theorem mint_normal (hS : Start (code ia) solmateAbs M Act m) {dst : Address} {v : Word}
    (hd : TwoWordCall m.frame.msg.data 0x40c10f19 (Word.ofAddress dst) v) (hdst : dst ∈ Act)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : 60000 ≤ m.frame.gasLeft) :
    Halts m (OpMatches solmateAbs M Act (.mint m.frame.msg.caller dst v.toNat) m) := by
  have hpre := pre_eq hS hval
  have hb := bal_le_supply hS dst
  have hv : v = word v.toNat := by simp [word]
  have hvl := v.isLt
  unfold OpMatches
  simp only [M, solmateModel_op, stepOp_mint]
  split_ifs with hov
  · refine (mint_halts_revert m hS.fresh hval hd hS.size (by omega) ?_).mono
      fun mf o _ h => ?_
    · rw [← supply_read (Act := Act), ← hpre]; unfold MAX at hov; omega
    · obtain ⟨⟨out, rfl⟩, -⟩ := h; trivial
  · refine (mint_halts_ok m hS.fresh hval hst hd hS.size hg ?_).mono fun mf o _ hok => ?_
    · rw [← supply_read (Act := Act), ← hpre]; unfold MAX at hov; omega
    rw [hpre] at hov hb
    have hrw := read_mintWorld (crypto := m.ctx.crypto) (w := m.world)
      (token := m.frame.msg.currentTarget) hS.sound hdst hvl (by omega) hb
    rw [← hv] at hrw
    refine ⟨⟨_, hok.1⟩, ?_, ?_, hok.2.2.1, hok.2.2.2.1⟩
    · show solmateRead _ _ _ _ = _
      rw [hok.2.1, hrw.1, hpre]
    · rw [hok.2.1]; exact hrw.2

set_option maxHeartbeats 1000000 in
/-- **`burn(src, v)` in a normal frame** ends as `stepOp` says. -/
theorem burn_normal (hS : Start (code ia) solmateAbs M Act m) {src : Address} {v : Word}
    (hd : TwoWordCall m.frame.msg.data 0x9dc29fac (Word.ofAddress src) v) (hsrc : src ∈ Act)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : 60000 ≤ m.frame.gasLeft) :
    Halts m (OpMatches solmateAbs M Act (.burn m.frame.msg.caller src v.toNat) m) := by
  have hpre := pre_eq hS hval
  have hb := bal_le_supply hS src
  have hv : v = word v.toNat := by simp [word]
  have hvl := v.isLt
  have hbs : (pre solmateAbs Act m).bal src =
      (m.world.sload m.frame.msg.currentTarget
        (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate src)).toNat := by
    rw [hpre]; exact bal_read hsrc
  unfold OpMatches
  simp only [M, solmateModel_op, stepOp_burn]
  split_ifs with hlt
  · refine (burn_halts_revert m hS.fresh hval hd hS.size (by omega) (by omega)).mono
      fun mf o _ h => ?_
    obtain ⟨⟨out, rfl⟩, -⟩ := h; trivial
  · refine (burn_halts_ok m hS.fresh hval hst hd hS.size hg (by omega)).mono
      fun mf o _ hok => ?_
    rw [hpre] at hlt hb
    have hrw := read_burnWorld (crypto := m.ctx.crypto) (w := m.world)
      (token := m.frame.msg.currentTarget) hS.sound hsrc hvl (by omega) hb
    rw [← hv] at hrw
    refine ⟨⟨_, hok.1⟩, ?_, ?_, hok.2.2.1, hok.2.2.2.1⟩
    · show solmateRead _ _ _ _ = _
      rw [hok.2.1, hrw.1, hpre]
    · rw [hok.2.1]; exact hrw.2

end Verified.Solmate.ERC20.Spec
