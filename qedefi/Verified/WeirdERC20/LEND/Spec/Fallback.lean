import Verified.WeirdERC20.LEND.Spec.Views

/-!
# LEND under the spec: the sale state, unknown selectors and short calldata

LEND (solc 0.4.16) has a payable fallback, `function() payable { buyTokens(); }`, and
`buyTokens()` requires `currentState` to be `PresaleRunning` or `ICORunning`. In the final
state (the model's invariant) it reverts: empty calldata, a selector none of the dispatcher's
34, and calldata of one to three bytes (read zero-padded; its padded selector has a zero low
byte, `lend_not_sel`) all end in `REVERT`, as the model's `other` call says. The code reads
`currentState` as `slot3 / 256⁰ & 0xff` and checks it is a valid enum (`> 5` is `INVALID`):
in the final state it reads `5` (`phase_word`).
-/

namespace Verified.WeirdERC20.LEND.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.LEND.Contracts
open Verified.Solady.Spec (LowHalts halts_split RevertPost)
open Verified.Solady.Spec.AnyGas

/-- `currentState` as the code reads it is `ICOFinished` (`5`) in the final state. -/
theorem phase_of {x : Word} (h : x.toNat % 256 = 5) : 255#256 &&& Word.div x 1#256 = 5#256 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, Word.div, BitVec.toNat_udiv, BitVec.toNat_ofNat]
  rw [show (255 : Nat) % 2 ^ 256 = 2 ^ 8 - 1 by decide, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod]
  simpa using h

/-- With the frame's world in the final state, `currentState` reads `5`. -/
theorem phase_word {Act : Finset Address} {m : Machine} (hs : Start LEND.runtimeCode abs M Act m) :
    255#256 &&& Word.div (m.world.sload m.frame.msg.currentTarget 3#256) 1#256 = 5#256 :=
  phase_of (wf_slot3 hs).1

/-- The dispatcher's `EQ` tests all fail on an unknown selector. -/
theorem lend_unknown {data : ByteArray} (h : Abi.selectorOf data ∉ sel) :
    let s := BitVec.ofNat 256 (Abi.selectorOf data)
    Word.eq 0x737732b2#256 s = 0 ∧
    Word.eq 0x6cb5291e#256 s = 0 ∧
    Word.eq 0xf88607e4#256 s = 0 ∧
    Word.eq 0xe7cf7b34#256 s = 0 ∧
    Word.eq 0x1350acbd#256 s = 0 ∧
    Word.eq 0x62dc6e21#256 s = 0 ∧
    Word.eq 0xe92e5f03#256 s = 0 ∧
    Word.eq 0x0acdd69f#256 s = 0 ∧
    Word.eq 0x902d55a5#256 s = 0 ∧
    Word.eq 0xdd62ed3e#256 s = 0 ∧
    Word.eq 0x095ea7b3#256 s = 0 ∧
    Word.eq 0x70a08231#256 s = 0 ∧
    Word.eq 0xd0febe4c#256 s = 0 ∧
    Word.eq 0xd7b91bcc#256 s = 0 ∧
    Word.eq 0x1d511879#256 s = 0 ∧
    Word.eq 0x0c3f6acf#256 s = 0 ∧
    Word.eq 0x313ce567#256 s = 0 ∧
    Word.eq 0xaf35c6c7#256 s = 0 ∧
    Word.eq 0xe2fdcc17#256 s = 0 ∧
    Word.eq 0x98d5fdca#256 s = 0 ∧
    Word.eq 0x43d42780#256 s = 0 ∧
    Word.eq 0x06fdde03#256 s = 0 ∧
    Word.eq 0x269f96c9#256 s = 0 ∧
    Word.eq 0x56de96db#256 s = 0 ∧
    Word.eq 0x7cb2b79c#256 s = 0 ∧
    Word.eq 0x047fc9aa#256 s = 0 ∧
    Word.eq 0x95d89b41#256 s = 0 ∧
    Word.eq 0x085c1cee#256 s = 0 ∧
    Word.eq 0x2a709b14#256 s = 0 ∧
    Word.eq 0xd7ca9949#256 s = 0 ∧
    Word.eq 0x18160ddd#256 s = 0 ∧
    Word.eq 0xa9059cbb#256 s = 0 ∧
    Word.eq 0x23b872dd#256 s = 0 ∧
    Word.eq 0x7362377b#256 s = 0 := by
  have hs := Verified.Solady.Spec.selectorOf_lt data
  simp only [sel, LEND.selectors, List.map, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, and_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34⟩ := h
  exact ⟨Verified.Solady.Spec.eq_sel_ne (k := 0x737732b2) hs (by decide) (by simpa using h1),
    Verified.Solady.Spec.eq_sel_ne (k := 0x6cb5291e) hs (by decide) (by simpa using h2),
    Verified.Solady.Spec.eq_sel_ne (k := 0xf88607e4) hs (by decide) (by simpa using h3),
    Verified.Solady.Spec.eq_sel_ne (k := 0xe7cf7b34) hs (by decide) (by simpa using h4),
    Verified.Solady.Spec.eq_sel_ne (k := 0x1350acbd) hs (by decide) (by simpa using h5),
    Verified.Solady.Spec.eq_sel_ne (k := 0x62dc6e21) hs (by decide) (by simpa using h6),
    Verified.Solady.Spec.eq_sel_ne (k := 0xe92e5f03) hs (by decide) (by simpa using h7),
    Verified.Solady.Spec.eq_sel_ne (k := 0x0acdd69f) hs (by decide) (by simpa using h8),
    Verified.Solady.Spec.eq_sel_ne (k := 0x902d55a5) hs (by decide) (by simpa using h9),
    Verified.Solady.Spec.eq_sel_ne (k := 0xdd62ed3e) hs (by decide) (by simpa using h10),
    Verified.Solady.Spec.eq_sel_ne (k := 0x095ea7b3) hs (by decide) (by simpa using h11),
    Verified.Solady.Spec.eq_sel_ne (k := 0x70a08231) hs (by decide) (by simpa using h12),
    Verified.Solady.Spec.eq_sel_ne (k := 0xd0febe4c) hs (by decide) (by simpa using h13),
    Verified.Solady.Spec.eq_sel_ne (k := 0xd7b91bcc) hs (by decide) (by simpa using h14),
    Verified.Solady.Spec.eq_sel_ne (k := 0x1d511879) hs (by decide) (by simpa using h15),
    Verified.Solady.Spec.eq_sel_ne (k := 0x0c3f6acf) hs (by decide) (by simpa using h16),
    Verified.Solady.Spec.eq_sel_ne (k := 0x313ce567) hs (by decide) (by simpa using h17),
    Verified.Solady.Spec.eq_sel_ne (k := 0xaf35c6c7) hs (by decide) (by simpa using h18),
    Verified.Solady.Spec.eq_sel_ne (k := 0xe2fdcc17) hs (by decide) (by simpa using h19),
    Verified.Solady.Spec.eq_sel_ne (k := 0x98d5fdca) hs (by decide) (by simpa using h20),
    Verified.Solady.Spec.eq_sel_ne (k := 0x43d42780) hs (by decide) (by simpa using h21),
    Verified.Solady.Spec.eq_sel_ne (k := 0x06fdde03) hs (by decide) (by simpa using h22),
    Verified.Solady.Spec.eq_sel_ne (k := 0x269f96c9) hs (by decide) (by simpa using h23),
    Verified.Solady.Spec.eq_sel_ne (k := 0x56de96db) hs (by decide) (by simpa using h24),
    Verified.Solady.Spec.eq_sel_ne (k := 0x7cb2b79c) hs (by decide) (by simpa using h25),
    Verified.Solady.Spec.eq_sel_ne (k := 0x047fc9aa) hs (by decide) (by simpa using h26),
    Verified.Solady.Spec.eq_sel_ne (k := 0x95d89b41) hs (by decide) (by simpa using h27),
    Verified.Solady.Spec.eq_sel_ne (k := 0x085c1cee) hs (by decide) (by simpa using h28),
    Verified.Solady.Spec.eq_sel_ne (k := 0x2a709b14) hs (by decide) (by simpa using h29),
    Verified.Solady.Spec.eq_sel_ne (k := 0xd7ca9949) hs (by decide) (by simpa using h30),
    Verified.Solady.Spec.eq_sel_ne (k := 0x18160ddd) hs (by decide) (by simpa using h31),
    Verified.Solady.Spec.eq_sel_ne (k := 0xa9059cbb) hs (by decide) (by simpa using h32),
    Verified.Solady.Spec.eq_sel_ne (k := 0x23b872dd) hs (by decide) (by simpa using h33),
    Verified.Solady.Spec.eq_sel_ne (k := 0x7362377b) hs (by decide) (by simpa using h34)⟩

/-- Short calldata reads as a selector none of LEND's (every one has a nonzero low byte). -/
theorem lend_not_sel {data : ByteArray}
    (hd : data.size < 4 ∨ Abi.selectorOf data ∉ sel) : Abi.selectorOf data ∉ sel := by
  rcases hd with h | h
  · have h0 := BNB.Spec.selectorOf_short h
    intro hm
    simp only [sel, LEND.selectors, List.map, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp at h <;> omega
  · exact h

set_option maxHeartbeats 0 in
theorem fallback_low (m : Machine) (hf : Fresh LEND.runtimeCode m)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hd : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ sel)
    (hph : 255#256 &&& Word.div (m.world.sload m.frame.msg.currentTarget 3#256) 1#256 = 5#256) :
    LowHalts m RevertPost := by
  intro H hF _
  apply WP.halts_of_false
  by_cases h0 : m.frame.msg.data.size = 0
  · have hz : Word.iszero (ofNat m.frame.msg.data.size) = 1 := by rw [h0]; decide
    solady_fresh_intro
    hwp_steps [hz, hph]
  · obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31, e32, e33, e34⟩ := lend_unknown (lend_not_sel hd)
    have hsel' := BNB.Spec.div_selector m.frame.msg.data
    have hz := BNB.Spec.calldatasize_pos (n := m.frame.msg.data.size) (by omega) hsz
    solady_fresh_intro
    hwp_steps [hz, hsel', hph, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31, e32, e33, e34]

set_option maxHeartbeats 0 in
theorem fallback_high (m : Machine) (hf : Fresh LEND.runtimeCode m)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hd : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ sel)
    (hph : 255#256 &&& Word.div (m.world.sload m.frame.msg.currentTarget 3#256) 1#256 = 5#256)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m RevertPost := by
  simp only [g₀] at hg
  apply WP.halts_of_false
  by_cases h0 : m.frame.msg.data.size = 0
  · have hz : Word.iszero (ofNat m.frame.msg.data.size) = 1 := by rw [h0]; decide
    solady_fresh_intro
    pwp_steps [hz, hph]
    exact ⟨_, rfl⟩
  · obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31, e32, e33, e34⟩ := lend_unknown (lend_not_sel hd)
    have hsel' := BNB.Spec.div_selector m.frame.msg.data
    have hz := BNB.Spec.calldatasize_pos (n := m.frame.msg.data.size) (by omega) hsz
    solady_fresh_intro
    pwp_steps [hz, hsel', hph, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31, e32, e33, e34]
    exact ⟨_, rfl⟩

theorem lend_call_other (s : LEND.State Address) (c : Address) (v : ℕ) (hw : M.wf s) :
    M.call s c (.other v) = .halt .revert := by
  obtain ⟨hp, -⟩ := hw
  simp [M, QEDefi.ERC20.Spec.LEND.model, QEDefi.ERC20.Spec.LEND.call,
    QEDefi.ERC20.Spec.LEND.step, QEDefi.ERC20.Spec.LEND.buy, hp]

/-- **Empty calldata and unknown selectors** revert in the final sale state, as the model's
`other` call. -/
theorem fallback_spec : FallbackSpec LEND.runtimeCode abs M g₀ sel := by
  intro Act m hs hd
  refine halts_split (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => fallback_high m hs.fresh hs.size hd (phase_word hs) hG.1)
    (fallback_low m hs.fresh hs.size hd (phase_word hs)) ?_
  rintro mf o ⟨out, rfl⟩
  rw [lend_call_other _ _ _ hs.wf]
  exact ⟨out, rfl⟩

end Verified.WeirdERC20.LEND.Spec
