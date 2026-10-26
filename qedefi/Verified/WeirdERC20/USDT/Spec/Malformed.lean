import Verified.WeirdERC20.USDT.Spec.Spec
import Verified.WeirdERC20.USDT.Spec.MalformedRuns
import Verified.WeirdERC20.Common.Post
import EvmLogic.Tx.Exec

/-!
# USDT with any calldata: `MalformedSpec` except `transferOwnership` and `deprecate`

**`usdt_malformed`**: in every frame of the mainnet USDT code (solc 0.4.18) that `Start` admits
(a live token: not deprecated, `usdtAbs`), with any calldata naming only actors, any value and
any gas, except `transferOwnership` and `deprecate` (`usdtExcl`: the owner and the deprecation
are not part of `usdtModel`), the frame fails, changes nothing, or ends as an ERC-20 call or an
operation of `usdtModel`. By selector:

* calldata shorter than a selector or an unknown selector: `usdt_fallback` (it reverts);
* the sixteen getters, and `totalSupply`, `balanceOf`, `allowance` past their deprecation
  branch (the token is not deprecated), change nothing (a read-only region);
* the eight operations (`pause`, `unpause`, `addBlackList`, `removeBlackList`,
  `destroyBlackFunds`, `setParams`, `issue`, `redeem`): with value they revert; otherwise `ops`
  decodes the calldata itself (zero-padded words, masked addresses) and `usdt_ops` applies;
* `transfer`, `approve`, `transferFrom`: with value, paused, a blacklisted payer or too few
  argument words (`onlyPayloadSize`) they revert; otherwise, past the last calldata read, the
  frame runs as the frame whose calldata is the ABI encoding of the decoded words
  (`Verified.WeirdERC20.Common.transport`), and `usdt_calls` applies to that call.

**`usdt_complete`**: `ERC20Spec.Complete` (USDT has no `permit`) with `excl = usdtExcl`.
-/

set_option linter.unusedSimpArgs false

namespace Verified.WeirdERC20.USDT.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.USDT.Contracts
open Verified.WeirdERC20.USDT.Spec Verified.WeirdERC20.Common
open Verified.Common.Malformed (Unchanged halts_pure inCert_top)
open EvmLogic.AbsInt

/-- The entry points `usdtModel` does not describe: `transferOwnership(address)` and
`deprecate(address)`. -/
def usdtExcl : List Nat := [0xf2fde38b, 0x0753c30c]

section
variable {Act : Finset Address} {m : Machine}

/-- `MalformedSpec`'s frame-end condition for USDT. -/
abbrev Post (Act : Finset Address) (m : Machine) : Machine → Outcome → Prop :=
  LPost usdtAbs M ops opAddrs none Act m

/-- **A frame `Start` admits runs a token that is not deprecated** (in its own world: the value
moved, the storage did not). -/
theorem dep_of_start (hS : Start USDT.runtimeCode usdtAbs M Act m) :
    byte20 m.world m.frame.msg.currentTarget 10#256 = 0 := by
  have hl := (live_of_start hS).1.1
  rw [deprecatedField_get] at hl
  have hcode : (m.frame.snapshot.1.code m.frame.msg.currentTarget).size ≠ 0 := by
    have h := hS.hasCode
    rwa [hS.launched, EvmLogic.Tx.code_transferValue] at h
  have hk := EvmLogic.Program.Nested.keep_transferValue (msg := m.frame.msg) hcode
  rw [← hS.launched] at hk
  show 255#256 &&& (m.world.sload _ 10#256).div _ = 0
  rw [hk.sload]
  exact hl

/-- An argument word, as an address, names an actor (it is a word of the calldata, or past it
and `0`). -/
theorem arg_mem (hAct : calldataAddrs m.frame.msg.data ⊆ Act) (i : Nat) :
    Word.toAddress (aw m.frame.msg.data i) ∈ Act := by
  by_cases h : 4 + 32 * i < m.frame.msg.data.size
  · exact hAct (mem_calldataAddrs h)
  · have : aw m.frame.msg.data i = 0 := by
      simp only [aw, readBytes, show m.frame.msg.data.size ≤ 4 + 32 * i by omega, ↓reduceIte]
      decide
    rw [this]
    exact hAct (Finset.mem_insert_self _ _)

theorem post_getter (hS : Start USDT.runtimeCode usdtAbs M Act m) {sel q : Nat}
    (hge : (sel, q) ∈ getterEntries) (hsel : Abi.selectorOf m.frame.msg.data = sel)
    (h4 : 4 ≤ m.frame.msg.data.size) : Halts m (Post Act m) := by
  have hin : InT usdtGetters q [.top] :=
    usdtGetters_seed (List.mem_append_left _ (List.mem_map.2 ⟨(sel, q), hge, rfl⟩))
  refine lpost_unchanged ?_
  rcases getter_dispatch hge m hS.fresh hsel h4 hS.size with
    ⟨s, hst, hpc, hs, hcode, h1, h2, h3⟩ | h
  · refine Halts.of_steps hst ((halts_pure usdtGetters_cert usdtGetters_pure s hcode
      (inCert_top hin hpc hs)).mono fun mf _ _ ⟨g1, g2, g3⟩ => .inr ?_)
    exact ⟨g1.trans h1, g2.trans h2, g3.trans h3⟩
  · exact h.mono fun _ _ _ h => .inl h

theorem post_view
    (hrun : WP m (AtView m) (fun _ o => Fails o)) : Halts m (Post Act m) := by
  refine lpost_unchanged ?_
  rcases hrun with ⟨s, hst, hin, hcode, h1, h2, h3⟩ | h
  · refine Halts.of_steps hst ((halts_pure usdtGetters_cert usdtGetters_pure s hcode
      hin).mono fun mf _ _ ⟨g1, g2, g3⟩ => .inr ?_)
    exact ⟨g1.trans h1, g2.trans h2, g3.trans h3⟩
  · exact h.mono fun _ _ _ h => .inl h

theorem value_toNat (h : m.frame.msg.value = 0) : m.frame.msg.value.toNat = 0 := by
  rw [h]; rfl

theorem post_op (hS : Start USDT.runtimeCode usdtAbs M Act m) {sel q : Nat}
    (hge : (sel, q) ∈ opEntries) (hsel : Abi.selectorOf m.frame.msg.data = sel)
    (h4 : 4 ≤ m.frame.msg.data.size) {e : Variant.Op Address}
    (hops : ops m.frame.msg.caller m.frame.msg.data 0 = some e)
    (hA : ∀ a ∈ opAddrs e, a ∈ Act) : Halts m (Post Act m) := by
  rcases op_value hge m hS.fresh hsel h4 hS.size with ⟨-, -, hv⟩ | h
  · exact lpost_op usdt_ops hS (by rw [value_toNat hv]; exact hops) hA
  · exact lpost_fails h

/-! ## The clean calls -/

/-- The clean calldata of a body taking an `address` and a word. -/
def clean2 (sel : Nat) (d : ByteArray) : ByteArray := Abi.encodeCall sel [aa d 0, aw d 1]

/-- The clean calldata of `transferFrom`. -/
def clean3 (d : ByteArray) : ByteArray := Abi.encodeCall 0x23b872dd [aa d 0, aa d 1, aw d 2]

theorem aw_clean2_0 (sel : Nat) (d : ByteArray) : aw (clean2 sel d) 0 = aa d 0 :=
  Abi.calldataload_encodeCall_0 _ _ _

theorem aw_clean2_1 (sel : Nat) (d : ByteArray) : aw (clean2 sel d) 1 = aw d 1 :=
  Abi.calldataload_encodeCall_1 _ _ _ _

theorem aw_clean3_0 (d : ByteArray) : aw (clean3 d) 0 = aa d 0 :=
  Abi.calldataload_encodeCall_0 _ _ _

theorem aw_clean3_1 (d : ByteArray) : aw (clean3 d) 1 = aa d 1 :=
  Abi.calldataload_encodeCall_1 _ _ _ _

theorem aw_clean3_2 (d : ByteArray) : aw (clean3 d) 2 = aw d 2 :=
  Abi.calldataload_encodeCall_2 _ _ _ _ _

theorem aa_aa (d : ByteArray) (i : Nat) : Word.ofAddress (Word.toAddress (aa d i)) = aa d i := by
  simp [aa, Word.toAddress_ofAddress]

/-- `Args` of an ABI encoding. -/
theorem args_encodeCall {sel : Nat} (hsel : sel < 2 ^ 32) (ws : List Word) :
    Args (Abi.encodeCall sel ws) sel ws :=
  ⟨by rw [Abi.selectorOf_encodeCall, Nat.mod_eq_of_lt hsel], by rw [Abi.size_encodeCall],
    fun i h => Abi.calldataload_encodeCall sel ws i h⟩

theorem word_toNat_self (w : Word) : word w.toNat = w := by
  simp [word]

theorem encodes_transfer (d : ByteArray) :
    (Call.transfer (Word.toAddress (aw d 0)) (aw d 1).toNat).Encodes (clean2 0xa9059cbb d) :=
  ⟨(aw d 1).isLt, by rw [word_toNat_self]; exact args_encodeCall (by norm_num) _⟩

theorem encodes_approve (d : ByteArray) :
    (Call.approve (Word.toAddress (aw d 0)) (aw d 1).toNat).Encodes (clean2 0x095ea7b3 d) :=
  ⟨(aw d 1).isLt, by rw [word_toNat_self]; exact args_encodeCall (by norm_num) _⟩

theorem encodes_transferFrom (d : ByteArray) :
    (Call.transferFrom (Word.toAddress (aw d 0)) (Word.toAddress (aw d 1))
      (aw d 2).toNat).Encodes (clean3 d) :=
  ⟨(aw d 2).isLt, by rw [word_toNat_self]; exact args_encodeCall (by norm_num) _⟩

theorem clean_gas {D' : ByteArray} :
    (clean D' (m.frame.gasLeft + 10000) m).frame.gasLeft = m.frame.gasLeft + 10000 := by
  simp only [clean, setData, Verified.OpenZeppelin.ERC20.Spec.high,
    Verified.OpenZeppelin.ERC20.Spec.hi, Verified.OpenZeppelin.ERC20.Spec.setKind,
    EvmLogic.Program.Nested.bump]
  omega

theorem aa_clean3_0 (d : ByteArray) : aa (clean3 d) 0 = aa d 0 := by
  simp only [aa, aw_clean3_0, Word.toAddress_ofAddress]

theorem stT_clean (d : ByteArray) : stT (clean2 0xa9059cbb d) = stT d := by
  simp only [stT, aa, aw_clean2_0, aw_clean2_1, Word.toAddress_ofAddress]

theorem stA_clean (d : ByteArray) : stA (clean2 0x095ea7b3 d) = stA d := by
  simp only [stA, aa, aw_clean2_0, aw_clean2_1, Word.toAddress_ofAddress]

theorem stF_clean (d : ByteArray) : stF (clean3 d) = stF d := by
  simp only [stF, aa, aw_clean3_0, aw_clean3_1, aw_clean3_2, Word.toAddress_ofAddress]

/-! ## Dirty calls -/

set_option maxHeartbeats 1000000 in
theorem post_transfer (hS : Start USDT.runtimeCode usdtAbs M Act m)
    (hAct : calldataAddrs m.frame.msg.data ⊆ Act)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xa9059cbb) (h4 : 4 ≤ m.frame.msg.data.size) :
    Halts m (Post Act m) := by
  have hf := hS.fresh
  have hdep := dep_of_start hS
  rcases transfer_dirty m hf hsel h4 hS.size hdep with
    ⟨s, hst, hsE, hg, hv, hsize, hp, hb⟩ | hF
  · rw [hsE] at hst
    have hD : (clean2 0xa9059cbb m.frame.msg.data).size = 68 := by
      simp [clean2, Abi.size_encodeCall]
    refine lpost_call_dirty (usdt_calls _) hS (dirtyRunS_of (K := 10000) usdtBodies_cert usdtBodies_safe hf
      (by rw [hD]; norm_num) hst hg ?_ ⟨[.top, .top, .top, .top, .top, .const 5785, .top, .top, .const 1930, .top], usdtBodies_seed (q := 0x26b6) (by simp [bodySeeds]),
        by simp [entryS, stT, StackOk, AVal.Holds]⟩) (encodes_transfer _) trivial ?_
    · refine (transfer_clean (clean (clean2 0xa9059cbb m.frame.msg.data) (m.frame.gasLeft + 10000) m)
        (fresh_clean hf (G := m.frame.gasLeft + 10000) (by omega) (clean2 0xa9059cbb m.frame.msg.data))
        (by simp [clean, setData, clean2, Abi.selectorOf_encodeCall]) (by simp [clean, setData, hD])
        (by simp [clean, setData, hD]) hv (by rw [clean_gas]; omega) hdep hp hb).mono_left ?_
      rintro s' ⟨h1, h2⟩
      refine ⟨h1.trans ?_, by rw [clean_gas] at h2; omega⟩
      rw [show (clean (clean2 0xa9059cbb m.frame.msg.data) (m.frame.gasLeft + 10000) m).frame.msg.data = clean2 0xa9059cbb m.frame.msg.data from rfl,
        stT_clean]
      rfl
    · intro a ha
      simp only [Call.addrs, List.mem_singleton] at ha
      exact ha ▸ arg_mem hAct 0
  · exact lpost_fails hF

set_option maxHeartbeats 1000000 in
theorem post_approve (hS : Start USDT.runtimeCode usdtAbs M Act m)
    (hAct : calldataAddrs m.frame.msg.data ⊆ Act)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x095ea7b3) (h4 : 4 ≤ m.frame.msg.data.size) :
    Halts m (Post Act m) := by
  have hf := hS.fresh
  have hdep := dep_of_start hS
  rcases approve_dirty m hf hsel h4 hS.size hdep with ⟨s, hst, hsE, hg, hv, hsize⟩ | hF
  · rw [hsE] at hst
    have hD : (clean2 0x095ea7b3 m.frame.msg.data).size = 68 := by
      simp [clean2, Abi.size_encodeCall]
    refine lpost_call_dirty (usdt_calls _) hS (dirtyRunS_of (K := 10000) usdtBodies_cert usdtBodies_safe hf
      (by rw [hD]; norm_num) hst hg ?_ ⟨[.top, .top, .top, .const 3259, .top, .top, .top, .const 674, .top], usdtBodies_seed (q := 0x2026) (by simp [bodySeeds]),
        by simp [entryS, stA, StackOk, AVal.Holds]⟩)
      (encodes_approve _) trivial ?_
    · refine (approve_clean (clean (clean2 0x095ea7b3 m.frame.msg.data) (m.frame.gasLeft + 10000) m)
        (fresh_clean hf (G := m.frame.gasLeft + 10000) (by omega) (clean2 0x095ea7b3 m.frame.msg.data))
        (by simp [clean, setData, clean2, Abi.selectorOf_encodeCall]) (by simp [clean, setData, hD])
        (by simp [clean, setData, hD]) hv (by rw [clean_gas]; omega) hdep).mono_left ?_
      rintro s' ⟨h1, h2⟩
      refine ⟨h1.trans ?_, by rw [clean_gas] at h2; omega⟩
      rw [show (clean (clean2 0x095ea7b3 m.frame.msg.data) (m.frame.gasLeft + 10000) m).frame.msg.data = clean2 0x095ea7b3 m.frame.msg.data from rfl,
        stA_clean]
      rfl
    · intro a ha
      simp only [Call.addrs, List.mem_singleton] at ha
      exact ha ▸ arg_mem hAct 0
  · exact lpost_fails hF

set_option maxHeartbeats 1000000 in
theorem post_transferFrom (hS : Start USDT.runtimeCode usdtAbs M Act m)
    (hAct : calldataAddrs m.frame.msg.data ⊆ Act)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x23b872dd) (h4 : 4 ≤ m.frame.msg.data.size) :
    Halts m (Post Act m) := by
  have hf := hS.fresh
  have hdep := dep_of_start hS
  rcases transferFrom_dirty m hf hsel h4 hS.size hdep with
    ⟨s, hst, hsE, hg, hv, hsize, hp, hb⟩ | hF
  · rw [hsE] at hst
    have hD : (clean3 m.frame.msg.data).size = 100 := by simp [clean3, Abi.size_encodeCall]
    refine lpost_call_dirty (usdt_calls _) hS (dirtyRunS_of (K := 10000) usdtBodies_cert usdtBodies_safe hf
      (by rw [hD]; norm_num) hst hg ?_ ⟨[.top, .top, .top, .top, .top, .top, .top, .const 4247, .top, .top, .top,
          .const 914, .top], usdtBodies_seed (q := 0x21c8) (by simp [bodySeeds]),
        by simp [entryS, stF, StackOk, AVal.Holds]⟩) (encodes_transferFrom _) trivial ?_
    · refine (transferFrom_clean (clean (clean3 m.frame.msg.data) (m.frame.gasLeft + 10000) m)
        (fresh_clean hf (G := m.frame.gasLeft + 10000) (by omega) (clean3 m.frame.msg.data))
        (by simp [clean, setData, clean3, Abi.selectorOf_encodeCall]) (by simp [clean, setData, hD])
        (by simp [clean, setData, hD]) hv (by rw [clean_gas]; omega) hdep hp
        (by rw [show (clean (clean3 m.frame.msg.data) (m.frame.gasLeft + 10000) m).frame.msg.data =
          clean3 m.frame.msg.data from rfl, aa_clean3_0]; exact hb)).mono_left ?_
      rintro s' ⟨h1, h2⟩
      refine ⟨h1.trans ?_, by rw [clean_gas] at h2; omega⟩
      rw [show (clean (clean3 m.frame.msg.data) (m.frame.gasLeft + 10000) m).frame.msg.data = clean3 m.frame.msg.data from rfl,
        stF_clean, aa_clean3_0]
      rfl
    · intro a ha
      simp only [Call.addrs, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact arg_mem hAct 0
      · exact arg_mem hAct 1
  · exact lpost_fails hF

end

/-! ## The theorems -/

/-- The dispatcher's selectors. -/
theorem sel_eq : sel = [0xe5b5019a, 0x3eaaf86b, 0x0ecb93c0, 0xdd62ed3e, 0x5c658165, 0x095ea7b3,
    0x70a08231, 0x27e235e3, 0xdd644f72, 0x313ce567, 0x0753c30c, 0x0e136b19, 0xf3bdc228,
    0x59bf1abe, 0x893d20e8, 0xe47d6060, 0xcc872b66, 0x35390714, 0x06fdde03, 0x8da5cb5b,
    0x8456cb59, 0x5c975abb, 0xdb006a75, 0xe4997dc5, 0xc0324c77, 0x95d89b41, 0x18160ddd,
    0xa9059cbb, 0x23b872dd, 0xf2fde38b, 0x3f4ba83a, 0x26976e3f] := by
  decide

/-- **USDT with any calldata, except `transferOwnership` and `deprecate`**: every frame whose
calldata names only actors fails, changes nothing, or ends as an ERC-20 call or an operation of
`usdtModel` for the actors. -/
theorem usdt_malformed : MalformedSpec USDT.runtimeCode usdtAbs M ops opAddrs none usdtExcl := by
  refine malformed_of fun Act m hS hAct hex => ?_
  by_cases hfb : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ sel
  · exact lpost_fallback usdt_fallback hS hfb
  simp only [not_or, not_lt, not_not] at hfb
  obtain ⟨h4, hmem⟩ := hfb
  rw [sel_eq] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  have hdep := dep_of_start hS
  have hc := hS.caller
  have hA1 : ∀ (u : Address), u = Word.toAddress (aw m.frame.msg.data 0) →
      ∀ a ∈ [u], a ∈ Act := by
    rintro u rfl a ha
    simp only [List.mem_singleton] at ha
    exact ha ▸ arg_mem hAct 0
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h
  · exact post_getter hS (q := 0x091d) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 0x0488) (by simp [getterEntries]) h h4
  · exact post_op hS (q := 0x02dc) (e := .setBlacklisted m.frame.msg.caller (Word.toAddress (aw m.frame.msg.data 0)) true)
      (by simp [opEntries]) h h4
      (by simp [ops, h, argAddr, argWord, show ¬ m.frame.msg.data.size < 4 by omega]) (hA1 _ rfl)
  · exact post_view (allowance_view m hS.fresh h h4 hS.size hdep)
  · exact post_getter hS (q := 0x0517) (by simp [getterEntries]) h h4
  · exact post_approve hS hAct h h4
  · exact post_view (balanceOf_view m hS.fresh h h4 hS.size hdep)
  · exact post_getter hS (q := 0x03e9) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 0x086a) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 0x0436) (by simp [getterEntries]) h h4
  · exact absurd ⟨h4, by rw [h]; simp [usdtExcl]⟩ hex
  · exact post_getter hS (q := 0x02a4) (by simp [getterEntries]) h h4
  · exact post_op hS (q := 0x098a) (e := .destroyBlackFunds m.frame.msg.caller (Word.toAddress (aw m.frame.msg.data 0)))
      (by simp [opEntries]) h h4
      (by simp [ops, h, argAddr, argWord, show ¬ m.frame.msg.data.size < 4 by omega]) (hA1 _ rfl)
  · exact post_getter hS (q := 0x04c6) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 0x0612) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 0x0893) (by simp [getterEntries]) h h4
  · exact post_op hS (q := 0x07c3) (e := .mint m.frame.msg.caller m.frame.msg.caller (aw m.frame.msg.data 0).toNat)
      (by simp [opEntries]) h h4
      (by simp [ops, h, argAddr, argWord, show ¬ m.frame.msg.data.size < 4 by omega])
      (by intro a ha; simp [opAddrs] at ha)
  · exact post_getter hS (q := 0x045f) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 0x019b) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 0x0667) (by simp [getterEntries]) h h4
  · exact post_op hS (q := 0x0608) (e := .setPaused m.frame.msg.caller true)
      (by simp [opEntries]) h h4
      (by simp [ops, h, argAddr, argWord, show ¬ m.frame.msg.data.size < 4 by omega])
      (by intro a ha; simp [opAddrs] at ha)
  · exact post_getter hS (q := 0x0583) (by simp [getterEntries]) h h4
  · exact post_op hS (q := 0x07e6) (e := .burn m.frame.msg.caller m.frame.msg.caller (aw m.frame.msg.data 0).toNat)
      (by simp [opEntries]) h h4
      (by simp [ops, h, argAddr, argWord, show ¬ m.frame.msg.data.size < 4 by omega])
      (by intro a ha; simp [opAddrs] at ha)
  · exact post_op hS (q := 0x08ef) (e := .setBlacklisted m.frame.msg.caller (Word.toAddress (aw m.frame.msg.data 0)) false)
      (by simp [opEntries]) h h4
      (by simp [ops, h, argAddr, argWord, show ¬ m.frame.msg.data.size < 4 by omega]) (hA1 _ rfl)
  · exact post_op hS (q := 0x0797) (e := .setParams m.frame.msg.caller (aw m.frame.msg.data 0).toNat (aw m.frame.msg.data 1).toNat)
      (by simp [opEntries]) h h4
      (by simp [ops, h, argAddr, argWord, show ¬ m.frame.msg.data.size < 4 by omega])
      (by intro a ha; simp [opAddrs] at ha)
  · exact post_getter hS (q := 0x06bc) (by simp [getterEntries]) h h4
  · exact post_view (totalSupply_view m hS.fresh h h4 hS.size hdep)
  · exact post_transfer hS hAct h h4
  · exact post_transferFrom hS hAct h h4
  · exact absurd ⟨h4, by rw [h]; simp [usdtExcl]⟩ hex
  · exact post_op hS (q := 0x04bc) (e := .setPaused m.frame.msg.caller false)
      (by simp [opEntries]) h h4
      (by simp [ops, h, argAddr, argWord, show ¬ m.frame.msg.data.size < 4 by omega])
      (by intro a ha; simp [opAddrs] at ha)
  · exact post_getter hS (q := 0x0394) (by simp [getterEntries]) h h4

/-- **The complete spec of USDT**: `ERC20Spec` and `MalformedSpec` except `transferOwnership`
and `deprecate` (no `permit`). -/
theorem usdt_complete :
    ERC20Spec.Complete USDT.runtimeCode usdtAbs M g₀ sel ops opAddrs none usdtExcl :=
  ⟨usdt_erc20Spec, fun _ _ h => (by cases h), usdt_malformed⟩

end Verified.WeirdERC20.USDT.Spec.Malformed
