import Verified.WETH9.Spec.Spec
import Verified.WETH9.Spec.MalformedCert
import Verified.WETH9.Spec.MalformedPrefix
import Verified.WeirdERC20.Common.Post

/-!
# WETH9 with any calldata: `MalformedSpec` except `withdraw`

**`weth9_malformed`**: in every frame of the mainnet WETH9 code (solc 0.4.19), with any calldata
naming only actors (`calldataAddrs`, which contains `0`: solc 0.4 reads an argument word past
the end of the calldata as zero, so a missing `address` argument is `0`), any value and any
gas, except `withdraw` (`weth9Excl`: it sends ether to the caller and runs the caller's code),
the frame fails, changes nothing, or ends as an ERC-20 call or a `deposit` of `weth9Model`. By
selector:

* calldata shorter than a selector or an unknown selector: `weth9_fallbackSpec` (`deposit`);
* the six getters change nothing (`getter_halts`);
* `deposit()`: `weth9Ops` decodes the calldata itself (`weth9_opSpec`);
* `transfer`, `approve`, `transferFrom`: with value they revert; otherwise the frame runs as the
  frame whose calldata is the ABI encoding of the decoded words (zero-padded, `address` words
  masked) (`Verified.WeirdERC20.Common.transport`), and `weth9_callSpec` applies to that call:
  its accounts are words of the calldata or `0`.

**`weth9_complete`**: `ERC20Spec.Complete` (no `permit`) with `excl = weth9Excl`.
-/

set_option linter.unusedSimpArgs false

namespace Verified.WETH9.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.WETH9 Verified.WETH9.Contracts
open Verified.WETH9.Spec Verified.WeirdERC20.Common Verified.Solady.Spec.AnyGas
open Verified.WeirdERC20.BNB.Spec (div_selector argWord)
open Verified.Common.Malformed (Unchanged halts_pure inCert_top)
open EvmLogic.AbsInt

/-- The entry points `weth9Model` does not describe: `withdraw(uint256)` (it sends ether to the
caller, running the caller's code). -/
def weth9Excl : List Nat := [0x2e1a7d4d]

/-! ## The getters -/

/-- The dispatcher's run to a getter's dispatch target. -/
def AtGetter (m : Machine) (q : Nat) (sel : Nat) (s : Machine) : Prop :=
  s.frame.pc = q ∧ s.frame.stack = [BitVec.ofNat 256 sel] ∧ s.frame.code = WETH9.runtimeCode ∧
    Unchanged m s

set_option maxHeartbeats 0 in
theorem getter_dispatch {sel q : Nat} (hge : (sel, q) ∈ getterEntries) (m : Machine)
    (hf : Fresh WETH9.runtimeCode m) (hsel : Abi.selectorOf m.frame.msg.data = sel)
    (h4 : 4 ≤ m.frame.msg.data.size) (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (AtGetter m q sel) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  simp only [getterEntries, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hge
  rcases hge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    solady_fresh_intro
    hwp_steps stop_at [0x00b9, 0x01a1, 0x0266, 0x0295, 0x02e2, 0x03d4] [hsel', hz]
    exact WP.ret ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **A getter fails or changes nothing**, with any value, arguments and gas. -/
theorem getter_halts {sel q : Nat} (hge : (sel, q) ∈ getterEntries) (m : Machine)
    (hf : Fresh WETH9.runtimeCode m) (hsel : Abi.selectorOf m.frame.msg.data = sel)
    (h4 : 4 ≤ m.frame.msg.data.size) (hsz : m.frame.msg.data.size < 2 ^ 64) :
    Halts m (fun mf o => Fails o ∨ Unchanged m mf) := by
  have hin : InT wethGetters q [.top] :=
    wethGetters_seed (List.mem_map.2 ⟨(sel, q), hge, rfl⟩)
  rcases getter_dispatch hge m hf hsel h4 hsz with ⟨s, hst, hpc, hs, hcode, h1, h2, h3⟩ | h
  · refine Halts.of_steps hst ((halts_pure wethGetters_cert wethGetters_pure s hcode
      (inCert_top hin hpc hs)).mono fun mf _ _ ⟨g1, g2, g3⟩ => .inr ?_)
    exact ⟨g1.trans h1, g2.trans h2, g3.trans h3⟩
  · exact h.mono fun _ _ _ h => .inl h

/-! ## The clean calls -/

/-- The clean calldata of a body taking an `address` and a word. -/
def clean2 (sel : Nat) (d : ByteArray) : ByteArray :=
  Abi.encodeCall sel [Word.ofAddress (Word.toAddress (argWord d 0)), argWord d 1]

/-- The clean calldata of `transferFrom`. -/
def clean3 (d : ByteArray) : ByteArray :=
  Abi.encodeCall 0x23b872dd [Word.ofAddress (Word.toAddress (argWord d 0)),
    Word.ofAddress (Word.toAddress (argWord d 1)), argWord d 2]

theorem st2_clean2 (sel : Nat) (d : ByteArray) (ret selw : Word) :
    st2 (clean2 sel d) ret selw = st2 d ret selw := by
  simp only [st2, clean2, argWord, Nat.reduceMul, Nat.reduceAdd, Abi.calldataload_encodeCall_0,
    Abi.calldataload_encodeCall_1, Word.toAddress_ofAddress]

theorem st3_clean3 (d : ByteArray) (ret selw : Word) : st3 (clean3 d) ret selw = st3 d ret selw := by
  simp only [st3, clean3, argWord, Nat.reduceMul, Nat.reduceAdd, Abi.calldataload_encodeCall_0,
    Abi.calldataload_encodeCall_1, Abi.calldataload_encodeCall_2, Word.toAddress_ofAddress]

/-- `Args` of an ABI encoding. -/
theorem args_encodeCall {sel : Nat} (hsel : sel < 2 ^ 32) (ws : List Word) :
    Args (Abi.encodeCall sel ws) sel ws :=
  ⟨by rw [Abi.selectorOf_encodeCall, Nat.mod_eq_of_lt hsel], by rw [Abi.size_encodeCall],
    fun i h => Abi.calldataload_encodeCall sel ws i h⟩

theorem word_toNat_self (w : Word) : word w.toNat = w := by
  simp [word]

theorem encodes_transfer (d : ByteArray) :
    (Call.transfer (Word.toAddress (argWord d 0)) (argWord d 1).toNat).Encodes
      (clean2 0xa9059cbb d) :=
  ⟨(argWord d 1).isLt, by rw [word_toNat_self]; exact args_encodeCall (by norm_num) _⟩

theorem encodes_approve (d : ByteArray) :
    (Call.approve (Word.toAddress (argWord d 0)) (argWord d 1).toNat).Encodes
      (clean2 0x095ea7b3 d) :=
  ⟨(argWord d 1).isLt, by rw [word_toNat_self]; exact args_encodeCall (by norm_num) _⟩

theorem encodes_transferFrom (d : ByteArray) :
    (Call.transferFrom (Word.toAddress (argWord d 0)) (Word.toAddress (argWord d 1))
      (argWord d 2).toNat).Encodes (clean3 d) :=
  ⟨(argWord d 2).isLt, by rw [word_toNat_self]; exact args_encodeCall (by norm_num) _⟩

/-! ## Dirty frames -/

section
variable {Act : Finset Address} {m : Machine}

/-- **A dirty frame is a `DirtyRun`.** -/
theorem dirtyRun {st : ByteArray → List Word} {pc c sel : Nat} {D' : ByteArray}
    (hclean : ∀ x : Machine, Fresh WETH9.runtimeCode x → Abi.selectorOf x.frame.msg.data = sel →
      4 ≤ x.frame.msg.data.size → x.frame.msg.data.size < 2 ^ 64 →
      x.frame.msg.value = 0 → 10000 ≤ x.frame.gasLeft →
      WP x (fun s => s = entry mem60 x pc (st x.frame.msg.data) c) (fun _ _ => False))
    (hD' : st D' = st m.frame.msg.data) (hc : c ≤ 10000)
    (hsel : Abi.selectorOf D' = sel) (hD4 : 4 ≤ D'.size) (hD : D'.size < 2 ^ 64)
    (hf : Fresh WETH9.runtimeCode m) (hval : m.frame.msg.value = 0) {g : Nat}
    (hst : Steps m (entryG mem60 m pc (st m.frame.msg.data) g)) (hg : g ≤ m.frame.gasLeft)
    {s : AStack} (hseed : (pc, s) ∈ bodySeeds)
    (hstk : StackOk (fun _ => 0) s (st m.frame.msg.data)) :
    DirtyRun WETH9.runtimeCode m D' := by
  refine dirtyRun_of wethBodies_cert wethBodies_safe hf hD hst hg hc ?_
    ⟨s, wethBodies_seed hseed, hstk⟩
  have h := hclean (clean D' (m.frame.gasLeft + 10000) m)
    (fresh_clean hf (G := m.frame.gasLeft + 10000) (by omega) D') hsel hD4 hD hval
    (by simp [clean, setData, Verified.OpenZeppelin.ERC20.Spec.high,
      Verified.OpenZeppelin.ERC20.Spec.hi, Verified.OpenZeppelin.ERC20.Spec.setKind,
      EvmLogic.Program.Nested.bump])
  rw [show (clean D' (m.frame.gasLeft + 10000) m).frame.msg.data = D' from rfl, hD'] at h
  exact h

/-- `MalformedSpec`'s frame-end condition for WETH9. -/
abbrev Post (Act : Finset Address) (m : Machine) : Machine → Outcome → Prop :=
  LPost weth9Abs weth9Model weth9Ops weth9OpAddrs none Act m

/-- An argument word names an actor: a word of the calldata (`calldataAddrs`), or a word past
its end, which reads `0`. -/
theorem arg_mem0 {d : ByteArray} (hAct : calldataAddrs d ⊆ Act) (h0 : (0 : Address) ∈ Act)
    (i : Nat) : Word.toAddress (argWord d i) ∈ Act := by
  by_cases h : 4 + 32 * i < d.size
  · exact hAct (mem_calldataAddrs h)
  · have : argWord d i = 0 := by
      simp only [argWord, readBytes, show d.size ≤ 4 + 32 * i by omega, ↓reduceIte]
      decide
    rw [this]
    exact h0

theorem post_getter (hS : Start WETH9.runtimeCode weth9Abs weth9Model Act m) {sel q : Nat}
    (hge : (sel, q) ∈ getterEntries) (hsel : Abi.selectorOf m.frame.msg.data = sel)
    (h4 : 4 ≤ m.frame.msg.data.size) : Halts m (Post Act m) :=
  lpost_unchanged (getter_halts hge m hS.fresh hsel h4 hS.size)

end

/-! ## The theorem -/

/-- The dispatcher's selectors. -/
theorem sel_eq : weth9Sel = [0xdd62ed3e, 0x095ea7b3, 0x70a08231, 0x313ce567, 0xd0e30db0,
    0x06fdde03, 0x95d89b41, 0x18160ddd, 0xa9059cbb, 0x23b872dd, 0x2e1a7d4d] := by
  decide

/-- `weth9_malformed` for any actors containing the calldata's accounts and `0`. -/
theorem weth9_malformed_zero (Act : Finset Address) (m : Machine)
    (hS : Start WETH9.runtimeCode weth9Abs weth9Model Act m)
    (hAct : calldataAddrs m.frame.msg.data ⊆ Act) (h0 : (0 : Address) ∈ Act)
    (hex : ¬ (4 ≤ m.frame.msg.data.size ∧ Abi.selectorOf m.frame.msg.data ∈ weth9Excl)) :
    Halts m (Post Act m) := by
  by_cases hfb : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ weth9Sel
  · exact lpost_fallback weth9_fallbackSpec hS hfb
  simp only [not_or, not_lt, not_not] at hfb
  obtain ⟨h4, hmem⟩ := hfb
  rw [sel_eq] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  have hf := hS.fresh
  have hsz := hS.size
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h
  · exact post_getter hS (q := 0x03d4) (by simp [getterEntries]) h h4
  · -- approve
    rcases approve_dirty m hf h h4 hsz with ⟨s, hst, hsE, hg, hv⟩ | hF
    · rw [hsE] at hst
      have hD : (clean2 0x095ea7b3 m.frame.msg.data).size = 68 := by
        simp [clean2, Abi.size_encodeCall]
      refine lpost_call_dirty (weth9_callSpec _) hS
        (dirtyRun (st := fun d => st2 d 391#256 157198259#256) approve_clean
          (st2_clean2 _ _ _ _) (by norm_num) (by simp [clean2, Abi.selectorOf_encodeCall])
          (by omega) (by omega) hf hv hst hg (s := [.top, .top, .const 391, .top])
          (by decide) ⟨trivial, trivial, rfl, trivial, trivial⟩)
        (encodes_approve _) trivial ?_
      intro a ha
      simp only [Call.addrs, List.mem_singleton] at ha
      exact ha ▸ arg_mem0 hAct h0 0
    · exact lpost_fails hF
  · exact post_getter hS (q := 0x0295) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 0x0266) (by simp [getterEntries]) h h4
  · -- deposit
    refine lpost_op weth9_opSpec hS (e := .deposit m.frame.msg.caller m.frame.msg.value.toNat)
      ?_ ?_
    · simp only [weth9Ops, depositSelector, h, h4, and_self, ↓reduceIte]
    · intro a ha
      simp only [weth9OpAddrs, List.mem_singleton] at ha
      exact ha ▸ hS.caller
  · exact post_getter hS (q := 0x00b9) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 0x02e2) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 0x01a1) (by simp [getterEntries]) h h4
  · -- transfer
    rcases transfer_dirty m hf h h4 hsz with ⟨s, hst, hsE, hg, hv⟩ | hF
    · rw [hsE] at hst
      have hD : (clean2 0xa9059cbb m.frame.msg.data).size = 68 := by
        simp [clean2, Abi.size_encodeCall]
      refine lpost_call_dirty (weth9_callSpec _) hS
        (dirtyRun (st := fun d => st2 d 944#256 2835717307#256) transfer_clean
          (st2_clean2 _ _ _ _) (by norm_num) (by simp [clean2, Abi.selectorOf_encodeCall])
          (by omega) (by omega) hf hv hst hg (s := [.top, .top, .const 944, .top])
          (by decide) ⟨trivial, trivial, rfl, trivial, trivial⟩)
        (encodes_transfer _) trivial ?_
      intro a ha
      simp only [Call.addrs, List.mem_singleton] at ha
      exact ha ▸ arg_mem0 hAct h0 0
    · exact lpost_fails hF
  · -- transferFrom
    rcases transferFrom_dirty m hf h h4 hsz with ⟨s, hst, hsE, hg, hv⟩ | hF
    · rw [hsE] at hst
      have hD : (clean3 m.frame.msg.data).size = 100 := by simp [clean3, Abi.size_encodeCall]
      refine lpost_call_dirty (weth9_callSpec _) hS
        (dirtyRun (st := fun d => st3 d 553#256 599290589#256) transferFrom_clean
          (st3_clean3 _ _ _) (by norm_num) (by simp [clean3, Abi.selectorOf_encodeCall])
          (by omega) (by omega) hf hv hst hg (s := [.top, .top, .top, .const 553, .top])
          (by decide) ⟨trivial, trivial, trivial, rfl, trivial, trivial⟩)
        (encodes_transferFrom _) trivial ?_
      intro a ha
      simp only [Call.addrs, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact arg_mem0 hAct h0 0
      · exact arg_mem0 hAct h0 1
    · exact lpost_fails hF
  · exact absurd ⟨h4, by rw [h]; simp [weth9Excl]⟩ hex

/-- **WETH9 with any calldata, except `withdraw`**: every frame whose calldata names only actors
fails, changes nothing, or ends as an ERC-20 call or a `deposit` of `weth9Model` for the
actors. -/
theorem weth9_malformed :
    MalformedSpec WETH9.runtimeCode weth9Abs weth9Model weth9Ops weth9OpAddrs none weth9Excl :=
  malformed_of fun Act m hS hAct hex =>
    weth9_malformed_zero Act m hS hAct (hAct (Finset.mem_insert_self _ _)) hex

/-- **The complete spec of WETH9**: `ERC20Spec` and `MalformedSpec` except `withdraw` (no
`permit`). -/
theorem weth9_complete :
    ERC20Spec.Complete WETH9.runtimeCode weth9Abs weth9Model weth9Gas weth9Sel weth9Ops
      weth9OpAddrs none weth9Excl :=
  ⟨weth9_erc20Spec, fun _ _ h => (by cases h), weth9_malformed⟩

end Verified.WETH9.Spec.Malformed
