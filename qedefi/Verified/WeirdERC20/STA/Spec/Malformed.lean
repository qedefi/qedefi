import Verified.WeirdERC20.STA.Spec.Spec
import Verified.WeirdERC20.STA.Spec.MalformedGetters
import Verified.WeirdERC20.Common.Transport

/-!
# Statera with any calldata: `MalformedSpec`

**`sta_malformed`**: in every frame of the mainnet Statera code (solc 0.5.0), with any calldata,
any value and any gas, the frame fails, changes nothing, or ends as an ERC-20 call or an
operation of `staModel` (for the actors and the accounts the call names). By selector:

* calldata shorter than a selector or an unknown selector: `fallback_spec` (Statera has no
  fallback function: it reverts);
* the eight getters change nothing, whatever their arguments (`getter_halts`);
* `destroy(v)`: with no value and a whole argument word, `staOps` decodes the calldata itself
  (`ops_spec`); otherwise it reverts;
* `transfer`, `approve`, `transferFrom` and `destroyFrom`, `upAllowance`, `downAllowance`:
  with value or too few argument words they revert; otherwise solc 0.5's decoder masks each
  `address` word to its low 160 bits, so the frame runs as the frame whose calldata is the
  ABI encoding of the call with the masked addresses (`Verified.WeirdERC20.Common.transport`),
  and `calls_spec`/`ops_spec` apply to that call, for the actors extended by its accounts.

**`sta_complete`**: `ERC20Spec.Complete` (Statera has no `permit`).
-/

set_option linter.unusedSimpArgs false

namespace Verified.WeirdERC20.STA.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.STA.Contracts
open Verified.WeirdERC20.STA.Spec Verified.WeirdERC20.Common
open Verified.Common.Malformed EvmLogic.AbsInt
open Verified.OpenZeppelin.ERC20.Spec (high hi setKind)

/-! ## The clean frame reaches the image of the dirty entry -/

theorem entry_clean (D' : ByteArray) (G : Nat) (m : Machine) (pc : Nat) (st : List Word)
    (c g : Nat) (hmG : m.frame.gasLeft ≤ G) (hg : g + c ≤ G) :
    entry (clean D' G m) pc st c = img D' (G - c - g) G [] (.call 0 0) (entryG m pc st g) := by
  obtain ⟨ctx, pre, w, tr, ow, cr, ⟨msg, code, jd, pc0, st0, mem, gas, rd, sub, snap, kind⟩,
    ps⟩ := m
  simp only at hmG
  simp only [entry, entryG, clean, img, setData, high, hi, setKind,
    EvmLogic.Program.Nested.bump, Machine.mk.injEq, Frame.mk.injEq, true_and, and_true]
  omega

/-- `Args` of an ABI encoding. -/
theorem args_encodeCall {sel : Nat} (hsel : sel < 2 ^ 32) (ws : List Word) :
    Args (Abi.encodeCall sel ws) sel ws :=
  ⟨by rw [Abi.selectorOf_encodeCall, Nat.mod_eq_of_lt hsel], by rw [Abi.size_encodeCall],
    fun i h => Abi.calldataload_encodeCall sel ws i h⟩

theorem argWord_encodeCall {sel : Nat} {ws : List Word} (i : Nat) (h : i < ws.length) :
    argWord (Abi.encodeCall sel ws) i = ws[i] :=
  Abi.calldataload_encodeCall sel ws i h

theorem inCert_body {m : Machine} {pc : Nat} {s : AStack} (hseed : (pc, s) ∈ bodySeeds)
    (hpc : m.frame.pc = pc) (hst : StackOk (fun _ => 0) s m.frame.stack) :
    InCert (fun _ => 0) staBodies m :=
  ⟨s, hpc ▸ staBodies_seed hseed, hst⟩

theorem steps_of_wp {m : Machine} {Q : Machine → Prop} (h : WP m Q (fun _ _ => False)) :
    ∃ s, Steps m s ∧ Q s := by
  rcases h with h | ⟨_, _, _, _, _, h⟩
  · exact h
  · exact h.elim

/-- The clean calldata of a body taking an `address` and a word. -/
def clean2 (sel : Nat) (d : ByteArray) : ByteArray :=
  Abi.encodeCall sel [Word.ofAddress (Word.toAddress (argWord d 0)), argWord d 1]

/-- The clean calldata of `transferFrom`. -/
def clean3 (d : ByteArray) : ByteArray :=
  Abi.encodeCall 0x23b872dd [Word.ofAddress (Word.toAddress (argWord d 0)),
    Word.ofAddress (Word.toAddress (argWord d 1)), argWord d 2]

theorem st2_clean2 (sel : Nat) (d : ByteArray) (ret selw : Word) :
    st2 (clean2 sel d) ret selw = st2 d ret selw := by
  simp only [st2, clean2, argWord, Nat.reduceMul, Nat.reduceAdd, Abi.calldataload_encodeCall_0, Abi.calldataload_encodeCall_1,
    Word.toAddress_ofAddress]

theorem st3_clean3 (d : ByteArray) : st3 (clean3 d) = st3 d := by
  simp only [st3, clean3, argWord, Nat.reduceMul, Nat.reduceAdd, Abi.calldataload_encodeCall_0, Abi.calldataload_encodeCall_1,
    Abi.calldataload_encodeCall_2, Word.toAddress_ofAddress]

/-- **A dirty two-argument frame is a `DirtyRun`**: the dispatcher runs for the dirty frame
(`hst`) and for its clean counterpart (`hclean`), and the body is a data-safe region. -/
theorem dirtyRun2 {sel pc c : Nat} {ret selw : Word} (hsel : sel < 2 ^ 32)
    (hclean : ∀ m : Machine, Fresh STA.runtimeCode m → Abi.selectorOf m.frame.msg.data = sel →
      68 ≤ m.frame.msg.data.size → m.frame.msg.data.size < 2 ^ 64 →
      m.frame.msg.value = 0 → 10000 ≤ m.frame.gasLeft →
      WP m (fun s => s = entry m pc (st2 m.frame.msg.data ret selw) c) (fun _ _ => False))
    (hseed : (pc, [.top, .top, .const ret.toNat, .top]) ∈ bodySeeds) (hc : c ≤ 10000)
    {m : Machine} (hf : Fresh STA.runtimeCode m) (hval : m.frame.msg.value = 0) {g : Nat}
    (hst : Steps m (entryG m pc (st2 m.frame.msg.data ret selw) g)) (hg : g ≤ m.frame.gasLeft) :
    DirtyRun STA.runtimeCode m (clean2 sel m.frame.msg.data) := by
  have hD : (clean2 sel m.frame.msg.data).size = 68 := by simp [clean2, Abi.size_encodeCall]
  refine ⟨by omega, m.frame.gasLeft + 10000, m.frame.gasLeft + 10000 - c - g, _, _, _,
    staBodies, by omega, hst, rfl, ?_, staBodies_cert, staBodies_safe, hf.frame.1,
    inCert_body hseed rfl ⟨trivial, trivial, rfl, trivial, trivial⟩⟩
  obtain ⟨s, hs, rfl⟩ := steps_of_wp (hclean _ (fresh_clean hf (G := m.frame.gasLeft + 10000) (by omega)
    (clean2 sel m.frame.msg.data))
    (by simp [clean, setData, clean2, Abi.selectorOf_encodeCall]; omega)
    (by simp [clean, setData, hD]) (by simp [clean, setData, hD]) hval
    (by simp [clean, setData, high, hi, setKind, EvmLogic.Program.Nested.bump]))
  have he := entry_clean (clean2 sel m.frame.msg.data) (m.frame.gasLeft + 10000) m pc
    (st2 m.frame.msg.data ret selw) c g (by omega) (by omega)
  have hd : (clean (clean2 sel m.frame.msg.data) (m.frame.gasLeft + 10000) m).frame.msg.data =
    clean2 sel m.frame.msg.data := rfl
  rw [hd, st2_clean2, he] at hs
  exact hs

/-- **A dirty `transferFrom` frame is a `DirtyRun`.** -/
theorem dirtyRun3 {m : Machine} (hf : Fresh STA.runtimeCode m) (hval : m.frame.msg.value = 0)
    {g : Nat} (hst : Steps m (entryG m 0x0583 (st3 m.frame.msg.data) g))
    (hg : g ≤ m.frame.gasLeft) :
    DirtyRun STA.runtimeCode m (clean3 m.frame.msg.data) := by
  have hD : (clean3 m.frame.msg.data).size = 100 := by simp [clean3, Abi.size_encodeCall]
  refine ⟨by omega, m.frame.gasLeft + 10000, m.frame.gasLeft + 10000 - 367 - g, _, _, _,
    staBodies, by omega, hst, rfl, ?_, staBodies_cert, staBodies_safe, hf.frame.1,
    inCert_body (pc := 0x0583) (s := [.top, .top, .top, .const 478, .top])
      (by simp [bodySeeds]) rfl ⟨trivial, trivial, trivial, rfl, trivial, trivial⟩⟩
  obtain ⟨s, hs, rfl⟩ := steps_of_wp (transferFrom_clean _ (fresh_clean hf (G := m.frame.gasLeft + 10000) (by omega)
    (clean3 m.frame.msg.data))
    (by simp [clean, setData, clean3, Abi.selectorOf_encodeCall])
    (by simp [clean, setData, hD]) (by simp [clean, setData, hD]) hval
    (by simp [clean, setData, high, hi, setKind, EvmLogic.Program.Nested.bump]))
  have he := entry_clean (clean3 m.frame.msg.data) (m.frame.gasLeft + 10000) m 0x0583
    (st3 m.frame.msg.data) 367 g (by omega) (by omega)
  have hd : (clean (clean3 m.frame.msg.data) (m.frame.gasLeft + 10000) m).frame.msg.data =
    clean3 m.frame.msg.data := rfl
  rw [hd, st3_clean3, he] at hs
  exact hs

/-! ## The clean calls -/

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

theorem addrArg_ofAddress (a : Address) : addrArg (Word.ofAddress a) = some a := by
  have h := a.isLt
  simp only [addrArg, EvmLogic.AbsInt.toNat_ofAddress, h, ite_true, Word.toAddress_ofAddress]

/-- What `staOps` decodes from the clean calldata of a two-argument entry point. -/
theorem staOps_clean2 (c : Address) (sel : Nat) (d : ByteArray) :
    staOps c (clean2 sel d) 0 =
      if sel % 2 ^ 32 = 0x9d118770 then
        some (.burn c c (Word.ofAddress (Word.toAddress (argWord d 0))).toNat)
      else if sel % 2 ^ 32 = 0x33393efa then
        some (.burnFrom c (Word.toAddress (argWord d 0)) (argWord d 1).toNat)
      else if sel % 2 ^ 32 = 0xe5981a42 then
        some (.adjustAllowance c (Word.toAddress (argWord d 0)) true (argWord d 1).toNat)
      else if sel % 2 ^ 32 = 0xdf401a96 then
        some (.adjustAllowance c (Word.toAddress (argWord d 0)) false (argWord d 1).toNat)
      else none := by
  simp only [staOps, clean2, Abi.size_encodeCall, Abi.selectorOf_encodeCall, argWord,
    Nat.reduceMul, Nat.reduceAdd, Abi.calldataload_encodeCall_0, Abi.calldataload_encodeCall_1,
    addrArg_ofAddress, Option.map_some, List.length_cons, List.length_nil]
  simp

/-! ## The theorems -/

/-- The dispatcher's selectors. -/
theorem sel_eq : sel = [0xdd62ed3e, 0x095ea7b3, 0x70a08231, 0xc5ac0ded, 0x09260db7, 0x313ce567,
    0x9d118770, 0x33393efa, 0xdf401a96, 0x06fdde03, 0x95d89b41, 0x18160ddd, 0xa9059cbb,
    0x23b872dd, 0xe5981a42] := by
  decide

section
variable {Act : Finset Address} {m : Machine}

/-- `MalPost` of Statera. -/
abbrev Post (Act : Finset Address) (m : Machine) : Machine → Outcome → Prop :=
  MalPost staAbs M staOps staOpAddrs none Act m

theorem post_getter (hS : Start STA.runtimeCode staAbs M Act m) {sel q : Nat}
    (hge : (sel, q) ∈ getterEntries) (hsel : Abi.selectorOf m.frame.msg.data = sel)
    (h4 : 4 ≤ m.frame.msg.data.size) : Halts m (Post Act m) :=
  (getter_halts hge m hS.fresh hsel h4 hS.size).mono fun _ _ _ h => by
    rcases h with h | h
    · exact .inl h
    · exact .inr (.inl h)

theorem value_toNat {m : Machine} (h : m.frame.msg.value = 0) : m.frame.msg.value.toNat = 0 := by
  rw [h]; rfl

end

/-- **Statera with any calldata**: every frame fails, changes nothing, or ends as an ERC-20
call or an operation of `staModel` (for the actors and the accounts it names). -/
theorem sta_malformed : MalformedSpec STA.runtimeCode staAbs M staOps staOpAddrs none := by
  refine malformedSpec_of fun Act m hS => ?_
  by_cases hfb : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ sel
  · exact post_fallback fallback_spec hS hfb
  simp only [not_or, not_lt, not_not] at hfb
  obtain ⟨h4, hmem⟩ := hfb
  rw [sel_eq] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  have hf := hS.fresh
  have hsz := hS.size
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact post_getter hS (q := 0x0370) (by simp [getterEntries]) h h4
  · rcases approve_dirty m hf h h4 hsz with ⟨s, hst, hs, hg, hv, -⟩ | hF
    · rw [hs] at hst
      exact post_call_dirty (calls_spec _) hS
        (dirtyRun2 (by norm_num) approve_clean (by decide) (by norm_num) hf hv hst hg)
        (encodes_approve _) trivial
    · exact post_fails hF
  · exact post_getter hS (q := 0x02b0) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 0x035b) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 0x0169) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 0x024a) (by simp [getterEntries]) h h4
  · rcases destroy_dirty m hf h h4 hsz with ⟨-, -, hv, h36⟩ | hF
    · refine post_op ops_spec hS (e := .burn m.frame.msg.caller m.frame.msg.caller
        (argWord m.frame.msg.data 0).toNat) ?_
      rw [value_toNat hv]
      simp only [staOps, h, show ¬ m.frame.msg.data.size < 36 by omega]
      simp
    · exact post_fails hF
  · rcases destroyFrom_dirty m hf h h4 hsz with ⟨s, hst, hs, hg, hv, -⟩ | hF
    · rw [hs] at hst
      refine post_op_dirty ops_spec hS (e := .burnFrom m.frame.msg.caller (Word.toAddress (argWord m.frame.msg.data 0)) (argWord m.frame.msg.data 1).toNat)
        (dirtyRun2 (by norm_num) destroyFrom_clean (by decide) (by norm_num) hf hv hst hg) ?_
      rw [value_toNat hv, staOps_clean2]
      simp
    · exact post_fails hF
  · rcases downAllowance_dirty m hf h h4 hsz with ⟨s, hst, hs, hg, hv, -⟩ | hF
    · rw [hs] at hst
      refine post_op_dirty ops_spec hS (e := .adjustAllowance m.frame.msg.caller (Word.toAddress (argWord m.frame.msg.data 0)) false (argWord m.frame.msg.data 1).toNat)
        (dirtyRun2 (by norm_num) downAllowance_clean (by decide) (by norm_num) hf hv hst hg) ?_
      rw [value_toNat hv, staOps_clean2]
      simp
    · exact post_fails hF
  · exact post_getter hS (q := 0x00df) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 0x02e3) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 0x01f2) (by simp [getterEntries]) h h4
  · rcases transfer_dirty m hf h h4 hsz with ⟨s, hst, hs, hg, hv, -⟩ | hF
    · rw [hs] at hst
      exact post_call_dirty (calls_spec _) hS
        (dirtyRun2 (by norm_num) transfer_clean (by decide) (by norm_num) hf hv hst hg)
        (encodes_transfer _) trivial
    · exact post_fails hF
  · rcases transferFrom_dirty m hf h h4 hsz with ⟨s, hst, hs, hg, hv, -⟩ | hF
    · rw [hs] at hst
      exact post_call_dirty (calls_spec _) hS (dirtyRun3 hf hv hst hg)
        (encodes_transferFrom _) trivial
    · exact post_fails hF
  · rcases upAllowance_dirty m hf h h4 hsz with ⟨s, hst, hs, hg, hv, -⟩ | hF
    · rw [hs] at hst
      refine post_op_dirty ops_spec hS (e := .adjustAllowance m.frame.msg.caller (Word.toAddress (argWord m.frame.msg.data 0)) true (argWord m.frame.msg.data 1).toNat)
        (dirtyRun2 (by norm_num) upAllowance_clean (by decide) (by norm_num) hf hv hst hg) ?_
      rw [value_toNat hv, staOps_clean2]
      simp
    · exact post_fails hF

/-- **The complete spec of Statera**: `ERC20Spec` and `MalformedSpec` (no `permit`). -/
theorem sta_complete :
    ERC20Spec.Complete STA.runtimeCode staAbs M g₀ sel staOps staOpAddrs none :=
  ⟨sta_spec, fun _ _ h => (by cases h), sta_malformed⟩

end Verified.WeirdERC20.STA.Spec.Malformed
