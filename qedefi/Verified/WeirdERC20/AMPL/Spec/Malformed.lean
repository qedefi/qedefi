import Verified.WeirdERC20.AMPL.Spec.Spec
import Verified.WeirdERC20.AMPL.Spec.MalformedInit
import Verified.WeirdERC20.Common.Post

/-!
# AMPL with any calldata: `MalformedSpec`, up to `permit`

**`ampl_malformed r`**: `MalformedSpec` for AMPL's implementation code (solc 0.7.6, ABI coder
v1), with no entry point excluded and any signature recovery `r` for `permit`, from
**`PermitResidue r`**: the `permit` frames with no value and all seven argument words end as the
model's `permit` with the recovery `r` (or fail, or change nothing). AMPL's `permit` has no
proof yet; for the right `r` (the address `ecrecover` returns for AMPL's EIP-712 digest,
`address(0)` when the recovery fails, which AMPL's code accepts as an owner,
`ampl_permit_zero_owner`) the residue is what `MalformedSpec` asks of those frames. Every other
frame, with any calldata, value and gas, is proved here. By selector:

* calldata shorter than a selector or an unknown selector: `fallback_spec`;
* any value: the dispatcher's first check fails (`value_low`, `value_dirty`);
* the sixteen getters change nothing, whatever their arguments (`getter_halts`);
* `transfer`, `approve`, `transferFrom`, `increaseAllowance`, `decreaseAllowance`,
  `transferAll`, `transferAllFrom`, `setMonetaryPolicy`, `transferOwnership`: with too few
  argument words they revert; otherwise the decoder masks each `address` word to its low 160
  bits, so the frame runs as the frame whose calldata is the ABI encoding of the call with the
  masked addresses (`Verified.WeirdERC20.Common.transport`), and `calls_spec`/`ops_spec` apply
  to that call; its accounts are accounts the calldata names, so actors;
* `rebase(epoch, Δ)` and `renounceOwnership()`: with no value and enough argument words
  `amplOps` decodes the calldata itself (`ops_spec`); otherwise they revert;
* the two `initialize` functions revert on an initialized instance (`init_addr_low`,
  `init_strings_low`), which every `Start` frame is (`live_of_wf`);
* `permit`: with value or too few words it reverts; otherwise `PermitResidue r`.
-/

set_option linter.unusedSimpArgs false

namespace Verified.WeirdERC20.AMPL.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.AMPL.Contracts
open Verified.WeirdERC20.AMPL.Spec Verified.WeirdERC20.Common
open Verified.Common.Malformed EvmLogic.AbsInt
open Verified.OpenZeppelin.ERC20.Spec (high hi setKind)
open QEDefi.ERC20.Spec.AMPL (AState AmplOp)

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

theorem steps_of_wp {m : Machine} {Q : Machine → Prop} (h : WP m Q (fun _ _ => False)) :
    ∃ s, Steps m s ∧ Q s := by
  rcases h with h | ⟨_, _, _, _, _, h⟩
  · exact h
  · exact h.elim

/-- `Args` of an ABI encoding. -/
theorem args_encodeCall {sel : Nat} (hsel : sel < 2 ^ 32) (ws : List Word) :
    Args (Abi.encodeCall sel ws) sel ws :=
  ⟨by rw [Abi.selectorOf_encodeCall, Nat.mod_eq_of_lt hsel], by rw [Abi.size_encodeCall],
    fun i h => Abi.calldataload_encodeCall sel ws i h⟩

/-- **A dirty frame of an entry point taking an `address` is a `DirtyRun`**: the dispatcher
runs for the dirty frame (`hst`) and for its clean counterpart `cl d` (`hclean`), and the body
is a data-safe region. -/
theorem dirtyRun {sel pc c k : Nat} {st : ByteArray → List Word} {cl : ByteArray → ByteArray}
    {s : AStack} (hcsel : ∀ d, Abi.selectorOf (cl d) = sel) (hcsize : ∀ d, (cl d).size = 4 + k)
    (hk : 4 + k < 2 ^ 64) (hstc : ∀ d, st (cl d) = st d)
    (hclean : ∀ m : Machine, Fresh AMPL.runtimeCode m → Abi.selectorOf m.frame.msg.data = sel →
      4 + k ≤ m.frame.msg.data.size → m.frame.msg.data.size < 2 ^ 64 →
      m.frame.msg.value = 0 → 10000 ≤ m.frame.gasLeft →
      WP m (fun s => s = entry m pc (st m.frame.msg.data) c) (fun _ _ => False))
    (hseed : (pc, s) ∈ bodySeeds) (hok : ∀ d, StackOk (fun _ => 0) s (st d)) (hc : c ≤ 10000)
    {m : Machine} (hf : Fresh AMPL.runtimeCode m) (hval : m.frame.msg.value = 0) {g : Nat}
    (hst : Steps m (entryG m pc (st m.frame.msg.data) g)) (hg : g ≤ m.frame.gasLeft) :
    DirtyRun AMPL.runtimeCode m (cl m.frame.msg.data) := by
  have hD := hcsize m.frame.msg.data
  refine ⟨by omega, m.frame.gasLeft + 10000, m.frame.gasLeft + 10000 - c - g, _, _, _,
    amplBodies, by omega, hst, rfl, ?_, amplBodies_cert, amplBodies_safe, hf.frame.1,
    ⟨s, amplBodies_seed hseed, hok _⟩⟩
  obtain ⟨s, hs, rfl⟩ := steps_of_wp (hclean _
    (fresh_clean hf (G := m.frame.gasLeft + 10000) (by omega) (cl m.frame.msg.data))
    (hcsel _) (by simp only [clean, setData]; omega) (by simp only [clean, setData]; omega) hval
    (by simp [clean, setData, high, hi, setKind, EvmLogic.Program.Nested.bump]))
  have he := entry_clean (cl m.frame.msg.data) (m.frame.gasLeft + 10000) m pc
    (st m.frame.msg.data) c g (by omega) (by omega)
  have hd : (clean (cl m.frame.msg.data) (m.frame.gasLeft + 10000) m).frame.msg.data =
    cl m.frame.msg.data := rfl
  rw [hd, hstc, he] at hs
  exact hs

/-! ## The clean calldata -/

/-- The clean calldata of an entry point taking an `address`. -/
def clean1 (sel : Nat) (d : ByteArray) : ByteArray := Abi.encodeCall sel [maddr d 0]

/-- The clean calldata of an entry point taking an `address` and a word. -/
def clean2 (sel : Nat) (d : ByteArray) : ByteArray :=
  Abi.encodeCall sel [maddr d 0, argWord d 1]

/-- The clean calldata of `transferAllFrom`. -/
def cleanAA (d : ByteArray) : ByteArray := Abi.encodeCall 0x84d4b410 [maddr d 0, maddr d 1]

/-- The clean calldata of `transferFrom`. -/
def clean3 (d : ByteArray) : ByteArray :=
  Abi.encodeCall 0x23b872dd [maddr d 0, maddr d 1, argWord d 2]

theorem st1_clean1 (sel : Nat) (d : ByteArray) (ret selw : Word) :
    st1 (clean1 sel d) ret selw = st1 d ret selw := by
  simp only [st1, clean1, maddr, argWord, Nat.reduceMul, Nat.reduceAdd,
    Abi.calldataload_encodeCall_0, Word.toAddress_ofAddress]

theorem st2_clean2 (sel : Nat) (d : ByteArray) (ret selw : Word) :
    st2 (clean2 sel d) ret selw = st2 d ret selw := by
  simp only [st2, clean2, maddr, argWord, Nat.reduceMul, Nat.reduceAdd,
    Abi.calldataload_encodeCall_0, Abi.calldataload_encodeCall_1, Word.toAddress_ofAddress]

theorem stAA_cleanAA (d : ByteArray) : stAA (cleanAA d) = stAA d := by
  simp only [stAA, cleanAA, maddr, argWord, Nat.reduceMul, Nat.reduceAdd,
    Abi.calldataload_encodeCall_0, Abi.calldataload_encodeCall_1, Word.toAddress_ofAddress]

theorem st3_clean3 (d : ByteArray) : st3 (clean3 d) = st3 d := by
  simp only [st3, clean3, maddr, argWord, Nat.reduceMul, Nat.reduceAdd,
    Abi.calldataload_encodeCall_0, Abi.calldataload_encodeCall_1,
    Abi.calldataload_encodeCall_2, Word.toAddress_ofAddress]

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

theorem addrArg_ofAddress (a : Address) : addrArg (Word.ofAddress a) = some a := by
  have h := a.isLt
  simp only [addrArg, EvmLogic.AbsInt.toNat_ofAddress, h, ite_true, Word.toAddress_ofAddress]


theorem ops_transferAll (c : Address) (d : ByteArray) :
    amplOps c (clean1 0xa3a7e7f3 d) 0 =
      some (.base (.transferAll c (Word.toAddress (argWord d 0)))) := by
  simp [amplOps, clean1, Abi.size_encodeCall, Abi.selectorOf_encodeCall, argWord,
    Abi.calldataload_encodeCall_0, addrArg_ofAddress]

theorem ops_setMP (c : Address) (d : ByteArray) :
    amplOps c (clean1 0x8b5a6a08 d) 0 =
      some (.setMonetaryPolicy c (Word.toAddress (argWord d 0))) := by
  simp [amplOps, clean1, Abi.size_encodeCall, Abi.selectorOf_encodeCall, argWord,
    Abi.calldataload_encodeCall_0, addrArg_ofAddress]

theorem ops_transferOwnership (c : Address) (d : ByteArray) :
    amplOps c (clean1 0xf2fde38b d) 0 =
      some (.transferOwnership c (Word.toAddress (argWord d 0))) := by
  simp [amplOps, clean1, Abi.size_encodeCall, Abi.selectorOf_encodeCall, argWord,
    Abi.calldataload_encodeCall_0, addrArg_ofAddress]

theorem ops_inc (c : Address) (d : ByteArray) :
    amplOps c (clean2 0x39509351 d) 0 =
      some (.base (.adjustAllowance c (Word.toAddress (argWord d 0)) true (argWord d 1).toNat)) := by
  simp [amplOps, clean2, Abi.size_encodeCall, Abi.selectorOf_encodeCall, argWord,
    Abi.calldataload_encodeCall_0, Abi.calldataload_encodeCall_1, addrArg_ofAddress]

theorem ops_dec (c : Address) (d : ByteArray) :
    amplOps c (clean2 0xa457c2d7 d) 0 =
      some (.base (.adjustAllowance c (Word.toAddress (argWord d 0)) false
        (argWord d 1).toNat)) := by
  simp [amplOps, clean2, Abi.size_encodeCall, Abi.selectorOf_encodeCall, argWord,
    Abi.calldataload_encodeCall_0, Abi.calldataload_encodeCall_1, addrArg_ofAddress]

theorem ops_transferAllFrom (c : Address) (d : ByteArray) :
    amplOps c (cleanAA d) 0 = some (.base (.transferAllFrom c (Word.toAddress (argWord d 0))
      (Word.toAddress (argWord d 1)))) := by
  simp [amplOps, cleanAA, Abi.size_encodeCall, Abi.selectorOf_encodeCall, argWord,
    Abi.calldataload_encodeCall_0, Abi.calldataload_encodeCall_1, addrArg_ofAddress]

theorem ops_rebase (c : Address) {d : ByteArray} (hsel : Abi.selectorOf d = 0x7a43e23f)
    (h68 : 68 ≤ d.size) : amplOps c d 0 = some (.rebase c (argWord d 1).toInt) := by
  simp [amplOps, hsel, show ¬ d.size < 4 by omega, show ¬ d.size < 36 by omega,
    show ¬ d.size < 68 by omega]

theorem ops_renounce (c : Address) {d : ByteArray} (hsel : Abi.selectorOf d = 0x715018a6)
    (h4 : 4 ≤ d.size) : amplOps c d 0 = some (.renounceOwnership c) := by
  simp [amplOps, hsel, show ¬ d.size < 4 by omega]

/-! ## The theorem -/

/-- The dispatcher's selectors. -/
theorem sel_eq : sel = [0x3644e515, 0xe1b11da4, 0x78160376, 0x30adf81f, 0xdd62ed3e, 0x095ea7b3,
    0x70a08231, 0x313ce567, 0xa457c2d7, 0x39509351, 0xc4d66de8, 0x1624f6c6, 0x8f32d59b,
    0x8e27d7d7, 0x06fdde03, 0x7ecebe00, 0x8da5cb5b, 0xd505accf, 0x7a43e23f, 0x715018a6,
    0x1da24f3e, 0xb1bf962d, 0x8b5a6a08, 0x95d89b41, 0x18160ddd, 0xa9059cbb, 0xa3a7e7f3,
    0x84d4b410, 0x23b872dd, 0xf2fde38b] := by
  decide

section
variable {Act : Finset Address} {m : Machine}

/-- `MalformedSpec`'s frame-end condition for AMPL, with the recovery `r`. -/
abbrev Post (r : Machine → ℕ → Address) (Act : Finset Address) (m : Machine) :
    Machine → Outcome → Prop :=
  LPost amplAbs M amplOps amplOpAddrs (some r) Act m

/-- **The `permit` frames left open**: no value, all seven argument words (the decoder masks
`owner` and `spender` and `v`, and checks nothing else), calldata naming only actors. -/
def PermitResidue (r : Machine → ℕ → Address) : Prop :=
  ∀ Act m, Start AMPL.runtimeCode amplAbs M Act m →
    calldataAddrs m.frame.msg.data ⊆ Act → m.frame.msg.value = 0 →
    Abi.selectorOf m.frame.msg.data = 0xd505accf → 228 ≤ m.frame.msg.data.size →
    Halts m (Post r Act m)

theorem post_getter {r : Machine → ℕ → Address} (hS : Start AMPL.runtimeCode amplAbs M Act m)
    {sel q : Nat} (hge : (sel, q) ∈ getterEntries) (hsel : Abi.selectorOf m.frame.msg.data = sel)
    (h4 : 4 ≤ m.frame.msg.data.size) : Halts m (Post r Act m) :=
  lpost_unchanged (getter_halts hge m hS.fresh hsel h4 hS.size)

theorem value_toNat (h : m.frame.msg.value = 0) : m.frame.msg.value.toNat = 0 := by
  rw [h]; rfl

/-- A masked argument word names an actor. -/
theorem arg_mem {d : ByteArray} (hAct : calldataAddrs d ⊆ Act) {i : Nat}
    (h : 4 + 32 * i < d.size) : Word.toAddress (argWord d i) ∈ Act :=
  hAct (mem_calldataAddrs h)

end

/-- **AMPL with any calldata**, given the `permit` frames with no value and all their words
(`PermitResidue r`): every frame whose calldata names only actors fails, changes nothing, or
ends as an ERC-20 call (a `permit` with the recovery `r`) or an operation of `amplModel`, for
the actors; no entry point is excluded. -/
theorem ampl_malformed (r : Machine → ℕ → Address) (hres : PermitResidue r) :
    MalformedSpec AMPL.runtimeCode amplAbs M amplOps amplOpAddrs (some r) [] := by
  refine malformed_of fun Act m hS hAct _ => ?_
  by_cases hfb : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ sel
  · exact lpost_fallback fallback_spec hS hfb
  simp only [not_or, not_lt, not_not] at hfb
  obtain ⟨h4, hmem⟩ := hfb
  have hf := hS.fresh
  have hsz := hS.size
  by_cases hv0 : m.frame.msg.value = 0
  swap
  · exact lpost_fails (value_low m hf hv0)
  have hL : Live m.world m.frame.msg.currentTarget := live_of_wf (by
    rw [← pre_eq hS hv0]; exact hS.wf)
  have hA1 : ∀ {P : Address → Prop}, 68 ≤ m.frame.msg.data.size →
      P (Word.toAddress (argWord m.frame.msg.data 0)) →
      ∀ a ∈ [Word.toAddress (argWord m.frame.msg.data 0)], P a := by
    intro P _ h a ha
    simp only [List.mem_singleton] at ha
    exact ha ▸ h
  rw [sel_eq] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact post_getter hS (q := 1132) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 1754) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 1230) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 1094) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 1708) (by simp [getterEntries]) h h4
  · rcases approve_dirty m hf h h4 hsz with ⟨s, hst, hs, hg, hv, hsz'⟩ | hF
    · rw [hs] at hst
      exact lpost_call_dirty (calls_spec _) hS
        (dirtyRun (st := fun d => st2 d 648#256 157198259#256) (cl := clean2 0x095ea7b3) (k := 64) (s := [.top, .top, .const 648, .top])
          (fun d => by simp [clean2, Abi.selectorOf_encodeCall])
          (fun d => by simp [clean2, Abi.size_encodeCall]) (by norm_num) (fun d => st2_clean2 _ d _ _)
          approve_clean (by decide) (fun _ => ⟨trivial, trivial, rfl, trivial, trivial⟩) (by norm_num) hf hv hst hg)
        (encodes_approve _) trivial (hA1 hsz' (arg_mem hAct (i := 0) (by omega)))
    · exact lpost_fails hF
  · exact post_getter hS (q := 1184) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 1102) (by simp [getterEntries]) h h4
  · rcases decreaseAllowance_dirty m hf h h4 hsz with ⟨s, hst, hs, hg, hv, hsz'⟩ | hF
    · rw [hs] at hst
      refine lpost_op_dirty ops_spec hS
        (dirtyRun (st := fun d => st2 d 648#256 2757214935#256) (cl := clean2 0xa457c2d7) (k := 64) (s := [.top, .top, .const 648, .top])
          (fun d => by simp [clean2, Abi.selectorOf_encodeCall])
          (fun d => by simp [clean2, Abi.size_encodeCall]) (by norm_num) (fun d => st2_clean2 _ d _ _)
          decreaseAllowance_clean (by decide) (fun _ => ⟨trivial, trivial, rfl, trivial, trivial⟩) (by norm_num) hf hv hst hg)
        (by rw [value_toNat hv]; exact ops_dec _ _) ?_
      intro a ha
      simp only [amplOpAddrs, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha
      exact arg_mem hAct (i := 0) (by omega)
    · exact lpost_fails hF
  · rcases increaseAllowance_dirty m hf h h4 hsz with ⟨s, hst, hs, hg, hv, hsz'⟩ | hF
    · rw [hs] at hst
      refine lpost_op_dirty ops_spec hS
        (dirtyRun (st := fun d => st2 d 648#256 961581905#256) (cl := clean2 0x39509351) (k := 64) (s := [.top, .top, .const 648, .top])
          (fun d => by simp [clean2, Abi.selectorOf_encodeCall])
          (fun d => by simp [clean2, Abi.size_encodeCall]) (by norm_num) (fun d => st2_clean2 _ d _ _)
          increaseAllowance_clean (by decide) (fun _ => ⟨trivial, trivial, rfl, trivial, trivial⟩) (by norm_num) hf hv hst hg)
        (by rw [value_toNat hv]; exact ops_inc _ _) ?_
      intro a ha
      simp only [amplOpAddrs, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha
      exact arg_mem hAct (i := 0) (by omega)
    · exact lpost_fails hF
  · exact lpost_fails (init_addr_low m hf h h4 hsz hL hS.hasCode hS.codeBound)
  · exact lpost_fails (init_strings_low m hf h h4 hsz hL hS.hasCode hS.codeBound)
  · exact post_getter hS (q := 1439) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 1431) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 479) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 1273) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 1395) (by simp [getterEntries]) h h4
  · rcases permit_dirty m hf h h4 hsz with ⟨-, -, hv, h228⟩ | hF
    · exact hres Act m hS hAct hv h h228
    · exact lpost_fails hF
  · rcases rebase_dirty m hf h h4 hsz with ⟨-, -, hv, h68⟩ | hF
    · exact lpost_op ops_spec hS (by rw [value_toNat hv]; exact ops_rebase _ h h68)
        (fun a ha => by simp [amplOpAddrs] at ha)
    · exact lpost_fails hF
  · rcases value_dirty m hf with ⟨-, -, hv⟩ | hF
    · exact lpost_op ops_spec hS (by rw [value_toNat hv]; exact ops_renounce _ h h4)
        (fun a ha => by simp [amplOpAddrs] at ha)
    · exact lpost_fails hF
  · exact post_getter hS (q := 1002) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 1581) (by simp [getterEntries]) h h4
  · rcases setMonetaryPolicy_dirty m hf h h4 hsz with ⟨s, hst, hs, hg, hv, hsz'⟩ | hF
    · rw [hs] at hst
      refine lpost_op_dirty ops_spec hS
        (dirtyRun (st := fun d => st1 d 974#256 2337958408#256) (cl := clean1 0x8b5a6a08) (k := 32) (s := [.top, .const 974, .top])
          (fun d => by simp [clean1, Abi.selectorOf_encodeCall])
          (fun d => by simp [clean1, Abi.size_encodeCall]) (by norm_num) (fun d => st1_clean1 _ d _ _)
          setMonetaryPolicy_clean (by decide) (fun _ => ⟨trivial, rfl, trivial, trivial⟩) (by norm_num) hf hv hst hg)
        (by rw [value_toNat hv]; exact ops_setMP _ _) ?_
      intro a ha
      simp only [amplOpAddrs, List.mem_cons, List.not_mem_nil, or_false] at ha
    · exact lpost_fails hF
  · exact post_getter hS (q := 1447) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 976) (by simp [getterEntries]) h h4
  · rcases transfer_dirty m hf h h4 hsz with ⟨s, hst, hs, hg, hv, hsz'⟩ | hF
    · rw [hs] at hst
      exact lpost_call_dirty (calls_spec _) hS
        (dirtyRun (st := fun d => st2 d 648#256 2835717307#256) (cl := clean2 0xa9059cbb) (k := 64) (s := [.top, .top, .const 648, .top])
          (fun d => by simp [clean2, Abi.selectorOf_encodeCall])
          (fun d => by simp [clean2, Abi.size_encodeCall]) (by norm_num) (fun d => st2_clean2 _ d _ _)
          transfer_clean (by decide) (fun _ => ⟨trivial, trivial, rfl, trivial, trivial⟩) (by norm_num) hf hv hst hg)
        (encodes_transfer _) trivial (hA1 hsz' (arg_mem hAct (i := 0) (by omega)))
    · exact lpost_fails hF
  · rcases transferAll_dirty m hf h h4 hsz with ⟨s, hst, hs, hg, hv, hsz'⟩ | hF
    · rw [hs] at hst
      refine lpost_op_dirty ops_spec hS
        (dirtyRun (st := fun d => st1 d 648#256 2745690099#256) (cl := clean1 0xa3a7e7f3) (k := 32) (s := [.top, .const 648, .top])
          (fun d => by simp [clean1, Abi.selectorOf_encodeCall])
          (fun d => by simp [clean1, Abi.size_encodeCall]) (by norm_num) (fun d => st1_clean1 _ d _ _)
          transferAll_clean (by decide) (fun _ => ⟨trivial, rfl, trivial, trivial⟩) (by norm_num) hf hv hst hg)
        (by rw [value_toNat hv]; exact ops_transferAll _ _) ?_
      intro a ha
      simp only [amplOpAddrs, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha
      exact arg_mem hAct (i := 0) (by omega)
    · exact lpost_fails hF
  · rcases transferAllFrom_dirty m hf h h4 hsz with ⟨s, hst, hs, hg, hv, hsz'⟩ | hF
    · rw [hs] at hst
      refine lpost_op_dirty ops_spec hS
        (dirtyRun (st := stAA) (cl := cleanAA) (k := 64) (s := [.top, .top, .const 648, .top])
          (fun d => by simp [cleanAA, Abi.selectorOf_encodeCall])
          (fun d => by simp [cleanAA, Abi.size_encodeCall]) (by norm_num) stAA_cleanAA
          transferAllFrom_clean (by decide) (fun _ => ⟨trivial, trivial, rfl, trivial, trivial⟩) (by norm_num) hf hv hst hg)
        (by rw [value_toNat hv]; exact ops_transferAllFrom _ _) ?_
      intro a ha
      simp only [amplOpAddrs, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact arg_mem hAct (i := 0) (by omega)
      · exact arg_mem hAct (i := 1) (by omega)
    · exact lpost_fails hF
  · rcases transferFrom_dirty m hf h h4 hsz with ⟨s, hst, hs, hg, hv, hsz'⟩ | hF
    · rw [hs] at hst
      refine lpost_call_dirty (calls_spec _) hS
        (dirtyRun (st := st3) (cl := clean3) (k := 96) (s := [.top, .top, .top, .const 648, .top])
          (fun d => by simp [clean3, Abi.selectorOf_encodeCall])
          (fun d => by simp [clean3, Abi.size_encodeCall]) (by norm_num) st3_clean3
          transferFrom_clean (by decide) (fun _ => ⟨trivial, trivial, trivial, rfl, trivial, trivial⟩) (by norm_num) hf hv hst hg)
        (encodes_transferFrom _) trivial ?_
      intro a ha
      simp only [Call.addrs, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact arg_mem hAct (i := 0) (by omega)
      · exact arg_mem hAct (i := 1) (by omega)
    · exact lpost_fails hF
  · rcases transferOwnership_dirty m hf h h4 hsz with ⟨s, hst, hs, hg, hv, hsz'⟩ | hF
    · rw [hs] at hst
      refine lpost_op_dirty ops_spec hS
        (dirtyRun (st := fun d => st1 d 974#256 4076725131#256) (cl := clean1 0xf2fde38b) (k := 32) (s := [.top, .const 974, .top])
          (fun d => by simp [clean1, Abi.selectorOf_encodeCall])
          (fun d => by simp [clean1, Abi.size_encodeCall]) (by norm_num) (fun d => st1_clean1 _ d _ _)
          transferOwnership_clean (by decide) (fun _ => ⟨trivial, rfl, trivial, trivial⟩) (by norm_num) hf hv hst hg)
        (by rw [value_toNat hv]; exact ops_transferOwnership _ _) ?_
      intro a ha
      simp only [amplOpAddrs, List.mem_cons, List.not_mem_nil, or_false] at ha
    · exact lpost_fails hF

end Verified.WeirdERC20.AMPL.Spec.Malformed
