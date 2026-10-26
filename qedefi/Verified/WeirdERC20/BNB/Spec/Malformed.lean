import Verified.WeirdERC20.BNB.Spec.Spec
import Verified.WeirdERC20.BNB.Spec.MalformedCert
import Verified.WeirdERC20.BNB.Spec.MalformedPrefix
import Verified.WeirdERC20.Common.Post

/-!
# BNB with any calldata: `MalformedSpec` except `withdrawEther`

**`bnb_malformed`**: in every frame of the mainnet BNB code (solc 0.4.12), with any calldata
naming only actors, any value and any gas, except `withdrawEther(uint256)` (`bnbExcl`: it sends
the token's ether to the owner, which no model action describes), the frame fails, changes
nothing, or ends as an ERC-20 call or an operation of `bnbModel`. By selector:

* calldata shorter than a selector or an unknown selector: `fallback_spec` (the payable
  fallback keeps the ether);
* the eight getters change nothing, whatever their arguments (`getter_halts`);
* `transfer`, `approve`, `transferFrom`, `burn`, `freeze`, `unfreeze`: with value they revert;
  otherwise solc 0.4's decoder reads each argument word zero-padded and masks each `address`
  word to its low 160 bits, so the frame runs as the frame whose calldata is the ABI encoding of
  the call with these words (`Verified.WeirdERC20.Common.transport`), and `calls_spec`/`ops_spec`
  apply to that call. Its accounts are actors (masked words of the calldata, `calldataAddrs`),
  except a missing recipient (`0`), with which `transfer`/`transferFrom` revert, and a missing
  spender, with which `approve` reverts (its value is then `0`).

**`bnb_complete`**: `ERC20Spec.Complete` (BNB has no `permit`) with `excl = bnbExcl`.
-/

set_option linter.unusedSimpArgs false

namespace Verified.WeirdERC20.BNB.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.BNB.Contracts
open Verified.WeirdERC20.BNB.Spec Verified.WeirdERC20.Common Verified.Solady.Spec.AnyGas
open Verified.Common.Malformed (Unchanged halts_pure inCert_top)
open EvmLogic.AbsInt

/-- The entry points `bnbModel` does not describe: `withdrawEther(uint256)`. -/
def bnbExcl : List Nat := [0x3bed33ce]

/-! ## The getters -/

/-- The dispatcher's run to a getter's dispatch target. -/
def AtGetter (m : Machine) (q : Nat) (sel : Nat) (s : Machine) : Prop :=
  s.frame.pc = q ∧ s.frame.stack = [BitVec.ofNat 256 sel] ∧ s.frame.code = BNB.runtimeCode ∧
    Unchanged m s

set_option maxHeartbeats 0 in
theorem getter_dispatch {sel q : Nat} (hge : (sel, q) ∈ getterEntries) (m : Machine)
    (hf : Fresh BNB.runtimeCode m) (hsel : Abi.selectorOf m.frame.msg.data = sel)
    (h4 : 4 ≤ m.frame.msg.data.size) (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (AtGetter m q sel) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  simp only [getterEntries, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hge
  rcases hge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    solady_fresh_intro
    hwp_steps stop_at [0x00e2, 0x01cb, 0x026d, 0x0335, 0x0382, 0x03d7, 0x04a8, 0x0530] [hsel', hz]
    exact WP.ret ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **A getter fails or changes nothing**, with any value, arguments and gas. -/
theorem getter_halts {sel q : Nat} (hge : (sel, q) ∈ getterEntries) (m : Machine)
    (hf : Fresh BNB.runtimeCode m) (hsel : Abi.selectorOf m.frame.msg.data = sel)
    (h4 : 4 ≤ m.frame.msg.data.size) (hsz : m.frame.msg.data.size < 2 ^ 64) :
    Halts m (fun mf o => Fails o ∨ Unchanged m mf) := by
  have hin : InT bnbGetters q [.top] :=
    bnbGetters_seed (List.mem_map.2 ⟨(sel, q), hge, rfl⟩)
  rcases getter_dispatch hge m hf hsel h4 hsz with ⟨s, hst, hpc, hs, hcode, h1, h2, h3⟩ | h
  · refine Halts.of_steps hst ((halts_pure bnbGetters_cert bnbGetters_pure s hcode
      (inCert_top hin hpc hs)).mono fun mf _ _ ⟨g1, g2, g3⟩ => .inr ?_)
    exact ⟨g1.trans h1, g2.trans h2, g3.trans h3⟩
  · exact h.mono fun _ _ _ h => .inl h

/-! ## The clean calls -/

/-- The clean calldata of a body taking one word. -/
def clean1 (sel : Nat) (d : ByteArray) : ByteArray := Abi.encodeCall sel [argWord d 0]

/-- The clean calldata of a body taking an `address` and a word. -/
def clean2 (sel : Nat) (d : ByteArray) : ByteArray :=
  Abi.encodeCall sel [Word.ofAddress (Word.toAddress (argWord d 0)), argWord d 1]

/-- The clean calldata of `transferFrom`. -/
def clean3 (d : ByteArray) : ByteArray :=
  Abi.encodeCall 0x23b872dd [Word.ofAddress (Word.toAddress (argWord d 0)),
    Word.ofAddress (Word.toAddress (argWord d 1)), argWord d 2]

theorem st1_clean1 (sel : Nat) (d : ByteArray) (ret selw : Word) :
    st1 (clean1 sel d) ret selw = st1 d ret selw := by
  simp only [st1, clean1, argWord, Nat.reduceMul, Nat.reduceAdd, Abi.calldataload_encodeCall_0]

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

/-- What `bnbOps` decodes from the clean calldata of a one-word entry point. -/
theorem bnbOps_clean1 (c : Address) (sel : Nat) (d : ByteArray) :
    bnbOps c (clean1 sel d) 0 =
      if sel % 2 ^ 32 = 0x42966c68 then some (.burn c c (argWord d 0).toNat)
      else if sel % 2 ^ 32 = 0xd7a78db8 then some (.freeze c (argWord d 0).toNat)
      else if sel % 2 ^ 32 = 0x6623fc46 then some (.unfreeze c (argWord d 0).toNat)
      else none := by
  simp only [bnbOps, clean1, Abi.size_encodeCall, Abi.selectorOf_encodeCall, argWord,
    Nat.reduceMul, Nat.reduceAdd, Abi.calldataload_encodeCall_0, List.length_cons,
    List.length_nil]
  simp

/-! ## Dirty frames -/

section
variable {Act : Finset Address} {m : Machine}

/-- **A dirty frame is a `DirtyRun`**: the dispatcher reaches the body entry for it (`hst`)
and for its clean counterpart (`hclean`, the same stack), and the body is a data-safe region. -/
theorem dirtyRun {st : ByteArray → List Word} {pc c sel : Nat} {D' : ByteArray}
    (hclean : ∀ x : Machine, Fresh BNB.runtimeCode x → Abi.selectorOf x.frame.msg.data = sel →
      4 ≤ x.frame.msg.data.size → x.frame.msg.data.size < 2 ^ 64 →
      x.frame.msg.value = 0 → 10000 ≤ x.frame.gasLeft →
      WP x (fun s => s = entry mem60 x pc (st x.frame.msg.data) c) (fun _ _ => False))
    (hD' : st D' = st m.frame.msg.data) (hc : c ≤ 10000)
    (hsel : Abi.selectorOf D' = sel) (hD4 : 4 ≤ D'.size) (hD : D'.size < 2 ^ 64)
    (hf : Fresh BNB.runtimeCode m) (hval : m.frame.msg.value = 0) {g : Nat}
    (hst : Steps m (entryG mem60 m pc (st m.frame.msg.data) g)) (hg : g ≤ m.frame.gasLeft)
    {s : AStack} (hseed : (pc, s) ∈ bodySeeds)
    (hstk : StackOk (fun _ => 0) s (st m.frame.msg.data)) :
    DirtyRun BNB.runtimeCode m D' := by
  refine dirtyRun_of bnbBodies_cert bnbBodies_safe hf hD hst hg hc ?_
    ⟨s, bnbBodies_seed hseed, hstk⟩
  have h := hclean (clean D' (m.frame.gasLeft + 10000) m)
    (fresh_clean hf (G := m.frame.gasLeft + 10000) (by omega) D') hsel hD4 hD hval
    (by simp [clean, setData, Verified.OpenZeppelin.ERC20.Spec.high,
      Verified.OpenZeppelin.ERC20.Spec.hi, Verified.OpenZeppelin.ERC20.Spec.setKind,
      EvmLogic.Program.Nested.bump])
  rw [show (clean D' (m.frame.gasLeft + 10000) m).frame.msg.data = D' from rfl, hD'] at h
  exact h

/-- `MalformedSpec`'s frame-end condition for BNB. -/
abbrev Post (Act : Finset Address) (m : Machine) : Machine → Outcome → Prop :=
  LPost bnbAbs M bnbOps bnbOpAddrs none Act m

theorem value_toNat (h : m.frame.msg.value = 0) : m.frame.msg.value.toNat = 0 := by
  rw [h]; rfl

/-- A masked argument word inside the calldata names an actor. -/
theorem arg_mem {d : ByteArray} (hAct : calldataAddrs d ⊆ Act) {i : Nat}
    (h : 4 + 32 * i < d.size) : Word.toAddress (argWord d i) ∈ Act :=
  hAct (mem_calldataAddrs h)

theorem post_getter (hS : Start BNB.runtimeCode bnbAbs M Act m) {sel q : Nat}
    (hge : (sel, q) ∈ getterEntries) (hsel : Abi.selectorOf m.frame.msg.data = sel)
    (h4 : 4 ≤ m.frame.msg.data.size) : Halts m (Post Act m) :=
  lpost_unchanged (getter_halts hge m hS.fresh hsel h4 hS.size)

theorem post_short (h : WP m (fun _ => False) (fun _ o => Fails o)) : Halts m (Post Act m) :=
  lpost_fails (WP.halts_of_false h)

/-- A one-word operation (`burn`, `freeze`, `unfreeze`). -/
theorem post_op1 (hS : Start BNB.runtimeCode bnbAbs M Act m) {sel pc c : Nat} {ret selw : Word}
    (hsel128 : sel < 2 ^ 32)
    (hclean : ∀ x : Machine, Fresh BNB.runtimeCode x → Abi.selectorOf x.frame.msg.data = sel →
      4 ≤ x.frame.msg.data.size → x.frame.msg.data.size < 2 ^ 64 →
      x.frame.msg.value = 0 → 10000 ≤ x.frame.gasLeft →
      WP x (fun s => s = entry mem60 x pc (st1 x.frame.msg.data ret selw) c) (fun _ _ => False))
    (hdirty : WP m (fun s => s = entryG mem60 m pc (st1 m.frame.msg.data ret selw)
      s.frame.gasLeft ∧ s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0)
      (fun _ o => Fails o))
    (hc : c ≤ 10000) (hseed : (pc, [.top, .const ret.toNat, .top]) ∈ bodySeeds) {e : Variant.Op Address}
    (hops : bnbOps m.frame.msg.caller (clean1 sel m.frame.msg.data) 0 = some e)
    (hA : ∀ a ∈ bnbOpAddrs e, a ∈ Act) : Halts m (Post Act m) := by
  rcases hdirty with ⟨s, hst, hs, hg, hv⟩ | hF
  · rw [hs] at hst
    have hD : (clean1 sel m.frame.msg.data).size = 36 := by simp [clean1, Abi.size_encodeCall]
    refine lpost_op_dirty ops_spec hS
      (dirtyRun (st := fun d => st1 d ret selw) (sel := sel) hclean (st1_clean1 _ _ _ _) hc
        (by rw [clean1, Abi.selectorOf_encodeCall, Nat.mod_eq_of_lt hsel128]) (by omega) (by omega)
        hS.fresh hv hst hg hseed ⟨trivial, rfl, trivial, trivial⟩) ?_ hA
    rw [value_toNat hv]; exact hops
  · exact lpost_fails hF

end

/-! ## The theorems -/

/-- The dispatcher's selectors. -/
theorem sel_eq : sel = [0xdd62ed3e, 0x095ea7b3, 0x70a08231, 0x42966c68, 0x313ce567, 0xd7a78db8,
    0xcd4217c1, 0x06fdde03, 0x8da5cb5b, 0x95d89b41, 0x18160ddd, 0xa9059cbb, 0x23b872dd,
    0x6623fc46, 0x3bed33ce] := by
  decide

/-- **BNB with any calldata, except `withdrawEther`**: every frame whose calldata names only
actors fails, changes nothing, or ends as an ERC-20 call or an operation of `bnbModel` for the
actors. -/
theorem bnb_malformed : MalformedSpec BNB.runtimeCode bnbAbs M bnbOps bnbOpAddrs none bnbExcl := by
  refine malformed_of fun Act m hS hAct hex => ?_
  by_cases hfb : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ sel
  · exact lpost_fallback fallback_spec hS hfb
  simp only [not_or, not_lt, not_not] at hfb
  obtain ⟨h4, hmem⟩ := hfb
  rw [sel_eq] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  have hf := hS.fresh
  have hsz := hS.size
  have hc := hS.caller
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact post_getter hS (q := 0x0530) (by simp [getterEntries]) h h4
  · -- approve
    by_cases hs : m.frame.msg.data.size ≤ 36
    · exact post_short (approve_short m hf h h4 hs hsz)
    rcases approve_dirty m hf h h4 hsz with ⟨s, hst, hsE, hg, hv⟩ | hF
    · rw [hsE] at hst
      have hD : (clean2 0x095ea7b3 m.frame.msg.data).size = 68 := by
        simp [clean2, Abi.size_encodeCall]
      refine lpost_call_dirty (calls_spec _) hS
        (dirtyRun (st := fun d => st2 d 433#256 157198259#256) approve_clean
          (st2_clean2 _ _ _ _) (by norm_num) (by simp [clean2, Abi.selectorOf_encodeCall])
          (by omega) (by omega) hf hv hst hg (s := [.top, .top, .const 433, .top])
          (by decide) ⟨trivial, trivial, rfl, trivial, trivial⟩)
        (encodes_approve _) trivial ?_
      intro a ha
      simp only [Call.addrs, List.mem_singleton] at ha
      exact ha ▸ arg_mem hAct (i := 0) (by omega)
    · exact lpost_fails hF
  · exact post_getter hS (q := 0x0335) (by simp [getterEntries]) h h4
  · exact post_op1 hS (e := .burn m.frame.msg.caller m.frame.msg.caller (argWord m.frame.msg.data 0).toNat)
      (by norm_num) burn_clean (burn_dirty m hf h h4 hsz) (by norm_num)
      (by decide) (by rw [bnbOps_clean1]; simp)
      (by intro a ha; simp only [bnbOpAddrs, List.mem_singleton] at ha; exact ha ▸ hc)
  · exact post_getter hS (q := 0x026d) (by simp [getterEntries]) h h4
  · exact post_op1 hS (e := .freeze m.frame.msg.caller (argWord m.frame.msg.data 0).toNat)
      (by norm_num) freeze_clean (freeze_dirty m hf h h4 hsz) (by norm_num)
      (by decide) (by rw [bnbOps_clean1]; simp) (by intro a ha; simp [bnbOpAddrs] at ha)
  · exact post_getter hS (q := 0x04a8) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 0x00e2) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 0x0382) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 0x03d7) (by simp [getterEntries]) h h4
  · exact post_getter hS (q := 0x01cb) (by simp [getterEntries]) h h4
  · -- transfer
    by_cases hs : m.frame.msg.data.size = 4
    · exact post_short (transfer_short m hf h h4 (by omega) hsz)
    rcases transfer_dirty m hf h h4 hsz with ⟨s, hst, hsE, hg, hv⟩ | hF
    · rw [hsE] at hst
      have hD : (clean2 0xa9059cbb m.frame.msg.data).size = 68 := by
        simp [clean2, Abi.size_encodeCall]
      refine lpost_call_dirty (calls_spec _) hS
        (dirtyRun (st := fun d => st2 d 1190#256 2835717307#256) transfer_clean
          (st2_clean2 _ _ _ _) (by norm_num) (by simp [clean2, Abi.selectorOf_encodeCall])
          (by omega) (by omega) hf hv hst hg (s := [.top, .top, .const 1190, .top])
          (by decide) ⟨trivial, trivial, rfl, trivial, trivial⟩)
        (encodes_transfer _) trivial ?_
      intro a ha
      simp only [Call.addrs, List.mem_singleton] at ha
      exact ha ▸ arg_mem hAct (i := 0) (by omega)
    · exact lpost_fails hF
  · -- transferFrom
    by_cases hs : m.frame.msg.data.size ≤ 36
    · exact post_short (transferFrom_short m hf h h4 hs hsz)
    rcases transferFrom_dirty m hf h h4 hsz with ⟨s, hst, hsE, hg, hv⟩ | hF
    · rw [hsE] at hst
      have hD : (clean3 m.frame.msg.data).size = 100 := by simp [clean3, Abi.size_encodeCall]
      refine lpost_call_dirty (calls_spec _) hS
        (dirtyRun (st := fun d => st3 d 595#256 599290589#256) transferFrom_clean
          (st3_clean3 _ _ _) (by norm_num) (by simp [clean3, Abi.selectorOf_encodeCall])
          (by omega) (by omega) hf hv hst hg (s := [.top, .top, .top, .const 595, .top])
          (by decide) ⟨trivial, trivial, trivial, rfl, trivial, trivial⟩)
        (encodes_transferFrom _) trivial ?_
      intro a ha
      simp only [Call.addrs, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact arg_mem hAct (i := 0) (by omega)
      · exact arg_mem hAct (i := 1) (by omega)
    · exact lpost_fails hF
  · exact post_op1 hS (e := .unfreeze m.frame.msg.caller (argWord m.frame.msg.data 0).toNat)
      (by norm_num) unfreeze_clean (unfreeze_dirty m hf h h4 hsz) (by norm_num)
      (by decide) (by rw [bnbOps_clean1]; simp) (by intro a ha; simp [bnbOpAddrs] at ha)
  · exact absurd ⟨h4, by rw [h]; simp [bnbExcl]⟩ hex

/-- **The complete spec of BNB**: `ERC20Spec` and `MalformedSpec` except `withdrawEther` (no
`permit`). -/
theorem bnb_complete :
    ERC20Spec.Complete BNB.runtimeCode bnbAbs M g₀ sel bnbOps bnbOpAddrs none bnbExcl :=
  ⟨bnb_spec, fun _ _ h => (by cases h), bnb_malformed⟩

end Verified.WeirdERC20.BNB.Spec.Malformed
