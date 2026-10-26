import QEDefi.ERC20.Spec.Bytecode
import EvmLogic.Program.Reentrancy.Halts
import Verified.Common.Malformed.Region
import Verified.Solmate.ERC4626.UnknownSelectors

/-!
# `MalformedSpec` from the exact obligations

`MalPost` is the frame-end condition of `MalformedSpec`. Each way a frame can end that the
spec admits has its rule here, for any token:

* `post_fails`, `post_reverts`: the frame fails;
* `post_unchanged`: the frame changes no world, transient storage or logs (a getter, through
  `halts_pure`);
* `post_call`: the calldata **is** the ABI encoding of an ERC-20 call (`Call.Encodes`), so
  `CallSpec` applies, for the actors extended by the call's accounts whenever their hash
  hypotheses hold (the frame halts in any case, `halts_any`);
* `post_fallback`: short calldata or an unknown selector, through `FallbackSpec`;
* `post_op`: calldata the decoder `ops` accepts, through `OpSpec`;
* `post_permit`: a `permit` with the token's own recovery, through `PermitSpec`
  (`post_permit_of`: through any proof for the frame).

**The reduction** of malformed calldata to these rules: the decoders of solc ≥ 0.8 revert
unless the calldata holds every argument word and the `address` words are clean (`CleanAddr`),
and then the calldata is the encoding of a call (`encodes_transfer`, `encodes_transferFrom`,
`encodes_approve`, `args_permit`).
-/

namespace Verified.Common.Malformed
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Solidity EvmLogic.Program.Reentrancy
open QEDefi.ERC20 QEDefi.ERC20.Spec
open Verified.Solmate.ERC4626 (argWord CleanAddr)

variable {σ E : Type} {code : ByteArray} {abs : TokenAbs σ} {M : TokenModel σ Address E}
  {ops : Address → ByteArray → ℕ → Option E} {opAddrs : E → List Address}
  {rec : Option (Machine → ℕ → Address)} {Act : Finset Address} {m : Machine}

/-- **The frame-end condition of `MalformedSpec`**, for the actors `Act` and the frame `m`. -/
def MalPost (abs : TokenAbs σ) (M : TokenModel σ Address E)
    (ops : Address → ByteArray → ℕ → Option E) (opAddrs : E → List Address)
    (rec : Option (Machine → ℕ → Address)) (Act : Finset Address) (m : Machine) :
    Machine → Outcome → Prop := fun mf o =>
  Fails o ∨
  (mf.world = m.world ∧ mf.transient = m.transient ∧ mf.frame.sub.logs = m.frame.sub.logs) ∨
  (∃ c, Explains rec m c ∧
    let Act' := Act ∪ c.addrs.toFinset
    (abs.Sound m.ctx.crypto Act' → M.wf (pre abs Act' m) →
      Matches abs Act' m mf o (M.events (pre abs Act' m) m.frame.msg.caller c)
        (M.call (pre abs Act' m) m.frame.msg.caller c))) ∨
  (∃ d e, ops m.frame.msg.caller d m.frame.msg.value.toNat = some e ∧
    let Act' := Act ∪ (opAddrs e).toFinset
    (abs.Sound m.ctx.crypto Act' → M.wf (pre abs Act' m) →
      (∃ s', M.op (pre abs Act' m) e = some s') ∧ OpMatches abs M Act' e m mf o))

/-- `MalformedSpec` is `MalPost` in every starting frame. -/
theorem malformedSpec_of
    (h : ∀ Act m, Start code abs M Act m → Halts m (MalPost abs M ops opAddrs rec Act m)) :
    MalformedSpec code abs M ops opAddrs rec := h

/-! ## The rules -/

theorem post_fails (h : Halts m fun _ o => Fails o) :
    Halts m (MalPost abs M ops opAddrs rec Act m) :=
  h.mono fun _ _ _ h => .inl h

theorem post_reverts (h : Halts m fun _ o => ∃ out, o = .revert out) :
    Halts m (MalPost abs M ops opAddrs rec Act m) :=
  h.mono fun _ _ _ ⟨_, ho⟩ => .inl (by rw [ho]; trivial)

theorem post_unchanged (h : Halts m fun mf _ => Unchanged m mf) :
    Halts m (MalPost abs M ops opAddrs rec Act m) :=
  h.mono fun _ _ _ h => .inr (.inl h)

/-- `Start` for more actors, given their hash hypotheses and well-formedness. -/
theorem start_extend (hS : Start code abs M Act m) (A : Finset Address)
    (hs : abs.Sound m.ctx.crypto (Act ∪ A)) (hw : M.wf (pre abs (Act ∪ A) m)) :
    Start code abs M (Act ∪ A) m :=
  ⟨hS.fresh, hS.launched, hS.value, hS.precompiles, hS.size,
    Finset.mem_union_left _ hS.caller, hs, hw, hS.hasCode⟩

/-- **An encoded ERC-20 call** ends as `CallSpec` says, for the actors and its accounts. -/
theorem post_call {g₀ : Nat} {c : Call Address} (hcs : CallSpec code abs M g₀ c)
    (hS : Start code abs M Act m) (henc : c.Encodes m.frame.msg.data) (hex : Explains rec m c) :
    Halts m (MalPost abs M ops opAddrs rec Act m) := by
  by_cases h : abs.Sound m.ctx.crypto (Act ∪ c.addrs.toFinset) ∧
      M.wf (pre abs (Act ∪ c.addrs.toFinset) m)
  · refine (hcs _ m (start_extend hS _ h.1 h.2) henc fun a ha =>
      Finset.mem_union_right _ (List.mem_toFinset.2 ha)).mono fun mf o _ hp => ?_
    rcases hp with hm | ⟨hf, -⟩
    · exact .inr (.inr (.inl ⟨c, hex, fun _ _ => hm⟩))
    · exact .inl hf
  · exact (halts_any hS.precompiles).mono fun _ _ _ _ =>
      .inr (.inr (.inl ⟨c, hex, fun hs hw => absurd ⟨hs, hw⟩ h⟩))

/-- **Short calldata or an unknown selector** ends as `FallbackSpec` says. -/
theorem post_fallback {g₀ : Nat} {sel : List Nat} (hfs : FallbackSpec code abs M g₀ sel)
    (hS : Start code abs M Act m)
    (hsel : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ sel) :
    Halts m (MalPost abs M ops opAddrs rec Act m) := by
  have hA : Act ∪ (Call.other (A := Address) m.frame.msg.value.toNat).addrs.toFinset = Act := by
    simp [Call.addrs]
  refine (hfs Act m hS hsel).mono fun mf o _ hp => ?_
  rcases hp with hm | ⟨hf, -⟩
  · refine .inr (.inr (.inl ⟨.other m.frame.msg.value.toNat, trivial, ?_⟩))
    dsimp only
    rw [hA]
    exact fun _ _ => hm
  · exact .inl hf

/-- **Calldata the decoder accepts** ends as `OpSpec` says, for the actors and the
operation's accounts. -/
theorem post_op {g₀ : Nat} (hos : OpSpec code abs M g₀ ops opAddrs)
    (hS : Start code abs M Act m) {e : E}
    (hops : ops m.frame.msg.caller m.frame.msg.data m.frame.msg.value.toNat = some e) :
    Halts m (MalPost abs M ops opAddrs rec Act m) := by
  by_cases h : abs.Sound m.ctx.crypto (Act ∪ (opAddrs e).toFinset) ∧
      M.wf (pre abs (Act ∪ (opAddrs e).toFinset) m)
  · by_cases hsome : ∃ s', M.op (pre abs (Act ∪ (opAddrs e).toFinset) m) e = some s'
    · refine (hos _ m e (start_extend hS _ h.1 h.2) hops fun a ha =>
        Finset.mem_union_right _ (List.mem_toFinset.2 ha)).mono fun mf o _ hp => ?_
      rcases hp with hm | ⟨hf, -⟩
      · exact .inr (.inr (.inr ⟨_, e, hops, fun _ _ => ⟨hsome, hm⟩⟩))
      · exact .inl hf
    · refine (hos _ m e (start_extend hS _ h.1 h.2) hops fun a ha =>
        Finset.mem_union_right _ (List.mem_toFinset.2 ha)).mono fun mf o _ hp => ?_
      rcases hp with hm | ⟨hf, -⟩
      · left
        unfold OpMatches at hm
        split at hm
        · rename_i s' hs'
          exact absurd ⟨s', hs'⟩ hsome
        · exact hm
      · exact .inl hf
  · exact (halts_any hS.precompiles).mono fun _ _ _ _ =>
      .inr (.inr (.inr ⟨_, e, hops, fun hs hw => absurd ⟨hs, hw⟩ h⟩))

/-- **A `permit` frame that ends as the model's `permit` with the token's own recovery** (or
fails) for every set of actors containing its accounts. -/
theorem post_permit_of {r : Machine → ℕ → Address} (hrec : rec = some r)
    (hS : Start code abs M Act m) {o sp : Address} {v : ℕ} {live : Bool}
    (h : ∀ Act', Start code abs M Act' m → o ∈ Act' → sp ∈ Act' →
      Halts m fun mf out =>
        Matches abs Act' m mf out
          (M.events (pre abs Act' m) m.frame.msg.caller (.permit o sp v live (r m)))
          (M.call (pre abs Act' m) m.frame.msg.caller (.permit o sp v live (r m))) ∨ Fails out) :
    Halts m (MalPost abs M ops opAddrs rec Act m) := by
  let c : Call Address := .permit o sp v live (r m)
  have hex : Explains rec m c := ⟨r, hrec, fun _ => rfl⟩
  by_cases hA : abs.Sound m.ctx.crypto (Act ∪ c.addrs.toFinset) ∧
      M.wf (pre abs (Act ∪ c.addrs.toFinset) m)
  · refine (h _ (start_extend hS _ hA.1 hA.2)
      (Finset.mem_union_right _ (List.mem_toFinset.2 (by simp [c, Call.addrs])))
      (Finset.mem_union_right _ (List.mem_toFinset.2 (by simp [c, Call.addrs])))).mono
      fun mf out _ hp => ?_
    rcases hp with hm | hf
    · exact .inr (.inr (.inl ⟨c, hex, fun _ _ => hm⟩))
    · exact .inl hf
  · exact (halts_any hS.precompiles).mono fun _ _ _ _ =>
      .inr (.inr (.inl ⟨c, hex, fun hs hw => absurd ⟨hs, hw⟩ hA⟩))

/-- **A `permit` with ABI arguments**, when `ecrecover` runs the precompile and the frame has
less than `2⁶⁴` gas, ends as `PermitSpec` says, with the token's own recovery. -/
theorem post_permit {gp : Machine → Nat} {r : Machine → ℕ → Address}
    (hps : PermitSpec code abs M gp r) (hrec : rec = some r) (hS : Start code abs M Act m)
    {o sp : Address} {v dl pv pr ps : Word}
    (hargs : Args m.frame.msg.data 0xd505accf
      [Word.ofAddress o, Word.ofAddress sp, v, dl, pv, pr, ps])
    (hE : EcrecoverPlain m) (hg : m.frame.gasLeft < 2 ^ 64) :
    Halts m (MalPost abs M ops opAddrs rec Act m) :=
  post_permit_of hrec hS fun _ hS' ho hsp =>
    (hps _ m o sp v dl pv pr ps hS' ho hsp hE hg hargs).mono fun _ _ _ hp =>
      hp.imp_right fun h => h.1

/-! ## Clean arguments are an encoding -/

theorem ofAddress_toAddress_of_clean {w : Word} (h : w &&& addressMask = w) :
    Word.ofAddress (Word.toAddress w) = w := by
  apply BitVec.eq_of_toNat_eq
  have h' := congrArg BitVec.toNat h
  simp only [addressMask, BitVec.toNat_and, BitVec.toNat_ofNat] at h'
  rw [Nat.mod_eq_of_lt (by decide : 2 ^ 160 - 1 < 2 ^ 256), Nat.and_two_pow_sub_one_eq_mod] at h'
  simp only [Word.ofAddress, Word.toAddress, BitVec.toNat_setWidth]
  have hw := w.isLt
  rw [Nat.mod_eq_of_lt (by have := Nat.mod_lt w.toNat (by decide : 0 < 2 ^ 160); omega)]
  exact h'

theorem clean_ofAddress {d : ByteArray} {j : Nat} (h : CleanAddr d j) :
    Word.ofAddress (Word.toAddress (argWord d j)) = argWord d j :=
  ofAddress_toAddress_of_clean h

theorem word_toNat_self (w : Word) : word w.toNat = w := by
  simp [word]

/-- Calldata with selector `sel` holding the argument words `ws`. -/
theorem args_of {d : ByteArray} {sel : Nat} {ws : List Word} (hsel : Abi.selectorOf d = sel)
    (hsize : 4 + 32 * ws.length ≤ d.size) (hw : ∀ i (h : i < ws.length), argWord d i = ws[i]) :
    Args d sel ws :=
  ⟨hsel, hsize, hw⟩

/-- **`transfer` with all its words and a clean recipient is an encoded call.** -/
theorem encodes_transfer {d : ByteArray} (hsel : Abi.selectorOf d = 0xa9059cbb)
    (hsize : 68 ≤ d.size) (h0 : CleanAddr d 0) :
    (Call.transfer (Word.toAddress (argWord d 0)) (argWord d 1).toNat).Encodes d := by
  refine ⟨(argWord d 1).isLt, args_of hsel (by simpa using hsize) fun i hi => ?_⟩
  simp only [List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · exact (clean_ofAddress h0).symm
  · exact (word_toNat_self _).symm

/-- **`approve` with all its words and a clean spender is an encoded call.** -/
theorem encodes_approve {d : ByteArray} (hsel : Abi.selectorOf d = 0x095ea7b3)
    (hsize : 68 ≤ d.size) (h0 : CleanAddr d 0) :
    (Call.approve (Word.toAddress (argWord d 0)) (argWord d 1).toNat).Encodes d := by
  refine ⟨(argWord d 1).isLt, args_of hsel (by simpa using hsize) fun i hi => ?_⟩
  simp only [List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · exact (clean_ofAddress h0).symm
  · exact (word_toNat_self _).symm

/-- **`transferFrom` with all its words and clean accounts is an encoded call.** -/
theorem encodes_transferFrom {d : ByteArray} (hsel : Abi.selectorOf d = 0x23b872dd)
    (hsize : 100 ≤ d.size) (h0 : CleanAddr d 0) (h1 : CleanAddr d 1) :
    (Call.transferFrom (Word.toAddress (argWord d 0)) (Word.toAddress (argWord d 1))
      (argWord d 2).toNat).Encodes d := by
  refine ⟨(argWord d 2).isLt, args_of hsel (by simpa using hsize) fun i hi => ?_⟩
  simp only [List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  · exact (clean_ofAddress h0).symm
  · exact (clean_ofAddress h1).symm
  · exact (word_toNat_self _).symm

/-- **`permit` with all its words and clean accounts** has ABI arguments. -/
theorem args_permit {d : ByteArray} (hsel : Abi.selectorOf d = 0xd505accf)
    (hsize : 228 ≤ d.size) (h0 : CleanAddr d 0) (h1 : CleanAddr d 1) :
    Args d 0xd505accf [Word.ofAddress (Word.toAddress (argWord d 0)),
      Word.ofAddress (Word.toAddress (argWord d 1)), argWord d 2, argWord d 3, argWord d 4,
      argWord d 5, argWord d 6] := by
  refine args_of hsel (by simpa using hsize) fun i hi => ?_
  simp only [List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (clean_ofAddress h0).symm
  · exact (clean_ofAddress h1).symm
  all_goals rfl

/-! ## A clean `uint8` (`permit`'s `v`) -/

/-- The `v` word of a `permit` is a clean `uint8`. -/
def CleanU8 (d : ByteArray) : Prop := argWord d 4 &&& 255#256 = argWord d 4

theorem cleanU8_iff {d : ByteArray} : CleanU8 d ↔ (argWord d 4).toNat < 256 := by
  unfold CleanU8
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat] at this
    rw [show (255 : Nat) % 2 ^ 256 = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod] at this
    rw [← this]; exact Nat.mod_lt _ (by decide)
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [show (255 : Nat) % 2 ^ 256 = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt h

theorem eq_and_255_zero {d : ByteArray} (h : ¬ CleanU8 d) :
    Word.eq (argWord d 4) (argWord d 4 &&& 255#256) = 0 := by
  unfold Word.eq Word.ofBool
  have : (argWord d 4 == argWord d 4 &&& 255#256) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro he
    exact h (by unfold CleanU8; exact he.symm)
  rw [this]; rfl

end Verified.Common.Malformed
