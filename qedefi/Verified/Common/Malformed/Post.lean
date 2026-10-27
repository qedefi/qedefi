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
* `post_call`: the calldata **is** the ABI encoding of an ERC-20 call (`Call.Encodes`) whose
  accounts are actors, so `CallSpec` applies; the accounts are actors because they are
  argument words of the calldata (`argAddr_mem`: `MalformedSpec` asks `calldataAddrs ⊆ Act`);
* `post_fallback`: short calldata or an unknown selector, through `FallbackSpec`;
* `post_op`: calldata the decoder `ops` accepts, through `OpSpec`;
* `post_permit`: a `permit` with the token's own recovery, through `PermitSpec`
  (`post_permit_of`: through any proof for the frame).

**The reduction** of malformed calldata to these rules: the decoders of solc ≥ 0.8 revert
unless the calldata holds every argument word and the `address` words are clean (`CleanAddr`),
and then the calldata is the encoding of a call (`encodes_transfer`, `encodes_transferFrom`,
`encodes_approve`, `args_permit`; `post_transfer`, `post_approve`, `post_transferFrom` combine
them with `post_call`).
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
  (∃ c, Explains rec m c ∧ (∀ a ∈ c.addrs, a ∈ Act) ∧
    Matches abs Act m mf o (M.events (pre abs Act m) m.frame.msg.caller c)
      (M.call (pre abs Act m) m.frame.msg.caller c)) ∨
  (∃ d e, ops m.frame.msg.caller d m.frame.msg.value.toNat = some e ∧
    (∀ a ∈ opAddrs e, a ∈ Act) ∧ (∃ s', M.op (pre abs Act m) e = some s') ∧
    OpMatches abs M Act e m mf o)

/-- `MalformedSpec` is `MalPost` in every starting frame whose calldata names only actors and
whose selector is not excluded. -/
theorem malformedSpec_of {excl : List Nat}
    (h : ∀ Act m, Start code abs M Act m → calldataAddrs m.frame.msg.data ⊆ Act →
      ¬ (4 ≤ m.frame.msg.data.size ∧ Abi.selectorOf m.frame.msg.data ∈ excl) →
      Halts m (MalPost abs M ops opAddrs rec Act m)) :
    MalformedSpec code abs M ops opAddrs rec excl := h

/-! ## The calldata's accounts -/

/-- **A complete argument word, read as an address, is one of the calldata's accounts.** -/
theorem argAddr_mem_calldataAddrs {d : ByteArray} {j : Nat} (hj : 4 + 32 * (j + 1) ≤ d.size) :
    Word.toAddress (argWord d j) ∈ calldataAddrs d := by
  unfold calldataAddrs
  rw [Finset.mem_insert, List.mem_toFinset, List.mem_map]
  exact .inr ⟨j, List.mem_range.2 (by omega), rfl⟩

/-- **The zero address is one of the calldata's accounts** (what a decoder without length
checks reads past the end). -/
theorem zero_mem_calldataAddrs (d : ByteArray) : (0 : Address) ∈ calldataAddrs d :=
  Finset.mem_insert_self _ _

theorem argAddr_mem {d : ByteArray} (hcd : calldataAddrs d ⊆ Act) {j : Nat}
    (hj : 4 + 32 * (j + 1) ≤ d.size) : Word.toAddress (argWord d j) ∈ Act :=
  hcd (argAddr_mem_calldataAddrs hj)

/-- The first argument word, as the only account an operation names. -/
theorem argAddr0_list {d : ByteArray} (hcd : calldataAddrs d ⊆ Act) (hj : 36 ≤ d.size) :
    ∀ a ∈ [Word.toAddress (argWord d 0)], a ∈ Act := fun a ha => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha; exact argAddr_mem hcd (by omega)

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

/-- **An encoded ERC-20 call whose accounts are actors** ends as `CallSpec` says. -/
theorem post_call {g₀ : Nat} {c : Call Address} (hcs : CallSpec code abs M g₀ c)
    (hS : Start code abs M Act m) (henc : c.Encodes m.frame.msg.data) (hex : Explains rec m c)
    (hA : ∀ a ∈ c.addrs, a ∈ Act) :
    Halts m (MalPost abs M ops opAddrs rec Act m) :=
  (hcs Act m hS henc hA).mono fun _ _ _ hp => by
    rcases hp with hm | ⟨hf, -⟩
    · exact .inr (.inr (.inl ⟨c, hex, hA, hm⟩))
    · exact .inl hf

/-- **Short calldata or an unknown selector** ends as `FallbackSpec` says. -/
theorem post_fallback {g₀ : Nat} {sel : List Nat} (hfs : FallbackSpec code abs M g₀ sel)
    (hS : Start code abs M Act m)
    (hsel : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ sel) :
    Halts m (MalPost abs M ops opAddrs rec Act m) :=
  (hfs Act m hS hsel).mono fun _ _ _ hp => by
    rcases hp with hm | ⟨hf, -⟩
    · exact .inr (.inr (.inl ⟨.other m.frame.msg.value.toNat, trivial,
        fun a ha => by simp [Call.addrs] at ha, hm⟩))
    · exact .inl hf

/-- **Calldata the decoder accepts, naming actors**, ends as `OpSpec` says. -/
theorem post_op {g₀ : Nat} (hos : OpSpec code abs M g₀ ops opAddrs)
    (hS : Start code abs M Act m) {e : E}
    (hops : ops m.frame.msg.caller m.frame.msg.data m.frame.msg.value.toNat = some e)
    (hA : ∀ a ∈ opAddrs e, a ∈ Act) :
    Halts m (MalPost abs M ops opAddrs rec Act m) :=
  (hos Act m e hS hops hA).mono fun _ _ _ hp => by
    rcases hp with hm | ⟨hf, -⟩
    · by_cases hsome : ∃ s', M.op (pre abs Act m) e = some s'
      · exact .inr (.inr (.inr ⟨_, e, hops, hA, hsome, hm⟩))
      · left
        unfold OpMatches at hm
        split at hm
        · rename_i s' hs'
          exact absurd ⟨s', hs'⟩ hsome
        · exact hm
    · exact .inl hf

/-- **A `permit` frame naming actors that ends as the model's `permit` with the token's own
recovery** (or fails). -/
theorem post_permit_of {r : Machine → ℕ → Address} (hrec : rec = some r)
    {o sp : Address} {v : ℕ} {live : Bool} (ho : o ∈ Act) (hsp : sp ∈ Act)
    (h : Halts m fun mf out =>
      Matches abs Act m mf out
        (M.events (pre abs Act m) m.frame.msg.caller (.permit o sp v live (r m)))
        (M.call (pre abs Act m) m.frame.msg.caller (.permit o sp v live (r m))) ∨ Fails out) :
    Halts m (MalPost abs M ops opAddrs rec Act m) :=
  h.mono fun _ _ _ hp => by
    rcases hp with hm | hf
    · exact .inr (.inr (.inl ⟨.permit o sp v live (r m), ⟨r, hrec, fun _ => rfl⟩,
        fun a ha => by simp only [Call.addrs, List.mem_cons, List.not_mem_nil, or_false] at ha
                       rcases ha with rfl | rfl <;> assumption, hm⟩))
    · exact .inl hf

/-- **A `permit` with ABI arguments naming actors**, when `ecrecover` runs the precompile and
the frame has less than `2⁶⁴` gas, ends as `PermitSpec` says, with the token's own recovery. -/
theorem post_permit {gp : Machine → Nat} {r : Machine → ℕ → Address}
    (hps : PermitSpec code abs M gp r) (hrec : rec = some r) (hS : Start code abs M Act m)
    {o sp : Address} {v dl pv pr ps : Word} (ho : o ∈ Act) (hsp : sp ∈ Act)
    (hargs : Args m.frame.msg.data 0xd505accf
      [Word.ofAddress o, Word.ofAddress sp, v, dl, pv, pr, ps])
    (hE : EcrecoverPlain m) (hg : m.frame.gasLeft < 2 ^ 64) :
    Halts m (MalPost abs M ops opAddrs rec Act m) :=
  post_permit_of hrec ho hsp
    ((hps Act m o sp v dl pv pr ps hS ho hsp hE hg hargs).mono fun _ _ _ hp =>
      hp.imp_right fun h => h.1)

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

/-! ## Well-formed calls through the exact obligations -/

/-- **`transfer` with all its words and a clean recipient, in calldata naming only actors.** -/
theorem post_transfer {g₀ : Nat} (hcs : ∀ c, CallSpec code abs M g₀ c)
    (hS : Start code abs M Act m) (hcd : calldataAddrs m.frame.msg.data ⊆ Act)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xa9059cbb) (hsize : 68 ≤ m.frame.msg.data.size)
    (h0 : CleanAddr m.frame.msg.data 0) : Halts m (MalPost abs M ops opAddrs rec Act m) :=
  post_call (hcs _) hS (encodes_transfer hsel hsize h0) trivial fun a ha => by
    simp only [Call.addrs, List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha; exact argAddr_mem hcd (by omega)

/-- **`approve` with all its words and a clean spender, in calldata naming only actors.** -/
theorem post_approve {g₀ : Nat} (hcs : ∀ c, CallSpec code abs M g₀ c)
    (hS : Start code abs M Act m) (hcd : calldataAddrs m.frame.msg.data ⊆ Act)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x095ea7b3) (hsize : 68 ≤ m.frame.msg.data.size)
    (h0 : CleanAddr m.frame.msg.data 0) : Halts m (MalPost abs M ops opAddrs rec Act m) :=
  post_call (hcs _) hS (encodes_approve hsel hsize h0) trivial fun a ha => by
    simp only [Call.addrs, List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha; exact argAddr_mem hcd (by omega)

/-- **`transferFrom` with all its words and clean accounts, in calldata naming only actors.** -/
theorem post_transferFrom {g₀ : Nat} (hcs : ∀ c, CallSpec code abs M g₀ c)
    (hS : Start code abs M Act m) (hcd : calldataAddrs m.frame.msg.data ⊆ Act)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x23b872dd) (hsize : 100 ≤ m.frame.msg.data.size)
    (h0 : CleanAddr m.frame.msg.data 0) (h1 : CleanAddr m.frame.msg.data 1) :
    Halts m (MalPost abs M ops opAddrs rec Act m) :=
  post_call (hcs _) hS (encodes_transferFrom hsel hsize h0 h1) trivial fun a ha => by
    simp only [Call.addrs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact argAddr_mem hcd (by omega)
    · exact argAddr_mem hcd (by omega)

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
