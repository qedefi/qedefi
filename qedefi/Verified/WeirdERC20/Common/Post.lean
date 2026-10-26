import Verified.WeirdERC20.Common.Transport

/-!
# `MalformedSpec` from the exact obligations, for solc 0.4/0.5 tokens

`LPost` is the frame-end condition of `MalformedSpec`, for the actors `Act` (which include
every account the calldata can name, `calldataAddrs`). The rules:

* `lpost_fails`, `lpost_unchanged`: the frame fails, or changes no world, transient storage or
  logs (a getter);
* `lpost_fallback`: short calldata or an unknown selector, through `FallbackSpec`;
* `lpost_op`: calldata the decoder `ops` accepts, through `OpSpec`;
* `lpost_call_dirty`, `lpost_op_dirty`: calldata whose clean counterpart (`DirtyRun`, the
  dispatcher masks `address` words) encodes an ERC-20 call or an operation, through `CallSpec`
  or `OpSpec` of the clean frame (`transport`).

`mem_calldataAddrs`: a masked argument word is an account the calldata names, so the accounts
of the clean call are actors.
-/

namespace Verified.WeirdERC20.Common
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.GasMono
open QEDefi.ERC20 QEDefi.ERC20.Spec EvmLogic.Solidity
open Verified.OpenZeppelin.ERC20.Spec (SuccessPost fails_of_failed failed_of_fails MatchesOk
  matchesOk_of matches_of)

variable {σ E : Type} {code : ByteArray} {abs : TokenAbs σ} {M : TokenModel σ Address E}
  {ops : Address → ByteArray → ℕ → Option E} {opAddrs : E → List Address}
  {rec : Option (Machine → ℕ → Address)} {Act : Finset Address} {m : Machine}

/-- **The frame-end condition of `MalformedSpec`**, for the actors `Act` and the frame `m`. -/
def LPost (abs : TokenAbs σ) (M : TokenModel σ Address E)
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

/-- `MalformedSpec` is `LPost` in every starting frame outside `excl`. -/
theorem malformed_of {excl : List Nat}
    (h : ∀ Act m, Start code abs M Act m → calldataAddrs m.frame.msg.data ⊆ Act →
      ¬ (4 ≤ m.frame.msg.data.size ∧ Abi.selectorOf m.frame.msg.data ∈ excl) →
      Halts m (LPost abs M ops opAddrs rec Act m)) :
    MalformedSpec code abs M ops opAddrs rec excl := h

/-- **An argument word, read as an address, is an account the calldata names.** -/
theorem mem_calldataAddrs {d : ByteArray} {i : Nat} (h : 4 + 32 * i < d.size) :
    Word.toAddress (Bytes.toWord (readBytes d (4 + 32 * i) 32)) ∈ calldataAddrs d := by
  refine Finset.mem_insert_of_mem ?_
  simp only [List.mem_toFinset, List.mem_map, List.mem_range]
  exact ⟨i, by omega, rfl⟩

theorem lpost_fails (h : Halts m fun _ o => Fails o) :
    Halts m (LPost abs M ops opAddrs rec Act m) :=
  h.mono fun _ _ _ h => .inl h

theorem lpost_unchanged (h : Halts m fun mf o => Fails o ∨
      (mf.world = m.world ∧ mf.transient = m.transient ∧ mf.frame.sub.logs = m.frame.sub.logs)) :
    Halts m (LPost abs M ops opAddrs rec Act m) :=
  h.mono fun _ _ _ h => h.imp_right .inl

/-- **Short calldata or an unknown selector** ends as `FallbackSpec` says. -/
theorem lpost_fallback {g₀ : Nat} {sel : List Nat} (hfs : FallbackSpec code abs M g₀ sel)
    (hS : Start code abs M Act m)
    (hsel : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ sel) :
    Halts m (LPost abs M ops opAddrs rec Act m) :=
  (hfs Act m hS hsel).mono fun _ _ _ hp => by
    rcases hp with hm | ⟨hf, -⟩
    · exact .inr (.inr (.inl ⟨.other m.frame.msg.value.toNat, trivial,
        fun a ha => by simp [Call.addrs] at ha, hm⟩))
    · exact .inl hf

/-- `OpMatches` with an outcome of the model: a success, or a failure. -/
theorem lpost_of_opMatches {e : E} {d : ByteArray}
    (hops : ops m.frame.msg.caller d m.frame.msg.value.toNat = some e)
    (hA : ∀ a ∈ opAddrs e, a ∈ Act) {mf : Machine} {o : Outcome}
    (h : OpMatches abs M Act e m mf o) : LPost abs M ops opAddrs rec Act m mf o := by
  cases hop : M.op (pre abs Act m) e with
  | none =>
    unfold OpMatches at h
    rw [hop] at h
    exact .inl h
  | some s' => exact .inr (.inr (.inr ⟨d, e, hops, hA, ⟨s', hop⟩, h⟩))

/-- **Calldata the decoder accepts** ends as `OpSpec` says. -/
theorem lpost_op {g₀ : Nat} (hos : OpSpec code abs M g₀ ops opAddrs)
    (hS : Start code abs M Act m) {e : E}
    (hops : ops m.frame.msg.caller m.frame.msg.data m.frame.msg.value.toNat = some e)
    (hA : ∀ a ∈ opAddrs e, a ∈ Act) :
    Halts m (LPost abs M ops opAddrs rec Act m) :=
  (hos Act m e hS hops hA).mono fun _ _ _ hp => by
    rcases hp with hm | ⟨hf, -⟩
    · exact lpost_of_opMatches hops hA hm
    · exact .inl hf

/-- **A dirty ERC-20 call** whose clean counterpart (calldata `D'`) is the encoding of the call
`c`, naming actors, ends as `CallSpec` says of `c`. -/
theorem lpost_call_dirty {g₀ : Nat} {c : Call Address}
    (hcs : CallSpec code abs M g₀ c) (hS : Start code abs M Act m)
    {D' : ByteArray} (hr : DirtyRun code m D') (henc : c.Encodes D') (hex : Explains rec m c)
    (hA : ∀ a ∈ c.addrs, a ∈ Act) :
    Halts m (LPost abs M ops opAddrs rec Act m) := by
  have hsum : ∀ G, m.frame.gasLeft ≤ G → Halts (clean D' G m) fun mf o =>
      Failed o ∨ ∃ out, o = .success out ∧
        MatchesOk abs Act m (M.events (pre abs Act m) m.frame.msg.caller c)
          (M.call (pre abs Act m) m.frame.msg.caller c)
          out mf.world mf.transient mf.frame.sub.logs := fun G hG =>
    (hcs _ _ (start_clean hS hG hr.1) henc hA).mono fun mf o _ hp => by
      rcases hp with hm | ⟨hfl, -⟩
      · exact matchesOk_of hm
      · exact .inl (failed_of_fails hfl)
  refine (transport' hr hsum).mono fun mf o _ hp => ?_
  rcases hp with hfl | ⟨out, rfl, hq, hcr⟩
  · exact .inl (fails_of_failed hfl)
  · exact .inr (.inr (.inl ⟨c, hex, hA, matches_of hq hcr⟩))

/-- What a successful frame must satisfy for `OpMatches` of an operation whose model outcome
is `s'`, minus its created accounts. -/
def OpOk (abs : TokenAbs σ) (Act : Finset Address) (m : Machine) (s' : σ) : SuccessPost :=
  fun _ W T _ => abs.read m.ctx.crypto Act W m.frame.msg.currentTarget = s' ∧
    FrameKeeps abs m.ctx.crypto Act m.frame.msg.currentTarget m.world W ∧ T = m.transient

/-- **A dirty operation** whose clean counterpart (calldata `D'`) the decoder accepts as `e`,
naming actors, ends as `OpSpec` says of `e`. -/
theorem lpost_op_dirty {g₀ : Nat} (hos : OpSpec code abs M g₀ ops opAddrs)
    (hS : Start code abs M Act m) {D' : ByteArray} (hr : DirtyRun code m D')
    {e : E} (hops : ops m.frame.msg.caller D' m.frame.msg.value.toNat = some e)
    (hA : ∀ a ∈ opAddrs e, a ∈ Act) :
    Halts m (LPost abs M ops opAddrs rec Act m) := by
  have hspec := fun G (hG : m.frame.gasLeft ≤ G) =>
    hos _ _ e (start_clean hS hG hr.1) hops hA
  cases hop : M.op (pre abs Act m) e with
  | none =>
    have hsum : ∀ G, m.frame.gasLeft ≤ G → Halts (clean D' G m) fun mf o =>
        Failed o ∨ ∃ out, o = .success out ∧
          (fun (_ : ByteArray) (_ : World) (_ : TransientStorage) (_ : Array Log) => False)
            out mf.world mf.transient mf.frame.sub.logs := fun G hG =>
      (hspec G hG).mono fun mf o _ hp => by
        rcases hp with hm | ⟨hfl, -⟩
        · unfold OpMatches at hm
          have hop' : M.op (pre abs Act (clean D' G m)) e = none := hop
          rw [hop'] at hm
          exact .inl (failed_of_fails hm)
        · exact .inl (failed_of_fails hfl)
    refine (transport' hr (Q := fun _ _ _ _ => False) hsum).mono fun mf o _ hp => ?_
    rcases hp with hfl | ⟨out, rfl, hq, -⟩
    · exact .inl (fails_of_failed hfl)
    · exact hq.elim
  | some s' =>
    have hsum : ∀ G, m.frame.gasLeft ≤ G → Halts (clean D' G m) fun mf o =>
        Failed o ∨ ∃ out, o = .success out ∧
          OpOk abs Act m s' out mf.world mf.transient mf.frame.sub.logs := fun G hG =>
      (hspec G hG).mono fun mf o _ hp => by
        rcases hp with hm | ⟨hfl, -⟩
        · unfold OpMatches at hm
          have hop' : M.op (pre abs Act (clean D' G m)) e = some s' := hop
          rw [hop'] at hm
          obtain ⟨⟨out, ho⟩, h1, h2, h3, -⟩ := hm
          exact .inr ⟨out, ho, h1, h2, h3⟩
        · exact .inl (failed_of_fails hfl)
    refine (transport' hr hsum).mono fun mf o _ hp => ?_
    rcases hp with hfl | ⟨out, rfl, ⟨h1, h2, h3⟩, hcr⟩
    · exact .inl (fails_of_failed hfl)
    · refine .inr (.inr (.inr ⟨D', e, hops, hA, ⟨s', hop⟩, ?_⟩))
      unfold OpMatches
      rw [hop]
      exact ⟨⟨out, rfl⟩, h1, h2, h3, hcr⟩

end Verified.WeirdERC20.Common
