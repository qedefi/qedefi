import QEDefi.ERC20.Spec.Bytecode
import EvmLogic.Program.Call
import EvmLogic.Program.Nested.Frame

/-!
# Calling a verified token from another contract

The callee-summary rules a contract that calls a token proved to be `M` (`ERC20Spec`) uses: at
a `CALL` without value to the token whose input window encodes an ERC-20 call (`Callee.call`),
or a `STATICCALL` encoding a view (`Callee.view`), the caller continues, after the token's
frame, with the model's outcome (`Callee.Ends`): the return data, the token's new model state
as the actors see it, nothing else changed, the events logged; or a failure. This is what
proofs of vaults over verified tokens use.

`Callee.start_launchCall`: the machine `launchCall` builds for a call to the token's code
satisfies `Start` (fresh, `launched`, the value moved or zero), for actors containing the caller.
-/

namespace QEDefi.ERC20.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program

variable {σ E : Type}

namespace Callee

/-! ## Starting the token's frame -/

/-- **`Start` holds for the frame `launchCall` pushes**, from a machine running the standard
precompiles (as every machine the interpreter builds does), for a call running the token's code
(not a precompile) at an account holding code shorter than `2²⁵⁶` bytes, whose value is zero or moves from another
account without wrapping the token's balance, with payable calldata, for actors containing the
caller whose hash hypotheses hold, from a world where the token's model state satisfies its
invariant. -/
theorem start_launchCall {code : ByteArray} {abs : TokenAbs σ} {M : TokenModel σ Address E}
    {Act : Finset Address} {m : Machine} {req : CallRequest}
    (hpre : precompileOf m.precompiles req.msg = none)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx) (hcode : req.msg.code = code)
    (hval : req.msg.value = 0 ∨ (req.msg.shouldTransferValue = true ∧
      req.msg.caller ≠ req.msg.currentTarget ∧
      (m.world.balance req.msg.currentTarget).toNat + req.msg.value.toNat < 2 ^ 256))
    (hsize : req.msg.data.size < 2 ^ 64) (hcaller : req.msg.caller ∈ Act)
    (hsound : abs.Sound m.ctx.crypto Act)
    (hwf : M.wf (abs.read m.ctx.crypto Act m.world req.msg.currentTarget))
    (hhas : (m.world.code req.msg.currentTarget).size ≠ 0)
    (hbound : (m.world.code req.msg.currentTarget).size < 2 ^ 256) :
    Start code abs M Act (launchCall m req) := by
  have hl : launchCall m req =
      { m with
        world := transferValue m.world req.msg
        frame := Frame.init req.msg (.call req.retOffset req.retSize) (m.world, m.transient)
        parents := m.frame :: m.parents } := by
    simp only [launchCall, hpre]
  rw [hl]
  exact
    { fresh := hcode ▸ fresh_init _ req.msg _ _ rfl
      launched := rfl
      value := hval
      precompiles := hstd
      size := hsize
      caller := hcaller
      sound := hsound
      wf := hwf
      hasCode := by
        show ((transferValue m.world req.msg).code req.msg.currentTarget).size ≠ 0
        rw [(Nested.keep_transferValue (msg := req.msg) hhas).code]; exact hhas
      codeBound := by
        show ((transferValue m.world req.msg).code req.msg.currentTarget).size < 2 ^ 256
        rw [(Nested.keep_transferValue (msg := req.msg) hhas).code]; exact hbound }

/-! ## How the token's frame ends, for its caller -/

/-- **The token's frame ended (`mf`, `o`) as the model result `res` says**, seen from its caller:
the token at `t`, the caller's world `w` and transient storage `tr` before the call, events
`evs`. On success, the model's return data, the model's new state through `abs` for the actors,
nothing else changed (`FrameKeeps`), transient storage kept, exactly the model's events in the
frame's logs; on failure, the model's kind of failure. -/
def Ends (abs : TokenAbs σ) (Act : Finset Address) (crypto : Crypto) (t : Address) (w : World)
    (tr : TransientStorage) (evs : List (Event Address)) (mf : Machine) (o : Outcome) :
    Result σ → Prop
  | .ok s' ret =>
    o = .success (retBytes ret) ∧ abs.read crypto Act mf.world t = s' ∧
      FrameKeeps abs crypto Act t w mf.world ∧ mf.transient = tr ∧
      mf.frame.sub.logs = (evs.map (eventLog t)).toArray
  | .halt .revert => ∃ out, o = .revert out
  | .halt .invalid => ∃ e, o = .halt e

/-- `Matches` for a frame started by `Frame.init` (empty logs) is `Ends`. -/
theorem ends_of_matches {abs : TokenAbs σ} {Act : Finset Address} {mc mf : Machine}
    {o : Outcome} {evs : List (Event Address)} {res : Result σ} {msg : Message}
    {kind : FrameKind} {snap : World × TransientStorage} (hf : mc.frame = Frame.init msg kind snap)
    (h : Matches abs Act mc mf o evs res) :
    Ends abs Act mc.ctx.crypto mc.frame.msg.currentTarget mc.world mc.transient evs mf o res := by
  match res, h with
  | .ok s' ret, ⟨ho, hread, hkeep, htr, _, hlogs⟩ =>
    refine ⟨ho, hread, hkeep, htr, ?_⟩
    rw [hlogs, hf]
    show #[] ++ _ = _
    simp
  | .halt .revert, h => exact h
  | .halt .invalid, h => exact h

/-! ## `CALL` to the token -/

variable {code : ByteArray} {abs : TokenAbs σ} {M : TokenModel σ Address E} {g₀ : Nat}
  {Act : Finset Address} {m : Machine} {gas toW inOff inSize outOff outSize : Word}
  {rest : List Word} {Q : Machine → Prop} {H : Machine → Outcome → Prop}

/-- The calldata of a call with input window `[inOff, inOff + inSize)`. -/
abbrev callData (m : Machine) (inOff inSize outOff outSize : Word) : ByteArray :=
  readBytes (callMemory m inOff inSize outOff outSize).bytes inOff.toNat inSize.toNat

/-- **Callee rule for an ERC-20 call to a verified token.** At a `CALL` without value to the
token at `t = toW` (its code `code`, not a precompile, no designator), from a machine running the
standard precompiles, whose input window encodes
the ERC-20 call `c`, with the caller's account and the accounts of `c` actors whose hash
hypotheses hold and the token's state satisfying its invariant, the caller continues after the
token's frame with the model's outcome of `c` by the caller's account in the token's state
before the call (`Ends`), or, with less than `g₀` gas forwarded or in a static context, with a
failure. -/
theorem call {c : Call Address} (hc : CallSpec code abs M g₀ c)
    (hcode : m.frame.code[m.frame.pc]? = some 0xf1)
    (hstk : m.frame.stack = gas :: toW :: 0 :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize ≤
      m.frame.gasLeft)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = false)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (htok : m.world.code (Word.toAddress toW) = code) (hreal : code.size ≠ 0)
    (hbound : code.size < 2 ^ 256)
    (hsize : inSize.toNat < 2 ^ 64)
    (hcaller : m.frame.msg.currentTarget ∈ Act) (haddrs : ∀ x ∈ c.addrs, x ∈ Act)
    (hsound : abs.Sound m.ctx.crypto Act)
    (hwf : M.wf (abs.read m.ctx.crypto Act m.world (Word.toAddress toW)))
    (he : c.Encodes (callData m inOff inSize outOff outSize))
    (k : ∀ mf o, SameFrame (call0Child m gas toW inOff inSize outOff outSize rest) mf →
      (Ends abs Act m.ctx.crypto (Word.toAddress toW) m.world m.transient
          (M.events (abs.read m.ctx.crypto Act m.world (Word.toAddress toW))
            m.frame.msg.currentTarget c) mf o
          (M.call (abs.read m.ctx.crypto Act m.world (Word.toAddress toW))
            m.frame.msg.currentTarget c) ∨
        (Fails o ∧ ¬ (g₀ ≤ (callGas m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff
          outSize).subCall ∧ m.frame.msg.isStatic = false))) →
      WP (resumeAfter (call0Caller m gas toW inOff inSize outOff outSize rest) m.parents mf o)
        Q H) :
    WP m Q H := by
  set mc := call0Child m gas toW inOff inSize outOff outSize rest
  have hfr : mc.frame = Frame.init mc.frame.msg (.call outOff.toNat outSize.toNat)
      (m.world, m.transient) := rfl
  have hs : Start code abs M Act mc :=
    { fresh := by
        have := fresh_init mc mc.frame.msg _ _ hfr
        rwa [show mc.frame.msg.code = code from htok] at this
      launched := (transferValue_zero _ _ rfl).symm
      value := .inl rfl
      precompiles := hstd
      size := by show (callData m inOff inSize outOff outSize).size < _; simpa using hsize
      caller := hcaller
      sound := hsound
      wf := hwf
      hasCode := by
        show (m.world.code (Word.toAddress toW)).size ≠ 0
        rw [htok]; exact hreal
      codeBound := by
        show (m.world.code (Word.toAddress toW)).size < 2 ^ 256
        rw [htok]; exact hbound }
  refine WP.call0 hcode hstk hdel hgas hdepth hpre (hc Act mc hs he haddrs) fun mf o hH hsf => ?_
  refine k mf o hsf ?_
  rcases hH with hm | ⟨hf, hn⟩
  · exact .inl (ends_of_matches hfr hm)
  · refine .inr ⟨hf, fun ⟨h1, h2⟩ => hn ⟨h1, ?_, rfl⟩⟩
    show (false || m.frame.msg.isStatic) = false
    rw [h2]; rfl

/-- **Callee rule for an ERC-20 call with enough gas**: outside a static context and with at
least `g₀` gas forwarded, the caller continues with the model's outcome. -/
theorem call_normal {c : Call Address} (hc : CallSpec code abs M g₀ c)
    (hcode : m.frame.code[m.frame.pc]? = some 0xf1)
    (hstk : m.frame.stack = gas :: toW :: 0 :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize ≤
      m.frame.gasLeft)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = false)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (htok : m.world.code (Word.toAddress toW) = code) (hreal : code.size ≠ 0)
    (hbound : code.size < 2 ^ 256)
    (hsize : inSize.toNat < 2 ^ 64)
    (hcaller : m.frame.msg.currentTarget ∈ Act) (haddrs : ∀ x ∈ c.addrs, x ∈ Act)
    (hsound : abs.Sound m.ctx.crypto Act)
    (hwf : M.wf (abs.read m.ctx.crypto Act m.world (Word.toAddress toW)))
    (he : c.Encodes (callData m inOff inSize outOff outSize))
    (hg₀ : g₀ ≤ (callGas m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize).subCall)
    (hstatic : m.frame.msg.isStatic = false)
    (k : ∀ mf o, SameFrame (call0Child m gas toW inOff inSize outOff outSize rest) mf →
      Ends abs Act m.ctx.crypto (Word.toAddress toW) m.world m.transient
          (M.events (abs.read m.ctx.crypto Act m.world (Word.toAddress toW))
            m.frame.msg.currentTarget c) mf o
          (M.call (abs.read m.ctx.crypto Act m.world (Word.toAddress toW))
            m.frame.msg.currentTarget c) →
      WP (resumeAfter (call0Caller m gas toW inOff inSize outOff outSize rest) m.parents mf o)
        Q H) :
    WP m Q H :=
  call hc hcode hstk hdel hgas hdepth hpre hstd htok hreal hbound hsize hcaller haddrs hsound hwf he
    fun mf o hsf h => h.elim (k mf o hsf) fun hf => (hf.2 ⟨hg₀, hstatic⟩).elim

/-! ## `STATICCALL` of a view -/

/-- The child machine of a `STATICCALL` (see `step_staticcall`). -/
abbrev staticChild (m : Machine) (gas toW inOff inSize outOff outSize : Word)
    (rest : List Word) : Machine :=
  { m with
    frame := Frame.init
      (childMsg m m.frame.msg.currentTarget (Word.toAddress toW) (Word.toAddress toW) 0
        (callGas m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize).subCall true true
        inOff inSize outOff outSize)
      (.call outOff.toNat outSize.toNat) (m.world, m.transient)
    parents := callerFrame m rest (callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff
      outSize) (Word.toAddress toW) inOff inSize outOff outSize :: m.parents }

/-- **Callee rule for a view of a verified token.** At a `STATICCALL` to the token, from a
machine running the standard precompiles, whose input window encodes the view `v`, with the caller's account and the view's accounts actors, the
caller continues after the token's frame with one returned word holding the model's value and
nothing changed, or, with less than `g₀` gas forwarded, with a failure. -/
theorem view {v : View} (hv : ViewSpec code abs M g₀ v)
    (hcode : m.frame.code[m.frame.pc]? = some 0xfa)
    (hstk : m.frame.stack = gas :: toW :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize ≤
      m.frame.gasLeft)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = false)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (htok : m.world.code (Word.toAddress toW) = code) (hreal : code.size ≠ 0)
    (hbound : code.size < 2 ^ 256)
    (hsize : inSize.toNat < 2 ^ 64)
    (hcaller : m.frame.msg.currentTarget ∈ Act) (haddrs : ∀ x ∈ v.addrs, x ∈ Act)
    (hsound : abs.Sound m.ctx.crypto Act)
    (hwf : M.wf (abs.read m.ctx.crypto Act m.world (Word.toAddress toW)))
    (he : v.Encodes (callData m inOff inSize outOff outSize))
    (k : ∀ mf o, SameFrame (staticChild m gas toW inOff inSize outOff outSize rest) mf →
      ((∃ x : Word, o = .success (Bytes.ofWord x) ∧
          x.toNat = v.value M (abs.read m.ctx.crypto Act m.world (Word.toAddress toW)) ∧
          mf.world = m.world ∧ mf.transient = m.transient ∧ mf.frame.sub.logs = #[]) ∨
        (Fails o ∧ ¬ g₀ ≤ (callGas m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff
          outSize).subCall)) →
      WP (resumeAfter (callerFrame m rest (callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize
        outOff outSize) (Word.toAddress toW) inOff inSize outOff outSize) m.parents mf o) Q H) :
    WP m Q H := by
  set mc := staticChild m gas toW inOff inSize outOff outSize rest
  have hfr : mc.frame = Frame.init mc.frame.msg (.call outOff.toNat outSize.toNat)
      (m.world, m.transient) := rfl
  have hs : Start code abs M Act mc :=
    { fresh := by
        have := fresh_init mc mc.frame.msg _ _ hfr
        rwa [show mc.frame.msg.code = code from htok] at this
      launched := (transferValue_zero _ _ rfl).symm
      value := .inl rfl
      precompiles := hstd
      size := by show (callData m inOff inSize outOff outSize).size < _; simpa using hsize
      caller := hcaller
      sound := hsound
      wf := hwf
      hasCode := by
        show (m.world.code (Word.toAddress toW)).size ≠ 0
        rw [htok]; exact hreal
      codeBound := by
        show (m.world.code (Word.toAddress toW)).size < 2 ^ 256
        rw [htok]; exact hbound }
  refine WP.staticcall hcode hstk hdel hgas hdepth hpre (hv Act mc hs he haddrs)
    fun mf o hH hsf => k mf o hsf ?_
  rcases hH with ⟨x, ho, hx, hw, htr, -, hlogs⟩ | ⟨hf, hn⟩
  · refine .inl ⟨x, ho, hx, hw, htr, ?_⟩
    rw [hlogs]; rfl
  · exact .inr ⟨hf, fun h1 => hn ⟨h1, rfl⟩⟩

end Callee

end QEDefi.ERC20.Spec
