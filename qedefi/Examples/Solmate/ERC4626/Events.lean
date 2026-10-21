import QEDefi.ERC4626.Events
import Examples.Solmate.ERC4626.Abstraction
import QEDefi.ERC4626.Logs
import EvmLogic.Solidity.Word

/-!
# Events as EVM logs

`encode vault asset evs` turns the model's events (`QEDefi.ERC4626.Events`) into the logs the
compiled contracts emit; `EventsPost m L` says a frame appends exactly `L` or reverts with
`L = #[]`; `events_call` and `resumeAfter_eventsPost` lift it to top-level and nested calls.
-/

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 QEDefi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open QEDefi.Math QEDefi.ERC20 QEDefi.ERC4626.Solmate

/-! ## The model's events as logs -/

def _root_.QEDefi.ERC4626.Solmate.Emitter.addr (vault asset : Address) : Emitter → Address
  | .vault => vault
  | .asset => asset

/-- An event of the model as the log the deployed contracts emit (amounts as ABI words). -/
def _root_.QEDefi.ERC4626.Solmate.Event.toLog (vault asset : Address) : Event Address → Log
  | .transfer e src dst v => transferLog (e.addr vault asset) src dst (BitVec.ofNat 256 v)
  | .approval e o sp v => approvalLog (e.addr vault asset) o sp (BitVec.ofNat 256 v)
  | .deposit c o a s => depositLog vault c o (BitVec.ofNat 256 a) (BitVec.ofNat 256 s)
  | .withdraw c r o a s =>
    withdrawLog vault c r o (BitVec.ofNat 256 a) (BitVec.ofNat 256 s)

/-- The logs of a list of events, in order. -/
def encode (vault asset : Address) (evs : List (Event Address)) : Array Log :=
  (evs.map (Event.toLog vault asset)).toArray

@[simp] theorem encode_nil (vault asset : Address) : encode vault asset [] = #[] := rfl

theorem encode_append (vault asset : Address) (e₁ e₂ : List (Event Address)) :
    encode vault asset (e₁ ++ e₂) = encode vault asset e₁ ++ encode vault asset e₂ := by
  simp [encode]

theorem push_eq_encode {vault asset : Address} {L : Array Log} {e : Event Address} {l : Log}
    (h : e.toLog vault asset = l) : L.push l = L ++ encode vault asset [e] := by
  simp [encode, h]

theorem toLog_transfer (vault asset : Address) (e : Emitter) (src dst : Address) (v : Word) :
    (Event.transfer e src dst v.toNat).toLog vault asset =
      transferLog (e.addr vault asset) src dst v := by
  simp [Event.toLog]

theorem toLog_approval (vault asset : Address) (e : Emitter) (o sp : Address) (v : Word) :
    (Event.approval e o sp v.toNat).toLog vault asset =
      approvalLog (e.addr vault asset) o sp v := by
  simp [Event.toLog]

/-! ## The events of the entry points -/

theorem append_three (L : Array Log) (a b c : Log) :
    L ++ #[a, b, c] = ((L.push a).push b).push c := by
  simp only [← Array.append_singleton, Array.append_assoc]
  rfl

theorem encode_withdraw (vault asset caller receiver owner : Address) (assets : Word)
    (s : State Address) (v : ℕ) :
    encode vault asset (Events.withdraw vault caller receiver owner assets.toNat (some (s, v))) =
      #[transferLog vault owner 0 (BitVec.ofNat 256 v),
        withdrawLog vault caller receiver owner assets (BitVec.ofNat 256 v),
        transferLog asset vault receiver assets] := by
  simp [encode, Events.withdraw, Event.toLog, Emitter.addr]

theorem encode_redeem (vault asset caller receiver owner : Address) (shares : Word)
    (s : State Address) (v : ℕ) :
    encode vault asset (Events.redeem vault caller receiver owner shares.toNat (some (s, v))) =
      #[transferLog vault owner 0 shares,
        withdrawLog vault caller receiver owner (BitVec.ofNat 256 v) shares,
        transferLog asset vault receiver (BitVec.ofNat 256 v)] := by
  simp [encode, Events.redeem, Event.toLog, Emitter.addr]

theorem encode_deposit (vault asset caller receiver : Address) (assets : Word)
    (s : State Address) (v : ℕ) :
    encode vault asset (Events.deposit vault caller receiver assets.toNat (some (s, v))) =
      #[transferLog asset caller vault assets, transferLog vault 0 receiver (BitVec.ofNat 256 v),
        depositLog vault caller receiver assets (BitVec.ofNat 256 v)] := by
  simp [encode, Events.deposit, Event.toLog, Emitter.addr]

theorem encode_mint4626 (vault asset caller receiver : Address) (shares : Word)
    (s : State Address) (v : ℕ) :
    encode vault asset (Events.mint4626 vault caller receiver shares.toNat (some (s, v))) =
      #[transferLog asset caller vault (BitVec.ofNat 256 v), transferLog vault 0 receiver shares,
        depositLog vault caller receiver (BitVec.ofNat 256 v) shares] := by
  simp [encode, Events.mint4626, Event.toLog, Emitter.addr]

/-! ## Frames and top-level calls -/

/-- How a frame ends with respect to logs, when the model says that the call emits the logs
`L`: success after appending exactly `L` to the frame's logs; or a revert while the model
emits nothing; never an exceptional halt. -/
def EventsPost (m : Machine) (L : Array Log) (mf : Machine) (o : Outcome) : Prop :=
  match o with
  | .success _ => mf.frame.sub.logs = m.frame.sub.logs ++ L
  | .revert _ => L = #[]
  | .halt _ => False

theorem eventsPost_success {m mf : Machine} {L : Array Log} {out : ByteArray}
    (h : mf.frame.sub.logs = m.frame.sub.logs ++ L) : EventsPost m L mf (.success out) := h

theorem eventsPost_revert {m mf : Machine} {o : Outcome} (h : ∃ out, o = .revert out) :
    EventsPost m #[] mf o := by
  obtain ⟨out, rfl⟩ := h; rfl

/-- **Nested calls.** After a fresh callee frame ending as `EventsPost` says, the caller's logs
are its own followed by `L`. -/
theorem resumeAfter_eventsPost {mc mf : Machine} {p : Frame} {ps : List Frame} {o : Outcome}
    {L : Array Log} {a b : Nat} (h0 : mc.frame.sub.logs = #[]) (hk : mf.frame.kind = .call a b)
    (h : EventsPost mc L mf o) : (resumeAfter p ps mf o).frame.sub.logs = p.sub.logs ++ L := by
  unfold EventsPost at h
  split at h
  · rw [resumeAfter_success_logs hk, h, h0, Array.empty_append]
  · subst h; rw [resumeAfter_revert_logs hk, Array.append_empty]
  · exact h.elim

/-- **Top level.** A frame summary `EventsPost` of a top-level call gives the logs of the
result of `processMessageCall`: exactly `L` (on revert, `L = #[]`). -/
theorem events_call {ctx : Context} {w : World} {tr : TransientStorage} {code : ByteArray}
    {a caller : Address} {data : ByteArray} {gas : Nat} {wa : AddressSet} {wk : StorageKeySet}
    {L : Array Log} (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hdel : delegatedAddress? code = none) (hpre : Precompile.isPrecompile ctx.fork a = false)
    (h : Halts (startMachine ctx w tr (callMsg code a caller data gas wa wk))
      (EventsPost (startMachine ctx w tr (callMsg code a caller data gas wa wk)) L)) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res,
      processMessageCall fuel ctx w tr (callMsg code a caller data gas wa wk) = .ok res ∧
      res.logs = L := by
  obtain ⟨n, hn⟩ := processMessageCall_of_halts (a := a)
    (msg := callMsg code a caller data gas wa wk) hdeleg hdel rfl rfl hpre rfl rfl h
  refine ⟨n, fun fuel hle => ?_⟩
  obtain ⟨mf, o, hH, hs, hrun⟩ := hn fuel hle
  refine ⟨_, hrun, ?_⟩
  have hk : mf.frame.kind = .call 0 0 := hs.kind
  unfold EventsPost at hH
  split at hH
  · rw [topLevelResult_logs_success hk, hH, startMachine_logs, Array.empty_append]
  · subst hH; rfl
  · exact hH.elim

theorem logs_of_processMessageCall {fuel : Nat} {ctx : Context} {w : World} {tr : TransientStorage}
    {msg : Message} {r : MessageResult} (h : processMessageCall fuel ctx w tr msg = .ok r)
    {L : Array Log} (hs : r.success = true → r.logs = L) (hf : r.success = false → L = #[]) :
    r.logs = L := by
  cases hr : r.success
  · rw [processMessageCall_logs_of_fail h hr, hf hr]
  · exact hs hr

end Examples.Solmate.ERC4626
