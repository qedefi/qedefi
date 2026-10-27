import QEDefi.ERC20.Spec.Bytecode
import EvmLogic.Program.SummaryDeleg
import EvmLogic.Tx.Lift

/-!
# What every token gets from `ERC20Spec`: top-level calls and transactions

`ERC20Spec code abs M g₀ sel ops` is a statement about frames. Here it is lifted, once for every
token, to the result of `processMessageCall` for a top-level call to the token, for every
transaction type (EIP-7702 authorizations included), and to whole transactions
(`EvmLean.Tx.process`).

* `TopLevel.Msg`: the hypotheses of a top-level call to the token at `a` (its code is real code,
  not a precompile, no value, calldata payable). `TopLevel.start`: the machine the interpreter
  starts, after the authorizations; `TopLevel.Msg.start_ok`: it satisfies `Start`
  (`start_startMachine`).
* `TopLevel.Ends`: `processMessageCall` terminates, and every result it returns (at any fuel)
  satisfies a property. `TopLevel.call`, `view`, `fallback`, `op`: the results of the four
  obligations, through `abs`: `Shows` (success, return data, model state, frame, transient
  storage, logs) or `Failed`; `call_normal` … with enough gas and outside a static context.
* `TopLevel.tx_call`: a successful transaction calling the token leaves the token in the model's
  state after the call, or (out of gas, or a failing model call) in its state before.
-/

namespace QEDefi.ERC20.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Solidity

variable {σ E : Type}

namespace TopLevel

/-! ## Results of top-level calls -/

/-- **A failed top-level message result** from the world `w₀` and transient storage `tr`: not
successful, everything rolled back, no logs. -/
def Failed (w₀ : World) (tr : TransientStorage) (r : MessageResult) : Prop :=
  r.success = false ∧ r.world = w₀ ∧ r.transientStorage = tr ∧ r.logs = #[]

/-- **The result `r` of a top-level call to the token at `a` shows the model result `res`**
(with events `evs`), from the world `w₀` and transient storage `tr` the call ran in: on success,
the model's return data, the model's new state through `abs`, nothing changed outside the
token's footprint (`FrameKeeps`), transient storage kept, exactly the model's events logged; on
failure, rolled back, by `REVERT` or by an exceptional halt (all gas consumed) as the model
says. -/
def Shows (abs : TokenAbs σ) (crypto : Crypto) (Act : Finset Address) (a : Address) (w₀ : World)
    (tr : TransientStorage) (evs : List (Event Address)) (r : MessageResult) : Result σ → Prop
  | .ok s' ret =>
    r.success = true ∧ r.output = retBytes ret ∧ abs.read crypto Act r.world a = s' ∧
      FrameKeeps abs crypto Act a w₀ r.world ∧ r.transientStorage = tr ∧
      r.logs = (evs.map (eventLog a)).toArray
  | .halt .revert => Failed w₀ tr r ∧ r.reverted = true
  | .halt .invalid => Failed w₀ tr r ∧ r.reverted = false ∧ r.gasLeft = 0

/-- **`processMessageCall` ends with results satisfying `P`**: it returns a result for all large
enough fuel, and every result it returns, at any fuel, satisfies `P`. -/
def Ends (ctx : Context) (w : World) (tr : TransientStorage) (msg : Message)
    (P : MessageResult → Prop) : Prop :=
  (∃ n, ∀ fuel, n ≤ fuel → ∃ r, processMessageCall fuel ctx w tr msg = .ok r) ∧
    ∀ fuel r, processMessageCall fuel ctx w tr msg = .ok r → P r

theorem Ends.mono {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    {P Q : MessageResult → Prop} (h : Ends ctx w tr msg P) (hPQ : ∀ r, P r → Q r) :
    Ends ctx w tr msg Q :=
  ⟨h.1, fun fuel r hr => hPQ r (h.2 fuel r hr)⟩

/-- **Fuel monotonicity of `processMessageCall`**: once it has a result, more fuel gives the
same result. -/
theorem processMessageCall_mono {n n' : Nat} {ctx : Context} {w : World} {tr : TransientStorage}
    {msg : Message} {r : MessageResult} (h : processMessageCall n ctx w tr msg = .ok r)
    (hle : n ≤ n') : processMessageCall n' ctx w tr msg = .ok r := by
  unfold processMessageCall processMessageCallWith at h ⊢
  generalize applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg = d
    at h ⊢
  obtain ⟨w', msg', refund⟩ := d
  dsimp only at h ⊢
  split at h
  · exact h
  · rename_i m hi
    cases hr : run n m with
    | error e => rw [hr] at h; cases h
    | ok r0 =>
      rw [hr] at h
      rw [run_mono hr hle]
      exact h

/-- **Results at every fuel**: a result for all large enough fuel satisfying `P` gives `Ends`. -/
theorem ends_of_eventually {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    {P : MessageResult → Prop}
    (h : ∃ n, ∀ fuel, n ≤ fuel → ∃ r, processMessageCall fuel ctx w tr msg = .ok r ∧ P r) :
    Ends ctx w tr msg P := by
  obtain ⟨n, hn⟩ := h
  refine ⟨⟨n, fun fuel hle => (hn fuel hle).imp fun _ h => h.1⟩, fun fuel r hr => ?_⟩
  obtain ⟨r', hr', hP⟩ := hn (max n fuel) (Nat.le_max_left _ _)
  rw [processMessageCall_mono hr (Nat.le_max_right _ _)] at hr'
  cases hr'
  exact hP

/-! ## Starting a top-level frame -/

/-- **`Start` holds for the machine of a top-level call** (`startMachine`): its snapshot is
`(w, tr)` and no value moves (`transferValue_zero`). -/
theorem start_startMachine {code : ByteArray} {abs : TokenAbs σ} {M : TokenModel σ Address E}
    {Act : Finset Address} {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    (hcode : msg.code = code) (hval : msg.value = 0) (hsize : msg.data.size < 2 ^ 64)
    (hcaller : msg.caller ∈ Act) (hsound : abs.Sound ctx.crypto Act)
    (hwf : M.wf (abs.read ctx.crypto Act w msg.currentTarget))
    (hhas : (w.code msg.currentTarget).size ≠ 0)
    (hbound : (w.code msg.currentTarget).size < 2 ^ 256) :
    Start code abs M Act (startMachine ctx w tr msg) where
  fresh := hcode ▸ fresh_startMachine ctx w tr msg
  launched := (transferValue_zero w msg hval).symm
  value := .inl hval
  precompiles := rfl
  size := hsize
  caller := hcaller
  sound := hsound
  wf := hwf
  hasCode := hhas
  codeBound := hbound

/-- **A top-level call to the token at `a`**: `a` holds the token's code `code`, which is real
code (not empty, not an EIP-7702 designator, shorter than `2²⁵⁶` bytes: EIP-170 caps deployed
code at 24576), and is not a precompile; the message calls `a`
and runs its code, at depth zero, with no value, and its calldata is shorter than `2⁶⁴`
bytes (`Start.size`). Transactions build such messages (`tx_call`). -/
structure Msg (code : ByteArray) (ctx : Context) (w : World) (msg : Message) (a : Address) :
    Prop where
  atA : w.code a = code
  real : code.size ≠ 0
  bound : code.size < 2 ^ 256
  deleg : delegatedAddress? code = none
  msgCode : msg.code = code
  target : msg.target = some a
  codeAddress : msg.codeAddress = some a
  current : msg.currentTarget = a
  pre : Precompile.isPrecompile ctx.fork a = false
  value : msg.value = 0
  depth : msg.depth = 0
  size : msg.data.size < 2 ^ 64

/-- The world a top-level call runs in: after the transaction's authorizations. -/
abbrev world (ctx : Context) (w : World) (msg : Message) : World := (delegated ctx w msg).1

/-- The message a top-level call runs: after the transaction's authorizations. -/
abbrev dmsg (ctx : Context) (w : World) (msg : Message) : Message := (delegated ctx w msg).2.1

/-- The machine a top-level call starts. -/
abbrev start (ctx : Context) (w : World) (tr : TransientStorage) (msg : Message) : Machine :=
  startMachine ctx (world ctx w msg) tr (dmsg ctx w msg)

/-- The authorizations keep everything but the code, nonce and storage of accounts holding no
code or a designator: the calldata is kept. -/
theorem dmsg_data (ctx : Context) (w : World) (msg : Message) :
    (dmsg ctx w msg).data = msg.data := by
  unfold dmsg delegated applyTopLevelDelegation
  split
  · rfl
  · split
    · rfl
    · rfl
    · generalize (if ctx.tx.authorizations.isEmpty = true then _ else _) = t
      obtain ⟨w', warm, refund, code'⟩ := t
      dsimp only
      split <;> rfl

namespace Msg

variable {code : ByteArray} {ctx : Context} {w : World} {msg : Message} {a : Address}

/-- The authorizations leave the token's account. -/
theorem account (h : Msg code ctx w msg a) : (world ctx w msg).account a = w.account a :=
  (applyTopLevelDelegation_frame ctx _ w msg).1.account_eq (by rw [h.atA]; exact h.real)
    (by rw [h.atA]; exact h.deleg)

theorem worldCode (h : Msg code ctx w msg a) : (world ctx w msg).code a = code := by
  show ((world ctx w msg).account a).code = code
  rw [h.account]; exact h.atA

/-- The token's model state is the same after the authorizations. -/
theorem read (h : Msg code ctx w msg a) (abs : TokenAbs σ) (crypto : Crypto)
    (Act : Finset Address) :
    abs.read crypto Act (world ctx w msg) a = abs.read crypto Act w a :=
  abs.read_congr crypto Act w (world ctx w msg) a
    (fun k _ => by simp only [World.sload, h.account])
    (by simp only [World.balance, h.account])

/-- What the authorizations keep of the message. -/
theorem dmsg_facts (h : Msg code ctx w msg a) :
    (dmsg ctx w msg).code = code ∧ (dmsg ctx w msg).currentTarget = a ∧
      (dmsg ctx w msg).caller = msg.caller ∧ (dmsg ctx w msg).target = some a ∧
      (dmsg ctx w msg).gas = msg.gas ∧ (dmsg ctx w msg).value = 0 ∧
      (dmsg ctx w msg).isStatic = msg.isStatic ∧ (dmsg ctx w msg).data = msg.data := by
  obtain ⟨-, hct, hcaller, htarget, -, hstatic, hgas, hval, -, -, hc⟩ :=
    applyTopLevelDelegation_frame ctx (PrecompileImpl.standard ctx).isPrecompile w msg
  have hcode := ((hc a (h.msgCode.trans h.atA.symm) h.codeAddress).1
    (by rw [h.worldCode]; exact h.deleg)).1
  refine ⟨hcode.trans h.worldCode, hct.trans h.current, hcaller, htarget.trans h.target, hgas,
    hval.trans h.value, hstatic, dmsg_data ctx w msg⟩

/-- **`Start` for a top-level call to the token**, in the world after the authorizations. -/
theorem start_ok (h : Msg code ctx w msg a) {abs : TokenAbs σ} {M : TokenModel σ Address E}
    {Act : Finset Address} (tr : TransientStorage) (hcaller : msg.caller ∈ Act)
    (hsound : abs.Sound ctx.crypto Act) (hwf : M.wf (abs.read ctx.crypto Act w a)) :
    Start code abs M Act (start ctx w tr msg) := by
  obtain ⟨hcode, hct, hcl, -, -, hval, -, hdata⟩ := h.dmsg_facts
  refine start_startMachine hcode hval (by rw [hdata]; exact h.size) (by rw [hcl]; exact hcaller)
    hsound ?_ ?_ ?_
  · rw [hct, h.read]; exact hwf
  · rw [hct, h.worldCode]; exact h.real
  · rw [hct, h.worldCode]; exact h.bound

/-- The model state at the start of the frame is the token's state before the call. -/
theorem pre_start (h : Msg code ctx w msg a) (abs : TokenAbs σ) (Act : Finset Address)
    (tr : TransientStorage) :
    Spec.pre abs Act (start ctx w tr msg) = abs.read ctx.crypto Act w a := by
  show abs.read ctx.crypto Act (world ctx w msg) (dmsg ctx w msg).currentTarget = _
  rw [h.dmsg_facts.2.1, h.read]

/-- The top-level result of the frame ending `(mf, o)`. -/
abbrev result (ctx : Context) (w : World) (msg : Message) (mf : Machine) (o : Outcome) :
    MessageResult :=
  addRefund (delegated ctx w msg).2.2
    (topLevelResult msg.target (frameResult mf o).2.1 (frameResult mf o).2.2 (frameResult mf o).1)

/-- **Top-level glue for the token**: a frame summary of the start machine gives `Ends`. -/
theorem ends (h : Msg code ctx w msg a) {tr : TransientStorage} {H : Machine → Outcome → Prop}
    {P : MessageResult → Prop} (hH : Halts (start ctx w tr msg) H)
    (hP : ∀ mf o, SameFrame (start ctx w tr msg) mf → H mf o → P (result ctx w msg mf o)) :
    Ends ctx w tr msg P := by
  apply ends_of_eventually
  obtain ⟨n, hn⟩ := processMessageCall_of_halts_7702 (h.msgCode.trans h.atA.symm)
    (by rw [h.worldCode]; exact h.deleg) h.target h.codeAddress h.pre h.value h.depth hH
  exact ⟨n, fun fuel hle => by
    obtain ⟨mf, o, hHo, hs, hr⟩ := hn fuel hle
    exact ⟨_, hr, hP mf o hs hHo⟩⟩

theorem result_success {tr : TransientStorage} {mf : Machine} {out : ByteArray}
    (hs : SameFrame (start ctx w tr msg) mf) :
    (result ctx w msg mf (.success out)).success = true ∧
      (result ctx w msg mf (.success out)).output = out ∧
      (result ctx w msg mf (.success out)).world = mf.world ∧
      (result ctx w msg mf (.success out)).transientStorage = mf.transient ∧
      (result ctx w msg mf (.success out)).logs = mf.frame.sub.logs := by
  have hk : mf.frame.kind = .call 0 0 := hs.kind
  obtain ⟨h1, h2, h3, -, h5⟩ := topLevelResult_success_call (t := msg.target) (out := out) hk
  refine ⟨h1, h2, h3, ?_, h5⟩
  simp only [result, addRefund, frameResult_success_call hk]
  unfold topLevelResult
  split <;> rfl

theorem result_fail {tr : TransientStorage} {mf : Machine} {o : Outcome}
    (hs : SameFrame (start ctx w tr msg) mf) (ho : Fails o) :
    Failed (world ctx w msg) tr (result ctx w msg mf o) ∧
      (∀ out, o = .revert out → (result ctx w msg mf o).reverted = true) ∧
      (∀ e, o = .halt e →
        (result ctx w msg mf o).reverted = false ∧ (result ctx w msg mf o).gasLeft = 0) := by
  have hsnap : mf.frame.snapshot = (world ctx w msg, tr) := hs.snapshot
  match o, ho with
  | .revert out, _ =>
    simp only [result, addRefund, frameResult_revert, hsnap, topLevelResult, Failed,
      ChildResult.success, MessageResult.success]
    simp
  | .halt e, _ =>
    simp only [result, addRefund, frameResult_halt, hsnap, topLevelResult, Failed,
      ChildResult.success, MessageResult.success]
    simp

/-- **A frame matching the model gives a result showing it.** -/
theorem shows_of_matches (h : Msg code ctx w msg a) {abs : TokenAbs σ} {Act : Finset Address}
    {tr : TransientStorage} {mf : Machine} {o : Outcome} {evs : List (Event Address)}
    {res : Result σ} (hs : SameFrame (start ctx w tr msg) mf)
    (hm : Matches abs Act (start ctx w tr msg) mf o evs res) :
    Shows abs ctx.crypto Act a (world ctx w msg) tr evs (result ctx w msg mf o) res := by
  have hct : (start ctx w tr msg).frame.msg.currentTarget = a := h.dmsg_facts.2.1
  match res, hm with
  | .ok s' ret, ⟨ho, hread, hkeep, htr, _, hlogs⟩ =>
    subst ho
    obtain ⟨r1, r2, r3, r4, r5⟩ := result_success (ctx := ctx) (w := w) (msg := msg)
      (out := retBytes ret) hs
    rw [hct] at hread hkeep hlogs
    refine ⟨r1, r2, by rw [r3]; exact hread, by rw [r3]; exact hkeep, by rw [r4]; exact htr, ?_⟩
    rw [r5, hlogs]
    show #[] ++ _ = _
    simp
  | .halt .revert, ⟨out, ho⟩ =>
    subst ho
    have := result_fail (ctx := ctx) (w := w) (msg := msg) hs (o := .revert out) trivial
    exact ⟨this.1, this.2.1 out rfl⟩
  | .halt .invalid, ⟨e, ho⟩ =>
    subst ho
    have := result_fail (ctx := ctx) (w := w) (msg := msg) hs (o := .halt e) trivial
    exact ⟨this.1, this.2.2 e rfl⟩

theorem normal_start (h : Msg code ctx w msg a) {tr : TransientStorage} {g₀ : Nat} :
    Normal g₀ (start ctx w tr msg) ↔ g₀ ≤ msg.gas ∧ msg.isStatic = false := by
  obtain ⟨-, -, -, -, hgas, hval, hstatic, -⟩ := h.dmsg_facts
  show g₀ ≤ (dmsg ctx w msg).gas ∧ (dmsg ctx w msg).isStatic = false ∧ (dmsg ctx w msg).value = 0
    ↔ _
  rw [hgas, hval, hstatic]
  simp

end Msg

/-! ## The four obligations at the top level

Every statement holds for every set of actors `Act` containing the sender and the accounts the
call names, whose hash hypotheses hold; the model state is the token as they see it. -/

variable {code : ByteArray} {abs : TokenAbs σ} {M : TokenModel σ Address E} {g₀ : Nat}
  {Act : Finset Address} {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
  {a : Address}

/-- **An ERC-20 call at the top level.** A top-level call to the token whose calldata encodes
`c` ends; for actors containing the sender and the accounts of `c`, each result shows the
model's outcome of `c` by the sender in the token's state before the call (through `abs`), or,
with less than `g₀` gas or in a static context, failed. -/
theorem call {c : Call Address} (hc : CallSpec code abs M g₀ c) (h : Msg code ctx w msg a)
    (hcaller : msg.caller ∈ Act) (haddrs : ∀ x ∈ c.addrs, x ∈ Act)
    (hsound : abs.Sound ctx.crypto Act) (hwf : M.wf (abs.read ctx.crypto Act w a))
    (he : c.Encodes msg.data) :
    Ends ctx w tr msg fun r =>
      Shows abs ctx.crypto Act a (world ctx w msg) tr
        (M.events (abs.read ctx.crypto Act w a) msg.caller c) r
        (M.call (abs.read ctx.crypto Act w a) msg.caller c) ∨
      (Failed (world ctx w msg) tr r ∧ ¬ (g₀ ≤ msg.gas ∧ msg.isStatic = false)) := by
  obtain ⟨-, -, hcl, -, -, -, -, hdata⟩ := h.dmsg_facts
  have hs := h.start_ok tr hcaller hsound hwf (M := M)
  refine h.ends (hc Act _ hs (by show c.Encodes (dmsg ctx w msg).data; rw [hdata]; exact he)
    haddrs) fun mf o hsf hH => ?_
  have hpre := h.pre_start abs Act tr
  have hcl' : (start ctx w tr msg).frame.msg.caller = msg.caller := hcl
  rw [hpre, hcl'] at hH
  rcases hH with hm | ⟨hf, hn⟩
  · exact .inl (h.shows_of_matches hsf hm)
  · exact .inr ⟨(Msg.result_fail hsf hf).1, fun hn' => hn (h.normal_start.2 hn')⟩

/-- **An ERC-20 call at the top level, with enough gas**: every result shows the model's
outcome. -/
theorem call_normal {c : Call Address} (hc : CallSpec code abs M g₀ c) (h : Msg code ctx w msg a)
    (hcaller : msg.caller ∈ Act) (haddrs : ∀ x ∈ c.addrs, x ∈ Act)
    (hsound : abs.Sound ctx.crypto Act) (hwf : M.wf (abs.read ctx.crypto Act w a))
    (he : c.Encodes msg.data) (hgas : g₀ ≤ msg.gas) (hstatic : msg.isStatic = false) :
    Ends ctx w tr msg fun r =>
      Shows abs ctx.crypto Act a (world ctx w msg) tr
        (M.events (abs.read ctx.crypto Act w a) msg.caller c) r
        (M.call (abs.read ctx.crypto Act w a) msg.caller c) :=
  (call hc h hcaller haddrs hsound hwf he).mono fun _ hr =>
    hr.resolve_right fun hf => hf.2 ⟨hgas, hstatic⟩

/-- **A view at the top level**: each result returns one word holding the model's value and
changes nothing (world, transient storage, no logs); or, with less than `g₀` gas, failed. -/
theorem view {v : View} (hv : ViewSpec code abs M g₀ v) (h : Msg code ctx w msg a)
    (hcaller : msg.caller ∈ Act) (haddrs : ∀ x ∈ v.addrs, x ∈ Act)
    (hsound : abs.Sound ctx.crypto Act) (hwf : M.wf (abs.read ctx.crypto Act w a))
    (he : v.Encodes msg.data) :
    Ends ctx w tr msg fun r =>
      (r.success = true ∧ (∃ x : Word, r.output = Bytes.ofWord x ∧
        x.toNat = v.value M (abs.read ctx.crypto Act w a)) ∧
        r.world = world ctx w msg ∧ r.transientStorage = tr ∧ r.logs = #[]) ∨
      (Failed (world ctx w msg) tr r ∧ ¬ g₀ ≤ msg.gas) := by
  obtain ⟨-, -, -, -, hgas, hval, -, hdata⟩ := h.dmsg_facts
  have hs := h.start_ok tr hcaller hsound hwf (M := M)
  refine h.ends (hv Act _ hs (by show v.Encodes (dmsg ctx w msg).data; rw [hdata]; exact he)
    haddrs) fun mf o hsf hH => ?_
  rw [h.pre_start abs Act tr] at hH
  rcases hH with ⟨x, ho, hx, hw, htr, -, hlogs⟩ | ⟨hf, hn⟩
  · subst ho
    obtain ⟨r1, r2, r3, r4, r5⟩ := Msg.result_success (ctx := ctx) (w := w) (msg := msg)
      (out := Bytes.ofWord x) hsf
    refine .inl ⟨r1, ⟨x, r2, hx⟩, by rw [r3, hw]; rfl, by rw [r4, htr]; rfl, by rw [r5, hlogs]; rfl⟩
  · refine .inr ⟨(Msg.result_fail hsf hf).1, fun hn' => hn ⟨?_, ?_⟩⟩
    · show g₀ ≤ (dmsg ctx w msg).gas; rw [hgas]; exact hn'
    · exact hval

/-- **Unknown selectors and short calldata at the top level** end as the model's fallback call
(`.other 0`: no value), or, with less than `g₀` gas or in a static context, fail. -/
theorem fallback {sel : List Nat} (hf : FallbackSpec code abs M g₀ sel) (h : Msg code ctx w msg a)
    (hcaller : msg.caller ∈ Act) (hsound : abs.Sound ctx.crypto Act)
    (hwf : M.wf (abs.read ctx.crypto Act w a))
    (hd : msg.data.size < 4 ∨ Abi.selectorOf msg.data ∉ sel) :
    Ends ctx w tr msg fun r =>
      Shows abs ctx.crypto Act a (world ctx w msg) tr
        (M.events (abs.read ctx.crypto Act w a) msg.caller (.other 0)) r
        (M.call (abs.read ctx.crypto Act w a) msg.caller (.other 0)) ∨
      (Failed (world ctx w msg) tr r ∧ ¬ (g₀ ≤ msg.gas ∧ msg.isStatic = false)) := by
  obtain ⟨-, -, hcaller', -, hgas, hval, hstatic, hdata⟩ := h.dmsg_facts
  have hs := h.start_ok tr hcaller hsound hwf (M := M)
  have hd' : (start ctx w tr msg).frame.msg.data.size < 4 ∨
      Abi.selectorOf (start ctx w tr msg).frame.msg.data ∉ sel := by
    show (dmsg ctx w msg).data.size < 4 ∨ Abi.selectorOf (dmsg ctx w msg).data ∉ sel
    rw [hdata]; exact hd
  refine h.ends (hf Act _ hs hd') fun mf o hsf hH => ?_
  have hcl : (start ctx w tr msg).frame.msg.caller = msg.caller := hcaller'
  have hv : (start ctx w tr msg).frame.msg.value.toNat = 0 := by
    show (dmsg ctx w msg).value.toNat = 0; rw [hval]; rfl
  rw [h.pre_start abs Act tr, hcl, hv] at hH
  rcases hH with hm | ⟨hf, hn⟩
  · exact .inl (h.shows_of_matches hsf hm)
  · refine .inr ⟨(Msg.result_fail hsf hf).1, fun ⟨h1, h2⟩ => hn ⟨?_, ?_⟩⟩
    · show g₀ ≤ (dmsg ctx w msg).gas; rw [hgas]; exact h1
    · show (dmsg ctx w msg).isStatic = false; rw [hstatic]; exact h2

/-- **Another entry point at the top level** (calldata the token's decoder `ops` maps to `e`,
whose accounts are actors): each result has the model's state `M.op` (success exactly when it
succeeds), nothing changed outside the footprint; or, with less than `g₀` gas or in a static
context, failed. -/
theorem op {ops : Address → ByteArray → ℕ → Option E} {opAddrs : E → List Address} {e : E}
    (hop : OpSpec code abs M g₀ ops opAddrs) (h : Msg code ctx w msg a)
    (hcaller : msg.caller ∈ Act) (haddrs : ∀ x ∈ opAddrs e, x ∈ Act)
    (hsound : abs.Sound ctx.crypto Act) (hwf : M.wf (abs.read ctx.crypto Act w a))
    (he : ops msg.caller msg.data 0 = some e) :
    Ends ctx w tr msg fun r =>
      (match M.op (abs.read ctx.crypto Act w a) e with
        | some s' => r.success = true ∧ abs.read ctx.crypto Act r.world a = s' ∧
          FrameKeeps abs ctx.crypto Act a (world ctx w msg) r.world ∧ r.transientStorage = tr
        | none => Failed (world ctx w msg) tr r) ∨
      (Failed (world ctx w msg) tr r ∧ ¬ (g₀ ≤ msg.gas ∧ msg.isStatic = false)) := by
  obtain ⟨-, hct, hcaller', -, hgas, hval, hstatic, hdata⟩ := h.dmsg_facts
  have hs := h.start_ok tr hcaller hsound hwf (M := M)
  have he' : ops (start ctx w tr msg).frame.msg.caller (start ctx w tr msg).frame.msg.data
      (start ctx w tr msg).frame.msg.value.toNat = some e := by
    show ops (dmsg ctx w msg).caller (dmsg ctx w msg).data (dmsg ctx w msg).value.toNat = _
    rw [hcaller', hdata, hval]; exact he
  refine h.ends (hop Act _ e hs he' haddrs) fun mf o hsf hH => ?_
  have hct' : (start ctx w tr msg).frame.msg.currentTarget = a := hct
  unfold OpMatches at hH
  rw [h.pre_start abs Act tr] at hH
  rcases hH with hm | ⟨hf, hn⟩
  · refine .inl ?_
    revert hm
    cases M.op (abs.read ctx.crypto Act w a) e with
    | some s' =>
      rintro ⟨⟨out, ho⟩, hread, hkeep, htr, -⟩
      subst ho
      obtain ⟨r1, -, r3, r4, -⟩ := Msg.result_success (ctx := ctx) (w := w) (msg := msg)
        (out := out) hsf
      rw [hct'] at hread hkeep
      exact ⟨r1, by rw [r3]; exact hread, by rw [r3]; exact hkeep, by rw [r4]; exact htr⟩
    | none => exact fun hf => (Msg.result_fail hsf hf).1
  · refine .inr ⟨(Msg.result_fail hsf hf).1, fun ⟨h1, h2⟩ => hn ⟨?_, ?_⟩⟩
    · show g₀ ≤ (dmsg ctx w msg).gas; rw [hgas]; exact h1
    · show (dmsg ctx w msg).isStatic = false; rw [hstatic]; exact h2

/-! ## Model state after a top-level call -/

/-- **The token's model state after an ERC-20 call at the top level**, as the actors see it:
the model's new state if the model call succeeds and the message succeeded, else the state
before. -/
theorem call_read {c : Call Address} (hc : CallSpec code abs M g₀ c) (h : Msg code ctx w msg a)
    (hcaller : msg.caller ∈ Act) (haddrs : ∀ x ∈ c.addrs, x ∈ Act)
    (hsound : abs.Sound ctx.crypto Act) (hwf : M.wf (abs.read ctx.crypto Act w a))
    (he : c.Encodes msg.data) {fuel : Nat} {r : MessageResult}
    (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    (∃ ret, r.success = true ∧ M.call (abs.read ctx.crypto Act w a) msg.caller c =
      .ok (abs.read ctx.crypto Act r.world a) ret) ∨
    (r.success = false ∧ abs.read ctx.crypto Act r.world a = abs.read ctx.crypto Act w a ∧
      ((∃ s' ret, M.call (abs.read ctx.crypto Act w a) msg.caller c = .ok s' ret) →
        ¬ (g₀ ≤ msg.gas ∧ msg.isStatic = false))) := by
  have hfail : Failed (world ctx w msg) tr r →
      r.success = false ∧ abs.read ctx.crypto Act r.world a = abs.read ctx.crypto Act w a :=
    fun hf => ⟨hf.1, by rw [hf.2.1]; exact h.read abs ctx.crypto Act⟩
  rcases (call (tr := tr) hc h hcaller haddrs hsound hwf he).2 fuel r hr with hs | ⟨hf, hn⟩
  · revert hs
    cases hres : M.call (abs.read ctx.crypto Act w a) msg.caller c with
    | ok s' ret =>
      rintro ⟨hsucc, -, hread, -⟩
      exact .inl ⟨ret, hsucc, by rw [hread]⟩
    | halt k =>
      intro hs
      have hf : Failed (world ctx w msg) tr r := by
        cases k with
        | revert => exact hs.1
        | invalid => exact hs.1
      exact .inr ⟨(hfail hf).1, (hfail hf).2, fun ⟨_, _, hok⟩ => by cases hok⟩
  · exact .inr ⟨(hfail hf).1, (hfail hf).2, fun _ => hn⟩

/-! ## Transactions -/

theorem prepareMessage_data_call {crypto : Crypto} {fork : Fork} {env : BlockEnv} {w : World}
    {tx : Transaction} {s : Address} {n g : Nat} {t : Address} (h : tx.to = some t) :
    (EvmLean.Tx.prepareMessage crypto fork env w tx s n g).data = tx.data := by
  unfold EvmLean.Tx.prepareMessage; rw [h]

/-- **A transaction calling the token.** A successful transaction (any type, fork, block,
authorizations) whose recipient is the token at `a` (real code `code`, not a precompile, not the
block's coinbase, which the transaction's reward would pay), with no value and calldata encoding
the ERC-20 call `c`, leaves the token, as actors containing its sender and the accounts of `c`
see it, in the model's state after `c` by the transaction's sender (`out.sender`), or in its
state before; in its state before when the model call fails; and in the model's state after
when the message had at least `g₀` gas (the transaction's gas less its intrinsic gas). -/
theorem tx_call {c : Call Address} (hc : CallSpec code abs M g₀ c) {fuel : Nat} {crypto : Crypto}
    {fork : Fork} {env : BlockEnv} {gasAvail blobAvail : Nat} {w : World}
    {tx : Transaction} {hint : Option Address} {out : EvmLean.Tx.TxOutput}
    (hp : EvmLean.Tx.process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out)
    (hto : tx.to = some a) (hcode : w.code a = code) (hreal : code.size ≠ 0)
    (hbound : code.size < 2 ^ 256)
    (hdel : delegatedAddress? code = none) (hpre : Precompile.isPrecompile fork a = false)
    (hcb : a ≠ env.coinbase) (hval : tx.value = 0) (hsize : tx.data.size < 2 ^ 64)
    (hcaller : out.sender ∈ Act) (haddrs : ∀ x ∈ c.addrs, x ∈ Act)
    (hsound : abs.Sound crypto Act) (hwf : M.wf (abs.read crypto Act w a))
    (he : c.Encodes tx.data) :
    (∃ ret, M.call (abs.read crypto Act w a) out.sender c =
      .ok (abs.read crypto Act out.world a) ret) ∨
    (abs.read crypto Act out.world a = abs.read crypto Act w a ∧
      ((∃ s' ret, M.call (abs.read crypto Act w a) out.sender c = .ok s' ret) →
        tx.gas < g₀ + (EvmLean.Tx.intrinsicGas tx).regular)) := by
  obtain ⟨i, ck, r, gu, hv, hck, hr, -, hout, hsender, -⟩ := EvmLogic.Tx.process_ok hp
  have hvi := EvmLogic.Tx.validate_ok hv
  have hrc : EvmLogic.Tx.RealCode (w.code a) :=
    EvmLogic.Tx.realCode_of_deleg (by rw [hcode]; exact hreal) (by rw [hcode]; exact hdel)
  have hsa : a ≠ ck.sender := fun e => EvmLogic.Tx.not_realCode_sender hck (e ▸ hrc)
  rw [hsender] at hcaller
  set s := ck.sender
  set w₁ := EvmLogic.Tx.prefixWorld w s
    (BitVec.ofNat 256 ((w.account s).balance.toNat - EvmLogic.Tx.upfrontFee fork env tx ck))
  have hacc : w₁.account a = w.account a := by
    rw [EvmLogic.Tx.account_prefixWorld]; simp only [hsa, ite_false]
  have hcode₁ : w₁.code a = code := by
    show (w₁.account a).code = code; rw [hacc]; exact hcode
  have hread₁ : abs.read crypto Act w₁ a = abs.read crypto Act w a :=
    abs.read_congr crypto Act w w₁ a (fun k _ => by simp only [World.sload, hacc])
      (by simp only [World.balance, hacc])
  set msg := EvmLean.Tx.prepareMessage crypto fork env w₁ tx s (w.account s).nonce
    (tx.gas - i.regular)
  obtain ⟨hct, hmc, hca⟩ := EvmLogic.Tx.prepareMessage_call crypto fork env tx w₁ s
    (w.account s).nonce (tx.gas - i.regular) hto
  have hdata : msg.data = tx.data := TopLevel.prepareMessage_data_call hto
  have hm : Msg code (EvmLogic.Tx.txContext crypto fork env tx ck) w₁ msg a :=
    { atA := hcode₁, real := hreal, bound := hbound, deleg := hdel, msgCode := hmc.trans hcode₁
      target := by rw [EvmLogic.Tx.prepareMessage_target, hto]
      codeAddress := hca, current := hct, pre := hpre
      value := by rw [EvmLogic.Tx.prepareMessage_value, hval]; rfl
      depth := EvmLogic.Tx.prepareMessage_depth ..
      size := by rw [hdata]; exact hsize }
  have hmcaller : msg.caller = s := EvmLogic.Tx.prepareMessage_caller ..
  have hmgas : msg.gas = tx.gas - i.regular := EvmLogic.Tx.prepareMessage_gas ..
  have hmstatic : msg.isStatic = false := EvmLogic.Tx.prepareMessage_isStatic ..
  have hres := call_read (tr := ∅) hc hm (by rw [hmcaller]; exact hcaller) haddrs hsound
    (by rw [EvmLogic.Tx.txContext_crypto, hread₁]; exact hwf) (by rw [hdata]; exact he) hr
  simp only [EvmLogic.Tx.txContext_crypto, hread₁, hmcaller, hmgas, hmstatic] at hres
  -- the suffix keeps the token's state
  obtain ⟨hnd, hsz⟩ := EvmLogic.Tx.processMessageCall_realCode hr
    (by rw [hcode₁]; exact EvmLogic.Tx.realCode_of_deleg hreal hdel)
  have hkeep := EvmLogic.Tx.keep_suffixWorld hsz hnd s env.coinbase
    ((tx.gas - gu) * ck.effectiveGasPrice) (gu * (ck.effectiveGasPrice - env.baseFee))
  have hpost : abs.read crypto Act out.world a = abs.read crypto Act r.world a := by
    rw [hout]
    refine abs.read_congr crypto Act _ _ a (fun k _ => ?_) ?_
    · simp only [World.sload, hkeep.1]
    · rw [EvmLogic.Tx.balance_suffixWorld _ _ _ _ _ hnd]
      simp only [EvmLogic.Tx.balance_creditBalance, hcb, hsa, ite_false]
  rw [hpost, hsender]
  rcases hres with ⟨ret, -, hok⟩ | ⟨-, hst, hn⟩
  · exact .inl ⟨ret, hok⟩
  · refine .inr ⟨hst, fun hex => ?_⟩
    have h1 := hn hex
    have h2 := hvi.2.1
    rw [← hvi.1]
    by_contra hlt
    exact h1 ⟨by omega, trivial⟩

end TopLevel

end QEDefi.ERC20.Spec
