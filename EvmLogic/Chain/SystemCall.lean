import EvmLogic.Chain.World

/-!
# System calls

A system call (`Block.systemCall`, `process_unchecked_system_transaction`) is a top-level
message call from `SYSTEM_ADDRESS` (`systemMessage`): depth 0, no value transfer, not static,
to a fixed system contract running its own code, with `SYSTEM_TRANSACTION_GAS`, in a context
whose origin is `SYSTEM_ADDRESS`, gas price the base fee and no EIP-7702 authorizations
(`systemContext`). Its world is the message's world after the EIP-161 clean-up
(`systemCall_ok`). The system contracts are the four of `systemContracts` (EIP-4788, EIP-2935,
EIP-7002, EIP-7251), none of them a precompile.

* **No code**: if the target holds no code (`systemCall_of_code_empty`), the call succeeds and
  the world is unchanged, except that the target is erased if it exists and is empty (it is
  touched, EIP-161). A *checked* system call (`checkedSystemCall`, Prague's request dequeues)
  instead makes the block invalid.
* **Protected contracts**: a system call is a `TopOk` top-level message for any set `P` of
  protected accounts not containing `SYSTEM_ADDRESS` (`topOk_systemMessage`), so the nested-call
  simulation applies: `systemCall_good` carries a `GoodOk` predicate across a system call, given
  the frame summaries of the protected frames it reaches (`hsum`, as for
  `processMessageCall_good`). A system contract without code needs nothing
  (`systemCall_good_of_code_empty`).
-/

namespace EvmLogic.Chain
open EvmLean EvmLean.Interpreter EvmLean.Block EvmLogic.Program EvmLogic.Program.Nested

/-- The system contracts called by blocks: EIP-4788 beacon roots (Cancun), EIP-2935 history
storage, EIP-7002 withdrawal requests and EIP-7251 consolidation requests (Prague). -/
def systemContracts : List Address :=
  [beaconRootsAddress, historyStorageAddress, withdrawalRequestAddress,
    consolidationRequestAddress]

/-- The context of a system call. -/
def systemContext (crypto : Crypto) (fork : Fork) (env : BlockEnv) : Context :=
  { crypto, fork, block := env, tx := { origin := systemAddress, gasPrice := env.baseFee } }

/-- The top-level message of a system call to `target` with calldata `data`. -/
def systemMessage (world : World) (target : Address) (data : ByteArray) : Message :=
  { caller := systemAddress, target := some target, currentTarget := target,
    gas := systemTransactionGas, value := 0, data, codeAddress := some target,
    code := world.code target, depth := 0, shouldTransferValue := false,
    isStatic := false, accessedAddresses := ∅, accessedStorageKeys := ∅ }

section Message
variable (world : World) (target : Address) (data : ByteArray)

@[simp] theorem systemMessage_caller : (systemMessage world target data).caller = systemAddress :=
  rfl
@[simp] theorem systemMessage_target : (systemMessage world target data).target = some target :=
  rfl
@[simp] theorem systemMessage_currentTarget :
    (systemMessage world target data).currentTarget = target := rfl
@[simp] theorem systemMessage_codeAddress :
    (systemMessage world target data).codeAddress = some target := rfl
@[simp] theorem systemMessage_code : (systemMessage world target data).code = world.code target :=
  rfl
@[simp] theorem systemMessage_depth : (systemMessage world target data).depth = 0 := rfl
@[simp] theorem systemMessage_gas :
    (systemMessage world target data).gas = systemTransactionGas := rfl
@[simp] theorem systemMessage_value : (systemMessage world target data).value = 0 := rfl
@[simp] theorem systemMessage_shouldTransferValue :
    (systemMessage world target data).shouldTransferValue = false := rfl
@[simp] theorem systemMessage_isStatic : (systemMessage world target data).isStatic = false := rfl
@[simp] theorem systemMessage_disablePrecompiles :
    (systemMessage world target data).disablePrecompiles = false := rfl

end Message

@[simp] theorem systemContext_authorizations (crypto : Crypto) (fork : Fork) (env : BlockEnv) :
    (systemContext crypto fork env).tx.authorizations = [] := rfl

/-- **What a system call is**: the top-level message `systemMessage` in `systemContext`, then
the EIP-161 clean-up of the touched accounts. -/
theorem systemCall_ok {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {world : World} {target : Address} {data : ByteArray} {w' : World} {res : MessageResult} :
    systemCall fuel crypto fork env world target data = .ok (w', res) ↔
      processMessageCall fuel (systemContext crypto fork env) world ∅
          (systemMessage world target data) = .ok res ∧
        w' = Tx.destroyTouchedEmpty res.world res.touchedAccounts := by
  unfold systemCall
  change (do
      let res ← processMessageCall fuel (systemContext crypto fork env) world ∅
        (systemMessage world target data)
      return (Tx.destroyTouchedEmpty res.world res.touchedAccounts, res) :
        Except OutOfFuel (World × MessageResult)) = _ ↔ _
  cases processMessageCall fuel (systemContext crypto fork env) world ∅
      (systemMessage world target data) with
  | error e => simp [bind, Except.bind]
  | ok r =>
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩

/-- The world of a system call is the message's world with some empty accounts erased. -/
theorem eraseEmpty_systemCall {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {world : World} {target : Address} {data : ByteArray} {w' : World} {res : MessageResult}
    (h : systemCall fuel crypto fork env world target data = .ok (w', res)) :
    EraseEmpty res.world w' := by
  obtain ⟨-, rfl⟩ := systemCall_ok.1 h
  exact eraseEmpty_destroyTouchedEmpty _ _

/-- The EIP-4788 call is the system call to the beacon-roots contract with the parent beacon
block root as calldata. -/
theorem beaconRootsCall_ok {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {world w' : World} (h : beaconRootsCall fuel crypto fork env world = .ok w') :
    ∃ res, systemCall fuel crypto fork env world beaconRootsAddress
      (Bytes.ofWord env.parentBeaconBlockRoot) = .ok (w', res) := by
  unfold beaconRootsCall at h
  cases hs : systemCall fuel crypto fork env world beaconRootsAddress
      (Bytes.ofWord env.parentBeaconBlockRoot) with
  | error e => rw [hs] at h; cases h
  | ok p => rw [hs] at h; cases h; exact ⟨p.2, rfl⟩

/-- **A checked system call** (`process_checked_system_transaction`) is a system call to a
contract holding code that succeeds. -/
theorem checkedSystemCall_ok {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {world : World} {target : Address} {data : ByteArray} {w' : World} {out : ByteArray}
    (h : checkedSystemCall fuel crypto fork env world target data = .ok (w', out)) :
    (world.code target).size ≠ 0 ∧ ∃ res, systemCall fuel crypto fork env world target data =
      .ok (w', res) ∧ res.success = true ∧ res.output = out := by
  unfold checkedSystemCall at h
  by_cases hc : (world.code target).size = 0
  · simp only [hc, ↓reduceIte] at h; cases h
  · simp only [hc, ↓reduceIte] at h
    refine ⟨hc, ?_⟩
    cases hs : systemCall fuel crypto fork env world target data with
    | error e => rw [hs] at h; cases h
    | ok p =>
      rw [hs] at h
      obtain ⟨w₁, r⟩ := p
      by_cases hr : r.success = true
      · simp only [Except.mapError, bind, Except.bind, hr, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨r, rfl, hr, rfl⟩
      · simp [Except.mapError, bind, Except.bind, hr, throw, throwThe, MonadExceptOf.throw] at h

/-! ## Precompiles -/

theorem isPrecompile_of_mem_systemContracts (fork : Fork) {a : Address}
    (ha : a ∈ systemContracts) : Precompile.isPrecompile fork a = false := by
  simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> cases fork <;> decide

/-! ## A system contract without code -/

theorem delegatedAddress?_empty : delegatedAddress? ByteArray.empty = none := by decide

/-- **A system call to an account without code** succeeds and leaves the world unchanged,
except that the target is erased if it exists and is empty. `hpre`: the target is not a
precompile, true of every system contract (`isPrecompile_of_mem_systemContracts`). -/
theorem systemCall_of_code_empty {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {world : World} {target : Address} {data : ByteArray} {w' : World} {res : MessageResult}
    (hcode : (world.code target).size = 0) (hpre : Precompile.isPrecompile fork target = false)
    (h : systemCall fuel crypto fork env world target data = .ok (w', res)) :
    res.success = true ∧ w' = eraseIfEmpty world target := by
  obtain ⟨hr, rfl⟩ := systemCall_ok.1 h
  have hce : world.code target = .empty := byteArray_eq_empty hcode
  obtain ⟨msg', hd, -, -, -, -, -, -, hsame⟩ :=
    applyTopLevelDelegation_spec (ctx := systemContext crypto fork env)
      (isPre := (PrecompileImpl.standard (systemContext crypto fork env)).isPrecompile)
      (w := world) (msg := systemMessage world target data) (.inr rfl)
  have hm : msg' = systemMessage world target data :=
    hsame (by rw [systemMessage_code, hce]; exact delegatedAddress?_empty)
  subst hm
  unfold processMessageCall processMessageCallWith at hr
  rw [hd] at hr
  dsimp only at hr
  have hi : initMachine (PrecompileImpl.standard (systemContext crypto fork env))
      (systemContext crypto fork env) world ∅ (systemMessage world target data) =
      .inr { ctx := systemContext crypto fork env,
             precompiles := PrecompileImpl.standard (systemContext crypto fork env),
             world := world, transient := ∅, originalWorld := world, createdAccounts := ∅,
             frame := Frame.init (systemMessage world target data) (.call 0 0) (world, ∅),
             parents := [] } := by
    unfold initMachine
    simp [precompileOf, PrecompileImpl.standard, systemContext, hpre, transferValue,
      Gas.stackDepthLimit]
  rw [hi] at hr
  dsimp only at hr
  cases fuel with
  | zero => simp [run, Except.map] at hr
  | succ fuel =>
    simp only [run, step, Frame.init, systemMessage_code, hce, ByteArray.size_empty,
      Nat.lt_irrefl, ↓reduceDIte, finishFrame, topLevelResult, ChildResult.success] at hr
    simp only [Option.isNone_none, Bool.not_false, Bool.and_self, ↓reduceIte, Except.map,
      Except.ok.injEq] at hr
    subst hr
    refine ⟨rfl, ?_⟩
    simp only [systemMessage_target]
    rw [eraseIfEmpty_eq]
    split
    · exact destroyTouchedEmpty_singleton _ _ |>.trans (eraseIfEmpty_eq _ _) |>.trans
        (by simp only [*, ↓reduceIte])
    · rw [destroyTouchedEmpty_empty]

/-! ## Protected contracts -/

/-- **A system call is a top-level message the nested simulation covers**, for any protected
accounts `P` not containing `SYSTEM_ADDRESS`: depth 0, an unprotected caller, a call of its
target running the target's own code. -/
theorem topOk_systemMessage {P : Address → Prop} (hsys : ¬ P systemAddress) (world : World)
    (target : Address) (data : ByteArray) : TopOk P world (systemMessage world target data) :=
  ⟨rfl, hsys, .inl rfl, fun _ _ => ⟨rfl, rfl⟩⟩

/-- **A system call keeps a `GoodOk` predicate**, given the frame summaries of the dangerous
frames it reaches, exactly as `processMessageCall_good` (whose hypotheses `TopOk`, no
authorizations and the gas bound hold of every system call). `SYSTEM_ADDRESS` must not be
protected; since protected accounts hold code in `Good` worlds (`GoodOk.code`), this holds as
soon as `SYSTEM_ADDRESS` holds no code in `world` (`not_protected_of_code_empty`), as on every
chain. -/
theorem systemCall_good {P : Address → Prop} {Good : World → Prop} (S : GoodOk P Good)
    (hsys : ¬ P systemAddress) {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {world : World} {target : Address} {data : ByteArray} {w' : World} {res : MessageResult}
    (hw : Good world)
    (hsum : ∀ m, Reaches (systemContext crypto fork env) world ∅ (systemMessage world target data) m →
      DangerStart P Good systemTransactionGas m → (∀ f ∈ m.parents, ¬ Danger P f) →
      Halts m (fun mf o => Good (frameResult mf o).2.1))
    (h : systemCall fuel crypto fork env world target data = .ok (w', res)) : Good w' := by
  obtain ⟨hr, rfl⟩ := systemCall_ok.1 h
  have hg := processMessageCall_good S hw (.inr rfl) (topOk_systemMessage hsys world target data)
    (Nat.le_refl _) hsum hr
  exact good_destroyTouchedEmpty S hg _

/-- **A system contract without code keeps every `GoodOk` predicate**, with no summary.
`hpre` as in `systemCall_of_code_empty`. -/
theorem systemCall_good_of_code_empty {P : Address → Prop} {Good : World → Prop}
    (S : GoodOk P Good) {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {world : World} {target : Address} {data : ByteArray} {w' : World} {res : MessageResult}
    (hw : Good world) (hcode : (world.code target).size = 0)
    (hpre : Precompile.isPrecompile fork target = false)
    (h : systemCall fuel crypto fork env world target data = .ok (w', res)) : Good w' := by
  obtain ⟨-, rfl⟩ := systemCall_of_code_empty hcode hpre h
  exact S.keep _ _ hw fun p hp =>
    (eraseEmpty_eraseIfEmpty world target).keep (S.code world hw p hp)

/-- A protected account is never a system contract without code. -/
theorem not_protected_of_code_empty {P : Address → Prop} {Good : World → Prop}
    (S : GoodOk P Good) {world : World} (hw : Good world) {target : Address}
    (hcode : (world.code target).size = 0) : ¬ P target :=
  fun hp => S.code world hw target hp hcode

end EvmLogic.Chain
