import EvmLean.Interpreter.Instructions

/-!
# Small-step execution

`step` is total and non-recursive: it executes one instruction, finishes the executing frame
(deposit code, roll back on failure, resume the parent or return the result), or starts a
child (precompiles run to completion at once). `run` iterates `step` with fuel.
-/

namespace EvmLean.Interpreter

/-- Fuel ran out before execution finished (not an EVM outcome; gas bounds execution). -/
structure OutOfFuel where
  deriving Inhabited, Repr

/-- The RIPEMD-160 precompile address (`0x03`). -/
def ripemd160Address : Address := 3

/-- Insert every element of `t` into `s`. -/
def AddressSet.union (s t : AddressSet) : AddressSet := t.foldl (fun acc a => acc.insert a) s

/-- A fresh child substate: nothing accrued, warm sets from the message. -/
def Substate.ofMessage (msg : Message) : Substate :=
  { accessedAddresses := msg.accessedAddresses, accessedStorageKeys := msg.accessedStorageKeys }

/-- Resume the parent `m.frame` with child result `r`, incl. the RIPEMD-160 touched quirk.
Mirrors the tail of `generic_call`/`generic_create`. -/
def resume (m : Machine) (r : ChildResult) : Machine :=
  let p := m.frame
  let ok := r.success
  let sub :=
    if ok then
      let touched := p.sub.touchedAccounts.union r.sub.touchedAccounts
      let touched :=
        if accountExistsAndIsEmpty m.world r.target then touched.insert r.target else touched
      { logs := p.sub.logs ++ r.sub.logs
        refundCounter := p.sub.refundCounter + r.sub.refundCounter
        accountsToDelete := p.sub.accountsToDelete.union r.sub.accountsToDelete
        touchedAccounts := touched
        -- The child's warm sets started as a copy of the parent's, so they are the union.
        accessedAddresses := r.sub.accessedAddresses
        accessedStorageKeys := r.sub.accessedStorageKeys }
    else
      let quirk := r.sub.touchedAccounts.contains ripemd160Address
        || (r.target == ripemd160Address && accountExistsAndIsEmpty m.world ripemd160Address)
      if quirk then
        { p.sub with touchedAccounts := p.sub.touchedAccounts.insert ripemd160Address }
      else p.sub
  let (returnData, result, memory) :=
    match r.kind with
    | .call retOffset retSize =>
      let out := r.output.extract 0 (min retSize r.output.size)
      let memory := if out.size = 0 then p.memory else p.memory.write retOffset out
      (r.output, (if ok then 1 else 0 : Word), memory)
    | .create =>
      ((if ok then .empty else r.output), (if ok then Word.ofAddress r.target else 0), p.memory)
  { m with frame := { p with
      gasLeft := p.gasLeft + r.gasLeft
      sub := sub
      returnData := returnData
      -- Cannot overflow: the `CALL*`/`CREATE*` instruction popped at least three items.
      stack := result :: p.stack
      memory := memory
      pc := p.pc + 1 } }

/-- Code-deposit checks (EIP-3541, deposit cost, EIP-170); the spec reports the size limit as
`OutOfGasError`, here `contractSizeExceeded`. -/
def depositCode (fork : Fork) (gasLeft : Nat) (code : ByteArray) : Except ExceptionalHalt Nat :=
  if code[0]? = some 0xef then .error .invalidContractPrefix
  else
    let cost := Gas.codeDepositCost code.size
    if gasLeft < cost then .error .outOfGas
    else if code.size > Gas.maxCodeSize fork then .error .contractSizeExceeded
    else .ok (gasLeft - cost)

/-- Top-level `MessageResult`; on failure (incl. `REVERT`) the substate is dropped. -/
def topLevelResult (target : Option Address) (world : World) (transient : TransientStorage)
    (r : ChildResult) : MessageResult :=
  if r.success then
    let touched :=
      match target with
      | some t =>
        if accountExistsAndIsEmpty world t then r.sub.touchedAccounts.insert t
        else r.sub.touchedAccounts
      | none => r.sub.touchedAccounts
    { gasLeft := r.gasLeft
      refundCounter := r.sub.refundCounter
      logs := r.sub.logs
      accountsToDelete := r.sub.accountsToDelete
      touchedAccounts := touched
      error := none
      reverted := false
      output := r.output
      world := world
      transientStorage := transient }
  else
    { gasLeft := r.gasLeft
      refundCounter := 0
      logs := #[]
      accountsToDelete := ∅
      touchedAccounts := ∅
      error := r.error
      reverted := r.reverted
      output := r.output
      world := world
      transientStorage := transient }

/-- Finish the executing frame with outcome `o`, then resume the parent or produce the result. -/
def finishFrame (m : Machine) (o : Outcome) : StepResult :=
  let f := m.frame
  let target := f.msg.currentTarget
  let failed (e : ExceptionalHalt) : ChildResult × World × TransientStorage :=
    ({ gasLeft := 0, error := some e, reverted := false, output := .empty, sub := f.sub,
       target, kind := f.kind }, f.snapshot.1, f.snapshot.2)
  let (r, world, transient) : ChildResult × World × TransientStorage :=
    match o with
    | .success out =>
      let ok (gasLeft : Nat) : ChildResult :=
        { gasLeft, error := none, reverted := false, output := out, sub := f.sub, target,
          kind := f.kind }
      match f.kind with
      | .call _ _ => (ok f.gasLeft, m.world, m.transient)
      | .create =>
        match depositCode m.ctx.fork f.gasLeft out with
        | .ok gasLeft => (ok gasLeft, setCode m.world target out, m.transient)
        | .error e => failed e
    | .revert out =>
      ({ gasLeft := f.gasLeft, error := none, reverted := true, output := out, sub := f.sub,
         target, kind := f.kind }, f.snapshot.1, f.snapshot.2)
    | .halt e => failed e
  match m.parents with
  | [] => .done (topLevelResult f.msg.target world transient r)
  | p :: ps => .running (resume { m with frame := p, parents := ps, world, transient } r)

/-- The precompile to run for `msg`, unless disabled by an EIP-7702 delegation. -/
def precompileOf (pre : PrecompileImpl) (msg : Message) : Option Address :=
  if msg.disablePrecompiles then none
  else
    match msg.codeAddress with
    | some a => if pre.isPrecompile a then some a else none
    | none => none

/-- Run precompile `a` for `msg` (value already transferred); restores `snapshot` on failure. -/
def runPrecompile (pre : PrecompileImpl) (a : Address) (msg : Message) (kind : FrameKind)
    (world : World) (transient : TransientStorage) (snapshot : World × TransientStorage) :
    ChildResult × World × TransientStorage :=
  let res := pre.run a msg.data msg.gas
  if res.success then
    ({ gasLeft := res.gasLeft, error := none, reverted := false, output := res.output,
       sub := Substate.ofMessage msg, target := msg.currentTarget, kind }, world, transient)
  else
    ({ gasLeft := 0, error := some .precompileFailure, reverted := false, output := .empty,
       sub := Substate.ofMessage msg, target := msg.currentTarget, kind },
     snapshot.1, snapshot.2)

/-- The world after `process_message`'s value transfer. -/
def transferValue (w : World) (msg : Message) : World :=
  if msg.shouldTransferValue && msg.value ≠ 0 then
    moveEther w msg.caller msg.currentTarget msg.value
  else w

/-- Start a child call: snapshot, transfer value, then run a precompile or push a frame. -/
def launchCall (m : Machine) (req : CallRequest) : Machine :=
  let msg := req.msg
  let snapshot := (m.world, m.transient)
  let world := transferValue m.world msg
  let kind := FrameKind.call req.retOffset req.retSize
  match precompileOf m.precompiles msg with
  | some a =>
    let (r, world, transient) := runPrecompile m.precompiles a msg kind world m.transient snapshot
    resume { m with world, transient } r
  | none =>
    { m with world, frame := Frame.init msg kind snapshot, parents := m.frame :: m.parents }

/-- Start of a creation: mark the account created, increment its nonce, transfer the value. -/
def beginCreate (world : World) (created : AddressSet) (msg : Message) : World × AddressSet :=
  let created := created.insert msg.currentTarget
  let world := incrementNonce world msg.currentTarget
  (transferValue world msg, created)

/-- Start a child creation; the frame's snapshot predates the nonce increment. -/
def launchCreate (m : Machine) (msg : Message) : Machine :=
  let snapshot := (m.world, m.transient)
  let (world, createdAccounts) := beginCreate m.world m.createdAccounts msg
  { m with world, createdAccounts, frame := Frame.init msg .create snapshot,
           parents := m.frame :: m.parents }

/-- One transition of the machine. Total and non-recursive. -/
def step (m : Machine) : StepResult :=
  let f := m.frame
  if h : f.pc < f.code.size then
    match (exec (Opcode.decode m.ctx.fork f.code[f.pc])).run m with
    | .error e => finishFrame m (.halt e)
    | .ok (.next, m') => .running m'
    | .ok (.stop out, m') => finishFrame m' (.success out)
    | .ok (.revert out, m') => finishFrame m' (.revert out)
    | .ok (.call req, m') => .running (launchCall m' req)
    | .ok (.create msg, m') => .running (launchCreate m' msg)
  else finishFrame m (.success .empty)

/-- Iterate `step` at most `fuel` times. -/
def run : Nat → Machine → Except OutOfFuel MessageResult
  | 0, _ => .error {}
  | fuel + 1, m =>
    match step m with
    | .done r => .ok r
    | .running m' => run fuel m'

end EvmLean.Interpreter
