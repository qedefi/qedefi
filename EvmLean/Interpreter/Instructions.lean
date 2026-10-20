import EvmLean.Opcode
import EvmLean.Interpreter.Monad
import EvmLean.Interpreter.Delegation

/-!
# Instruction semantics

`exec op` executes one instruction. Each case follows `vm/instructions/*.py` step by step,
including the order of pops, gas charges, checks and memory expansion (it decides which
halt is reported and whether an access was warmed). `CALL*`/`CREATE*` return a request that
`step` starts. The match is exhaustive, so a new opcode fails to compile until defined.
-/

namespace EvmLean.Interpreter

/-! ## Instruction shapes -/

/-- Pop two operands, charge `cost`, push `f x y` (top of stack is `x`). -/
def binOp (cost : Nat) (f : Word → Word → Word) : M Action := do
  let x ← pop
  let y ← pop
  charge cost
  push (f x y)
  advance
  return .next

/-- Pop one operand, charge `cost`, push `f x`. -/
def unOp (cost : Nat) (f : Word → Word) : M Action := do
  let x ← pop
  charge cost
  push (f x)
  advance
  return .next

/-- Pop three operands, charge `cost`, push `f x y z`. -/
def ternOp (cost : Nat) (f : Word → Word → Word → Word) : M Action := do
  let x ← pop
  let y ← pop
  let z ← pop
  charge cost
  push (f x y z)
  advance
  return .next

/-- Charge `cost`, push the value computed from the machine. -/
def pushValue (cost : Nat) (v : Machine → Word) : M Action := do
  charge cost
  push (v (← get))
  advance
  return .next

/-- A natural number as a word (modulo `2²⁵⁶`). -/
def ofNat (n : Nat) : Word := BitVec.ofNat 256 n

/-! ## Copy-style instructions -/

/-- Shared shape of `CALLDATACOPY`/`CODECOPY`: copy `size` zero-padded bytes of `src` to memory. -/
def copyToMemory (src : Machine → ByteArray) : M Action := do
  let memOff ← popNat
  let srcOff ← popNat
  let size ← popNat
  let ext ← memoryExpansion [(memOff, size)]
  charge (Gas.veryLow + Gas.copyCost size + ext.cost)
  expandMemory [(memOff, size)]
  writeMemory memOff (readBytes (src (← get)) srcOff size)
  advance
  return .next

/-! ## Calls (`instructions/system.py`) -/

/-- Parameters of `generic_call`. -/
structure CallParams where
  /-- Gas for the callee (including any stipend). -/
  gas : Nat
  /-- `CALLVALUE` of the callee. -/
  value : Word
  /-- `CALLER` of the callee. -/
  caller : Address
  /-- The callee's `ADDRESS`. -/
  to : Address
  /-- Whose code runs (the delegate, for a call to an EIP-7702 delegated account). -/
  codeAddress : Address
  /-- The code to run (`GenericCall.code`, resolved by `accessDelegation`). -/
  code : ByteArray
  /-- Reached through a delegation designator: do not run a precompile (EIP-7702). -/
  disablePrecompiles : Bool
  /-- Whether `value` moves from `caller` to `to`. -/
  shouldTransferValue : Bool
  /-- `STATICCALL`? -/
  isStaticcall : Bool
  /-- Input window offset. -/
  inOffset : Nat
  /-- Input window size. -/
  inSize : Nat
  /-- Output window offset. -/
  outOffset : Nat
  /-- Output window size. -/
  outSize : Nat

/-- Depth check, then request the child call. Mirrors `generic_call` up to `process_message`. -/
def genericCall (p : CallParams) : M Action := do
  setReturnData .empty
  let fr ← getFrame
  if fr.msg.depth + 1 > Gas.stackDepthLimit then
    refundGas p.gas
    push 0
    advance
    return .next
  let callData ← readMemory p.inOffset p.inSize
  let msg : Message := {
    caller := p.caller
    target := some p.to
    currentTarget := p.to
    gas := p.gas
    value := p.value
    data := callData
    codeAddress := some p.codeAddress
    code := p.code
    depth := fr.msg.depth + 1
    shouldTransferValue := p.shouldTransferValue
    isStatic := p.isStaticcall || fr.msg.isStatic
    accessedAddresses := fr.sub.accessedAddresses
    accessedStorageKeys := fr.sub.accessedStorageKeys
    disablePrecompiles := p.disablePrecompiles }
  return .call { msg, retOffset := p.outOffset, retSize := p.outSize }

/-- Which member of the `CALL*` family. -/
inductive CallKind where
  /-- `CALL`. -/
  | call
  /-- `CALLCODE`. -/
  | callcode
  /-- `DELEGATECALL`. -/
  | delegatecall
  /-- `STATICCALL`. -/
  | staticcall
  deriving DecidableEq

/-- `CALL`, `CALLCODE`, `DELEGATECALL`, `STATICCALL`, with EIP-7702 delegate resolution and cost. -/
def execCall (kind : CallKind) : M Action := do
  let gas ← popNat
  let target ← popAddress
  let value ← match kind with
    | .call | .callcode => pop
    | .delegatecall | .staticcall => pure 0
  let inOff ← popNat
  let inSize ← popNat
  let outOff ← popNat
  let outSize ← popNat
  let exts := [(inOff, inSize), (outOff, outSize)]
  let ext ← memoryExpansion exts
  let warm ← accessAddress target
  let (disablePrecompiles, codeAddress, code, delegationCost) ← accessDelegation target
  let m ← get
  let fr := m.frame
  let createCost :=
    match kind with
    | .call => if value = 0 || isAccountAlive m.world target then 0 else Gas.newAccount
    | .callcode | .delegatecall | .staticcall => 0
  let transferCost := if value = 0 then 0 else Gas.callValue
  let mcg := Gas.messageCallGas value.toNat gas fr.gasLeft ext.cost
    (Gas.accessCost warm + delegationCost + createCost + transferCost)
  charge (mcg.cost + ext.cost)
  if kind = .call && fr.msg.isStatic && value ≠ 0 then throw .writeInStaticContext
  expandMemory exts
  let self := fr.msg.currentTarget
  let params : CallParams :=
    match kind with
    | .call =>
      { gas := mcg.subCall, value, caller := self, to := target, codeAddress, code,
        disablePrecompiles, shouldTransferValue := true, isStaticcall := false,
        inOffset := inOff, inSize, outOffset := outOff, outSize }
    | .callcode =>
      { gas := mcg.subCall, value, caller := self, to := self, codeAddress, code,
        disablePrecompiles, shouldTransferValue := true, isStaticcall := false,
        inOffset := inOff, inSize, outOffset := outOff, outSize }
    | .delegatecall =>
      { gas := mcg.subCall, value := fr.msg.value, caller := fr.msg.caller, to := self,
        codeAddress, code, disablePrecompiles, shouldTransferValue := false,
        isStaticcall := false, inOffset := inOff, inSize, outOffset := outOff, outSize }
    | .staticcall =>
      { gas := mcg.subCall, value := 0, caller := self, to := target, codeAddress, code,
        disablePrecompiles, shouldTransferValue := true, isStaticcall := true,
        inOffset := inOff, inSize, outOffset := outOff, outSize }
  match kind with
  | .call | .callcode =>
    if (m.world.balance self).toNat < value.toNat then
      push 0
      setReturnData .empty
      refundGas mcg.subCall
      advance
      return .next
    else genericCall params
  | .delegatecall | .staticcall => genericCall params

/-! ## Creation (`instructions/system.py`) -/

/-- `CREATE`/`CREATE2`. Mirrors `generic_create`, but computes the address after the soft-failure
checks (it is pure, so this only skips hashing). -/
def execCreate (isCreate2 : Bool) : M Action := do
  let endowment ← pop
  let off ← popNat
  let size ← popNat
  let salt ← if isCreate2 then pop else pure 0
  let ext ← memoryExpansion [(off, size)]
  charge ((if isCreate2 then Gas.create2Cost size else Gas.createCost size) + ext.cost)
  expandMemory [(off, size)]
  -- generic_create
  let m ← get
  if size > Gas.maxInitCodeSize m.ctx.fork then throw .initCodeSizeExceeded
  let initCode ← readMemory off size
  let createGas := Gas.maxMessageCallGas (← getFrame).gasLeft
  modifyFrame fun fr => { fr with gasLeft := fr.gasLeft - createGas }
  requireNonStatic
  setReturnData .empty
  let fr ← getFrame
  let sender := fr.msg.currentTarget
  let senderAcc := m.world.account sender
  if senderAcc.balance.toNat < endowment.toNat || senderAcc.nonce = Gas.maxNonce
      || fr.msg.depth + 1 > Gas.stackDepthLimit then
    refundGas createGas
    push 0
    advance
    return .next
  let keccak := m.ctx.crypto.keccak256
  let addr :=
    if isCreate2 then create2Address keccak sender salt initCode
    else createAddress keccak sender senderAcc.nonce
  let _ ← accessAddress addr
  if !accountDeployable m.world addr then
    modifyWorld fun w => incrementNonce w sender
    push 0
    advance
    return .next
  modifyWorld fun w => incrementNonce w sender
  let fr ← getFrame
  return .create {
    caller := sender
    target := none
    currentTarget := addr
    gas := createGas
    value := endowment
    data := .empty
    codeAddress := none
    code := initCode
    depth := fr.msg.depth + 1
    shouldTransferValue := true
    isStatic := false
    accessedAddresses := fr.sub.accessedAddresses
    accessedStorageKeys := fr.sub.accessedStorageKeys }

/-- `RETURN`/`REVERT` output: pop `(offset, size)`, charge expansion, read memory. -/
def readOutput : M ByteArray := do
  let off ← popNat
  let size ← popNat
  let ext ← memoryExpansion [(off, size)]
  charge ext.cost
  expandMemory [(off, size)]
  readMemory off size

/-- `SELFDESTRUCT`; deletes only accounts created in this transaction (EIP-6780). -/
def execSelfdestruct : M Action := do
  let beneficiary ← popAddress
  let warm ← accessAddress beneficiary
  let m ← get
  let originator := m.frame.msg.currentTarget
  charge (Gas.selfdestructCost warm (isAccountAlive m.world beneficiary)
    (m.world.balance originator ≠ 0))
  requireNonStatic
  let balance := m.world.balance originator
  modifyWorld fun w => moveEther w originator beneficiary balance
  if m.createdAccounts.contains originator then
    modifyWorld fun w => setAccountBalance w originator 0
    modifySub fun s => { s with accountsToDelete := s.accountsToDelete.insert originator }
  -- EIP-161 touch of the beneficiary (pre-`state_tracker` specification).
  let w := (← get).world
  if accountExistsAndIsEmpty w beneficiary then
    modifySub fun s => { s with touchedAccounts := s.touchedAccounts.insert beneficiary }
  return .stop .empty

/-! ## Storage (`instructions/storage.py`) -/

/-- `SSTORE` (EIP-2200 / EIP-2929 / EIP-3529). Mirrors `sstore`. -/
def execSstore : M Action := do
  let key ← pop
  let new ← pop
  if (← getFrame).gasLeft ≤ Gas.callStipend then throw .outOfGas
  let m ← get
  let self := m.frame.msg.currentTarget
  let original := getStorageOriginal m.originalWorld m.createdAccounts self key
  let current := m.world.sload self key
  let warm ← accessStorageKey key
  let (cost, refund) := Gas.sstoreCostRefund original.toNat current.toNat new.toNat warm
  modifySub fun s => { s with refundCounter := s.refundCounter + refund }
  charge cost
  requireNonStatic
  modifyWorld fun w => setStorage w self key new
  advance
  return .next

/-! ## Logs (`instructions/log.py`) -/

/-- Pop `n` words, in pop order. -/
def popN : Nat → M (List Word)
  | 0 => pure []
  | n + 1 => do
    let x ← pop
    let xs ← popN n
    return x :: xs

/-- `LOG0`–`LOG4`. Mirrors `log_n`. -/
def execLog (n : Nat) : M Action := do
  let off ← popNat
  let size ← popNat
  let topics ← popN n
  let ext ← memoryExpansion [(off, size)]
  charge (Gas.logCost size n + ext.cost)
  expandMemory [(off, size)]
  requireNonStatic
  let data ← readMemory off size
  let entry : Log := { address := (← getFrame).msg.currentTarget, topics := topics.toArray,
                       data }
  modifySub fun s => { s with logs := s.logs.push entry }
  advance
  return .next

/-! ## Block (`instructions/block.py`) -/

/-- `BLOCKHASH` value: hash of one of the 256 most recent blocks, else zero. -/
def blockHashValue (env : BlockEnv) (n : Nat) : Word :=
  if env.number ≤ n ∨ env.number > n + 256 then 0
  else env.blockHashes[env.number - n - 1]?.getD 0

/-! ## The dispatcher -/

/-- Execute one instruction. Exhaustive over `Opcode`. -/
def exec : Opcode → M Action
  -- Stop and arithmetic (`arithmetic.py`, `control_flow.py`)
  | .stop => return .stop .empty
  | .add => binOp Gas.veryLow (· + ·)
  | .mul => binOp Gas.low (· * ·)
  | .sub => binOp Gas.veryLow (· - ·)
  | .div => binOp Gas.low Word.div
  | .sdiv => binOp Gas.low Word.sdiv
  | .mod => binOp Gas.low Word.mod
  | .smod => binOp Gas.low Word.smod
  | .addmod => ternOp Gas.mid Word.addmod
  | .mulmod => ternOp Gas.mid Word.mulmod
  | .exp => do
    let b ← pop
    let e ← pop
    charge (Gas.expCost e.toNat)
    push (Word.exp b e)
    advance
    return .next
  | .signextend => binOp Gas.low Word.signextend
  -- Comparison and bitwise (`comparison.py`, `bitwise.py`)
  | .lt => binOp Gas.veryLow Word.lt
  | .gt => binOp Gas.veryLow Word.gt
  | .slt => binOp Gas.veryLow Word.slt
  | .sgt => binOp Gas.veryLow Word.sgt
  | .eq => binOp Gas.veryLow Word.eq
  | .iszero => unOp Gas.veryLow Word.iszero
  | .and => binOp Gas.veryLow (· &&& ·)
  | .or => binOp Gas.veryLow (· ||| ·)
  | .xor => binOp Gas.veryLow (· ^^^ ·)
  | .not => unOp Gas.veryLow (~~~ ·)
  | .byte => binOp Gas.veryLow Word.byte
  | .shl => binOp Gas.veryLow Word.shl
  | .shr => binOp Gas.veryLow Word.shr
  | .sar => binOp Gas.veryLow Word.sar
  | .clz => do
    -- EIP-7939 (Osaka). `decode` already maps 0x1e to `invalid` before Osaka.
    if (← get).ctx.fork ≥ .osaka then unOp Gas.low Word.clz
    else throw .invalidOpcode
  -- Keccak (`keccak.py`)
  | .keccak256 => do
    let off ← popNat
    let size ← popNat
    let ext ← memoryExpansion [(off, size)]
    charge (Gas.keccak256Cost size + ext.cost)
    expandMemory [(off, size)]
    let data ← readMemory off size
    push ((← get).ctx.crypto.keccak256 data)
    advance
    return .next
  -- Environment (`environment.py`)
  | .address => pushValue Gas.base fun m => Word.ofAddress m.frame.msg.currentTarget
  | .balance => do
    let a ← popAddress
    let warm ← accessAddress a
    charge (Gas.accessCost warm)
    push ((← get).world.balance a)
    advance
    return .next
  | .origin => pushValue Gas.base fun m => Word.ofAddress m.ctx.tx.origin
  | .caller => pushValue Gas.base fun m => Word.ofAddress m.frame.msg.caller
  | .callvalue => pushValue Gas.base fun m => m.frame.msg.value
  | .calldataload => do
    let off ← popNat
    charge Gas.veryLow
    push (Bytes.toWord (readBytes (← getFrame).msg.data off 32))
    advance
    return .next
  | .calldatasize => pushValue Gas.base fun m => ofNat m.frame.msg.data.size
  | .calldatacopy => copyToMemory fun m => m.frame.msg.data
  | .codesize => pushValue Gas.base fun m => ofNat m.frame.code.size
  | .codecopy => copyToMemory fun m => m.frame.code
  | .gasprice => pushValue Gas.base fun m => ofNat m.ctx.tx.gasPrice
  | .extcodesize => do
    let a ← popAddress
    let warm ← accessAddress a
    charge (Gas.accessCost warm)
    push (ofNat ((← get).world.code a).size)
    advance
    return .next
  | .extcodecopy => do
    let a ← popAddress
    let memOff ← popNat
    let codeOff ← popNat
    let size ← popNat
    let ext ← memoryExpansion [(memOff, size)]
    let warm ← accessAddress a
    charge (Gas.accessCost warm + Gas.copyCost size + ext.cost)
    expandMemory [(memOff, size)]
    writeMemory memOff (readBytes ((← get).world.code a) codeOff size)
    advance
    return .next
  | .returndatasize => pushValue Gas.base fun m => ofNat m.frame.returnData.size
  | .returndatacopy => do
    let memOff ← popNat
    let dataOff ← popNat
    let size ← popNat
    let ext ← memoryExpansion [(memOff, size)]
    charge (Gas.veryLow + Gas.copyCost size + ext.cost)
    let rd := (← getFrame).returnData
    if dataOff + size > rd.size then throw .returnDataOutOfBounds
    expandMemory [(memOff, size)]
    writeMemory memOff (rd.extract dataOff (dataOff + size))
    advance
    return .next
  | .extcodehash => do
    let a ← popAddress
    let warm ← accessAddress a
    charge (Gas.accessCost warm)
    let m ← get
    let acc := m.world.account a
    push (if acc.isEmpty then 0 else m.ctx.crypto.keccak256 acc.code)
    advance
    return .next
  -- Block (`block.py`, `environment.py`)
  | .blockhash => do
    let n ← popNat
    charge Gas.blockhash
    push (blockHashValue (← get).ctx.block n)
    advance
    return .next
  | .coinbase => pushValue Gas.base fun m => Word.ofAddress m.ctx.block.coinbase
  | .timestamp => pushValue Gas.base fun m => ofNat m.ctx.block.timestamp
  | .number => pushValue Gas.base fun m => ofNat m.ctx.block.number
  | .prevrandao => pushValue Gas.base fun m => m.ctx.block.prevRandao
  | .gaslimit => pushValue Gas.base fun m => ofNat m.ctx.block.gasLimit
  | .chainid => pushValue Gas.base fun m => ofNat m.ctx.block.chainId
  | .selfbalance => pushValue Gas.fastStep fun m => m.world.balance m.frame.msg.currentTarget
  | .basefee => pushValue Gas.base fun m => ofNat m.ctx.block.baseFee
  | .blobhash => do
    let i ← popNat
    charge Gas.blobhash
    push ((← get).ctx.tx.blobVersionedHashes[i]?.getD 0)
    advance
    return .next
  | .blobbasefee =>
    pushValue Gas.base fun m => ofNat (Gas.blobGasPrice m.ctx.fork m.ctx.block.excessBlobGas)
  -- Stack, memory, storage, flow (`stack.py`, `memory.py`, `storage.py`, `control_flow.py`)
  | .pop => do
    let _ ← pop
    charge Gas.base
    advance
    return .next
  | .mload => do
    let off ← popNat
    let ext ← memoryExpansion [(off, 32)]
    charge (Gas.veryLow + ext.cost)
    expandMemory [(off, 32)]
    push ((← getFrame).memory.loadWord off)
    advance
    return .next
  | .mstore => do
    let off ← popNat
    let v ← pop
    let ext ← memoryExpansion [(off, 32)]
    charge (Gas.veryLow + ext.cost)
    expandMemory [(off, 32)]
    modifyFrame fun fr => { fr with memory := fr.memory.storeWord off v }
    advance
    return .next
  | .mstore8 => do
    let off ← popNat
    let v ← pop
    let ext ← memoryExpansion [(off, 1)]
    charge (Gas.veryLow + ext.cost)
    expandMemory [(off, 1)]
    modifyFrame fun fr => { fr with memory := fr.memory.storeByte off v }
    advance
    return .next
  | .sload => do
    let key ← pop
    let warm ← accessStorageKey key
    charge (if warm then Gas.warmAccess else Gas.coldStorageAccess)
    let m ← get
    push (m.world.sload m.frame.msg.currentTarget key)
    advance
    return .next
  | .sstore => execSstore
  | .jump => do
    let dest ← popNat
    charge Gas.mid
    if !isValidJumpDest (← getFrame).jumpDests dest then throw .invalidJumpDestination
    modifyFrame fun fr => { fr with pc := dest }
    return .next
  | .jumpi => do
    let dest ← popNat
    let cond ← pop
    charge Gas.high
    if cond = 0 then
      advance
    else if !isValidJumpDest (← getFrame).jumpDests dest then
      throw .invalidJumpDestination
    else
      modifyFrame fun fr => { fr with pc := dest }
    return .next
  | .pc => pushValue Gas.base fun m => ofNat m.frame.pc
  | .msize => pushValue Gas.base fun m => ofNat m.frame.memory.size
  | .gas => pushValue Gas.base fun m => ofNat m.frame.gasLeft
  | .jumpdest => do
    charge Gas.jumpdest
    advance
    return .next
  | .tload => do
    let key ← pop
    charge Gas.warmAccess
    let m ← get
    push (getTransient m.transient m.frame.msg.currentTarget key)
    advance
    return .next
  | .tstore => do
    let key ← pop
    let v ← pop
    charge Gas.warmAccess
    requireNonStatic
    modify fun m =>
      { m with transient := setTransient m.transient m.frame.msg.currentTarget key v }
    advance
    return .next
  | .mcopy => do
    let dst ← popNat
    let src ← popNat
    let len ← popNat
    let exts := [(src, len), (dst, len)]
    let ext ← memoryExpansion exts
    charge (Gas.veryLow + Gas.copyCost len + ext.cost)
    expandMemory exts
    let data ← readMemory src len
    writeMemory dst data
    advance
    return .next
  | .push n => do
    charge (if n.val = 0 then Gas.base else Gas.veryLow)
    let fr ← getFrame
    push (Bytes.toWord (readBytes fr.code (fr.pc + 1) n.val))
    advance (1 + n.val)
    return .next
  | .dup n => do
    charge Gas.veryLow
    match (← getFrame).stack[n.val]? with
    | none => throw .stackUnderflow
    | some x =>
      push x
      advance
      return .next
  | .swap n => do
    charge Gas.veryLow
    let st := (← getFrame).stack
    match st, st[n.val + 1]? with
    | top :: _, some x =>
      modifyFrame fun fr => { fr with stack := (st.set 0 x).set (n.val + 1) top }
      advance
      return .next
    | _, _ => throw .stackUnderflow
  | .log n => execLog n.val
  -- System (`system.py`)
  | .create => execCreate false
  | .call => execCall .call
  | .callcode => execCall .callcode
  | .«return» => return .stop (← readOutput)
  | .delegatecall => execCall .delegatecall
  | .create2 => execCreate true
  | .staticcall => execCall .staticcall
  | .revert => return .revert (← readOutput)
  | .invalid => throw .invalidOpcode
  | .selfdestruct => execSelfdestruct

end EvmLean.Interpreter
