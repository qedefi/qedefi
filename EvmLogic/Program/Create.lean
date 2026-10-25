import EvmLogic.Step.Basic
import EvmLogic.Step.Flow
import EvmLogic.Program.Call

/-!
# Contract creation: `CREATE` and `CREATE2`

`step_create`/`step_create2` push the child frame running the init code, with the exact charges
(`createCharge`: `32000`, the EIP-3860 init-code words, for `CREATE2` the hashing words, and
memory expansion) and the EIP-150 child gas (`createGas`: all but 1/64 of what is left,
`creatorGas_eq`). The new address is `newAddress`: `createAddress` of the creator's nonce, or the
`CREATE2` address of salt and init-code hash, both through `m.ctx.crypto.keccak256`.

Every other outcome of the instruction is a lemma too:

* exceptional halts: out of gas for the charge (`step_create_oog`), init code over the EIP-3860
  limit (`step_create_initcode`), a static frame (`step_create_static`);
* soft failures (`0` pushed, the child's gas returned, nothing else changes): insufficient
  balance, nonce at its EIP-2681 maximum, depth limit (`step_create_soft`);
* address collision (EIP-7610: nonce, code or storage at the new address; `0` pushed, the
  child's gas consumed, the creator's nonce incremented): `step_create_collision`.

`WP.create`/`WP.create2` are the callee-summary rules (`WP.call` for a creation frame) and
`WP.create_havoc`/`WP.create2_havoc` the rely–guarantee rules for **arbitrary init code**
(`WP.call_havoc`): the caller continues from every return whose world is `Good`. The return to
the creator is described by `resumeAfter_create_success` (code deposited, the address pushed),
`resumeAfter_create_deposit_fail`, `resumeAfter_create_revert`, `resumeAfter_create_halt`.
-/

section

namespace EvmLogic.Program
open EvmLean EvmLean.Interpreter

/-! ## The charges, the child and the creator -/

/-- The charge of `CREATE` (`b = false`) or `CREATE2` (`b = true`) for init code at
`[off, off + size)`: the static cost plus memory expansion. -/
def createCharge (m : Machine) (b : Bool) (off size : Word) : Nat :=
  (if b then Gas.create2Cost size.toNat else Gas.createCost size.toNat) +
    (Gas.extendMemory m.frame.memory.size [(off.toNat, size.toNat)]).cost

/-- The creator's memory after the expansion for the init code. -/
def createMemory (m : Machine) (off size : Word) : Memory :=
  m.frame.memory.expand off.toNat size.toNat

/-- The init code: `size` bytes of the expanded memory at `off`. -/
def initCodeOf (m : Machine) (off size : Word) : ByteArray :=
  readBytes (createMemory m off size).bytes off.toNat size.toNat

/-- The gas handed to the child (EIP-150): all but 1/64 of the gas left after the charge. -/
def createGas (m : Machine) (b : Bool) (off size : Word) : Nat :=
  Gas.maxMessageCallGas (m.frame.gasLeft - createCharge m b off size)

/-- The address of the new contract: `keccak256(rlp([sender, nonce]))` for `CREATE`,
`keccak256(0xff ‖ sender ‖ salt ‖ keccak256(initCode))` for `CREATE2`, with the machine's
`Crypto`. -/
def newAddress (m : Machine) (b : Bool) (off size salt : Word) : Address :=
  if b then
    create2Address m.ctx.crypto.keccak256 m.frame.msg.currentTarget salt (initCodeOf m off size)
  else
    createAddress m.ctx.crypto.keccak256 m.frame.msg.currentTarget
      (m.world.account m.frame.msg.currentTarget).nonce

/-- The child message of a creation: the init code runs at the new address with `value`, no
calldata, one level deeper, never static. -/
def createMsg (m : Machine) (b : Bool) (value off size salt : Word) : Message where
  caller := m.frame.msg.currentTarget
  target := none
  currentTarget := newAddress m b off size salt
  gas := createGas m b off size
  value := value
  data := .empty
  codeAddress := none
  code := initCodeOf m off size
  depth := m.frame.msg.depth + 1
  shouldTransferValue := true
  isStatic := false
  accessedAddresses := (m.frame.sub.warmAddr (newAddress m b off size salt)).accessedAddresses
  accessedStorageKeys := m.frame.sub.accessedStorageKeys

/-- The creator's frame while the child runs: arguments popped, charge and child gas taken,
memory expanded, the new address warm, return data cleared; the pc still at the `CREATE*`. -/
def creatorFrame (m : Machine) (b : Bool) (off size salt : Word) (rest : List Word) : Frame :=
  { m.frame with
    stack := rest
    gasLeft := m.frame.gasLeft - createCharge m b off size - createGas m b off size
    memory := createMemory m off size
    returnData := .empty
    sub := m.frame.sub.warmAddr (newAddress m b off size salt) }

/-- The machine running the init code: the creator's nonce incremented (this is the rollback
snapshot), then the new account marked created, its nonce set to one and the value moved. -/
def createChild (m : Machine) (b : Bool) (value off size salt : Word) (rest : List Word) :
    Machine :=
  { m with
    world := transferValue
      (incrementNonce (incrementNonce m.world m.frame.msg.currentTarget)
        (newAddress m b off size salt))
      (createMsg m b value off size salt)
    createdAccounts := m.createdAccounts.insert (newAddress m b off size salt)
    frame := Frame.init (createMsg m b value off size salt) .create
      (incrementNonce m.world m.frame.msg.currentTarget, m.transient)
    parents := creatorFrame m b off size salt rest :: m.parents }

/-- **The 63/64 rule**: the creator keeps exactly 1/64 of the gas left after the charge. -/
theorem creatorGas_eq (m : Machine) (b : Bool) (off size : Word) :
    m.frame.gasLeft - createCharge m b off size - createGas m b off size =
      (m.frame.gasLeft - createCharge m b off size) / 64 := by
  simp only [createGas, Gas.maxMessageCallGas]
  have := Nat.div_le_self (m.frame.gasLeft - createCharge m b off size) 64
  omega

theorem createGas_le (m : Machine) (b : Bool) (off size : Word) :
    createGas m b off size ≤ m.frame.gasLeft - createCharge m b off size := by
  simp only [createGas, Gas.maxMessageCallGas]; omega

/-! ## Decoding -/

theorem decode_create (fk : Fork) : Opcode.decode fk 0xf0 = .create := by cases fk <;> rfl

theorem decode_create2 (fk : Fork) : Opcode.decode fk 0xf5 = .create2 := by cases fk <;> rfl

/-! ## Starting the child -/

variable {m : Machine} {value off size salt : Word} {rest : List Word}

/-- **`CREATE` pushes the child frame** running the init code at `newAddress m false …`, when
the charge is affordable, the init code within the EIP-3860 limit, the frame non-static, the
creator able to pay `value`, its nonce below the maximum, the depth below the limit and the new
address free (EIP-7610: `accountDeployable`). -/
theorem step_create (hcode : m.frame.code[m.frame.pc]? = some 0xf0)
    (hstk : m.frame.stack = value :: off :: size :: rest)
    (hgas : createCharge m false off size ≤ m.frame.gasLeft)
    (hsize : size.toNat ≤ Gas.maxInitCodeSize m.ctx.fork)
    (hstatic : m.frame.msg.isStatic = false)
    (hbal : value.toNat ≤ (m.world.balance m.frame.msg.currentTarget).toNat)
    (hnonce : (m.world.account m.frame.msg.currentTarget).nonce ≠ Gas.maxNonce)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hfree : accountDeployable m.world (newAddress m false off size 0) = true) :
    step m = .running (createChild m false value off size 0 rest) := by
  have hg : ¬ m.frame.gasLeft < createCharge m false off size := Nat.not_lt.mpr hgas
  have hs : ¬ size.toNat > Gas.maxInitCodeSize m.ctx.fork := Nat.not_lt.mpr hsize
  have hd : ¬ m.frame.msg.depth + 1 > Gas.stackDepthLimit := Nat.not_lt.mpr hdepth
  have hb : ¬ (m.world.account m.frame.msg.currentTarget).balance.toNat < value.toNat :=
    Nat.not_lt.mpr hbal
  have hf : accountDeployable m.world (createAddress m.ctx.crypto.keccak256
      m.frame.msg.currentTarget (m.world.account m.frame.msg.currentTarget).nonce) = true := hfree
  simp only [createCharge, Bool.false_eq_true, ite_false] at hg
  rw [step_eq_of_code hcode, decode_create]
  simp only [exec, execCreate, popNat, pop, getFrame, modifyFrame, StateT.run_bind, hstk,
    StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, memoryExpansion,
    Bool.false_eq_true, ite_false, charge, hg, expandMemory, List.foldl, hs, readMemory,
    requireNonStatic, hstatic, setReturnData, hb, hnonce, hd, decide_false, Bool.or_false,
    run_accessAddress, hf, Bool.not_true, modifyWorld]
  simp only [pure, Except.pure, launchCreate, beginCreate]
  rfl

/-- **`CREATE2` pushes the child frame** running the init code at
`newAddress m true off size salt` (salt and init-code hash), under the conditions of
`step_create`. -/
theorem step_create2 (hcode : m.frame.code[m.frame.pc]? = some 0xf5)
    (hstk : m.frame.stack = value :: off :: size :: salt :: rest)
    (hgas : createCharge m true off size ≤ m.frame.gasLeft)
    (hsize : size.toNat ≤ Gas.maxInitCodeSize m.ctx.fork)
    (hstatic : m.frame.msg.isStatic = false)
    (hbal : value.toNat ≤ (m.world.balance m.frame.msg.currentTarget).toNat)
    (hnonce : (m.world.account m.frame.msg.currentTarget).nonce ≠ Gas.maxNonce)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hfree : accountDeployable m.world (newAddress m true off size salt) = true) :
    step m = .running (createChild m true value off size salt rest) := by
  have hg : ¬ m.frame.gasLeft < createCharge m true off size := Nat.not_lt.mpr hgas
  have hs : ¬ size.toNat > Gas.maxInitCodeSize m.ctx.fork := Nat.not_lt.mpr hsize
  have hd : ¬ m.frame.msg.depth + 1 > Gas.stackDepthLimit := Nat.not_lt.mpr hdepth
  have hb : ¬ (m.world.account m.frame.msg.currentTarget).balance.toNat < value.toNat :=
    Nat.not_lt.mpr hbal
  have hf : accountDeployable m.world (create2Address m.ctx.crypto.keccak256
      m.frame.msg.currentTarget salt (initCodeOf m off size)) = true := hfree
  simp only [createCharge, ite_true] at hg
  simp only [initCodeOf, createMemory] at hf
  rw [step_eq_of_code hcode, decode_create2]
  simp only [exec, execCreate, popNat, pop, getFrame, modifyFrame, StateT.run_bind, hstk,
    StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, memoryExpansion,
    ite_true, charge, hg, ite_false, expandMemory, List.foldl, hs, readMemory,
    requireNonStatic, hstatic, Bool.false_eq_true, setReturnData, hb, hnonce, hd, decide_false,
    Bool.or_false, run_accessAddress, hf, Bool.not_true, modifyWorld]
  simp only [pure, Except.pure, launchCreate, beginCreate]
  rfl

/-! ## The other outcomes of `CREATE`/`CREATE2` -/

/-- The opcode byte of `CREATE` (`b = false`) or `CREATE2` (`b = true`). -/
def createByte (b : Bool) : UInt8 := if b then 0xf5 else 0xf0

/-- The stack below `value :: off :: size`: `salt :: rest` for `CREATE2`, `rest` for `CREATE`
(the salt is then unused). -/
def createRest (b : Bool) (salt : Word) (rest : List Word) : List Word :=
  if b then salt :: rest else rest

@[simp] theorem createByte_false : createByte false = 0xf0 := rfl
@[simp] theorem createByte_true : createByte true = 0xf5 := rfl
@[simp] theorem createRest_false (salt : Word) (rest : List Word) :
    createRest false salt rest = rest := rfl
@[simp] theorem createRest_true (salt : Word) (rest : List Word) :
    createRest true salt rest = salt :: rest := rfl

/-- The unfolded charge, as `execCreate` computes it. -/
theorem createCharge_eq (m : Machine) (b : Bool) (off size : Word) :
    createCharge m b off size = (if b = true then Gas.create2Cost size.toNat
      else Gas.createCost size.toNat) +
        (Gas.extendMemory m.frame.memory.size [(off.toNat, size.toNat)]).cost := rfl

/-- The simp set reducing `execCreate` on a known stack. -/
macro "create_simp" " [" extra:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [exec, execCreate, popNat, pop, getFrame, modifyFrame, StateT.run_bind,
    StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, memoryExpansion, ite_true,
    ite_false, charge, expandMemory, List.foldl, readMemory, requireNonStatic, Bool.false_eq_true,
    setReturnData, decide_false, decide_true, Bool.or_false, Bool.or_true, Bool.false_or,
    Bool.true_or, run_accessAddress, Bool.not_true, Bool.not_false, modifyWorld, refundGas,
    push, advance, $extra,*])

/-- **Out of gas for the charge**: `CREATE*` halts with `outOfGas`. -/
theorem step_create_oog {b : Bool} (hcode : m.frame.code[m.frame.pc]? = some (createByte b))
    (hstk : m.frame.stack = value :: off :: size :: createRest b salt rest)
    (hgas : m.frame.gasLeft < createCharge m b off size) :
    step m = finishFrame m (.halt .outOfGas) := by
  refine step_of_exec_error hcode ?_
  rw [createCharge_eq] at hgas
  cases b
  · simp only [createRest_false] at hstk
    simp only [Bool.false_eq_true, ite_false] at hgas
    rw [createByte_false, decode_create]
    create_simp [hstk, hgas]
    rfl
  · simp only [createRest_true] at hstk
    simp only [ite_true] at hgas
    rw [createByte_true, decode_create2]
    create_simp [hstk, hgas]
    rfl

/-- **Init code over the EIP-3860 limit** (`2 · 24576` bytes): `CREATE*` halts with
`initCodeSizeExceeded` once the charge is paid. -/
theorem step_create_initcode {b : Bool}
    (hcode : m.frame.code[m.frame.pc]? = some (createByte b))
    (hstk : m.frame.stack = value :: off :: size :: createRest b salt rest)
    (hgas : createCharge m b off size ≤ m.frame.gasLeft)
    (hsize : Gas.maxInitCodeSize m.ctx.fork < size.toNat) :
    step m = finishFrame m (.halt .initCodeSizeExceeded) := by
  refine step_of_exec_error hcode ?_
  have hg := Nat.not_lt.mpr hgas
  rw [createCharge_eq] at hg
  have hs : size.toNat > Gas.maxInitCodeSize m.ctx.fork := hsize
  cases b
  · simp only [createRest_false] at hstk
    simp only [Bool.false_eq_true, ite_false] at hg
    rw [createByte_false, decode_create]
    create_simp [hstk, hg, hs]
    rfl
  · simp only [createRest_true] at hstk
    simp only [ite_true] at hg
    rw [createByte_true, decode_create2]
    create_simp [hstk, hg, hs]
    rfl

/-- **A static frame**: `CREATE*` halts with `writeInStaticContext` once the charge is paid and
the init-code size checked. -/
theorem step_create_static {b : Bool}
    (hcode : m.frame.code[m.frame.pc]? = some (createByte b))
    (hstk : m.frame.stack = value :: off :: size :: createRest b salt rest)
    (hgas : createCharge m b off size ≤ m.frame.gasLeft)
    (hsize : size.toNat ≤ Gas.maxInitCodeSize m.ctx.fork)
    (hstatic : m.frame.msg.isStatic = true) :
    step m = finishFrame m (.halt .writeInStaticContext) := by
  refine step_of_exec_error hcode ?_
  have hg := Nat.not_lt.mpr hgas
  rw [createCharge_eq] at hg
  have hs : ¬ size.toNat > Gas.maxInitCodeSize m.ctx.fork := Nat.not_lt.mpr hsize
  cases b
  · simp only [createRest_false] at hstk
    simp only [Bool.false_eq_true, ite_false] at hg
    rw [createByte_false, decode_create]
    create_simp [hstk, hg, hs, hstatic]
    rfl
  · simp only [createRest_true] at hstk
    simp only [ite_true] at hg
    rw [createByte_true, decode_create2]
    create_simp [hstk, hg, hs, hstatic]
    rfl

/-- The creator's machine after a soft failure: `0` pushed, the charge paid, memory expanded,
return data cleared; the child's gas comes back. -/
def createSoftFail (m : Machine) (b : Bool) (off size : Word) (rest : List Word) : Machine :=
  { m with frame := { m.frame with
    stack := 0 :: rest
    gasLeft := m.frame.gasLeft - createCharge m b off size
    memory := createMemory m off size
    returnData := .empty
    pc := m.frame.pc + 1 } }

/-- **Soft failure**: when the creator cannot pay `value`, its nonce is at the EIP-2681 maximum, or
the depth limit is reached, `CREATE*` pushes `0` and the frame continues with the charge paid
(the child's gas returned), the world unchanged and no address warmed. -/
theorem step_create_soft {b : Bool}
    (hcode : m.frame.code[m.frame.pc]? = some (createByte b))
    (hstk : m.frame.stack = value :: off :: size :: createRest b salt rest)
    (hlen : rest.length < 1024)
    (hgas : createCharge m b off size ≤ m.frame.gasLeft)
    (hsize : size.toNat ≤ Gas.maxInitCodeSize m.ctx.fork)
    (hstatic : m.frame.msg.isStatic = false)
    (hsoft : (m.world.balance m.frame.msg.currentTarget).toNat < value.toNat ∨
      (m.world.account m.frame.msg.currentTarget).nonce = Gas.maxNonce ∨
      Gas.stackDepthLimit < m.frame.msg.depth + 1) :
    step m = .running (createSoftFail m b off size rest) := by
  have hg := Nat.not_lt.mpr hgas
  have hle := createGas_le m b off size
  rw [createCharge_eq] at hg
  rw [createGas, createCharge_eq] at hle
  have hs : ¬ size.toNat > Gas.maxInitCodeSize m.ctx.fork := Nat.not_lt.mpr hsize
  have hl : ¬ Gas.stackLimit ≤ rest.length := Nat.not_le.mpr hlen
  have hsoft' : (decide ((m.world.account m.frame.msg.currentTarget).balance.toNat < value.toNat)
      || decide ((m.world.account m.frame.msg.currentTarget).nonce = Gas.maxNonce)
      || decide (m.frame.msg.depth + 1 > Gas.stackDepthLimit)) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    rcases hsoft with h | h | h
    · exact .inl (.inl h)
    · exact .inl (.inr h)
    · exact .inr h
  rw [step_eq_of_code hcode]
  cases b
  · simp only [createRest_false] at hstk
    simp only [Bool.false_eq_true, ite_false] at hg hle
    rw [createByte_false, decode_create]
    create_simp [hstk, hg, hs, hstatic, hsoft', hl, Nat.sub_add_cancel hle]
    rfl
  · simp only [createRest_true] at hstk
    simp only [ite_true] at hg hle
    rw [createByte_true, decode_create2]
    create_simp [hstk, hg, hs, hstatic, hsoft', hl, Nat.sub_add_cancel hle]
    rfl

/-- The creator's machine after an address collision: `0` pushed, the charge **and the child's
gas** consumed, memory expanded, return data cleared, the address warm, the creator's nonce
incremented. -/
def createCollision (m : Machine) (b : Bool) (off size salt : Word) (rest : List Word) :
    Machine :=
  { m with
    world := incrementNonce m.world m.frame.msg.currentTarget
    frame := { m.frame with
      stack := 0 :: rest
      gasLeft := m.frame.gasLeft - createCharge m b off size - createGas m b off size
      memory := createMemory m off size
      returnData := .empty
      sub := m.frame.sub.warmAddr (newAddress m b off size salt)
      pc := m.frame.pc + 1 } }

/-- **Address collision** (EIP-7610: the new address has a nonce, code or storage): `CREATE*`
pushes `0`, keeps none of the child's gas, and increments the creator's nonce. -/
theorem step_create_collision {b : Bool}
    (hcode : m.frame.code[m.frame.pc]? = some (createByte b))
    (hstk : m.frame.stack = value :: off :: size :: createRest b salt rest)
    (hlen : rest.length < 1024)
    (hgas : createCharge m b off size ≤ m.frame.gasLeft)
    (hsize : size.toNat ≤ Gas.maxInitCodeSize m.ctx.fork)
    (hstatic : m.frame.msg.isStatic = false)
    (hbal : value.toNat ≤ (m.world.balance m.frame.msg.currentTarget).toNat)
    (hnonce : (m.world.account m.frame.msg.currentTarget).nonce ≠ Gas.maxNonce)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hcoll : accountDeployable m.world (newAddress m b off size salt) = false) :
    step m = .running (createCollision m b off size salt rest) := by
  have hg := Nat.not_lt.mpr hgas
  rw [createCharge_eq] at hg
  have hs : ¬ size.toNat > Gas.maxInitCodeSize m.ctx.fork := Nat.not_lt.mpr hsize
  have hl : ¬ Gas.stackLimit ≤ rest.length := Nat.not_le.mpr hlen
  have hd : ¬ m.frame.msg.depth + 1 > Gas.stackDepthLimit := Nat.not_lt.mpr hdepth
  have hb : ¬ (m.world.account m.frame.msg.currentTarget).balance.toNat < value.toNat :=
    Nat.not_lt.mpr hbal
  rw [step_eq_of_code hcode]
  cases b
  · simp only [createRest_false] at hstk
    simp only [Bool.false_eq_true, ite_false] at hg
    have hc : accountDeployable m.world (createAddress m.ctx.crypto.keccak256
        m.frame.msg.currentTarget (m.world.account m.frame.msg.currentTarget).nonce) = false :=
      hcoll
    rw [createByte_false, decode_create]
    create_simp [hstk, hg, hs, hstatic, hb, hnonce, hd, hl, hc]
    rfl
  · simp only [createRest_true] at hstk
    simp only [ite_true] at hg
    have hc : accountDeployable m.world (create2Address m.ctx.crypto.keccak256
        m.frame.msg.currentTarget salt (initCodeOf m off size)) = false := hcoll
    simp only [initCodeOf, createMemory] at hc
    rw [createByte_true, decode_create2]
    create_simp [hstk, hg, hs, hstatic, hb, hnonce, hd, hl, hc]
    rfl

/-- A soft failure stays in the creator's frame (for `WP.of_step` with `step_create_soft`). -/
theorem sameFrame_createSoftFail (m : Machine) (b : Bool) (off size : Word) (rest : List Word) :
    SameFrame m (createSoftFail m b off size rest) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- An address collision stays in the creator's frame (for `WP.of_step` with
`step_create_collision`). -/
theorem sameFrame_createCollision (m : Machine) (b : Bool) (off size salt : Word)
    (rest : List Word) : SameFrame m (createCollision m b off size salt rest) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Returning to the creator -/

/-- **Return after a successful creation**: the code deposit succeeded (`depositCode` left `g`
gas), so the returned bytes are the new account's code, its address is pushed, the unused gas
returned, the return data cleared and the child's accrued substate merged. -/
theorem resumeAfter_create_success {p : Frame} {ps : List Frame} {mf : Machine}
    {out : ByteArray} {g : Nat} (hk : mf.frame.kind = .create)
    (hd : depositCode mf.ctx.fork mf.frame.gasLeft out = .ok g) :
    resumeAfter p ps mf (.success out) =
      { mf with
        parents := ps
        world := setCode mf.world mf.frame.msg.currentTarget out
        frame := { p with
          gasLeft := p.gasLeft + g
          sub := mergeSub p.sub mf.frame.sub (setCode mf.world mf.frame.msg.currentTarget out)
            mf.frame.msg.currentTarget
          returnData := .empty
          stack := Word.ofAddress mf.frame.msg.currentTarget :: p.stack
          pc := p.pc + 1 } } := by
  simp only [resumeAfter, frameResult, hk, hd, resume, ChildResult.success, Option.isNone_none,
    Bool.not_false, Bool.and_self, ite_true]
  rfl

/-- **Return after a failed code deposit** (EIP-3541 `0xef` prefix, deposit cost, EIP-170 size):
like an exceptional halt, `0` pushed, no gas returned, world and transient storage rolled back. -/
theorem resumeAfter_create_deposit_fail {p : Frame} {ps : List Frame} {mf : Machine}
    {out : ByteArray} {e : ExceptionalHalt} (hk : mf.frame.kind = .create)
    (hd : depositCode mf.ctx.fork mf.frame.gasLeft out = .error e) :
    resumeAfter p ps mf (.success out) =
      { mf with
        parents := ps
        world := mf.frame.snapshot.1
        transient := mf.frame.snapshot.2
        frame := { p with
          gasLeft := p.gasLeft
          sub := failSub p.sub mf.frame.sub mf.frame.snapshot.1 mf.frame.msg.currentTarget
          returnData := .empty
          stack := 0 :: p.stack
          pc := p.pc + 1 } } := by
  simp only [resumeAfter, frameResult, hk, hd, resume, ChildResult.success, Option.isNone_some,
    Bool.false_and, Bool.false_eq_true, ite_false, failSub, Nat.add_zero]

/-- **Return after the init code `REVERT`s**: `0` pushed, the revert data kept as return data,
the unused gas returned, world and transient storage rolled back. -/
theorem resumeAfter_create_revert {p : Frame} {ps : List Frame} {mf : Machine}
    {out : ByteArray} (hk : mf.frame.kind = .create) :
    resumeAfter p ps mf (.revert out) =
      { mf with
        parents := ps
        world := mf.frame.snapshot.1
        transient := mf.frame.snapshot.2
        frame := { p with
          gasLeft := p.gasLeft + mf.frame.gasLeft
          sub := failSub p.sub mf.frame.sub mf.frame.snapshot.1 mf.frame.msg.currentTarget
          returnData := out
          stack := 0 :: p.stack
          pc := p.pc + 1 } } := by
  simp only [resumeAfter, frameResult, hk, resume, ChildResult.success, Option.isNone_none,
    Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, failSub]

/-- **Return after the init code halts exceptionally**: `0` pushed, no gas returned, empty return
data, world and transient storage rolled back. -/
theorem resumeAfter_create_halt {p : Frame} {ps : List Frame} {mf : Machine}
    {e : ExceptionalHalt} (hk : mf.frame.kind = .create) :
    resumeAfter p ps mf (.halt e) =
      { mf with
        parents := ps
        world := mf.frame.snapshot.1
        transient := mf.frame.snapshot.2
        frame := { p with
          gasLeft := p.gasLeft
          sub := failSub p.sub mf.frame.sub mf.frame.snapshot.1 mf.frame.msg.currentTarget
          returnData := .empty
          stack := 0 :: p.stack
          pc := p.pc + 1 } } := by
  simp only [resumeAfter, frameResult, hk, resume, ChildResult.success, Option.isNone_some,
    Bool.false_and, Bool.false_eq_true, ite_false, failSub, Nat.add_zero]

/-- Whatever the init code does, the creator resumes at the next instruction with one more word
on its stack: the new address or `0`. -/
theorem resumeAfter_create_stack {p : Frame} {ps : List Frame} {mf : Machine} {o : Outcome}
    (hk : mf.frame.kind = .create) :
    (resumeAfter p ps mf o).frame.pc = p.pc + 1 ∧
      ((resumeAfter p ps mf o).frame.stack = Word.ofAddress mf.frame.msg.currentTarget :: p.stack ∨
       (resumeAfter p ps mf o).frame.stack = 0 :: p.stack) := by
  cases o with
  | success out =>
    cases hd : depositCode mf.ctx.fork mf.frame.gasLeft out with
    | ok g => rw [resumeAfter_create_success hk hd]; exact ⟨rfl, .inl rfl⟩
    | error e => rw [resumeAfter_create_deposit_fail hk hd]; exact ⟨rfl, .inr rfl⟩
  | revert out => rw [resumeAfter_create_revert hk]; exact ⟨rfl, .inr rfl⟩
  | halt e => rw [resumeAfter_create_halt hk]; exact ⟨rfl, .inr rfl⟩

/-! ## The callee-summary rules -/

/-- The child of a `CREATE*` is a fresh creation frame (`SameFrame` with it keeps `kind`). -/
@[simp] theorem createChild_kind (m : Machine) (b : Bool) (value off size salt : Word)
    (rest : List Word) : (createChild m b value off size salt rest).frame.kind = .create := rfl

/-- **Callee-summary rule for `CREATE`** (`step_create` + `WP.call`): if the init-code frame
`Halts` with `Hc`, the creator continues from `resumeAfter` of every end `Hc` allows
(`resumeAfter_create_success`/`_deposit_fail`/`_revert`/`_halt`). -/
theorem WP.create {Q : Machine → Prop} {H Hc : Machine → Outcome → Prop}
    (hcode : m.frame.code[m.frame.pc]? = some 0xf0)
    (hstk : m.frame.stack = value :: off :: size :: rest)
    (hgas : createCharge m false off size ≤ m.frame.gasLeft)
    (hsize : size.toNat ≤ Gas.maxInitCodeSize m.ctx.fork)
    (hstatic : m.frame.msg.isStatic = false)
    (hbal : value.toNat ≤ (m.world.balance m.frame.msg.currentTarget).toNat)
    (hnonce : (m.world.account m.frame.msg.currentTarget).nonce ≠ Gas.maxNonce)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hfree : accountDeployable m.world (newAddress m false off size 0) = true)
    (hcallee : Halts (createChild m false value off size 0 rest) Hc)
    (k : ∀ mf o, Hc mf o → SameFrame (createChild m false value off size 0 rest) mf →
      WP (resumeAfter (creatorFrame m false off size 0 rest) m.parents mf o) Q H) :
    WP m Q H :=
  WP.call (step_create hcode hstk hgas hsize hstatic hbal hnonce hdepth hfree) rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hcallee
    (fun mf o hs hc => k mf o hc hs)

/-- **Callee-summary rule for `CREATE2`** (`step_create2` + `WP.call`). -/
theorem WP.create2 {Q : Machine → Prop} {H Hc : Machine → Outcome → Prop}
    (hcode : m.frame.code[m.frame.pc]? = some 0xf5)
    (hstk : m.frame.stack = value :: off :: size :: salt :: rest)
    (hgas : createCharge m true off size ≤ m.frame.gasLeft)
    (hsize : size.toNat ≤ Gas.maxInitCodeSize m.ctx.fork)
    (hstatic : m.frame.msg.isStatic = false)
    (hbal : value.toNat ≤ (m.world.balance m.frame.msg.currentTarget).toNat)
    (hnonce : (m.world.account m.frame.msg.currentTarget).nonce ≠ Gas.maxNonce)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hfree : accountDeployable m.world (newAddress m true off size salt) = true)
    (hcallee : Halts (createChild m true value off size salt rest) Hc)
    (k : ∀ mf o, Hc mf o → SameFrame (createChild m true value off size salt rest) mf →
      WP (resumeAfter (creatorFrame m true off size salt rest) m.parents mf o) Q H) :
    WP m Q H :=
  WP.call (step_create2 hcode hstk hgas hsize hstatic hbal hnonce hdepth hfree) rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hcallee
    (fun mf o hs hc => k mf o hc hs)

end EvmLogic.Program

end
