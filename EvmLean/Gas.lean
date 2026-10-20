import EvmLean.Fork

/-!
# Gas schedule

Gas constants and cost functions, mirroring `vm/gas.py` and the inline costs in
`vm/instructions/*.py`. All quantities are `Nat`, so huge offsets just yield huge costs that
fail the gas check. Fork-dependent constants match on `Fork` exhaustively.
-/

namespace EvmLean.Gas

/-! ## Tiers and constants (`GasCosts`) -/

/-- `GasCosts.ZERO`. -/
def zero : Nat := 0
/-- `GasCosts.BASE`. -/
def base : Nat := 2
/-- `GasCosts.VERY_LOW`. -/
def veryLow : Nat := 3
/-- `GasCosts.LOW`. -/
def low : Nat := 5
/-- `GasCosts.MID`. -/
def mid : Nat := 8
/-- `GasCosts.HIGH`. -/
def high : Nat := 10
/-- `GasCosts.FAST_STEP` (`SELFBALANCE`). -/
def fastStep : Nat := 5

/-- `GasCosts.WARM_ACCESS` (EIP-2929). -/
def warmAccess : Nat := 100
/-- `GasCosts.COLD_ACCOUNT_ACCESS` (EIP-2929). -/
def coldAccountAccess : Nat := 2600
/-- `GasCosts.COLD_STORAGE_ACCESS` (EIP-2929). -/
def coldStorageAccess : Nat := 2100

/-- `GasCosts.STORAGE_SET`. -/
def storageSet : Nat := 20000
/-- `GasCosts.COLD_STORAGE_WRITE` (the EIP-2200 "reset" cost before the EIP-2929 discount). -/
def coldStorageWrite : Nat := 5000
/-- `GasCosts.REFUND_STORAGE_CLEAR` (EIP-3529). -/
def refundStorageClear : Int := 4800

/-- `GasCosts.CALL_STIPEND`; also the EIP-2200 `SSTORE` sentry (needs more than this left). -/
def callStipend : Nat := 2300
/-- `GasCosts.CALL_VALUE`. -/
def callValue : Nat := 9000
/-- `GasCosts.NEW_ACCOUNT`. -/
def newAccount : Nat := 25000

/-- `GasCosts.CODE_DEPOSIT_PER_BYTE`. -/
def codeDepositPerByte : Nat := 200
/-- `GasCosts.CODE_INIT_PER_WORD` (EIP-3860). -/
def codeInitPerWord : Nat := 2

/-- `GasCosts.MEMORY_PER_WORD`. -/
def memoryPerWord : Nat := 3

/-- `GasCosts.OPCODE_BLOCKHASH`. -/
def blockhash : Nat := 20
/-- `GasCosts.OPCODE_JUMPDEST`. -/
def jumpdest : Nat := 1
/-- `GasCosts.OPCODE_BLOBHASH`. -/
def blobhash : Nat := 3
/-- `GasCosts.OPCODE_COPY_PER_WORD` (also `OPCODE_RETURNDATACOPY_PER_WORD`). -/
def copyPerWord : Nat := 3
/-- `GasCosts.OPCODE_CREATE_BASE`. -/
def createBase : Nat := 32000
/-- `GasCosts.OPCODE_EXP_BASE`. -/
def expBase : Nat := 10
/-- `GasCosts.OPCODE_EXP_PER_BYTE`. -/
def expPerByte : Nat := 50
/-- `GasCosts.OPCODE_KECCAK256_BASE`. -/
def keccak256Base : Nat := 30
/-- `GasCosts.OPCODE_KECCAK256_PER_WORD`. -/
def keccak256PerWord : Nat := 6
/-- `GasCosts.OPCODE_LOG_BASE`. -/
def logBase : Nat := 375
/-- `GasCosts.OPCODE_LOG_DATA_PER_BYTE`. -/
def logDataPerByte : Nat := 8
/-- `GasCosts.OPCODE_LOG_TOPIC`. -/
def logTopic : Nat := 375
/-- `GasCosts.OPCODE_SELFDESTRUCT_BASE`. -/
def selfdestructBase : Nat := 5000
/-- `GasCosts.OPCODE_SELFDESTRUCT_NEW_ACCOUNT`. -/
def selfdestructNewAccount : Nat := 25000

/-! ## Limits -/

/-- `STACK_DEPTH_LIMIT` (`cancun/vm/interpreter.py`): maximum call depth. -/
def stackDepthLimit : Nat := 1024

/-- Maximum number of stack items (`cancun/vm/stack.py`). -/
def stackLimit : Nat := 1024

/-- `MAX_CODE_SIZE` (EIP-170). -/
def maxCodeSize : Fork → Nat
  | .cancun | .prague | .osaka => 0x6000

/-- `MAX_INIT_CODE_SIZE` (EIP-3860): twice the maximum code size. -/
def maxInitCodeSize (fork : Fork) : Nat := 2 * maxCodeSize fork

/-- Largest nonce before `CREATE` fails (EIP-2681). -/
def maxNonce : Nat := 2 ^ 64 - 1

/-! ## Helpers -/

/-- `ceil32`: round up to a multiple of 32. -/
def ceil32 (n : Nat) : Nat := (n + 31) / 32 * 32

/-- Number of 32-byte words needed to hold `n` bytes. -/
def words (n : Nat) : Nat := (n + 31) / 32

/-! ## Memory (`calculate_memory_gas_cost`, `calculate_gas_extend_memory`) -/

/-- `calculate_memory_gas_cost`: `3·w + w²/512` for `w` words. -/
def memoryCost (sizeInBytes : Nat) : Nat :=
  let w := words sizeInBytes
  memoryPerWord * w + w * w / 512

/-- Result of `extendMemory`: the gas to charge and the memory size afterwards. -/
structure ExtendMemory where
  /-- Gas to charge for the expansion. -/
  cost : Nat
  /-- Memory size in bytes after the expansion (a multiple of 32 if it grew). -/
  newSize : Nat
  deriving Repr, DecidableEq

/-- `calculate_gas_extend_memory`, returning the new size; zero-length accesses never expand. -/
def extendMemory (currentSize : Nat) (extensions : List (Nat × Nat)) : ExtendMemory :=
  extensions.foldl
    (fun acc (start, size) =>
      if size = 0 then acc
      else
        let before := ceil32 acc.newSize
        let after := ceil32 (start + size)
        if after ≤ before then acc
        else { cost := acc.cost + (memoryCost after - memoryCost before), newSize := after })
    { cost := 0, newSize := currentSize }

/-! ## Calls (`calculate_message_call_gas`, `max_message_call_gas`) -/

/-- All but one 64th (EIP-150). Mirrors `max_message_call_gas`. -/
def maxMessageCallGas (gas : Nat) : Nat := gas - gas / 64

/-- Gas charged to the caller and gas handed to the callee for a `CALL*`. -/
structure MessageCallGas where
  /-- Charged to the caller (excluding memory expansion). -/
  cost : Nat
  /-- Given to the callee, including the stipend; refundable if unused. -/
  subCall : Nat
  deriving Repr, DecidableEq

/-- `calculate_message_call_gas`: cap `gas` at all-but-1/64, add stipend on value transfer.
Uncapped if `extraGas + memoryCost` is unaffordable (the charge then fails). -/
def messageCallGas (value : Nat) (gas gasLeft memoryCost extraGas : Nat)
    (stipend : Nat := callStipend) : MessageCallGas :=
  let stipend := if value = 0 then 0 else stipend
  if gasLeft < extraGas + memoryCost then
    { cost := gas + extraGas, subCall := gas + stipend }
  else
    let gas := min gas (maxMessageCallGas (gasLeft - memoryCost - extraGas))
    { cost := gas + extraGas, subCall := gas + stipend }

/-! ## Creation -/

/-- EIP-3860 init code cost: 2 per word. Mirrors `init_code_cost`. -/
def initCodeCost (initCodeLength : Nat) : Nat := codeInitPerWord * words initCodeLength

/-- Static part of `CREATE`'s cost (memory expansion excluded). Mirrors `create`. -/
def createCost (initCodeLength : Nat) : Nat := createBase + initCodeCost initCodeLength

/-- Static part of `CREATE2`'s cost: `CREATE` plus hashing the init code. Mirrors `create2`. -/
def create2Cost (initCodeLength : Nat) : Nat :=
  createBase + keccak256PerWord * words initCodeLength + initCodeCost initCodeLength

/-- Code deposit cost of a created contract. Mirrors `process_create_message`. -/
def codeDepositCost (codeLength : Nat) : Nat := codeDepositPerByte * codeLength

/-! ## Opcode-specific dynamic costs -/

/-- Number of bytes in the minimal big-endian encoding of `n` (`0` for `0`). -/
def byteLength (n : Nat) : Nat := if n = 0 then 0 else (n.log2 + 1 + 7) / 8

/-- `EXP`: `10 + 50 · bytes(exponent)`. Mirrors `exp` in `instructions/arithmetic.py`. -/
def expCost (exponent : Nat) : Nat := expBase + expPerByte * byteLength exponent

/-- `KECCAK256` static part: `30 + 6 · words`. Mirrors `keccak`. -/
def keccak256Cost (size : Nat) : Nat := keccak256Base + keccak256PerWord * words size

/-- Copy cost of `size` bytes for the `*COPY` opcodes: `3 · words`. -/
def copyCost (size : Nat) : Nat := copyPerWord * words size

/-- `LOGn` static part: `375 + 8 · size + 375 · n`. Mirrors `log_n`. -/
def logCost (size topics : Nat) : Nat := logBase + logDataPerByte * size + logTopic * topics

/-- EIP-2929 account access cost. -/
def accessCost (warm : Bool) : Nat := if warm then warmAccess else coldAccountAccess

/-- `SSTORE` cost and refund delta (EIP-2200/2929/3529); `original` is the value at tx start. -/
def sstoreCostRefund (original current new : Nat) (warm : Bool) : Nat × Int :=
  let coldCost := if warm then 0 else coldStorageAccess
  let writeCost :=
    if original = current ∧ current ≠ new then
      if original = 0 then storageSet else coldStorageWrite - coldStorageAccess
    else warmAccess
  let refund : Int :=
    if current ≠ new then
      let r₁ : Int := if original ≠ 0 ∧ current ≠ 0 ∧ new = 0 then refundStorageClear else 0
      let r₂ : Int := if original ≠ 0 ∧ current = 0 then -refundStorageClear else 0
      let r₃ : Int :=
        if original = new then
          if original = 0 then (storageSet : Int) - warmAccess
          else (coldStorageWrite : Int) - coldStorageAccess - warmAccess
        else 0
      r₁ + r₂ + r₃
    else 0
  (coldCost + writeCost, refund)

/-- `SELFDESTRUCT` cost: base + cold access + `NEW_ACCOUNT` if value moves to a dead account. -/
def selfdestructCost (beneficiaryWarm beneficiaryAlive originatorHasBalance : Bool) : Nat :=
  selfdestructBase
    + (if beneficiaryWarm then 0 else coldAccountAccess)
    + (if !beneficiaryAlive && originatorHasBalance then selfdestructNewAccount else 0)

/-! ## Blob gas price (EIP-4844, EIP-7516) -/

/-- `GasCosts.BLOB_MIN_GASPRICE`. -/
def blobMinGasPrice : Nat := 1

/-- `GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION`; raised by EIP-7691 in Prague. -/
def blobBaseFeeUpdateFraction : Fork → Nat
  | .cancun => 3338477
  | .prague | .osaka => 5007716

/-- Taylor-series loop of `fake_exponential`; `acc` is the term (× `denominator`). -/
def fakeExponentialLoop (numerator denominator : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, output, _ => output
  | fuel + 1, i, output, acc =>
    if acc = 0 then output
    else fakeExponentialLoop numerator denominator fuel (i + 1) (output + acc)
      (acc * numerator / (denominator * i))

/-- Sufficient fuel for `fakeExponentialLoop`: past `N₀ = 2(num/den + 1)` terms at least
halve, so `N₀ + bitlength(term at N₀) + 1` steps reach zero. -/
def fakeExponentialFuel (factor numerator denominator : Nat) : Nat :=
  let n₀ := 2 * (numerator / denominator + 1)
  n₀ + (factor * denominator).log2 + 1 + n₀ * (numerator.log2 + 1) + 2

/-- EIP-4844 `fake_exponential` (`taylor_exponential`); zero denominator yields `0`. -/
def fakeExponential (factor numerator denominator : Nat) : Nat :=
  if denominator = 0 then 0
  else
    fakeExponentialLoop numerator denominator (fakeExponentialFuel factor numerator denominator)
      1 0 (factor * denominator) / denominator

/-- Blob base fee from excess blob gas (`calculate_blob_gas_price`). -/
def blobGasPrice (fork : Fork) (excessBlobGas : Nat) : Nat :=
  fakeExponential blobMinGasPrice excessBlobGas (blobBaseFeeUpdateFraction fork)

end EvmLean.Gas
