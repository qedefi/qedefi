import EvmLean.Gas

/-! Unit tests for `EvmLean.Gas`. -/

open EvmLean EvmLean.Gas

-- Memory: 3w + w²/512
#guard memoryCost 0 = 0
#guard memoryCost 1 = 3
#guard memoryCost 32 = 3
#guard memoryCost 33 = 6
#guard memoryCost (32 * 1024) = 3 * 1024 + 2048
#guard extendMemory 0 [(0, 32)] = { cost := 3, newSize := 32 }
#guard extendMemory 32 [(0, 32)] = { cost := 0, newSize := 32 }
#guard extendMemory 0 [(2 ^ 200, 0)] = { cost := 0, newSize := 0 }
#guard extendMemory 0 [(0, 32), (64, 32)] = { cost := 9, newSize := 96 }
#guard extendMemory 64 [(0, 1), (95, 1)] = { cost := 3, newSize := 96 }
-- Huge offsets are priced without allocating.
#guard (extendMemory 0 [(2 ^ 255, 32)]).cost > 2 ^ 400

-- EIP-150 call gas
#guard maxMessageCallGas 6400 = 6300
#guard messageCallGas 0 100000 50000 0 2600 = { cost := 46660 + 2600, subCall := 46660 }
#guard messageCallGas 1 1000 50000 0 9000 = { cost := 1000 + 9000, subCall := 1000 + 2300 }
#guard messageCallGas 0 5 10 0 100 = { cost := 105, subCall := 5 }
#guard messageCallGas 7 5 10 0 100 = { cost := 105, subCall := 2305 }

-- EXP, creation, copies, logs
#guard expCost 0 = 10
#guard expCost 255 = 60
#guard expCost 256 = 110
#guard expCost (2 ^ 256 - 1) = 10 + 50 * 32
#guard initCodeCost 33 = 4
#guard create2Cost 64 = 32000 + 12 + 4
#guard copyCost 0 = 0
#guard copyCost 33 = 6
#guard logCost 10 2 = 375 + 80 + 750
#guard keccak256Cost 64 = 42
#guard maxInitCodeSize .cancun = 49152

-- SSTORE (EIP-2200 + EIP-2929 + EIP-3529)
#guard sstoreCostRefund 0 0 1 true = (20000, 0)
#guard sstoreCostRefund 0 0 1 false = (22100, 0)
#guard sstoreCostRefund 0 0 0 true = (100, 0)
#guard sstoreCostRefund 1 1 0 true = (2900, 4800)
#guard sstoreCostRefund 1 0 1 true = (100, -4800 + 2800)
#guard sstoreCostRefund 0 1 0 true = (100, 19900)
#guard sstoreCostRefund 1 2 0 true = (100, 4800)
#guard sstoreCostRefund 1 2 1 true = (100, 2800)
#guard sstoreCostRefund 1 1 1 false = (2200, 0)

-- SELFDESTRUCT
#guard selfdestructCost true true true = 5000
#guard selfdestructCost false false true = 5000 + 2600 + 25000
#guard selfdestructCost true false false = 5000

-- fake_exponential, checked against the reference `taylor_exponential`
#guard fakeExponential 1 0 3338477 = 1
#guard fakeExponential 1 3338477 3338477 = 2
#guard fakeExponential 1 33384770 3338477 = 22026
#guard fakeExponential 1 100000000 3338477 = 10203769476395
#guard fakeExponential 1 33384770 5007716 = 785
#guard fakeExponential 5 7 3 = 50
#guard blobGasPrice .cancun 0 = 1
#guard blobGasPrice .prague 100000000 = 470442149
#guard fakeExponential 1 1 0 = 0
