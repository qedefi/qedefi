import EvmLeanSpecs.Refinement.EventsLog

/-!
# Tactics for the log companions of the vault's internal functions

`logs_simp [h, …]`: normalise the logs of a substate built by symbolic execution — warm sets,
refunds and successful child calls keep or concatenate logs (`warmKey_logs`, `mergeSub_logs`,
…) — using the extra facts `h` (typically the callee's or an internal function's logs).
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Interpreter EvmLean.Solidity

/-- Normalise the logs of a substate built by symbolic execution, with extra rewrite facts. -/
macro "logs_simp" " [" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp only [mergeSub_logs, failSub_logs, warmKey_logs, warmAddr_logs, addRefund_logs,
    ofMessage_logs, frameInit_logs, resumeWith_logs, Array.append_empty, Array.empty_append,
    Array.append_push, $hs,*]))

end EvmLeanSpecs.Refinement
