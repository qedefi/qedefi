import Snapshot.Run

/-!
# Checking a snapshot offline

Loads a snapshot (checking every code file against its hash) and replays each recorded call
in the Lean interpreter. A call passes if it reads only state the snapshot determines and
returns exactly what the node's `eth_call` returned (success flag and output bytes). No
network access.
-/

namespace Snapshot

open EvmLean Conformance

/-- Replay every recorded call; prints failures and a summary, returns the number of failures. -/
def checkSnapshot (dir : System.FilePath) (verbose : Bool := false) : IO Nat := do
  let s ← State.load dir
  let calls ← loadCalls dir
  let world := s.world
  let mut ok := 0
  let mut failures := 0
  for c in calls do
    match replay s world c with
    | .ok =>
      ok := ok + 1
      if verbose then IO.println s!"ok          {c.spec.label}"
    | .mismatch got =>
      failures := failures + 1
      IO.println s!"MISMATCH    {c.spec.label}: node {c.rpc.success} {hexOfBytes c.rpc.output |>.take 74}, \
        lean {got.success} {hexOfBytes got.output |>.take 74}"
    | .incomplete miss =>
      failures := failures + 1
      IO.println s!"INCOMPLETE  {c.spec.label}: reads {miss.accounts.size} accounts, \
        {miss.slotList.length} slots, {miss.blockNumbers.size} block hashes outside the snapshot"
    | .error e =>
      failures := failures + 1
      IO.println s!"ERROR       {c.spec.label}: {e}"
  IO.println s!"{dir}: chain {s.chainId} block {s.block} {s.fork.name}, {s.accounts.size} accounts; \
    {ok}/{calls.size} calls reproduce eth_call exactly"
  return failures

end Snapshot
