import Snapshot.Http
import Snapshot.Rpc
import Snapshot.Chain
import Snapshot.Access
import Snapshot.State
import Snapshot.Sources
import Snapshot.Run
import Snapshot.Fetch
import Snapshot.Check

/-!
# Snapshots of deployed contracts

Fetch once, search offline: the code, verified sources and the reachable state of deployed
contracts at one pinned block (`lake exe snapshot fetch`), loaded as an `EvmLean.World` with
its block environment (`Snapshot.State.load`, `State.world`, `State.context`), and calls on
it checked against the node's `eth_call` (`lake exe snapshot check`).
-/
