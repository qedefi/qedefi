import QEDefi.ERC20.Spec.Storage
import QEDefi.ERC20.Spec.Instances.GUSD
import Verified.WeirdERC20.GUSD.Contracts.GUSD
import Verified.WeirdERC20.GUSD.Contracts.GUSDImpl
import Verified.WeirdERC20.GUSD.Contracts.GUSDStore

/-!
# GUSD: the abstraction over three contracts, and what its spec needs

`ERC20Spec code abs M` is about one account: `abs.read` may depend only on the storage of the
executing account (`TokenAbs.read_congr`), and `Start` constrains only the code being run. For
GUSD that is the wrong statement. The token address runs `ERC20Proxy`, whose every ERC-20 call
`CALL`s `erc20Impl` (another account, whose code `Start` says nothing about), which `CALL`s the
store to write the ledger and the proxy back to emit the event. `ERC20Spec` of the proxy's code
alone is false: in a world where `erc20Impl` holds other code, a `transfer` does whatever that
code does. And the ledger is not in the proxy's storage at all, so no `TokenAbs` of the proxy
can read it.

What can be stated, and is stated here, is the system's abstraction: `read` of the model state
(`QEDefi.ERC20.Spec.GUSD.State`) from the storage of the three pinned accounts (the store's
ledger, the two `erc20Impl` pointers, the three custodians), the footprint per account, the
congruence `read_congr` over it, and the actors' hash hypothesis `Sound` (on the store's rows).
The model is `QEDefi.ERC20.Spec.GUSD.model implAddr`, whose `wf` requires both pointers to be
`implAddr`.

**A system-level spec needs**, beyond `ERC20Spec`'s data:

* a start condition on the world, not only on the frame: the frame runs at the pinned proxy
  address (the implementation's `onlyProxy` compares the caller with its immutable
  `erc20Proxy`), and the world holds `GUSDImpl.runtimeCode` at `implAddr` and
  `GUSDStore.runtimeCode` at `storeAddr` (both mainnet codes with the immutables filled in);
  with `wf`, the pointers then lead to that code;
* `Matches` and `FrameKeeps` over the three accounts: the store's storage changes only in the
  footprint (`sysFootprint`), the proxy's and the implementation's storage only in theirs
  (unchanged by every ERC-20 call), no other account, and the logs the proxy emits in the
  nested `emitTransfer`/`emitApproval` frames appended to the outer frame's logs;
* a gas bound for a call tree of depth 3 under the 63/64 rule;
* obligations for frames at the other two addresses: the implementation's own entry points
  (`burn`, `print`, `batchTransfer`, the custodian's lock-id protocol) are operations of the
  model, called on `implAddr`, not on the token address;
* a simulation rather than an equality for the custodians' two-step changes: the model folds
  `request…Change(new)` and `confirm…Change(lockId)` into one operation (and leaves the request
  maps and `lockRequestCount` out of the state), so `confirm…` needs the pending request in a
  state the model abstracts away.
-/

namespace Verified.WeirdERC20.GUSD.Spec
open EvmLean EvmLogic EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec

/-- The token address (`ERC20Proxy`). -/
def proxyAddr : Address := Contracts.GUSD.address
/-- The pinned implementation (`ERC20Impl`). -/
def implAddr : Address := Contracts.GUSDImpl.address
/-- The store (`ERC20Store`). -/
def storeAddr : Address := Contracts.GUSDStore.address

/-- `custodian` (all three contracts). -/
def custodianSlot : Word := 1
/-- `erc20Impl` (proxy and store). -/
def implSlot : Word := 3
/-- The store's `totalSupply`. -/
def supplySlot : Word := 5
/-- The store's `balances`. -/
def balancesSlot : Word := 6
/-- The store's `allowed`. -/
def allowedSlot : Word := 7

/-- **GUSD as the actors `Act` see it**, read from the three accounts: the store's ledger
(balances and allowances of the actors, the supply), the proxy's and the store's `erc20Impl`,
the three custodians (addresses as the low 160 bits of their slots). -/
noncomputable def sysRead (crypto : Crypto) (Act : Finset Address) (w : World) :
    GUSD.State Address :=
  (VState.ofToken ⟨readMap crypto Act w storeAddr balancesSlot, readSlot w storeAddr supplySlot,
      readMap2 crypto Act w storeAddr allowedSlot⟩ proxyAddr 0,
    { proxyImpl := Word.toAddress (w.sload proxyAddr implSlot)
      storeImpl := Word.toAddress (w.sload storeAddr implSlot)
      proxyCustodian := Word.toAddress (w.sload proxyAddr custodianSlot)
      implCustodian := Word.toAddress (w.sload implAddr custodianSlot)
      storeCustodian := Word.toAddress (w.sload storeAddr custodianSlot) })

/-- The slots `sysRead` depends on, per account. -/
def sysFootprint (crypto : Crypto) (Act : Finset Address) (a : Address) (k : Word) : Prop :=
  (a = proxyAddr ∧ (k = custodianSlot ∨ k = implSlot)) ∨
  (a = implAddr ∧ k = custodianSlot) ∨
  (a = storeAddr ∧ (k = custodianSlot ∨ k = implSlot ∨ k = supplySlot ∨
    MapSlots crypto Act balancesSlot k ∨ Map2Slots crypto Act allowedSlot k))

/-- `sysRead` depends on nothing but the footprint (no ether is read). -/
theorem sysRead_congr (crypto : Crypto) (Act : Finset Address) (w w' : World)
    (h : ∀ a k, sysFootprint crypto Act a k → w'.sload a k = w.sload a k) :
    sysRead crypto Act w' = sysRead crypto Act w := by
  simp only [sysRead]
  rw [readMap_congr (fun k hk => h _ k (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl hk)))⟩))),
    readMap2_congr (fun k hk => h _ k (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr hk)))⟩))),
    readSlot_congr (h _ _ (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inl rfl))⟩))),
    h _ _ (Or.inl ⟨rfl, Or.inr rfl⟩), h _ _ (Or.inl ⟨rfl, Or.inl rfl⟩),
    h _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩)),
    h _ _ (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl rfl)⟩)),
    h _ _ (Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩))]

/-- The actors' hash hypothesis: their rows of the store's `balances` and `allowed` are pairwise
distinct and none is a declared slot of the store (`0 … 7`). -/
def Sound (crypto : Crypto) (Act : Finset Address) : Prop :=
  ActorRows crypto Act [balancesSlot] [allowedSlot] [0, 1, 2, 3, 4, 5, 6, 7]

/-- **The GUSD model** for the pinned implementation. -/
noncomputable def M : TokenModel (GUSD.State Address) Address (GUSD.Op Address) :=
  QEDefi.ERC20.Spec.GUSD.model implAddr

/-- The token address's dispatcher selectors (the verified ABI of `ERC20Proxy`). -/
def sel : List Nat := Contracts.GUSD.selectors.map (·.2.toNat)

/-- The pinned addresses are distinct. -/
theorem addrs_ne : proxyAddr ≠ implAddr ∧ proxyAddr ≠ storeAddr ∧ implAddr ≠ storeAddr := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The pinned deployment is wired: in a world whose proxy and store point at `implAddr`, the
model's `wf` reduces to the supply bound. -/
theorem wf_sysRead_iff (crypto : Crypto) (Act : Finset Address) (w : World)
    (hp : Word.toAddress (w.sload proxyAddr implSlot) = implAddr)
    (hs : Word.toAddress (w.sload storeAddr implSlot) = implAddr) :
    M.wf (sysRead crypto Act w) ↔ YAMV2.SubSupply (sysRead crypto Act w).1 := by
  simp [M, GUSD.model, GUSD.WF, sysRead, hp, hs]

end Verified.WeirdERC20.GUSD.Spec
