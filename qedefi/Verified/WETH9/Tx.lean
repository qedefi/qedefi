import Verified.WETH9.Backed
import QEDefi.Solvency.Tx

/-!
# WETH9's ether backs its tokens after any transaction, gas and fees included

`weth9_backed` (`Verified.WETH9.Backed`) is about one top-level `processMessageCall`. Here the
whole transaction (`EvmLean.Tx.process`) is covered, with nothing assumed about the rest of it:

* the prefix (the sender's nonce, the upfront fee debit) keeps WETH9's storage, code and ether:
  `check` enforces EIP-3607, so WETH9, which holds code that is no EIP-7702 designator, is not
  the sender;
* the top-level message is `TopOk` (`EvmLogic.Tx.topOk_prepareMessage`), so `weth9_solvent`
  applies to it;
* the suffix keeps WETH9's storage and code (WETH9 is never self-destructed: its code was not
  created in the transaction, `EvmLogic.Tx.processMessageCall_realCode`) and can only raise its
  ether: the refund goes to the sender, and the coinbase reward, if WETH9 is the coinbase,
  cannot wrap because all ether stays below `2²⁵⁶` (`QEDefi.Solvency.process_keeps_ether`).

`weth9_solvent_tx`, `weth9_backed_tx`: from a world in which WETH9 is solvent, every successful
transaction before Prague or without EIP-7702 authorizations leaves `Σₐ balanceOf[a]` at most
WETH9's ether, and below `2²⁵⁶`. The hypotheses are those of `weth9_backed`, with the
delegation hypothesis on the transaction instead of its context.
-/

namespace Verified.WETH9
open EvmLean EvmLean.Interpreter EvmLean.Tx EvmLogic EvmLogic.Program EvmLogic.Program.Nested
  EvmLogic.Tx QEDefi.Solvency

/-- WETH9's deployed code is real code: not empty, no EIP-7702 designator. -/
theorem realCode_good {crypto : Crypto} {weth : Address} {w : World}
    (h : Good crypto weth w) : RealCode (w.code weth) := by
  rw [h.code]; exact realCode_of_deleg size_code deleg_code

/-- A change keeping WETH9's storage and code, not decreasing its ether and keeping all ether
below `2²⁵⁶` keeps it solvent. -/
theorem good_of_frame {crypto : Crypto} {weth : Address} {w w' : World}
    (h : Good crypto weth w) (hk : Keep weth w w')
    (hb : (w.balance weth).toNat ≤ (w'.balance weth).toNat) (hs : supply w' < 2 ^ 256) :
    Good crypto weth w' where
  code := by rw [hk.code]; exact h.code
  backed := by rw [owed_keep hk]; exact Nat.le_trans h.backed hb
  bounded := by rw [owed_keep hk]; exact h.bounded
  capped := hs

/-- **WETH9 stays solvent after any transaction**: from a world in which it is solvent, every
successful transaction (any sender, recipient, value, calldata, gas limit and fees; any fork,
block and coinbase; hashing with `crypto`), before Prague or without EIP-7702 authorizations,
ends in a world in which it is solvent — provided no `allowance` entry shares its slot with a
`balanceOf` entry. -/
theorem weth9_solvent_tx {crypto : Crypto} {weth : Address}
    (hK : Disjoint (allowanceSlots crypto) (balanceSlots crypto 3#256)) {fuel : Nat}
    {fork : Fork} {env : BlockEnv} {gasAvail blobAvail : Nat} {w : World} {tx : Transaction}
    {hint : Option Address} {out : TxOutput} (hw : Good crypto weth w)
    (hdeleg : fork < .prague ∨ tx.authorizations = [])
    (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    Good crypto weth out.world :=
  (process_keeps_ether (P := (· = weth)) (Inv := Good crypto weth)
    (fun _ hw _ hp => hp ▸ realCode_good hw) (fun _ hw => hw.capped)
    (fun _ _ _ _ h1 hm hr => weth9_solvent hK h1 hm.ctxCrypto (hm.deleg hdeleg) hm.top
      hm.transfers hr)
    (fun _ _ hw hk hs => good_of_frame hw (hk weth rfl).1 (hk weth rfl).2 hs) hdeleg hw h).1

/-- **WETH9's ether backs its tokens, after any transaction**: when the slots of
`balanceOf[a]` do not collide, after every successful transaction from a world in which WETH9 is
solvent (before Prague or without EIP-7702 authorizations),
`Σₐ balanceOf[a] ≤ address(weth).balance` and the sum is below `2²⁵⁶`, over all addresses. -/
theorem weth9_backed_tx {crypto : Crypto} {weth : Address}
    (hK : Disjoint (allowanceSlots crypto) (balanceSlots crypto 3#256))
    (hinj : Function.Injective (balSlot crypto)) {fuel : Nat} {fork : Fork} {env : BlockEnv}
    {gasAvail blobAvail : Nat} {w : World} {tx : Transaction} {hint : Option Address}
    {out : TxOutput} (hw : Good crypto weth w)
    (hdeleg : fork < .prague ∨ tx.authorizations = [])
    (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    ∑ a : Address, (out.world.sload weth (balSlot crypto a)).toNat ≤
        (out.world.balance weth).toNat ∧
      ∑ a : Address, (out.world.sload weth (balSlot crypto a)).toNat < 2 ^ 256 := by
  have hg := weth9_solvent_tx hK hw hdeleg h
  have he := owed_eq_sum_addresses (crypto := crypto) (base := 3#256) (bank := weth) out.world
    hinj
  exact ⟨he ▸ hg.backed, he ▸ hg.bounded⟩

end Verified.WETH9
