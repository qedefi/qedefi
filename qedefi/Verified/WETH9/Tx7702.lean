import Verified.WETH9.Tx
import Verified.WETH9.Backed7702

/-!
# WETH9's ether backs its tokens after any transaction, EIP-7702 included

`weth9_solvent_tx` and `weth9_backed_tx` (`Verified.WETH9.Tx`) cover the whole transaction but
assume it is before Prague or carries no EIP-7702 authorization. Authorizations only rewrite the
code and nonce of accounts holding empty code or a delegation designator, never WETH9's, and keep
every balance (`EvmLogic.Program.Delegation`), so the message call keeps WETH9 solvent
(`weth9_solvent_7702`) and creates no ether (`processMessageCall_supply_le_7702`) for every
transaction. The remaining hypotheses are those of `weth9_backed_tx`.
-/

namespace Verified.WETH9
open EvmLean EvmLean.Interpreter EvmLean.Tx EvmLogic EvmLogic.Program EvmLogic.Program.Nested
  EvmLogic.Tx QEDefi.Solvency

/-- **WETH9 stays solvent after any transaction**, EIP-7702 authorizations included: from a
world in which it is solvent, every successful transaction (any type, sender, recipient, value,
calldata, gas limit, fees and authorizations; any fork, block and coinbase; hashing with
`crypto`) ends in a world in which it is solvent — provided no `allowance` entry shares its slot
with a `balanceOf` entry. `weth9_solvent_tx` without its fork/authorization hypothesis. -/
theorem weth9_solvent_tx_7702 {crypto : Crypto} {weth : Address}
    (hK : Disjoint (allowanceSlots crypto) (balanceSlots crypto 3#256)) {fuel : Nat}
    {fork : Fork} {env : BlockEnv} {gasAvail blobAvail : Nat} {w : World} {tx : Transaction}
    {hint : Option Address} {out : TxOutput} (hw : Good crypto weth w)
    (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    Good crypto weth out.world :=
  (process_keeps_ether_7702 (P := (· = weth)) (Inv := Good crypto weth)
    (fun _ hw _ hp => hp ▸ realCode_good hw) (fun _ hw => hw.capped)
    (fun _ _ _ _ h1 hm hr => weth9_solvent_7702 hK h1 hm.ctxCrypto hm.top hm.transfers hr)
    (fun _ _ hw hk hs => good_of_frame hw (hk weth rfl).1 (hk weth rfl).2 hs) hw h).1

/-- **WETH9's ether backs its tokens, after any transaction**, EIP-7702 authorizations included:
when the slots of `balanceOf[a]` do not collide, after every successful transaction from a world
in which WETH9 is solvent, `Σₐ balanceOf[a] ≤ address(weth).balance` and the sum is below
`2²⁵⁶`, over all addresses. `weth9_backed_tx` without its fork/authorization hypothesis. -/
theorem weth9_backed_tx_7702 {crypto : Crypto} {weth : Address}
    (hK : Disjoint (allowanceSlots crypto) (balanceSlots crypto 3#256))
    (hinj : Function.Injective (balSlot crypto)) {fuel : Nat} {fork : Fork} {env : BlockEnv}
    {gasAvail blobAvail : Nat} {w : World} {tx : Transaction} {hint : Option Address}
    {out : TxOutput} (hw : Good crypto weth w)
    (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    ∑ a : Address, (out.world.sload weth (balSlot crypto a)).toNat ≤
        (out.world.balance weth).toNat ∧
      ∑ a : Address, (out.world.sload weth (balSlot crypto a)).toNat < 2 ^ 256 := by
  have hg := weth9_solvent_tx_7702 hK hw h
  have he := owed_eq_sum_addresses (crypto := crypto) (base := 3#256) (bank := weth) out.world
    hinj
  exact ⟨he ▸ hg.backed, he ▸ hg.bounded⟩

end Verified.WETH9
