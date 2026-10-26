import Verified.WETH9.Backed
import QEDefi.ERC20.Spec.Invariant

/-!
# WETH9's ether backs its tokens, under hash hypotheses about finitely many rows

`weth9_solvent` and `weth9_backed` (`Verified.WETH9.Backed`) assume
`Disjoint (allowanceSlots crypto) (balanceSlots crypto 3)` and
`Function.Injective (balSlot crypto)`.
Both are statements about **all** addresses: `allowanceSlots` has `2³²⁰` entries and
`balanceSlots` `2¹⁶⁰`, so for a random 256-bit function about `2³²⁰·2¹⁶⁰/2²⁵⁶ = 2²²⁴` pairs
collide, and `2¹⁶⁰` balance rows contain about `2⁶³` colliding pairs. For Keccak both hypotheses
are almost surely false, and the theorems, while consistent, say nothing about mainnet.

They cannot be replaced by a hypothesis about the inputs of a transaction alone. A collision
`allowance[c][g] = balanceOf[x]` exists for almost every caller `c` (`2¹⁶⁰` choices of `g`
against `2¹⁶⁰` balance rows), and a contract may compute `g` at run time, so whether a
transaction writes a colliding allowance row is a property of its execution. And such a write
does break solvency: `approve(g, v)` would set `balanceOf[x] = v`. The hypotheses here are
therefore about the rows the execution actually uses, finitely many:

* **`AllowOk_rows crypto msg`**: the two allowance rows a message to WETH9 can write,
  `allowance[caller][arg]` (`approve`) and `allowance[arg][caller]` (`transferFrom`'s debit),
  where `arg` is the address in its first calldata word, are not `balanceOf` rows.
* **`FramesOk_rows`** / **`TxFramesOk_rows`**: every non-static WETH9 frame that the message
  call (the transaction) reaches satisfies `AllowOk_rows` (`Reaches`, `TxReaches`). A
  transaction runs finitely many frames.
* for the sum over holders, **`Set.InjOn (balSlot crypto) A`** on the finite set of holders `A`
  summed over.

Why they are plausible for Keccak, modelled as a random function: a fixed allowance row is a
`balanceOf` row with probability at most `2¹⁶⁰/2²⁵⁶ = 2⁻⁹⁶`, so a fixed message fails
`AllowOk_rows` with probability at most `2⁻⁹⁵`, and a transaction with probability below `2⁻⁷⁵`
(it runs fewer than `2²⁰` frames: each starts with a `CALL` costing at least 100 gas, and no
block has had `2²⁶` gas). Building a transaction that violates
it requires exhibiting addresses `c`, `g`, `x` with
`keccak(g ‖ keccak(c ‖ 4)) = keccak(x ‖ 3)`: a collision between two Keccak families, about
`2¹²⁸` hash evaluations by the birthday bound. `A` with `|A| = n` has colliding `balanceOf` rows
with probability at most `n²/2²⁵⁷`.

`owed` (`QEDefi.Solvency.Bank`) sums over the *set* of `balanceOf` slots, so `Solvent` itself
needs no hash hypothesis; only the frame proof does, to know that an allowance write leaves every
balance row. Here: `AllowOk_rows`, implied by the old `hK` (`allowOk_of_disjoint_rows`), and
`weth_frame_rows`, `weth_frame` with `AllowOk_rows` of the frame's message for `hK`.
In `Verified.WETH9.RowsTx`:

* **`weth9_solvent_rows`**: any top-level message call (any fork, EIP-7702 authorizations
  included) keeps WETH9 solvent when the WETH9 frames it reaches satisfy `AllowOk_rows`.
* **`weth9_backed_rows`**: then `Σ_{a ∈ A} balanceOf[a] ≤ address(weth).balance`, and the sum is
  below `2²⁵⁶`, for every finite set of holders `A` whose `balanceOf` rows are distinct.
* **`weth9_solvent_tx_rows`**, **`weth9_backed_tx_rows`**: the same for whole transactions
  (`EvmLean.Tx.process`, EIP-7702 included).
-/

namespace Verified.WETH9
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
open QEDefi.Solvency
  EvmLogic.Program.Reentrancy EvmLogic.Solidity EvmLogic.AbsInt Verified.WETH9.Contracts

/-! ## The rows a frame writes -/

/-- The address in a message's first calldata word (`calldataload(4)`, masked): the spender of
`approve(guy, wad)`, the source of `transferFrom(src, dst, wad)`. -/
abbrev arg0_rows (msg : Message) : Address :=
  Word.toAddress (Bytes.toWord (readBytes msg.data 4 32))

/-- **The allowance rows a WETH9 frame may write are not `balanceOf` rows.** For a message to
WETH9 with first calldata word `arg`: `allowance[caller][arg]` (written by `approve(arg, ·)`)
and `allowance[arg][caller]` (debited by `transferFrom(arg, ·, ·)`) are not `balanceOf[x]` for
any `x`. Each fails for a random 256-bit function with probability at most `2⁻⁹⁶` (`2¹⁶⁰`
balance rows among `2²⁵⁶` words); exhibiting a message that fails it means finding a collision
between `keccak(g ‖ keccak(c ‖ 4))` and `keccak(x ‖ 3)`, about `2¹²⁸` Keccak evaluations. -/
structure AllowOk_rows (crypto : Crypto) (msg : Message) : Prop where
  /-- `allowance[caller][arg]`, the row `approve(arg, wad)` writes. -/
  own : mappingSlot crypto (Word.ofAddress (arg0_rows msg))
      (mappingSlot crypto (Word.ofAddress msg.caller) 4#256) ∉ balanceSlots crypto 3#256
  /-- `allowance[arg][caller]`, the row `transferFrom(arg, dst, wad)` debits. -/
  src : mappingSlot crypto (Word.ofAddress msg.caller)
      (mappingSlot crypto (Word.ofAddress (arg0_rows msg)) 4#256) ∉ balanceSlots crypto 3#256

/-- The global hypothesis of `weth9_solvent` implies `AllowOk_rows` for every message: the new
theorems generalize the old ones. -/
theorem allowOk_of_disjoint_rows {crypto : Crypto}
    (hK : Disjoint (allowanceSlots crypto) (balanceSlots crypto 3#256)) (msg : Message) :
    AllowOk_rows crypto msg :=
  ⟨allowance_not_mem hK _ _, allowance_not_mem hK _ _⟩

/-- A write to an allowance row that is no `balanceOf` row leaves every balance entry. -/
theorem sload_allowance_sstore_rows {crypto : Crypto} {a b : Address}
    (h : mappingSlot crypto (Word.ofAddress b) (mappingSlot crypto (Word.ofAddress a) 4#256) ∉
      balanceSlots crypto 3#256) (w : World) (bank c : Address) (v : Word) :
    (w.sstore bank
      (mappingSlot crypto (Word.ofAddress b) (mappingSlot crypto (Word.ofAddress a) 4#256)) v).sload
      bank (mappingSlot crypto (Word.ofAddress c) 3#256) =
      w.sload bank (mappingSlot crypto (Word.ofAddress c) 3#256) :=
  World.sload_sstore_ne_key _ _ _ fun he => h (he ▸ mem_balanceSlots crypto 3#256 c)

/-! ## Any frame of WETH9 -/

set_option hygiene false in
/-- A `LOG` at which the world is `Good` (by `g`), then the steps to `STOP`. -/
local macro "log_stop " b:num p:num g:term : tactic => `(tactic| (
  refine pwp_safe (b := $b) (p := $p) ‹_› ?_ rfl (by code_fact) (by decide) (by decide) ?_
  · dsimp only; exact $g
  · intro _ _ _ _ _ _
    dsimp only
    apwp_steps
    exact pwp_stop (by code_fact) rfl (by dsimp only; exact $g)))

set_option hygiene false in
/-- A `LOG` at which the world is `Good` (by `g`), then the steps to `RETURN`. -/
local macro "log_return " b:num p:num g:term : tactic => `(tactic| (
  refine pwp_safe (b := $b) (p := $p) ‹_› ?_ rfl (by code_fact) (by decide) (by decide) ?_
  · dsimp only; exact $g
  · intro _ _ _ _ _ _
    dsimp only
    apwp_steps
    exact pwp_return ‹_› (by code_fact) rfl rfl (by dsimp only; exact $g)))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
/-- **Every frame of WETH9 keeps it solvent**, for any gas and any calldata, when the two
allowance rows its message may write are not `balanceOf` rows (`AllowOk_rows`): `weth_frame`
with a hypothesis about this frame's rows for its global `hK`. -/
theorem weth_frame_rows {crypto : Crypto}
    (ctx : Context) (tr : TransientStorage) (ow : World) (created : AddressSet) (msg : Message)
    (jd : Array Bool) (sub : Substate) (snap : World × TransientStorage) (ko ks : Nat)
    (parents : List Frame) (g0 : Nat) (hA : AllowOk_rows crypto msg)
    (hsnap : Good crypto msg.currentTarget snap.1) (hst : msg.isStatic = false)
    (hcaller : msg.caller ≠ msg.currentTarget)
    (hstv : msg.shouldTransferValue = true)
    (haff : msg.value ≠ 0 → msg.value.toNat ≤ (snap.1.balance msg.caller).toNat)
    (hctx : ctx.crypto = crypto) :
    WP (Machine.mk ctx (PrecompileImpl.standard ctx) (transferValue snap.1 msg) tr ow created
      (Frame.mk msg WETH9.runtimeCode jd 0 [] {} g0 .empty sub snap (.call ko ks)) parents)
      (fun _ => False) (FailOk (Good crypto msg.currentTarget)) := by
  subst hctx
  have S := goodOps_solvent (crypto := ctx.crypto) (base := 3#256) (bank := msg.currentTarget)
    size_code deleg_code
  have hT : Good ctx.crypto msg.currentTarget (transferValue snap.1 msg) :=
    S.transfer hsnap fun _ h2 => ⟨haff h2, .inl hcaller⟩
  have hB := backed_transferValue (base := 3#256) size_code hsnap rfl hcaller hstv haff
  have hown := hA.own
  have hsrc := hA.src
  apwp_steps stop_at [0xb9, 0x1a1, 0x266, 0x2e2] [addressMask_and_ofAddress, mask_and_eq,
    Word.toAddress_ofAddress, keccak_mappingSlot, EvmLogic.Solidity.eq_self]
  -- the fallback (no selector matched): `deposit()`
  · log_stop 0xa2 4 (solvent_credit_unchecked hT.code hT.capped hB)
  -- `allowance(a, b)`
  · exact pwp_return ‹_› (by code_fact) rfl rfl hT
  -- `deposit()`
  · log_stop 0xa2 4 (solvent_credit_unchecked hT.code hT.capped hB)
  -- `transfer(dst, wad)`
  · log_return 0xa3 5 (solvent_move hT (le_of_iszero3 (by with_reducible assumption)))
  -- `symbol()`
  · exact view_wp (by simp) rfl rfl rfl hsnap hT
  -- `balanceOf(a)`
  · exact pwp_return ‹_› (by code_fact) rfl rfl hT
  -- `decimals()`
  · exact view_wp (by simp) rfl rfl rfl hsnap hT
  -- `withdraw(wad)`: the send with the stipend, the caller's entry already debited
  · have hbal := le_of_iszero3 ‹(Word.lt _ _).iszero.iszero.iszero ≠ 0›
    obtain ⟨hW1, howed⟩ := solvent_debit hT hbal
    refine pwp_call_stipend ‹_› (by code_fact) rfl rfl ?_ ?_
    · by_cases hw0 : Bytes.toWord (readBytes msg.data 4 32) = 0
      · rw [hw0]; decide
      · have hz : (Bytes.toWord (readBytes msg.data 4 32)).iszero = 0 := iszero_of_ne hw0
        have hn : (Bytes.toWord (readBytes msg.data 4 32)).toNat ≠ 0 := fun h =>
          hw0 (BitVec.eq_of_toNat_eq (by simpa using h))
        rw [hz]; simp [hn, Gas.callStipend]
    · intro m'' x hsf hpc hx hW
      obtain ⟨c'', p'', w'', t'', o'', cr'', ⟨msg'', code'', jd'', pc'', st'', mem'', g'', rd'',
        sub'', snap'', kind''⟩, par''⟩ := m''
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hsf
      dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 hpc hx hW
      subst c'' p'' o'' par'' msg'' code'' jd'' kind'' snap'' pc'' st''
      apwp_steps
      -- the recipient accepted: the debit and the send keep WETH9 solvent
      have hx0 := iszero_eq_zero (iszero_ne_zero ‹Word.iszero (Word.iszero x) ≠ 0›)
      obtain ⟨haff', hworld⟩ := hW.2 hx0
      have hgood : Good ctx.crypto msg.currentTarget w'' := by
        rw [hworld, Word.toAddress_ofAddress]
        split
        · exact hW1
        · refine solvent_send size_code hW1.code hW1.capped hcaller ?_ haff'
          rw [howed, World.balance_sstore]; exact hT.backed
      refine pwp_safe (b := 0xa2) (p := 4) ‹_› hgood rfl (by code_fact) (by decide) (by decide) ?_
      intro _ _ _ _ _ _
      dsimp only
      apwp_steps
      exact pwp_stop (by code_fact) rfl hgood
  -- `transferFrom(src, dst, wad)`, debiting the allowance
  · log_return 0xa3 5 (solvent_move (hT.sstore_other hsrc _)
      (by rw [sload_allowance_sstore_rows hsrc]
          exact le_of_iszero3 (by with_reducible assumption)))
  -- `transferFrom(src, dst, wad)`, unlimited allowance
  · log_return 0xa3 5 (solvent_move hT (le_of_iszero3 (by with_reducible assumption)))
  -- `transferFrom(src, dst, wad)`, debiting the allowance
  · log_return 0xa3 5 (solvent_move (hT.sstore_other hsrc _)
      (by rw [sload_allowance_sstore_rows hsrc]
          exact le_of_iszero3 (by with_reducible assumption)))
  -- `transferFrom(src, dst, wad)` by `src` itself
  · log_return 0xa3 5 (solvent_move hT (le_of_iszero3 (by with_reducible assumption)))
  -- `totalSupply()`
  · exact view_wp (by simp) rfl rfl rfl hsnap hT
  -- `approve(guy, wad)`
  · log_return 0xa3 5 (hT.sstore_other hown _)
  -- `name()`
  · exact view_wp (by simp) rfl rfl rfl hsnap hT
  -- calldata shorter than a selector: `deposit()`
  · log_stop 0xa2 4 (solvent_credit_unchecked hT.code hT.capped hB)

end Verified.WETH9
