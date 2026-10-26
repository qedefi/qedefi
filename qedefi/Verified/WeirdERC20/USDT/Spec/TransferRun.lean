import Verified.WeirdERC20.USDT.Spec.ViewOut
import Verified.WeirdERC20.USDT.Spec.Decide

/-!
# USDT `transfer(dst, v)` on the lift

`transfer_high`: every end of the lift of a `transfer` frame (`TransferOut`), with the words
the code computes: with value it reverts; paused, or the caller blacklisted, it reverts; then
SafeMath fails with `INVALID` when `v · basisPointsRate` overflows, the fee exceeds `v`, the
caller's balance is short, or a credit overflows; in a static frame the first `SSTORE` fails;
otherwise it debits the caller, credits `dst` with `v - fee`, credits the owner with the fee
when it is nonzero, logs the `Transfer`s and stops.
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Verified.WeirdERC20.USDT.Contracts EvmLogic.Program.Nested EvmLogic.GasMono
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.Math QEDefi.ERC4626

/-! ## The words the code computes -/

/-- The `balances` row of `a`, as the code hashes it. -/
abbrev balKey (crypto : Crypto) (a : Address) : Word :=
  crypto.keccak256 (Bytes.ofWord (Word.ofAddress a) ++ Bytes.ofWord 2#256)

/-- The `isBlackListed` row of `a`, as the code hashes it. -/
abbrev blackKey (crypto : Crypto) (a : Address) : Word :=
  crypto.keccak256 (Bytes.ofWord (Word.ofAddress a) ++ Bytes.ofWord 6#256)

/-- `paused` as the code reads it. -/
abbrev pausedW (w : World) (t : Address) : Word :=
  255#256 &&& (w.sload t 0#256).div 1461501637330902918203684832716283019655932542976#256

/-- `isBlackListed[a]` as the code reads it. -/
abbrev blackW (crypto : Crypto) (w : World) (t a : Address) : Word :=
  255#256 &&& (w.sload t (blackKey crypto a)).div 1#256

/-- `v.mul(basisPointsRate).div(10000)`. -/
abbrev fee0W (w : World) (t : Address) (v : Word) : Word :=
  (v * w.sload t 3#256).div 10000#256

/-- The fee: capped at `maximumFee`. -/
def xferFee (w : World) (t : Address) (v : Word) : Word :=
  if (w.sload t 4#256).toNat < (fee0W w t v).toNat then w.sload t 4#256 else fee0W w t v

theorem xferFee_zero (w : World) (t : Address) : xferFee w t 0#256 = 0#256 := by
  unfold xferFee
  have : fee0W w t 0#256 = 0#256 := by
    apply BitVec.eq_of_toNat_eq; simp [Word.div]
  rw [this]
  simp

/-- The owner's `balances` row, as the code hashes the owner it reads from `w`. -/
abbrev ownerKey (crypto : Crypto) (w : World) (t : Address) : Word :=
  crypto.keccak256 (Bytes.ofWord (1461501637330902918203684832716283019655932542975#256 &&&
    (1461501637330902918203684832716283019655932542975#256 &&&
      (1461501637330902918203684832716283019655932542975#256 &&&
        (w.sload t 0#256).div 1#256))) ++ Bytes.ofWord 2#256)

/-- After the debit of `src`. -/
abbrev xferW1 (crypto : Crypto) (w : World) (t src : Address) (v : Word) : World :=
  w.sstore t (balKey crypto src) (w.sload t (balKey crypto src) - v)

/-- After the credit of `dst`. -/
abbrev xferW2 (crypto : Crypto) (w : World) (t src dst : Address) (v fee : Word) : World :=
  (xferW1 crypto w t src v).sstore t (balKey crypto dst)
    ((xferW1 crypto w t src v).sload t (balKey crypto dst) + (v - fee))

/-- After the fee's credit of the owner (when nonzero). -/
def xferW3 (crypto : Crypto) (w : World) (t src dst : Address) (v fee : Word) : World :=
  if fee = 0#256 then xferW2 crypto w t src dst v fee
  else (xferW2 crypto w t src dst v fee).sstore t
    (ownerKey crypto (xferW2 crypto w t src dst v fee) t)
    ((xferW2 crypto w t src dst v fee).sload t
      (ownerKey crypto (xferW2 crypto w t src dst v fee) t) + fee)


/-! ## The ends of the lift -/

/-- SafeMath fails during the transfer of `v` from `src` to `dst` (with the fee `xferFee`):
`v · bps` overflows, the fee exceeds `v`, the balance of `src` is short, the credit of `dst`
overflows, or the owner's credit with a nonzero fee overflows. -/
def xferArithFail (crypto : Crypto) (w : World) (t src dst : Address) (v : Word) : Prop :=
  2 ^ 256 ≤ v.toNat * (w.sload t 3#256).toNat ∨
  v.toNat < (xferFee w t v).toNat ∨
  (w.sload t (balKey crypto src)).toNat < v.toNat ∨
  2 ^ 256 ≤ ((xferW1 crypto w t src v).sload t (balKey crypto dst)).toNat +
    (v - xferFee w t v).toNat ∨
  (xferFee w t v ≠ 0#256 ∧
    2 ^ 256 ≤ ((xferW2 crypto w t src dst v (xferFee w t v)).sload t
      (ownerKey crypto (xferW2 crypto w t src dst v (xferFee w t v)) t)).toNat +
      (xferFee w t v).toNat)

/-- The logs of a successful transfer: the fee's `Transfer` to the owner (when nonzero, with the
owner word `ow` the code reads), then the rest's `Transfer` to `dst`. -/
def xferLogs (logs : Array Log) (t src dst : Address) (v fee ow : Word) : Array Log :=
  if fee = 0#256 then logs.push (transferLog t src dst (v - fee))
  else (logs.push (eventLog t [transferTopic, Word.ofAddress src, ow] [fee])).push
    (transferLog t src dst (v - fee))

/-- What the lift of a `transfer(dst, v)` frame ends with. -/
def TransferOut (dst : Address) (v : Word) (m mf : Machine) (o : Outcome) : Prop :=
  (m.frame.msg.value ≠ 0 ∧ Fails o) ∨ (m.frame.msg.isStatic = true ∧ Fails o) ∨
  (m.frame.msg.value = 0 ∧
    ((pausedW m.world m.frame.msg.currentTarget ≠ 0#256 ∧ ∃ out, o = .revert out) ∨
     (pausedW m.world m.frame.msg.currentTarget = 0#256 ∧
      blackW m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller ≠ 0#256 ∧
      ∃ out, o = .revert out) ∨
     (pausedW m.world m.frame.msg.currentTarget = 0#256 ∧
      blackW m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller = 0#256 ∧
      xferArithFail m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller dst v ∧
      ∃ e, o = .halt e) ∨
     (pausedW m.world m.frame.msg.currentTarget = 0#256 ∧
      blackW m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller = 0#256 ∧
      ¬ xferArithFail m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller dst v ∧
      o = .success .empty ∧
      mf.world = xferW3 m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller dst v
        (xferFee m.world m.frame.msg.currentTarget v) ∧
      mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
      mf.frame.sub.logs = xferLogs m.frame.sub.logs m.frame.msg.currentTarget
        m.frame.msg.caller dst v (xferFee m.world m.frame.msg.currentTarget v)
        (1461501637330902918203684832716283019655932542975#256 &&&
          (1461501637330902918203684832716283019655932542975#256 &&&
            ((xferW3 m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller dst v
              (xferFee m.world m.frame.msg.currentTarget v)).sload
                m.frame.msg.currentTarget 0#256).div 1#256)))))

theorem transferOut_halt {dst : Address} {v : Word} {m mf : Machine} {e e' : ExceptionalHalt}
    (h : TransferOut dst v m mf (.halt e)) : TransferOut dst v m mf (.halt e') := by
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, ⟨h2, _, h3⟩ | ⟨h2, h3, _, h4⟩ | ⟨h2, h3, h4, -⟩ |
      ⟨h2, h3, h4, h5, -⟩⟩
  · exact .inl ⟨h1, trivial⟩
  · exact .inr (.inl ⟨h1, trivial⟩)
  · cases h3
  · cases h4
  · exact .inr (.inr ⟨h1, .inr (.inr (.inl ⟨h2, h3, h4, _, rfl⟩))⟩)
  · cases h5

/-- Run to the next halting instruction or undecided branch (the transfer's simp set). -/
macro "xrun" : tactic => `(tactic| usdt_run [ofAddress_and_addressMask, addressMask_and_ofAddress,
  expCost_20, expCost_0, Memory.read_64])

/-- `xrun` with extra simp lemmas. -/
macro "xrun" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| usdt_run
  [ofAddress_and_addressMask, addressMask_and_ofAddress, expCost_20, expCost_0, Memory.read_64,
    $ls,*])

end Verified.WeirdERC20.USDT.Spec
