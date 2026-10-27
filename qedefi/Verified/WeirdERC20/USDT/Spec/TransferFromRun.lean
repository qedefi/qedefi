import Verified.WeirdERC20.USDT.Spec.TransferRun

/-!
# USDT `transferFrom(src, dst, v)` on the lift: the words and the ends

`TransferFromOut`: every end of the lift of a `transferFrom` frame, in the words the code
computes: the guards (pause, the blacklisted `src`), SafeMath's failures (the fee's `mul`, the
allowance's `sub` unless it is `MAX_UINT`, the fee's and the balance's `sub`, the credits'
`add`), a static frame's `SSTORE`, and otherwise the allowance spent (unless infinite), the
transfer's writes from that world, and the `Transfer` logs.
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Verified.WeirdERC20.USDT.Contracts EvmLogic.Program.Nested EvmLogic.GasMono
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.Math QEDefi.ERC4626

/-- The `allowed[o][sp]` row, as the code hashes it. -/
abbrev allowKey (crypto : Crypto) (o sp : Address) : Word :=
  crypto.keccak256 (Bytes.ofWord (Word.ofAddress sp) ++
    Bytes.ofWord (crypto.keccak256 (Bytes.ofWord (Word.ofAddress o) ++ Bytes.ofWord 5#256)))

/-- The world after the allowance step: spent unless it is `MAX_UINT`. -/
def tfW0 (crypto : Crypto) (w : World) (t src sp : Address) (v : Word) : World :=
  if (w.sload t (allowKey crypto src sp)).toNat < 2 ^ 256 - 1 then
    w.sstore t (allowKey crypto src sp) (w.sload t (allowKey crypto src sp) - v)
  else w

/-- SafeMath fails during `transferFrom(src, dst, v)` by `sp` (fee from `w`, balances from the
world after the allowance step). -/
def tfArithFail (crypto : Crypto) (w : World) (t sp src dst : Address) (v : Word) : Prop :=
  2 ^ 256 ≤ v.toNat * (w.sload t 3#256).toNat ∨
  ((w.sload t (allowKey crypto src sp)).toNat < 2 ^ 256 - 1 ∧
    (w.sload t (allowKey crypto src sp)).toNat < v.toNat) ∨
  v.toNat < (xferFee w t v).toNat ∨
  ((tfW0 crypto w t src sp v).sload t (balKey crypto src)).toNat < v.toNat ∨
  2 ^ 256 ≤ ((xferW1 crypto (tfW0 crypto w t src sp v) t src v).sload t
    (balKey crypto dst)).toNat + (v - xferFee w t v).toNat ∨
  (xferFee w t v ≠ 0#256 ∧
    2 ^ 256 ≤ ((xferW2 crypto (tfW0 crypto w t src sp v) t src dst v (xferFee w t v)).sload t
      (ownerKey crypto (xferW2 crypto (tfW0 crypto w t src sp v) t src dst v
        (xferFee w t v)) t)).toNat + (xferFee w t v).toNat)

/-- What the lift of a `transferFrom(src, dst, v)` frame ends with. -/
def TransferFromOut (src dst : Address) (v : Word) (m mf : Machine) (o : Outcome) : Prop :=
  (m.frame.msg.value ≠ 0 ∧ Fails o) ∨ (m.frame.msg.isStatic = true ∧ Fails o) ∨
  (m.frame.msg.value = 0 ∧
    ((pausedW m.world m.frame.msg.currentTarget ≠ 0#256 ∧ ∃ out, o = .revert out) ∨
     (pausedW m.world m.frame.msg.currentTarget = 0#256 ∧
      blackW m.ctx.crypto m.world m.frame.msg.currentTarget src ≠ 0#256 ∧
      ∃ out, o = .revert out) ∨
     (pausedW m.world m.frame.msg.currentTarget = 0#256 ∧
      blackW m.ctx.crypto m.world m.frame.msg.currentTarget src = 0#256 ∧
      tfArithFail m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller src dst v ∧
      ∃ e, o = .halt e) ∨
     (pausedW m.world m.frame.msg.currentTarget = 0#256 ∧
      blackW m.ctx.crypto m.world m.frame.msg.currentTarget src = 0#256 ∧
      ¬ tfArithFail m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller src dst v ∧
      o = .success .empty ∧
      mf.world = xferW3 m.ctx.crypto
        (tfW0 m.ctx.crypto m.world m.frame.msg.currentTarget src m.frame.msg.caller v)
        m.frame.msg.currentTarget src dst v (xferFee m.world m.frame.msg.currentTarget v) ∧
      mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
      mf.frame.sub.logs = xferLogs m.frame.sub.logs m.frame.msg.currentTarget src dst v
        (xferFee m.world m.frame.msg.currentTarget v)
        (1461501637330902918203684832716283019655932542975#256 &&&
          (1461501637330902918203684832716283019655932542975#256 &&&
            ((xferW3 m.ctx.crypto
              (tfW0 m.ctx.crypto m.world m.frame.msg.currentTarget src m.frame.msg.caller v)
              m.frame.msg.currentTarget src dst v
              (xferFee m.world m.frame.msg.currentTarget v)).sload
                m.frame.msg.currentTarget 0#256).div 1#256)))))

theorem transferFromOut_halt {src dst : Address} {v : Word} {m mf : Machine}
    {e e' : ExceptionalHalt} (h : TransferFromOut src dst v m mf (.halt e)) :
    TransferFromOut src dst v m mf (.halt e') := by
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, ⟨h2, _, h3⟩ | ⟨h2, h3, _, h4⟩ | ⟨h2, h3, h4, -⟩ |
      ⟨h2, h3, h4, h5, -⟩⟩
  · exact .inl ⟨h1, trivial⟩
  · exact .inr (.inl ⟨h1, trivial⟩)
  · cases h3
  · cases h4
  · exact .inr (.inr ⟨h1, .inr (.inr (.inl ⟨h2, h3, h4, _, rfl⟩))⟩)
  · cases h5

end Verified.WeirdERC20.USDT.Spec
