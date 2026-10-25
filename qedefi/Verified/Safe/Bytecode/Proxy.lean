import Verified.Safe.Bytecode.Defs

/-!
# The `SafeProxy` frame

Every frame of the `SafeProxy` at `sf` (its own code), for a sender other than the Safe, ends
safely: it writes nothing and its only request is the `DELEGATECALL` of the singleton's code
(slot `0` holds `sg`, whose code is the singleton's), for the same sender (`proxy_frame`).
-/

namespace Verified.Safe.Guard

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested
open Verified.Safe.Contracts

namespace Dep

variable (D : Dep)

/-- A `SafeProxy` frame: every own path ends it, writing nothing, issuing only the
`DELEGATECALL` of the singleton. -/
abbrev Jproxy (crypto : Crypto) (chainId : Nat) (O T : Finset Address) (thr : Nat) (h₀ : Word)
    (fork : Fork) : Machine → Prop :=
  OwnG True (fun _ => True) (D.Rsf crypto chainId O T thr h₀ fork) (Own.SstoreOk fun _ => False)
    D.Csf (fun _ => False) (fun _ => False)

theorem proxy_frame {crypto : Crypto} {chainId : Nat} {O T : Finset Address} {thr : Nat}
    {h₀ : Word} {msg : Message} {ctx : Context} {w : World} {m : Machine}
    (htgt : msg.currentTarget = D.sf) (hcl : msg.caller ≠ D.sf)
    (hF : Fr ⟨msg, ctx, PrecompileImpl.standard ctx, SafeProxy.runtimeCode⟩ m 0 [] {} w) :
    D.Jproxy crypto chainId O T thr h₀ ctx.fork m := by
  own_explore
  case call50 =>
    rintro ⟨hG, -, hrc, -⟩ - req ⟨hcode, ht, hc, -⟩
    have hw : m.world = w := hF.world
    have hmsg : m.frame.msg = msg := hF.msg
    have hs : Word.toAddress (w.sload msg.currentTarget 0#256) = D.sg := by
      rw [← hw, htgt, show (0#256 : Word) = 0 from rfl, hG.2.2.singleton]; simp
    have hsg : m.world.code D.sg = SafeSingleton.runtimeCode := by
      rw [hrc _ (.inr (.inr (.inr (.inr rfl)))), D.code_sg]
    refine .inr (.inl ⟨rfl, .inr (.inr ⟨?_, ?_, ?_⟩)⟩)
    · rw [ht, hmsg, htgt]
    · rw [(hcode (.inr (by rw [hs, hsg]; exact deleg_sg))).1, hs, hsg]
    · rw [hc, hmsg]; exact hcl
  case doom50 => exact fun h => h.elim

end Dep

end Verified.Safe.Guard
