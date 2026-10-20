import EvmLogic.Tactic.WpStep
import EvmLogic.Program.Summary
import Examples.Solmate.Contracts.SolmateVault

/-!
# Scale check: a function of the real Solmate vault

`totalSupply()` of `EvmLean.Contracts.SolmateVault.runtimeCode` (5248 bytes), dispatcher and
body, by `wp_steps` alone: code bytes, `PUSH` immediates and jump destinations come from
kernel-checked facts (`EvmLeanProofs.Program.Code`, `jdCheck`), so the elaborator never
evaluates the large code. Elaboration takes a few seconds.
-/

namespace EvmLean.Program.Examples.VaultTotalSupply

open Interpreter Contracts

/-- Postcondition of `totalSupply()`: returns storage slot 2 of the executing account, world
unchanged. -/
def totalSupplyPost (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord (m.world.sload m.frame.msg.currentTarget 2)) ∧ mf.world = m.world

set_option maxHeartbeats 0 in
/-- **`totalSupply()` of the compiled Solmate vault** (5248 bytes of real solc output),
proved by symbolic execution of dispatcher and body, for any frame (top level or callee). -/
theorem totalSupply_halts (m : Machine) (hf : Fresh SolmateVault.runtimeCode m) (hval : m.frame.msg.value = 0)
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 256)
    (hsel : selectorOf m.frame.msg.data = 0x18160ddd#256) (hg : 5000 ≤ m.frame.gasLeft) :
    Halts m (totalSupplyPost m) := by
  apply WP.halts_of_false
  obtain ⟨hc, hj, hpc, hs, hmem, -, -⟩ := hf.frame
  clear hf
  simp only [selectorOf] at hsel
  have hlt : Word.lt (ofNat m.frame.msg.data.size) (BitVec.ofNat 256 4) = 0 := by
    rw [Word.lt_eq_zero_iff]; simp only [ofNat, BitVec.toNat_ofNat]; omega
  wp_intro m
  wp_steps [hval, hsel, hlt]
  exact ⟨rfl, rfl⟩

end EvmLean.Program.Examples.VaultTotalSupply
