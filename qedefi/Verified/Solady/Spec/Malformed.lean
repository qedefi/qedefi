import Verified.Solady.Spec.Spec
import Verified.Solady.Spec.MalformedCode
import Verified.Common.Malformed.Post

/-!
# `SoladyToken` with any calldata: `MalformedSpec`, up to `permit`

**`solady_malformed r`**: `MalformedSpec` for the compiled `SoladyToken`, with any signature
recovery `r` for `permit`, from **`PermitResidue r`**: the well-formed `permit` frames (clean
`owner` and `spender`, a `v` below 256, no value) end as the model's `permit` with recovery `r`
(or fail, or change nothing). Solady's `permit` has no proof yet (no `PermitSpec`, no recovery
function read off its code), so that residue is exactly the open part; for the right `r` (the
address `ecrecover` returns for Solady's EIP-712 digest) it is what `MalformedSpec` asks of
those frames. Every other frame, with any calldata, value and gas, is proved here:

* short calldata or an unknown selector: `fallback_spec`;
* any value: no function is payable, the frame fails (`value_low`);
* the eight getters change nothing, whatever their arguments (`getter_low`);
* `transfer`, `approve`, `transferFrom`, `mint`, `burn`: with every argument word and clean
  `address` words the calldata is an encoding and `calls_spec`/`ops_spec` apply; otherwise
  solc's decoder rejects it (`short_low`, `dirty0_low`, `dirty1_low`);
* `permit`: short calldata, a dirty `address` or a `v` of 256 or more fails.

**Solady's decoders.** Solady's `ERC20` reads its arguments in assembly, but its functions are
`public`, so solc's ABI decoder runs first in the compiled entry points (with length checks,
`address` and `uint8` validation): malformed calldata reverts before the assembly body, as for
a token written in Solidity. The reduction is the same as for OpenZeppelin's `ERC20Mock`.
-/

namespace Verified.Solady.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.Solady.Contracts Verified.Solady.Spec
open Verified.Common.Malformed
open Verified.Solmate.ERC4626 (CleanAddr)

variable {Act : Finset Address} {m : Machine}

/-- `MalPost` of `SoladyToken`, with the recovery `r`. -/
abbrev Post (r : Machine → ℕ → Address) (Act : Finset Address) (m : Machine) :
    Machine → Outcome → Prop :=
  MalPost soladyAbs M ops opAddrs (some r) Act m

/-- **The `permit` frames left open**: well-formed calldata (clean `owner` and `spender`, a `v`
below 256), no value. -/
def PermitResidue (r : Machine → ℕ → Address) : Prop :=
  ∀ Act m, Start SoladyToken.runtimeCode soladyAbs M Act m → m.frame.msg.value = 0 →
    Abi.selectorOf m.frame.msg.data = 0xd505accf → 228 ≤ m.frame.msg.data.size →
    CleanAddr m.frame.msg.data 0 → CleanAddr m.frame.msg.data 1 →
    CleanU8 m.frame.msg.data →
    Halts m (Post r Act m)

theorem sel_eq : sel = [0x3644e515, 0xdd62ed3e, 0x095ea7b3, 0x70a08231, 0x9dc29fac, 0x313ce567,
    0x40c10f19, 0x06fdde03, 0x7ecebe00, 0xd505accf, 0x95d89b41, 0x18160ddd, 0xa9059cbb,
    0x23b872dd] := rfl

theorem clean_lt {d : ByteArray} {j : Nat} (h : CleanAddr d j) :
    (Verified.Solmate.ERC4626.argWord d j).toNat < 2 ^ 160 := by
  have := congrArg BitVec.toNat h
  simp only [addressMask, BitVec.toNat_and, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by decide : 2 ^ 160 - 1 < 2 ^ 256), Nat.and_two_pow_sub_one_eq_mod] at this
  rw [← this]; exact Nat.mod_lt _ (by decide)

theorem ops_mint {d : ByteArray} {caller : Address} (hsel : Abi.selectorOf d = 0x40c10f19)
    (hs : 68 ≤ d.size) (hc : CleanAddr d 0) :
    ops caller d 0 = some (.mint caller (Word.toAddress (argWord d 0)) (argWord d 1).toNat) := by
  have hlt : (argWord d 0).toNat < 1461501637330902918203684832716283019655932542976 :=
    clean_lt hc
  simp [ops, addrArg, hsel, hlt, show ¬ d.size < 68 by omega]

theorem ops_burn {d : ByteArray} {caller : Address} (hsel : Abi.selectorOf d = 0x9dc29fac)
    (hs : 68 ≤ d.size) (hc : CleanAddr d 0) :
    ops caller d 0 = some (.burn caller (Word.toAddress (argWord d 0)) (argWord d 1).toNat) := by
  have hlt : (argWord d 0).toNat < 1461501637330902918203684832716283019655932542976 :=
    clean_lt hc
  simp [ops, addrArg, hsel, hlt, show ¬ d.size < 68 by omega]

/-- A two-word writing entry point: well formed, or it fails. -/
theorem post_two {r : Machine → ℕ → Address} (hS : Start SoladyToken.runtimeCode soladyAbs M Act m)
    {s : Nat} (hsh : (s, 64) ∈ writeShapes) (hsel : Abi.selectorOf m.frame.msg.data = s)
    (h4 : 4 ≤ m.frame.msg.data.size)
    (hok : 68 ≤ m.frame.msg.data.size → CleanAddr m.frame.msg.data 0 → Halts m (Post r Act m)) :
    Halts m (Post r Act m) := by
  by_cases hs : 68 ≤ m.frame.msg.data.size
  · by_cases hc : CleanAddr m.frame.msg.data 0
    · exact hok hs hc
    · exact post_fails (dirty0_low hsh m hS.fresh hsel hs hS.size hc)
  · exact post_fails (short_low hsh m hS.fresh hsel h4 (by omega))

/-- **`SoladyToken` with any calldata**, given the well-formed `permit` frames
(`PermitResidue r`): every frame fails, changes nothing, or ends as an ERC-20 call (a `permit`
with the recovery `r`) or a `mint`/`burn` of `soladyModel PERMIT2`, for the actors and the
accounts it names. -/
theorem solady_malformed (r : Machine → ℕ → Address) (hres : PermitResidue r) :
    MalformedSpec SoladyToken.runtimeCode soladyAbs M ops opAddrs (some r) := by
  refine malformedSpec_of fun Act m hS => ?_
  by_cases hfb : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ sel
  · exact post_fallback fallback_spec hS hfb
  simp only [not_or, not_lt, not_not] at hfb
  obtain ⟨h4, hmem⟩ := hfb
  by_cases hv : m.frame.msg.value = 0
  swap
  · exact post_fails (value_low m hS.fresh hv)
  have hv0 : m.frame.msg.value.toNat = 0 := by rw [hv]; rfl
  have getter : ∀ {s q : Nat}, (s, q) ∈ getterEntries → Abi.selectorOf m.frame.msg.data = s →
      Halts m (Post r Act m) := fun hge h =>
    (getter_low hge m hS.fresh h h4 hS.size).mono fun _ _ _ h => by
      rcases h with h | h
      · exact .inl h
      · exact .inr (.inl h)
  rw [sel_eq] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  -- DOMAIN_SEPARATOR
  · exact getter (q := 358) (by decide) h
  -- allowance
  · exact getter (q := 550) (by decide) h
  -- approve
  · exact post_two hS (by decide) h h4 fun hs hc =>
      post_call (calls_spec _) hS (encodes_approve h hs hc) trivial
  -- balanceOf
  · exact getter (q := 387) (by decide) h
  -- burn
  · exact post_two hS (by decide) h h4 fun hs hc =>
      post_op ops_spec hS (by rw [hv0]; exact ops_burn h hs hc)
  -- decimals
  · exact getter (q := 343) (by decide) h
  -- mint
  · exact post_two hS (by decide) h h4 fun hs hc =>
      post_op ops_spec hS (by rw [hv0]; exact ops_mint h hs hc)
  -- name
  · exact getter (q := 233) (by decide) h
  -- nonces
  · exact getter (q := 424) (by decide) h
  -- permit
  · by_cases hs : 228 ≤ m.frame.msg.data.size
    · by_cases hc0 : CleanAddr m.frame.msg.data 0
      · by_cases hc1 : CleanAddr m.frame.msg.data 1
        · by_cases hu : CleanU8 m.frame.msg.data
          · exact hres Act m hS hv h hs hc0 hc1 hu
          · exact post_fails (dirtyV_low m hS.fresh h hs hS.size hc0 hc1 hu)
        · exact post_fails (dirty1_low (n := 224) (by decide) m hS.fresh h hs hS.size hc0 hc1)
      · exact post_fails (dirty0_low (n := 224) (by decide) m hS.fresh h hs hS.size hc0)
    · exact post_fails (short_low (n := 224) (by decide) m hS.fresh h h4 (by omega))
  -- symbol
  · exact getter (q := 461) (by decide) h
  -- totalSupply
  · exact getter (q := 298) (by decide) h
  -- transfer
  · exact post_two hS (by decide) h h4 fun hs hc =>
      post_call (calls_spec _) hS (encodes_transfer h hs hc) trivial
  -- transferFrom
  · by_cases hs : 100 ≤ m.frame.msg.data.size
    · by_cases hc0 : CleanAddr m.frame.msg.data 0
      · by_cases hc1 : CleanAddr m.frame.msg.data 1
        · exact post_call (calls_spec _) hS (encodes_transferFrom h hs hc0 hc1) trivial
        · exact post_fails (dirty1_low (n := 96) (by decide) m hS.fresh h hs hS.size hc0 hc1)
      · exact post_fails (dirty0_low (n := 96) (by decide) m hS.fresh h hs hS.size hc0)
    · exact post_fails (short_low (n := 96) (by decide) m hS.fresh h h4 (by omega))

end Verified.Solady.Spec.Malformed
