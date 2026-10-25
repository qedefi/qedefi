import Verified.Solmate.ERC4626.Nested.Invariants

/-!
# Coverage: which frames are covered

`covered_of_funded`: every funded vault/asset frame is `Covered`, whatever its calldata, under
`CoverOk`, by case analysis over the 30 vault and 14 asset selectors (`vaultSelectors`,
`assetSelectors`, the ABI's). Hence `txOk_of`. See `docs/erc4626/details.md` §4.
-/

namespace Verified.Solmate.ERC4626.Nested
open Verified.Solmate.ERC20 QEDefi.ERC4626 QEDefi.Trace
open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts
open QEDefi.Math QEDefi.ERC20 QEDefi.ERC4626.Solmate QEDefi.Trace.Lift
open Verified.Solmate.ERC4626.Invariants Verified.Solmate.ERC20.Permit
open Verified.Solmate.ERC4626.Permit
open EvmLogic.Program.Nested (Keep KeepP GoodOk DangerStart Danger TopOk Reaches bottom)

variable {crypto : Crypto} {vault asset : Address} {Act : List Address} {K : VCall → Prop}
  {minGas : Nat}

/-! ## Decoding calldata -/

theorem ofAddress_toAddress_of_clean {d : ByteArray} {j : Nat} (h : CleanAddr d j) :
    Word.ofAddress (Word.toAddress (argWord d j)) = argWord d j := by
  have h' := congrArg BitVec.toNat h
  simp only [addressMask, BitVec.toNat_and, BitVec.toNat_ofNat] at h'
  rw [Nat.mod_eq_of_lt (by decide : 2 ^ 160 - 1 < 2 ^ 256), Nat.and_two_pow_sub_one_eq_mod] at h'
  apply BitVec.eq_of_toNat_eq
  simp only [Word.ofAddress, Word.toAddress, BitVec.toNat_setWidth]
  rw [h', Nat.mod_eq_of_lt (argWord d j).isLt]

theorem wellFormed_of {d : ByteArray} {k : Nat} {addrs : List Nat} (h : ¬ Malformed d k addrs) :
    4 + 32 * k ≤ d.size ∧ ∀ j ∈ addrs, CleanAddr d j := by
  have hs : 4 + 32 * k ≤ d.size := by
    by_contra hlt; exact h (.inl (by omega))
  refine ⟨hs, ?_⟩
  by_contra hne
  push Not at hne
  classical
  have hex : ∃ j, j ∈ addrs ∧ ¬ CleanAddr d j := hne
  refine h (.inr ⟨hs, Nat.find hex, (Nat.find_spec hex).1, fun j' hj' hlt => ?_,
    (Nat.find_spec hex).2⟩)
  by_contra hc
  exact Nat.find_min hex hlt ⟨hj', hc⟩

theorem wordCall_of {d : ByteArray} {s : Nat} (h : Abi.selectorOf d = s) (hs : 36 ≤ d.size) :
    WordCall d s (argWord d 0) := ⟨h, hs, rfl⟩

theorem addrCall_of {d : ByteArray} {s : Nat} (h : Abi.selectorOf d = s) (hs : 36 ≤ d.size)
    (hc : CleanAddr d 0) : AddrCall d s (Word.toAddress (argWord d 0)) :=
  ⟨h, hs, (ofAddress_toAddress_of_clean hc).symm⟩

theorem twoWordCall_of {d : ByteArray} {s : Nat} (h : Abi.selectorOf d = s) (hs : 68 ≤ d.size) :
    TwoWordCall d s (argWord d 0) (argWord d 1) := ⟨h, hs, rfl, rfl⟩

theorem threeWordCall_of {d : ByteArray} {s : Nat} (h : Abi.selectorOf d = s)
    (hs : 100 ≤ d.size) : ThreeWordCall d s (argWord d 0) (argWord d 1) (argWord d 2) :=
  ⟨h, hs, rfl, rfl, rfl⟩

theorem permitCall_of {d : ByteArray} (h : Abi.selectorOf d = 0xd505accf) (hs : 228 ≤ d.size)
    (hc0 : CleanAddr d 0) (hc1 : CleanAddr d 1) :
    PermitCall d (Word.toAddress (argWord d 0)) (Word.toAddress (argWord d 1)) (argWord d 2)
      (argWord d 3) (argWord d 4) (argWord d 5) (argWord d 6) :=
  ⟨h, hs, (ofAddress_toAddress_of_clean hc0).symm, (ofAddress_toAddress_of_clean hc1).symm, rfl,
    rfl, rfl, rfl, rfl⟩

theorem permitData_vault {m : Machine} (ht : m.frame.msg.currentTarget = vault)
    {o sp : Address} {v dl v' r s : Word} (hp : PermitCall m.frame.msg.data o sp v dl v' r s) :
    PermitData vault asset m (.approve o sp v) := by
  unfold PermitData; exact ⟨ht, dl, v', r, s, hp⟩

theorem permitData_asset {m : Machine} (ht : m.frame.msg.currentTarget = asset)
    {o sp : Address} {v dl v' r s : Word} (hp : PermitCall m.frame.msg.data o sp v dl v' r s) :
    PermitData vault asset m (.assetApprove o sp v) := by
  unfold PermitData; exact ⟨ht, dl, v', r, s, hp⟩

/-! ## Every selector -/

/-- The conditions beyond `FundedCall` under which a frame is covered: enough gas for the
stored `name`/`symbol` string, `DOMAIN_SEPARATOR()` in a covered case, `permit` with its frame
conditions. -/
structure CoverOk (m : Machine) : Prop where
  name : Abi.selectorOf m.frame.msg.data = 0x06fdde03 →
    Str.getterGas (Str.slotLen (m.world.sload m.frame.msg.currentTarget 0#256)) ≤
      m.frame.gasLeft
  symbol : Abi.selectorOf m.frame.msg.data = 0x95d89b41 →
    Str.getterGas (Str.slotLen (m.world.sload m.frame.msg.currentTarget 1#256)) ≤
      m.frame.gasLeft
  domain : Abi.selectorOf m.frame.msg.data = 0x3644e515 → DomainOk m
  permit : Abi.selectorOf m.frame.msg.data = 0xd505accf → PermitFrame m

theorem vault_known_covered {m : Machine} (ht : m.frame.msg.currentTarget = vault)
    (h4 : 4 ≤ m.frame.msg.data.size) (hmal : ¬ MalformedData vault asset m) (hc : CoverOk m)
    (hs : Abi.selectorOf m.frame.msg.data ∈ vaultSelectors) :
    (∃ c, Executes vault asset m c) ∨ ViewData vault asset m ∨
      ((∃ c, PermitData vault asset m c) ∧ PermitFrame m) := by
  have hw : ∀ {k addrs}, (Abi.selectorOf m.frame.msg.data, k, addrs) ∈ vaultArgShapes →
      4 + 32 * k ≤ m.frame.msg.data.size ∧ ∀ j ∈ addrs, CleanAddr m.frame.msg.data j :=
    fun hmem => wellFormed_of fun hm => hmal ⟨h4, _, _, .inl ⟨ht, hmem⟩, hm⟩
  simp only [vaultSelectors, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      | h | h | h | h | h | h | h | h | h
  · -- 0x01e1d114
    refine .inr (.inl (.inl ⟨ht, ?_⟩))
    iterate 10 right
    left
    exact ⟨h, h4⟩
  · -- 0x06fdde03
    exact .inr (.inl (.inr (.inr ⟨.inl ht, .inl ⟨⟨h, h4⟩, hc.name h⟩⟩)))
  · -- 0x07a2d13a
    obtain ⟨hsz, -⟩ := hw (k := 1) (addrs := []) (by rw [h]; decide)
    refine .inr (.inl (.inl ⟨ht, ?_⟩))
    right
    left
    exact ⟨_, wordCall_of h (by omega)⟩
  · -- 0x095ea7b3
    obtain ⟨hsz, hcl⟩ := hw (k := 2) (addrs := [0]) (by rw [h]; decide)
    have hd := twoWordCall_of h (by omega)
    rw [← ofAddress_toAddress_of_clean (hcl 0 (by simp))] at hd
    exact .inl ⟨.approve _ _ _, rfl, by rw [ht]; rfl, hd⟩
  · -- 0x0a28a477
    obtain ⟨hsz, -⟩ := hw (k := 1) (addrs := []) (by rw [h]; decide)
    refine .inr (.inl (.inl ⟨ht, ?_⟩))
    iterate 4 right
    left
    exact ⟨_, wordCall_of h (by omega)⟩
  · -- 0x18160ddd
    refine .inr (.inl (.inl ⟨ht, ?_⟩))
    iterate 12 right
    left
    exact ⟨h, h4⟩
  · -- 0x23b872dd
    obtain ⟨hsz, hcl⟩ := hw (k := 3) (addrs := [0, 1]) (by rw [h]; decide)
    have hd := threeWordCall_of h (by omega)
    rw [← ofAddress_toAddress_of_clean (hcl 0 (by simp))] at hd
    rw [← ofAddress_toAddress_of_clean (hcl 1 (by simp))] at hd
    exact .inl ⟨.transferFrom _ _ _ _, rfl, by rw [ht]; rfl, hd⟩
  · -- 0x313ce567
    refine .inr (.inl (.inl ⟨ht, ?_⟩))
    iterate 15 right
    left
    exact ⟨h, h4⟩
  · -- 0x3644e515
    exact .inr (.inl (.inr (.inr ⟨.inl ht, .inr (.inr ⟨⟨h, h4⟩, hc.domain h⟩)⟩)))
  · -- 0x38d52e0f
    refine .inr (.inl (.inl ⟨ht, ?_⟩))
    iterate 11 right
    left
    exact ⟨h, h4⟩
  · -- 0x402d267d
    obtain ⟨hsz, hcl⟩ := hw (k := 1) (addrs := [0]) (by rw [h]; decide)
    refine .inr (.inl (.inl ⟨ht, ?_⟩))
    iterate 6 right
    left
    exact ⟨_, addrCall_of h (by omega) (hcl 0 (by simp))⟩
  · -- 0x4cdad506
    obtain ⟨hsz, -⟩ := hw (k := 1) (addrs := []) (by rw [h]; decide)
    refine .inr (.inl (.inl ⟨ht, ?_⟩))
    iterate 5 right
    left
    exact ⟨_, wordCall_of h (by omega)⟩
  · -- 0x6e553f65
    obtain ⟨hsz, hcl⟩ := hw (k := 2) (addrs := [1]) (by rw [h]; decide)
    have hd := twoWordCall_of h (by omega)
    rw [← ofAddress_toAddress_of_clean (hcl 1 (by simp))] at hd
    exact .inl ⟨.deposit _ _ _, rfl, by rw [ht]; rfl, hd⟩
  · -- 0x70a08231
    obtain ⟨hsz, hcl⟩ := hw (k := 1) (addrs := [0]) (by rw [h]; decide)
    refine .inr (.inl (.inl ⟨ht, ?_⟩))
    iterate 13 right
    left
    exact ⟨_, addrCall_of h (by omega) (hcl 0 (by simp))⟩
  · -- 0x7ecebe00
    obtain ⟨hsz, hcl⟩ := hw (k := 1) (addrs := [0]) (by rw [h]; decide)
    refine .inr (.inl (.inl ⟨ht, ?_⟩))
    iterate 18 right
    exact ⟨_, addrCall_of h (by omega) (hcl 0 (by simp))⟩
  · -- 0x94bf804d
    obtain ⟨hsz, hcl⟩ := hw (k := 2) (addrs := [1]) (by rw [h]; decide)
    have hd := twoWordCall_of h (by omega)
    rw [← ofAddress_toAddress_of_clean (hcl 1 (by simp))] at hd
    exact .inl ⟨.mint _ _ _, rfl, by rw [ht]; rfl, hd⟩
  · -- 0x95d89b41
    exact .inr (.inl (.inr (.inr ⟨.inl ht, .inr (.inl ⟨⟨h, h4⟩, hc.symbol h⟩)⟩)))
  · -- 0xa9059cbb
    obtain ⟨hsz, hcl⟩ := hw (k := 2) (addrs := [0]) (by rw [h]; decide)
    have hd := twoWordCall_of h (by omega)
    rw [← ofAddress_toAddress_of_clean (hcl 0 (by simp))] at hd
    exact .inl ⟨.transfer _ _ _, rfl, by rw [ht]; rfl, hd⟩
  · -- 0xb3d7f6b9
    obtain ⟨hsz, -⟩ := hw (k := 1) (addrs := []) (by rw [h]; decide)
    refine .inr (.inl (.inl ⟨ht, ?_⟩))
    iterate 3 right
    left
    exact ⟨_, wordCall_of h (by omega)⟩
  · -- 0xb460af94
    obtain ⟨hsz, hcl⟩ := hw (k := 3) (addrs := [1, 2]) (by rw [h]; decide)
    have hd := threeWordCall_of h (by omega)
    rw [← ofAddress_toAddress_of_clean (hcl 1 (by simp))] at hd
    rw [← ofAddress_toAddress_of_clean (hcl 2 (by simp))] at hd
    exact .inl ⟨.withdraw _ _ _ _, rfl, by rw [ht]; rfl, hd⟩
  · -- 0xba087652
    obtain ⟨hsz, hcl⟩ := hw (k := 3) (addrs := [1, 2]) (by rw [h]; decide)
    have hd := threeWordCall_of h (by omega)
    rw [← ofAddress_toAddress_of_clean (hcl 1 (by simp))] at hd
    rw [← ofAddress_toAddress_of_clean (hcl 2 (by simp))] at hd
    exact .inl ⟨.redeem _ _ _ _, rfl, by rw [ht]; rfl, hd⟩
  · -- 0xbc368a8a
    refine .inr (.inl (.inl ⟨ht, ?_⟩))
    iterate 16 right
    left
    exact ⟨h, h4⟩
  · -- 0xc63d75b6
    obtain ⟨hsz, hcl⟩ := hw (k := 1) (addrs := [0]) (by rw [h]; decide)
    refine .inr (.inl (.inl ⟨ht, ?_⟩))
    iterate 7 right
    left
    exact ⟨_, addrCall_of h (by omega) (hcl 0 (by simp))⟩
  · -- 0xc6e6f592
    obtain ⟨hsz, -⟩ := hw (k := 1) (addrs := []) (by rw [h]; decide)
    refine .inr (.inl (.inl ⟨ht, ?_⟩))
    left
    exact ⟨_, wordCall_of h (by omega)⟩
  · -- 0xce96cb77
    obtain ⟨hsz, hcl⟩ := hw (k := 1) (addrs := [0]) (by rw [h]; decide)
    refine .inr (.inl (.inl ⟨ht, ?_⟩))
    iterate 8 right
    left
    exact ⟨_, addrCall_of h (by omega) (hcl 0 (by simp))⟩
  · -- 0xd505accf
    obtain ⟨hsz, hcl⟩ := hw (k := 7) (addrs := [0, 1]) (by rw [h]; decide)
    exact .inr (.inr ⟨⟨_, permitData_vault ht (permitCall_of h (by omega) (hcl 0 (by simp))
      (hcl 1 (by simp)))⟩, hc.permit h⟩)
  · -- 0xd905777e
    obtain ⟨hsz, hcl⟩ := hw (k := 1) (addrs := [0]) (by rw [h]; decide)
    refine .inr (.inl (.inl ⟨ht, ?_⟩))
    iterate 9 right
    left
    exact ⟨_, addrCall_of h (by omega) (hcl 0 (by simp))⟩
  · -- 0xdd62ed3e
    obtain ⟨hsz, hcl⟩ := hw (k := 2) (addrs := [0, 1]) (by rw [h]; decide)
    have hd := twoWordCall_of h (by omega)
    rw [← ofAddress_toAddress_of_clean (hcl 0 (by simp)),
      ← ofAddress_toAddress_of_clean (hcl 1 (by simp))] at hd
    refine .inr (.inl (.inl ⟨ht, ?_⟩))
    iterate 14 right
    left
    exact ⟨_, _, hd⟩
  · -- 0xef8b30f7
    obtain ⟨hsz, -⟩ := hw (k := 1) (addrs := []) (by rw [h]; decide)
    refine .inr (.inl (.inl ⟨ht, ?_⟩))
    iterate 2 right
    left
    exact ⟨_, wordCall_of h (by omega)⟩
  · -- 0xfc407ae7
    refine .inr (.inl (.inl ⟨ht, ?_⟩))
    iterate 17 right
    left
    exact ⟨h, h4⟩

theorem asset_known_covered {m : Machine} (ht : m.frame.msg.currentTarget = asset)
    (h4 : 4 ≤ m.frame.msg.data.size) (hmal : ¬ MalformedData vault asset m) (hc : CoverOk m)
    (hs : Abi.selectorOf m.frame.msg.data ∈ assetSelectors) :
    (∃ c, Executes vault asset m c) ∨ ViewData vault asset m ∨
      ((∃ c, PermitData vault asset m c) ∧ PermitFrame m) := by
  have hw : ∀ {k addrs}, (Abi.selectorOf m.frame.msg.data, k, addrs) ∈ assetArgShapes →
      4 + 32 * k ≤ m.frame.msg.data.size ∧ ∀ j ∈ addrs, CleanAddr m.frame.msg.data j :=
    fun hmem => wellFormed_of fun hm => hmal ⟨h4, _, _, .inr ⟨ht, hmem⟩, hm⟩
  simp only [assetSelectors, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · -- 0x06fdde03
    exact .inr (.inl (.inr (.inr ⟨.inr ht, .inl ⟨⟨h, h4⟩, hc.name h⟩⟩)))
  · -- 0x095ea7b3
    obtain ⟨hsz, hcl⟩ := hw (k := 2) (addrs := [0]) (by rw [h]; decide)
    have hd := twoWordCall_of h (by omega)
    rw [← ofAddress_toAddress_of_clean (hcl 0 (by simp))] at hd
    exact .inl ⟨.assetApprove _ _ _, rfl, by rw [ht]; rfl, hd⟩
  · -- 0x18160ddd
    refine .inr (.inl (.inr (.inl ⟨ht, ?_⟩)))
    right
    left
    exact ⟨h, h4⟩
  · -- 0x23b872dd
    obtain ⟨hsz, hcl⟩ := hw (k := 3) (addrs := [0, 1]) (by rw [h]; decide)
    have hd := threeWordCall_of h (by omega)
    rw [← ofAddress_toAddress_of_clean (hcl 0 (by simp))] at hd
    rw [← ofAddress_toAddress_of_clean (hcl 1 (by simp))] at hd
    exact .inl ⟨.assetTransferFrom _ _ _ _, rfl, by rw [ht]; rfl, hd⟩
  · -- 0x313ce567
    refine .inr (.inl (.inr (.inl ⟨ht, ?_⟩)))
    iterate 3 right
    left
    exact ⟨h, h4⟩
  · -- 0x3644e515
    exact .inr (.inl (.inr (.inr ⟨.inr ht, .inr (.inr ⟨⟨h, h4⟩, hc.domain h⟩)⟩)))
  · -- 0x40c10f19
    obtain ⟨hsz, hcl⟩ := hw (k := 2) (addrs := [0]) (by rw [h]; decide)
    have hd := twoWordCall_of h (by omega)
    rw [← ofAddress_toAddress_of_clean (hcl 0 (by simp))] at hd
    exact .inl ⟨.assetMint _ _ _, rfl, by rw [ht]; rfl, hd⟩
  · -- 0x70a08231
    obtain ⟨hsz, hcl⟩ := hw (k := 1) (addrs := [0]) (by rw [h]; decide)
    refine .inr (.inl (.inr (.inl ⟨ht, ?_⟩)))
    left
    exact ⟨_, addrCall_of (h.trans rfl) (by omega) (hcl 0 (by simp))⟩
  · -- 0x7ecebe00
    obtain ⟨hsz, hcl⟩ := hw (k := 1) (addrs := [0]) (by rw [h]; decide)
    refine .inr (.inl (.inr (.inl ⟨ht, ?_⟩)))
    iterate 4 right
    exact ⟨_, addrCall_of h (by omega) (hcl 0 (by simp))⟩
  · -- 0x95d89b41
    exact .inr (.inl (.inr (.inr ⟨.inr ht, .inr (.inl ⟨⟨h, h4⟩, hc.symbol h⟩)⟩)))
  · -- 0x9dc29fac
    obtain ⟨hsz, hcl⟩ := hw (k := 2) (addrs := [0]) (by rw [h]; decide)
    have hd := twoWordCall_of h (by omega)
    rw [← ofAddress_toAddress_of_clean (hcl 0 (by simp))] at hd
    exact .inl ⟨.assetBurn _ _ _, rfl, by rw [ht]; rfl, hd⟩
  · -- 0xa9059cbb
    obtain ⟨hsz, hcl⟩ := hw (k := 2) (addrs := [0]) (by rw [h]; decide)
    have hd := twoWordCall_of h (by omega)
    rw [← ofAddress_toAddress_of_clean (hcl 0 (by simp))] at hd
    exact .inl ⟨.assetTransfer _ _ _, rfl, by rw [ht]; rfl, hd⟩
  · -- 0xd505accf
    obtain ⟨hsz, hcl⟩ := hw (k := 7) (addrs := [0, 1]) (by rw [h]; decide)
    exact .inr (.inr ⟨⟨_, permitData_asset ht (permitCall_of h (by omega) (hcl 0 (by simp))
      (hcl 1 (by simp)))⟩, hc.permit h⟩)
  · -- 0xdd62ed3e
    obtain ⟨hsz, hcl⟩ := hw (k := 2) (addrs := [0, 1]) (by rw [h]; decide)
    have hd := twoWordCall_of h (by omega)
    rw [← ofAddress_toAddress_of_clean (hcl 0 (by simp)),
      ← ofAddress_toAddress_of_clean (hcl 1 (by simp))] at hd
    refine .inr (.inl (.inr (.inl ⟨ht, ?_⟩)))
    iterate 2 right
    left
    exact ⟨_, _, hd⟩

/-! ## Coverage -/

/-- **Every funded frame is covered**, whatever its calldata, given `CoverOk` (gas for the
stored strings, the covered `DOMAIN_SEPARATOR()` cases, the `permit` frame conditions). -/
theorem covered_of_funded {m : Machine} (hv : VaultStart vault asset m)
    (hdep : Deployed m.world vault asset) (hf : FundedCall vault minGas m) (hc : CoverOk m) :
    Covered vault asset minGas m := by
  have hne := hdep.vault_ne_asset
  refine .inr ⟨hf, ?_⟩
  by_cases h4 : m.frame.msg.data.size < 4
  · exact .inr (.inr (.inr (.inl (.inl h4))))
  have h4' : 4 ≤ m.frame.msg.data.size := by omega
  by_cases hmal : MalformedData vault asset m
  · exact .inr (.inr (.inr (.inr hmal)))
  have lift : ((∃ c, Executes vault asset m c) ∨ ViewData vault asset m ∨
      ((∃ c, PermitData vault asset m c) ∧ PermitFrame m)) →
      (∃ c, Executes vault asset m c) ∨ ViewData vault asset m ∨
        ((∃ c, PermitData vault asset m c) ∧ PermitFrame m) ∨ UnknownData vault asset m ∨
        MalformedData vault asset m := by
    rintro (h | h | h)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
  rcases hv.prot with ht | ht
  · by_cases hs : Abi.selectorOf m.frame.msg.data ∈ vaultSelectors
    · exact lift (vault_known_covered ht h4' hmal hc hs)
    · exact .inr (.inr (.inr (.inl (.inr ⟨h4', fun _ => hs,
        fun h => absurd (ht.symm.trans h) hne⟩))))
  · by_cases hs : Abi.selectorOf m.frame.msg.data ∈ assetSelectors
    · exact lift (asset_known_covered ht h4' hmal hc hs)
    · exact .inr (.inr (.inr (.inl (.inr ⟨h4', fun h => absurd (h.symm.trans ht) hne,
        fun _ => hs⟩))))

/-- **A transaction is covered** when every vault/asset frame started by other code carries
value (with at least 100 gas) or is funded with `CoverOk`, and its committed calls are
admitted. -/
theorem txOk_of {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    (h : ∀ m, Reaches ctx w tr msg m → VaultStart vault asset m → Deployed m.world vault asset →
      (∀ f ∈ m.parents, ¬ Danger (Prot vault asset) f) →
      ((m.frame.msg.value ≠ 0 ∧ 100 ≤ m.frame.gasLeft) ∨ (FundedCall vault minGas m ∧ CoverOk m)) ∧
        FrameAdmitted ctx.crypto vault asset Act K m)
    (hdep : ∀ m, Reaches ctx w tr msg m → VaultStart vault asset m → Deployed m.world vault asset) :
    TxOk vault asset minGas Act K ctx w tr msg := by
  intro m hm hv hp
  have hd := hdep m hm hv
  obtain ⟨hc, hadm⟩ := h m hm hv hd hp
  refine ⟨?_, hadm⟩
  rcases hc with hc | ⟨hf, hc⟩
  · exact .inl hc
  · exact covered_of_funded hv hd hf hc

end Verified.Solmate.ERC4626.Nested
