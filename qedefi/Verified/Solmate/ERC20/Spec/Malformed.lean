import Verified.Solmate.ERC20.Spec.MalformedCode
import Verified.Solmate.ERC20.Spec.PermitSpec
import Verified.Common.Malformed.Post

/-!
# Solmate's asset with any calldata: `MalformedSpec`, up to the open `permit` cases

**`solmate_malformed`**: `MalformedSpec` for the deployed `MockERC20` (any immutables), with
Solmate's own signature recovery `solmateRec`, from **`PermitResidue`**: the well-formed
`permit` frames that `permit_spec_case` does not cover. Every other frame, with any calldata,
value and gas, is proved here:

* short calldata or an unknown selector: `fallback_spec`;
* any value: no function is payable, the frame reverts (`value_reverts`);
* the eight getters (`name`, `symbol`, `decimals`, `DOMAIN_SEPARATOR`, `nonces`, `balanceOf`,
  `allowance`, `totalSupply`) change nothing, whatever their arguments (`getter_halts`, a
  read-only region);
* `transfer`, `approve`, `transferFrom`, `mint`, `burn`: with every argument word and clean
  `address` words the calldata is an encoding (`encodes_transfer`, …, `solmateOps`) and
  `calls_spec`/`ops_spec` apply; otherwise solc's decoder reverts (`asset_<f>_short`,
  `asset_<f>_dirty<j>`);
* `permit`: short calldata, a dirty `address` or a `v` word of 256 or more reverts in the
  decoder; well-formed calldata with `ecrecover` running the precompile, less than `2⁶⁴` gas
  and the domain separator in `Permit.DomainCase` (the deployment chain, or a short `name`)
  ends as `permit_spec_case` says.

Below 2000 gas a frame fails or ends as with more gas (`low`, `low2`: the paths read no gas).

`solmate_complete`: `ERC20Spec.Complete`, from `PermitSpec` and `PermitResidue`.

**What remains (`PermitResidue`)**: a well-formed `permit` (clean `owner`/`spender`, `v` below
256, no value) in a frame where `ecrecover` may not run the precompile (an EIP-7702 designator
at `0x01`), or with `2⁶⁴` gas or more, or off the deployment chain with a `name` of 32 bytes or
more (or an inconsistent `name` slot). These are `permit`'s own open cases (`PermitSpec`
excludes the first two; `permit_spec_case` the third).
-/

namespace Verified.Solmate.ERC20.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.Solmate
open Verified.Solmate.Contracts Verified.Solmate.ERC20 Verified.Solmate.ERC4626
open Verified.Solmate.ERC20.Spec Verified.Common.Malformed

variable {ia : SolmateAsset.Immutables} {Act : Finset Address} {m : Machine}

/-- `MalPost` of Solmate's asset, with its signature recovery. -/
abbrev Post (ia : SolmateAsset.Immutables) (Act : Finset Address) (m : Machine) :
    Machine → Outcome → Prop :=
  MalPost solmateAbs M solmateOps solmateOpAddrs (some (solmateRec ia)) Act m

/-- **The `permit` frames left open**: well-formed calldata (clean `owner` and `spender`, a
`v` below 256), no value, outside the case `permit_spec_case` covers. -/
def PermitResidue (ia : SolmateAsset.Immutables) : Prop :=
  ∀ Act m, Start (code ia) solmateAbs M Act m → m.frame.msg.value = 0 →
    Abi.selectorOf m.frame.msg.data = 0xd505accf → 228 ≤ m.frame.msg.data.size →
    CleanAddr m.frame.msg.data 0 → CleanAddr m.frame.msg.data 1 →
    CleanU8 m.frame.msg.data →
    ¬ (EcrecoverPlain m ∧ m.frame.gasLeft < 2 ^ 64 ∧
      Permit.DomainCase ia.initialChainId (ofNat m.ctx.block.chainId)
        (m.world.sload m.frame.msg.currentTarget 0#256)) →
    Halts m (Post ia Act m)

/-! ## Low gas -/

/-- The gas of the lifted frame. -/
abbrev Gh (m : Machine) : Nat := max m.frame.gasLeft 2000

/-- A code-level fact about every fresh frame with the calldata and value of `m` and 2000 gas
or more holds of its lift. -/
theorem of_hi {Q : Machine → Prop}
    (h : ∀ m', Fresh (code ia) m' → m'.frame.msg.data = m.frame.msg.data →
      m'.frame.msg.value = m.frame.msg.value → m'.frame.msg.data.size < 2 ^ 64 →
      2000 ≤ m'.frame.gasLeft → Q m')
    (hf : Fresh (code ia) m) (h64 : m.frame.msg.data.size < 2 ^ 64) : Q (hi (Gh m) m) :=
  h _ (hi_fresh hf (Nat.le_max_left _ _)) rfl rfl h64
    (by rw [hi_gas (Nat.le_max_left _ _)]; exact Nat.le_max_right _ _)

/-- **A spec path that reverts from 2000 gas fails at any gas.** -/
theorem fails_low (hS : Start (code ia) solmateAbs M Act m)
    (hc : m.frame.msg.value ≠ 0 ∨ m.frame.msg.data.size < 4 ∨
      Abi.selectorOf m.frame.msg.data ∉ assetSelectors ∨
      Abi.selectorOf m.frame.msg.data ∈ specSelectors)
    (h : ∀ m', Fresh (code ia) m' → m'.frame.msg.data = m.frame.msg.data →
      m'.frame.msg.value = m.frame.msg.value → m'.frame.msg.data.size < 2 ^ 64 →
      2000 ≤ m'.frame.gasLeft → Halts m' fun _ o => ∃ out, o = .revert out) :
    Halts m (Post ia Act m) :=
  post_fails ((low (P := fun _ _ => False) hS (Nat.le_max_left _ _)
    (Nat.le_trans (by decide) (Nat.le_max_right _ _)) hc (fun _ _ _ _ _ _ _ h => h)
    ((of_hi h hS.fresh hS.size).mono fun _ _ _ ⟨_, ho⟩ out h' => by
      rw [ho] at h'; cases h')).mono
    fun _ _ _ h => by
      rcases h with h | ⟨_, _, h⟩
      · exact h
      · exact h.elim)

/-- **A spec path that changes nothing from 2000 gas fails or changes nothing at any gas.** -/
theorem unchanged_low (hS : Start (code ia) solmateAbs M Act m)
    (hc : Abi.selectorOf m.frame.msg.data ∈ specSelectors)
    (h : ∀ m', Fresh (code ia) m' → m'.frame.msg.data = m.frame.msg.data →
      m'.frame.msg.value = m.frame.msg.value → m'.frame.msg.data.size < 2 ^ 64 →
      2000 ≤ m'.frame.gasLeft → Halts m' fun mf _ => Unchanged m' mf) :
    Halts m (Post ia Act m) :=
  (low (P := fun _ mf => Unchanged m mf) hS (Nat.le_max_left _ _)
    (Nat.le_trans (by decide) (Nat.le_max_right _ _)) (.inr (.inr (.inr hc)))
    (fun _ _ _ hw ht _ hl ⟨h1, h2, h3⟩ => ⟨hw.trans h1, ht.trans h2, hl.trans h3⟩)
    ((of_hi h hS.fresh hS.size).mono fun _ _ _ hu _ _ => hu)).mono
    fun _ _ _ h => by
      rcases h with h | ⟨_, _, h⟩
      · exact .inl h
      · exact .inr (.inl h)

/-- **A path through a new target that reverts from 2000 gas fails at any gas.** -/
theorem fails_low2 (hS : Start (code ia) solmateAbs M Act m) {q : Nat} (hq : q ∈ targets2)
    (hT : ∀ m', Fresh (code ia) m' → m'.frame.msg.data = m.frame.msg.data →
      m'.frame.msg.value = m.frame.msg.value → m'.frame.msg.data.size < 2 ^ 64 →
      2000 ≤ m'.frame.gasLeft → ∃ mT, Steps m' mT ∧ mT.frame.pc = q)
    (h : ∀ m', Fresh (code ia) m' → m'.frame.msg.data = m.frame.msg.data →
      m'.frame.msg.value = m.frame.msg.value → m'.frame.msg.data.size < 2 ^ 64 →
      2000 ≤ m'.frame.gasLeft → Halts m' fun _ o => ∃ out, o = .revert out) :
    Halts m (Post ia Act m) := by
  obtain ⟨mT, hs, hpc⟩ := of_hi hT hS.fresh hS.size
  exact post_fails ((low2 (P := fun _ _ => False) hS.fresh (Nat.le_max_left _ _)
    ⟨mT, hs, hpc ▸ hq⟩ (fun _ _ _ _ _ _ _ h => h)
    ((of_hi h hS.fresh hS.size).mono fun _ _ _ ⟨_, ho⟩ out h' => by
      rw [ho] at h'; cases h')).mono
    fun _ _ _ h => by
      rcases h with h | ⟨_, _, h⟩
      · exact h
      · exact h.elim)

/-- **A path through a new target that changes nothing from 2000 gas fails or changes nothing
at any gas.** -/
theorem unchanged_low2 (hS : Start (code ia) solmateAbs M Act m) {q : Nat} (hq : q ∈ targets2)
    (hT : ∀ m', Fresh (code ia) m' → m'.frame.msg.data = m.frame.msg.data →
      m'.frame.msg.value = m.frame.msg.value → m'.frame.msg.data.size < 2 ^ 64 →
      2000 ≤ m'.frame.gasLeft → ∃ mT, Steps m' mT ∧ mT.frame.pc = q)
    (h : ∀ m', Fresh (code ia) m' → m'.frame.msg.data = m.frame.msg.data →
      m'.frame.msg.value = m.frame.msg.value → m'.frame.msg.data.size < 2 ^ 64 →
      2000 ≤ m'.frame.gasLeft → Halts m' fun mf _ => Unchanged m' mf) :
    Halts m (Post ia Act m) := by
  obtain ⟨mT, hs, hpc⟩ := of_hi hT hS.fresh hS.size
  exact (low2 (P := fun _ mf => Unchanged m mf) hS.fresh (Nat.le_max_left _ _)
    ⟨mT, hs, hpc ▸ hq⟩
    (fun _ _ _ hw ht _ hl ⟨h1, h2, h3⟩ => ⟨hw.trans h1, ht.trans h2, hl.trans h3⟩)
    ((of_hi h hS.fresh hS.size).mono fun _ _ _ hu _ _ => hu)).mono
    fun _ _ _ h => by
      rcases h with h | ⟨_, _, h⟩
      · exact .inl h
      · exact .inr (.inl h)

/-! ## By selector -/

theorem spec_mem {s : Nat} (hs : s ∈ specSelectors) (h : Abi.selectorOf m.frame.msg.data = s) :
    Abi.selectorOf m.frame.msg.data ∈ specSelectors := h ▸ hs

/-- A getter of the spec (`balanceOf`, `allowance`, `totalSupply`). -/
theorem post_getter (hS : Start (code ia) solmateAbs M Act m) {sel q : Nat}
    (hge : (sel, q) ∈ getterEntries) (hsp : sel ∈ specSelectors) (hv : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = sel) (h4 : 4 ≤ m.frame.msg.data.size) :
    Halts m (Post ia Act m) :=
  unchanged_low hS (spec_mem hsp hsel) fun m' hf hd hv' h64 hg =>
    getter_halts hge m' hf (hv' ▸ hv) (hd ▸ hsel) (hd ▸ h4) h64 (by omega)

/-- A getter outside the spec (`name`, `symbol`, `decimals`, `DOMAIN_SEPARATOR`, `nonces`). -/
theorem post_getter2 (hS : Start (code ia) solmateAbs M Act m) {sel q : Nat}
    (hge : (sel, q) ∈ getterEntries) (hq : q ∈ targets2) (hv : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = sel) (h4 : 4 ≤ m.frame.msg.data.size) :
    Halts m (Post ia Act m) :=
  unchanged_low2 hS hq
    (fun m' hf hd hv' h64 hg => getter_reaches hge m' hf (hv' ▸ hv) (hd ▸ hsel) (hd ▸ h4) h64
      (by omega))
    (fun m' hf hd hv' h64 hg => getter_halts hge m' hf (hv' ▸ hv) (hd ▸ hsel) (hd ▸ h4) h64
      (by omega))

theorem solmateOps_mint {d : ByteArray} {caller : Address} (hsel : Abi.selectorOf d = 0x40c10f19)
    (hs : 68 ≤ d.size) (hc : CleanAddr d 0) :
    solmateOps caller d 0 =
      some (.mint caller (Word.toAddress (argWord d 0)) (argWord d 1).toNat) := by
  have h : AddrAmount d 0x40c10f19 := ⟨hsel, hs, hc⟩
  simp [solmateOps, h]

theorem solmateOps_burn {d : ByteArray} {caller : Address} (hsel : Abi.selectorOf d = 0x9dc29fac)
    (hs : 68 ≤ d.size) (hc : CleanAddr d 0) :
    solmateOps caller d 0 =
      some (.burn caller (Word.toAddress (argWord d 0)) (argWord d 1).toNat) := by
  have h : AddrAmount d 0x9dc29fac := ⟨hsel, hs, hc⟩
  have h' : ¬ AddrAmount d 0x40c10f19 := fun h' => by
    have := h'.1; rw [hsel] at this; cases this
  simp [solmateOps, h, h']

/-- `permit`: malformed calldata reverts in the decoder; well-formed calldata ends as
`permit_spec_case` says, or is in the residue. -/
theorem post_permit_solmate (hres : PermitResidue ia) (hS : Start (code ia) solmateAbs M Act m)
    (hv : m.frame.msg.value = 0) (hsel : Abi.selectorOf m.frame.msg.data = 0xd505accf)
    (h4 : 4 ≤ m.frame.msg.data.size) : Halts m (Post ia Act m) := by
  by_cases hs : 228 ≤ m.frame.msg.data.size
  swap
  · exact fails_low2 hS (q := 2430) (by decide)
      (fun m' hf hd hv' _ hg => permit_reaches_short m' hf (hv' ▸ hv) (hd ▸ hsel) (hd ▸ h4)
        (by rw [hd]; omega) hg)
      (fun m' hf hd hv' _ hg => asset_permit_short m' hf (hv' ▸ hv) (hd ▸ hsel) (hd ▸ h4)
        (by rw [hd]; omega) hg)
  by_cases hc0 : CleanAddr m.frame.msg.data 0
  swap
  · exact fails_low2 hS (q := 2273) (by decide)
      (fun m' hf hd hv' h64 hg => permit_reaches_dirty0 m' hf (hv' ▸ hv) (hd ▸ hsel) (hd ▸ hs)
        h64 (hd ▸ hc0) hg)
      (fun m' hf hd hv' h64 hg => asset_permit_dirty0 m' hf (hv' ▸ hv) (hd ▸ hsel) (hd ▸ hs)
        h64 (hd ▸ hc0) hg)
  by_cases hc1 : CleanAddr m.frame.msg.data 1
  swap
  · exact fails_low2 hS (q := 2273) (by decide)
      (fun m' hf hd hv' h64 hg => permit_reaches_dirty1 m' hf (hv' ▸ hv) (hd ▸ hsel) (hd ▸ hs)
        h64 (hd ▸ hc0) (hd ▸ hc1) hg)
      (fun m' hf hd hv' h64 hg => asset_permit_dirty1 m' hf (hv' ▸ hv) (hd ▸ hsel) (hd ▸ hs)
        h64 (hd ▸ hc0) (hd ▸ hc1) hg)
  by_cases hu : CleanU8 m.frame.msg.data
  swap
  · exact fails_low2 hS (q := 2488) (by decide)
      (fun m' hf hd hv' h64 hg => permit_reaches_dirtyV m' hf (hv' ▸ hv) (hd ▸ hsel) (hd ▸ hs)
        h64 (hd ▸ hc0) (hd ▸ hc1) (hd ▸ hu) hg)
      (fun m' hf hd hv' h64 hg => permit_dirtyV_halts m' hf (hv' ▸ hv) (hd ▸ hsel) (hd ▸ hs)
        h64 (hd ▸ hc0) (hd ▸ hc1) (hd ▸ hu) hg)
  by_cases hcase : EcrecoverPlain m ∧ m.frame.gasLeft < 2 ^ 64 ∧
      Permit.DomainCase ia.initialChainId (ofNat m.ctx.block.chainId)
        (m.world.sload m.frame.msg.currentTarget 0#256)
  · obtain ⟨hep, hgl, hdc⟩ := hcase
    have hA := args_permit hsel hs hc0 hc1
    exact post_permit_of rfl hS fun Act' hS' ho hsp =>
      (permit_spec_case Act' m _ _ _ _ _ _ _ hS' ho hsp hep hgl hA hdc).mono
        fun _ _ _ hp => hp.imp_right fun h => h.1
  · exact hres Act m hS hv hsel hs hc0 hc1 hu hcase

/-! ## The theorem -/

/-- **Solmate's asset with any calldata**, given the open `permit` cases (`PermitResidue`):
every frame fails, changes nothing, or ends as an ERC-20 call (a `permit` with Solmate's
recovery) or a `mint`/`burn` of `solmateModel`, for the actors and the accounts it names. -/
theorem solmate_malformed (hres : PermitResidue ia) :
    MalformedSpec (code ia) solmateAbs M solmateOps solmateOpAddrs (some (solmateRec ia)) := by
  refine malformedSpec_of fun Act m hS => ?_
  by_cases hfb : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ assetSelectors
  · exact post_fallback fallback_spec hS hfb
  simp only [not_or, not_lt, not_not] at hfb
  obtain ⟨h4, hmem⟩ := hfb
  by_cases hv : m.frame.msg.value = 0
  swap
  · exact fails_low hS (.inl hv) fun m' hf _ hv' _ hg =>
      value_reverts m' hf (hv' ▸ hv) (by omega)
  have hv0 : m.frame.msg.value.toNat = 0 := by rw [hv]; rfl
  have hmem' := hmem
  simp only [assetSelectors, List.mem_cons, List.not_mem_nil, or_false] at hmem'
  rcases hmem' with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  -- name
  · exact post_getter2 hS (q := 233) (by decide) (by decide) hv h h4
  -- approve
  · have hsp := spec_mem (by decide) h
    by_cases hs : 68 ≤ m.frame.msg.data.size
    · by_cases hc : CleanAddr m.frame.msg.data 0
      · exact post_call (calls_spec _) hS (encodes_approve h hs hc) trivial
      · exact fails_low hS (.inr (.inr (.inr hsp))) fun m' hf hd hv' h64 hg =>
          asset_approve_dirty0 m' hf (hv' ▸ hv) (hd ▸ h) (hd ▸ hs) h64 (hd ▸ hc) hg
    · exact fails_low hS (.inr (.inr (.inr hsp))) fun m' hf hd hv' _ hg =>
        asset_approve_short m' hf (hv' ▸ hv) (hd ▸ h) (hd ▸ h4) (by rw [hd]; omega) hg
  -- totalSupply
  · exact post_getter hS (q := 298) (by decide) (by decide) hv h h4
  -- transferFrom
  · have hsp := spec_mem (by decide) h
    by_cases hs : 100 ≤ m.frame.msg.data.size
    · by_cases hc0 : CleanAddr m.frame.msg.data 0
      · by_cases hc1 : CleanAddr m.frame.msg.data 1
        · exact post_call (calls_spec _) hS (encodes_transferFrom h hs hc0 hc1) trivial
        · exact fails_low hS (.inr (.inr (.inr hsp))) fun m' hf hd hv' h64 hg =>
            asset_transferFrom_dirty1 m' hf (hv' ▸ hv) (hd ▸ h) (hd ▸ hs) h64 (hd ▸ hc0)
              (hd ▸ hc1) hg
      · exact fails_low hS (.inr (.inr (.inr hsp))) fun m' hf hd hv' h64 hg =>
          asset_transferFrom_dirty0 m' hf (hv' ▸ hv) (hd ▸ h) (hd ▸ hs) h64 (hd ▸ hc0) hg
    · exact fails_low hS (.inr (.inr (.inr hsp))) fun m' hf hd hv' _ hg =>
        asset_transferFrom_short m' hf (hv' ▸ hv) (hd ▸ h) (hd ▸ h4) (by rw [hd]; omega) hg
  -- decimals
  · exact post_getter2 hS (q := 340) (by decide) (by decide) hv h h4
  -- DOMAIN_SEPARATOR
  · exact post_getter2 hS (q := 397) (by decide) (by decide) hv h h4
  -- mint
  · have hsp := spec_mem (by decide) h
    by_cases hs : 68 ≤ m.frame.msg.data.size
    · by_cases hc : CleanAddr m.frame.msg.data 0
      · exact post_op ops_spec hS (by rw [hv0]; exact solmateOps_mint h hs hc)
      · exact fails_low hS (.inr (.inr (.inr hsp))) fun m' hf hd hv' h64 hg =>
          asset_mint_dirty0 m' hf (hv' ▸ hv) (hd ▸ h) (hd ▸ hs) h64 (hd ▸ hc) hg
    · exact fails_low hS (.inr (.inr (.inr hsp))) fun m' hf hd hv' _ hg =>
        asset_mint_short m' hf (hv' ▸ hv) (hd ▸ h) (hd ▸ h4) (by rw [hd]; omega) hg
  -- balanceOf
  · exact post_getter hS (q := 426) (by decide) (by decide) hv h h4
  -- nonces
  · exact post_getter2 hS (q := 457) (by decide) (by decide) hv h h4
  -- symbol
  · exact post_getter2 hS (q := 488) (by decide) (by decide) hv h h4
  -- burn
  · have hsp := spec_mem (by decide) h
    by_cases hs : 68 ≤ m.frame.msg.data.size
    · by_cases hc : CleanAddr m.frame.msg.data 0
      · exact post_op ops_spec hS (by rw [hv0]; exact solmateOps_burn h hs hc)
      · exact fails_low hS (.inr (.inr (.inr hsp))) fun m' hf hd hv' h64 hg =>
          asset_burn_dirty0 m' hf (hv' ▸ hv) (hd ▸ h) (hd ▸ hs) h64 (hd ▸ hc) hg
    · exact fails_low hS (.inr (.inr (.inr hsp))) fun m' hf hd hv' _ hg =>
        asset_burn_short m' hf (hv' ▸ hv) (hd ▸ h) (hd ▸ h4) (by rw [hd]; omega) hg
  -- transfer
  · have hsp := spec_mem (by decide) h
    by_cases hs : 68 ≤ m.frame.msg.data.size
    · by_cases hc : CleanAddr m.frame.msg.data 0
      · exact post_call (calls_spec _) hS (encodes_transfer h hs hc) trivial
      · exact fails_low hS (.inr (.inr (.inr hsp))) fun m' hf hd hv' h64 hg =>
          asset_transfer_dirty0 m' hf (hv' ▸ hv) (hd ▸ h) (hd ▸ hs) h64 (hd ▸ hc) hg
    · exact fails_low hS (.inr (.inr (.inr hsp))) fun m' hf hd hv' _ hg =>
        asset_transfer_short m' hf (hv' ▸ hv) (hd ▸ h) (hd ▸ h4) (by rw [hd]; omega) hg
  -- permit
  · exact post_permit_solmate hres hS hv h h4
  -- allowance
  · exact post_getter hS (q := 553) (by decide) (by decide) hv h h4

/-- **The complete spec of Solmate's asset**, from the two open parts of `permit`: `PermitSpec`
in the frames `permit_spec_case` does not cover, and the frames `PermitSpec` itself excludes
(`PermitResidue`). Everything else is proved: `solmate_erc20Spec`, and `MalformedSpec` for
every other frame (`solmate_malformed`). -/
theorem solmate_complete (hperm : PermitSpec (code ia) solmateAbs M (solmateGp ia) (solmateRec ia))
    (hres : PermitResidue ia) :
    ERC20Spec.Complete (code ia) solmateAbs M g₀ assetSelectors solmateOps solmateOpAddrs
      (some (solmateGp ia, solmateRec ia)) :=
  ⟨solmate_erc20Spec ia, fun _ _ h => by cases h; exact hperm, solmate_malformed hres⟩

end Verified.Solmate.ERC20.Spec.Malformed
