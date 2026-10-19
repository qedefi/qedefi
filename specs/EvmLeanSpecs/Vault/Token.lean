module

public import EvmLeanSpecs.Vault.Arith

/-!
# ERC-20 ledgers

`Token A` is the storage of an ERC-20 contract over an actor type `A` (addresses):
balances as a finitely supported map `A →₀ ℕ`, the total supply, and the allowance matrix.
Both the vault's share token and the underlying asset are `Token`s.

Two families of operations mirror the two code bases exactly, including when they revert:

* **Solmate `ERC20`** (`transfer`, `transferFrom`, `approve`, `_mint`, `_burn`): checked
  subtraction on the debited balance, unchecked addition on the credited one, checked
  `totalSupply += amount` in `_mint`, `type(uint256).max` allowances are never decreased,
  no zero-address checks.
* **OpenZeppelin `ERC20`** v5 (`_update`, `_transfer`, `_mint`, `_burn`, `_approve`,
  `_spendAllowance`): the same arithmetic plus the zero-address reverts.

Unchecked additions are modelled as `ℕ` additions; they agree with the bytecode as long as
`Token.WF` (balances sum to `totalSupply ≤ MAX`) holds, which every operation preserves
(`WF_transfer`, `WF_ozUpdate`, …). Amounts are ABI-decoded `uint256`s, so callers of these
functions pass values `≤ MAX`.
-/

@[expose] public noncomputable section

namespace EvmLeanSpecs.Vault

open Finsupp

/-- Sum of all entries of a finitely supported balance map. -/
def total {A : Type} (f : A →₀ ℕ) : ℕ := f.sum fun _ v => v

/-- The storage of an ERC-20 token. -/
structure Token (A : Type) where
  /-- `balanceOf`. -/
  balanceOf : A →₀ ℕ
  /-- `totalSupply`. -/
  totalSupply : ℕ
  /-- `allowance[owner][spender]`. -/
  allowance : A → A → ℕ

namespace Token

variable {A : Type} [DecidableEq A]

/-- Well-formedness: balances sum to the total supply, which fits in a `uint256`. -/
def WF (t : Token A) : Prop := total t.balanceOf = t.totalSupply ∧ t.totalSupply ≤ MAX

/-- `allowance[owner][spender] = v`. -/
def setAllowance (t : Token A) (owner spender : A) (v : ℕ) : Token A :=
  { t with
    allowance := Function.update t.allowance owner (Function.update (t.allowance owner) spender v) }

/-! ## Solmate `ERC20` -/

/-- Solmate `ERC20.transfer(to, amount)` with `msg.sender = src`:
`balanceOf[src] -= amount` (checked), then `balanceOf[dst] += amount` (unchecked). -/
def transfer (t : Token A) (src dst : A) (v : ℕ) : Option (Token A) :=
  if t.balanceOf src < v then none
  else some { t with balanceOf := t.balanceOf - single src v + single dst v }

/-- The allowance step of Solmate `transferFrom`, `withdraw` and `redeem`:
`if (allowed != type(uint256).max) allowance[owner][spender] = allowed - amount;`
(checked subtraction). -/
def spend (t : Token A) (owner spender : A) (v : ℕ) : Option (Token A) :=
  if t.allowance owner spender = MAX then some t
  else if t.allowance owner spender < v then none
  else some (t.setAllowance owner spender (t.allowance owner spender - v))

/-- Solmate `ERC20.transferFrom(src, dst, amount)` with `msg.sender = spender`. -/
def transferFrom (t : Token A) (spender src dst : A) (v : ℕ) : Option (Token A) :=
  (t.spend src spender v).bind fun t => t.transfer src dst v

/-- Solmate `ERC20.approve(spender, amount)` with `msg.sender = owner`. -/
def approve (t : Token A) (owner spender : A) (v : ℕ) : Token A :=
  t.setAllowance owner spender v

/-- Solmate `ERC20._mint(to, amount)`: `totalSupply += amount` (checked), then
`balanceOf[to] += amount` (unchecked). Also `MockERC20.mint`. -/
def mint (t : Token A) (dst : A) (v : ℕ) : Option (Token A) :=
  if MAX < t.totalSupply + v then none
  else some { t with totalSupply := t.totalSupply + v, balanceOf := t.balanceOf + single dst v }

/-- Solmate `ERC20._burn(from, amount)`: `balanceOf[from] -= amount` (checked), then
`totalSupply -= amount` (unchecked). Also `MockERC20.burn`. -/
def burn (t : Token A) (src : A) (v : ℕ) : Option (Token A) :=
  if t.balanceOf src < v then none
  else some { t with totalSupply := t.totalSupply - v, balanceOf := t.balanceOf - single src v }

/-! ## OpenZeppelin `ERC20` (v5) -/

section Oz

variable [Zero A]

/-- OpenZeppelin `ERC20._update(from, to, value)`. -/
def ozUpdate (t : Token A) (src dst : A) (v : ℕ) : Option (Token A) :=
  let t1? : Option (Token A) :=
    if src = 0 then
      if MAX < t.totalSupply + v then none else some { t with totalSupply := t.totalSupply + v }
    else if t.balanceOf src < v then none
    else some { t with balanceOf := t.balanceOf - single src v }
  t1?.map fun t1 =>
    if dst = 0 then { t1 with totalSupply := t1.totalSupply - v }
    else { t1 with balanceOf := t1.balanceOf + single dst v }

/-- OpenZeppelin `ERC20._transfer(from, to, value)`. -/
def ozTransfer (t : Token A) (src dst : A) (v : ℕ) : Option (Token A) :=
  if src = 0 then none else if dst = 0 then none else t.ozUpdate src dst v

/-- OpenZeppelin `ERC20._mint(account, value)`. -/
def ozMint (t : Token A) (dst : A) (v : ℕ) : Option (Token A) :=
  if dst = 0 then none else t.ozUpdate 0 dst v

/-- OpenZeppelin `ERC20._burn(account, value)`. -/
def ozBurn (t : Token A) (src : A) (v : ℕ) : Option (Token A) :=
  if src = 0 then none else t.ozUpdate src 0 v

/-- OpenZeppelin `ERC20._approve(owner, spender, value, _)`. -/
def ozApprove (t : Token A) (owner spender : A) (v : ℕ) : Option (Token A) :=
  if owner = 0 then none else if spender = 0 then none else some (t.setAllowance owner spender v)

/-- OpenZeppelin `ERC20._spendAllowance(owner, spender, value)`. -/
def ozSpend (t : Token A) (owner spender : A) (v : ℕ) : Option (Token A) :=
  if t.allowance owner spender < MAX then
    if t.allowance owner spender < v then none
    else t.ozApprove owner spender (t.allowance owner spender - v)
  else some t

/-- OpenZeppelin `ERC20.transferFrom(from, to, value)` with `msg.sender = spender`. -/
def ozTransferFrom (t : Token A) (spender src dst : A) (v : ℕ) : Option (Token A) :=
  (t.ozSpend src spender v).bind fun t => t.ozTransfer src dst v

end Oz

/-! ## Sums -/

omit [DecidableEq A] in
theorem total_add_single (f : A →₀ ℕ) (a : A) (v : ℕ) :
    total (f + single a v) = total f + v := by
  unfold total
  rw [sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), sum_single_index rfl]

theorem sub_single_apply (f : A →₀ ℕ) (a x : A) (v : ℕ) :
    (f - single a v) x = if a = x then f x - v else f x := by
  rw [tsub_apply, single_apply]
  split_ifs <;> simp

theorem add_single_apply (f : A →₀ ℕ) (a x : A) (v : ℕ) :
    (f + single a v) x = if a = x then f x + v else f x := by
  rw [Finsupp.add_apply, single_apply]
  split_ifs <;> simp

theorem sub_single_add_single {f : A →₀ ℕ} {a : A} {v : ℕ} (h : v ≤ f a) :
    f - single a v + single a v = f := by
  ext x
  rw [add_single_apply, sub_single_apply]
  split_ifs with hx
  · subst hx; omega
  · rfl

theorem total_sub_single {f : A →₀ ℕ} {a : A} {v : ℕ} (h : v ≤ f a) :
    total (f - single a v) = total f - v := by
  have := total_add_single (f - single a v) a v
  rw [sub_single_add_single h] at this
  omega

theorem le_total (f : A →₀ ℕ) (a : A) : f a ≤ total f := by
  unfold total
  by_cases ha : a ∈ f.support
  · exact Finset.single_le_sum (f := fun x => f x) (fun _ _ => Nat.zero_le _) ha
  · simp [Finsupp.notMem_support_iff.1 ha]


/-! ## Effects of the Solmate operations -/

/-- Balance after a debit and a credit, at the credited account. -/
theorem move_apply_dst (f : A →₀ ℕ) {src dst : A} (v : ℕ) (h : src ≠ dst) :
    (f - single src v + single dst v) dst = f dst + v := by
  rw [add_single_apply, sub_single_apply]; simp [h]

/-- Balance after a debit and a credit, at the debited account. -/
theorem move_apply_src (f : A →₀ ℕ) {src dst : A} (v : ℕ) (h : src ≠ dst) :
    (f - single src v + single dst v) src = f src - v := by
  rw [add_single_apply, sub_single_apply]; simp [Ne.symm h]

/-- Balance after a debit and a credit, elsewhere. -/
theorem move_apply_other (f : A →₀ ℕ) {src dst x : A} (v : ℕ) (h1 : src ≠ x) (h2 : dst ≠ x) :
    (f - single src v + single dst v) x = f x := by
  rw [add_single_apply, sub_single_apply]; simp [h1, h2]

/-- A self-transfer leaves the balances unchanged. -/
theorem move_self {f : A →₀ ℕ} {a : A} {v : ℕ} (h : v ≤ f a) :
    f - single a v + single a v = f := sub_single_add_single h

theorem transfer_eq_some {t t' : Token A} {src dst : A} {v : ℕ} :
    t.transfer src dst v = some t' ↔
      v ≤ t.balanceOf src ∧ t' = { t with balanceOf := t.balanceOf - single src v + single dst v } := by
  unfold transfer
  split_ifs with h
  · simp only [false_iff, not_and]; omega
  · simp only [Option.some.injEq]; constructor
    · rintro rfl; exact ⟨by omega, rfl⟩
    · rintro ⟨-, rfl⟩; rfl

theorem spend_eq_some {t t' : Token A} {o sp : A} {v : ℕ} (h : t.spend o sp v = some t') :
    t'.balanceOf = t.balanceOf ∧ t'.totalSupply = t.totalSupply := by
  unfold spend at h
  split_ifs at h <;> cases h <;> exact ⟨rfl, rfl⟩

theorem transferFrom_eq_some {t t' : Token A} {sp src dst : A} {v : ℕ}
    (h : t.transferFrom sp src dst v = some t') :
    v ≤ t.balanceOf src ∧ t'.balanceOf = t.balanceOf - single src v + single dst v ∧
      t'.totalSupply = t.totalSupply := by
  unfold transferFrom at h
  obtain ⟨t1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨e1, e2⟩ := spend_eq_some h1
  obtain ⟨hv, rfl⟩ := transfer_eq_some.1 h2
  exact ⟨e1 ▸ hv, by simp [e1], e2⟩

omit [DecidableEq A] in
theorem mint_eq_some {t t' : Token A} {dst : A} {v : ℕ} :
    t.mint dst v = some t' ↔ t.totalSupply + v ≤ MAX ∧
      t' = { t with totalSupply := t.totalSupply + v, balanceOf := t.balanceOf + single dst v } := by
  unfold mint
  split_ifs with h
  · simp only [false_iff, not_and]; omega
  · simp only [Option.some.injEq]; constructor
    · rintro rfl; exact ⟨by omega, rfl⟩
    · rintro ⟨-, rfl⟩; rfl

theorem burn_eq_some {t t' : Token A} {src : A} {v : ℕ} :
    t.burn src v = some t' ↔ v ≤ t.balanceOf src ∧
      t' = { t with totalSupply := t.totalSupply - v, balanceOf := t.balanceOf - single src v } := by
  unfold burn
  split_ifs with h
  · simp only [false_iff, not_and]; omega
  · simp only [Option.some.injEq]; constructor
    · rintro rfl; exact ⟨by omega, rfl⟩
    · rintro ⟨-, rfl⟩; rfl

/-- In a well-formed ledger every balance is bounded by the total supply. -/
theorem balanceOf_le_totalSupply {t : Token A} (hw : t.WF) (a : A) :
    t.balanceOf a ≤ t.totalSupply := hw.1 ▸ le_total _ a

/-! ## Well-formedness is preserved -/

theorem WF_transfer {t t' : Token A} {src dst : A} {v : ℕ} (hw : t.WF)
    (h : t.transfer src dst v = some t') : t'.WF := by
  unfold transfer at h
  split_ifs at h with hv
  cases h
  refine ⟨?_, hw.2⟩
  simp only [total_add_single, total_sub_single (not_lt.1 hv)]
  have := le_total t.balanceOf src
  have := hw.1
  omega

theorem WF_setAllowance {t : Token A} (hw : t.WF) (o s : A) (v : ℕ) :
    (t.setAllowance o s v).WF := hw

theorem WF_spend {t t' : Token A} {o s : A} {v : ℕ} (hw : t.WF)
    (h : t.spend o s v = some t') : t'.WF := by
  unfold spend at h
  split_ifs at h <;> cases h <;> exact hw

theorem WF_transferFrom {t t' : Token A} {sp src dst : A} {v : ℕ} (hw : t.WF)
    (h : t.transferFrom sp src dst v = some t') : t'.WF := by
  unfold transferFrom at h
  obtain ⟨t1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
  exact WF_transfer (WF_spend hw h1) h2

theorem WF_approve {t : Token A} (hw : t.WF) (o s : A) (v : ℕ) : (t.approve o s v).WF := hw

omit [DecidableEq A] in
theorem WF_mint {t t' : Token A} {dst : A} {v : ℕ} (hw : t.WF)
    (h : t.mint dst v = some t') : t'.WF := by
  unfold mint at h
  split_ifs at h with hv
  cases h
  refine ⟨?_, not_lt.1 hv⟩
  simp only [total_add_single, hw.1]

theorem WF_burn {t t' : Token A} {src : A} {v : ℕ} (hw : t.WF)
    (h : t.burn src v = some t') : t'.WF := by
  unfold burn at h
  split_ifs at h with hv
  cases h
  refine ⟨?_, le_trans (Nat.sub_le _ _) hw.2⟩
  simp only [total_sub_single (not_lt.1 hv), hw.1]

section Oz

variable [Zero A]

theorem WF_ozUpdate {t t' : Token A} {src dst : A} {v : ℕ} (hw : t.WF)
    (h : t.ozUpdate src dst v = some t') : t'.WF := by
  obtain ⟨hw1, hw2⟩ := hw
  have hle := le_total t.balanceOf src
  unfold ozUpdate at h
  obtain ⟨t1, h1, rfl⟩ := Option.map_eq_some_iff.1 h
  by_cases hs : src = 0 <;> by_cases hd : dst = 0 <;> simp only [hs, hd, ↓reduceIte] at h1 ⊢
  · split_ifs at h1 with hv; cases h1
    exact ⟨by simp only; omega, by simp only; omega⟩
  · split_ifs at h1 with hv; cases h1
    exact ⟨by simp only [total_add_single]; omega, by simp only; omega⟩
  · split_ifs at h1 with hv; cases h1
    exact ⟨by simp only [total_sub_single (not_lt.1 hv)]; omega, by simp only; omega⟩
  · split_ifs at h1 with hv; cases h1
    exact ⟨by simp only [total_add_single, total_sub_single (not_lt.1 hv)]; omega, hw2⟩

theorem WF_ozTransfer {t t' : Token A} {src dst : A} {v : ℕ} (hw : t.WF)
    (h : t.ozTransfer src dst v = some t') : t'.WF := by
  unfold ozTransfer at h
  split_ifs at h
  exact WF_ozUpdate hw h

theorem WF_ozMint {t t' : Token A} {dst : A} {v : ℕ} (hw : t.WF)
    (h : t.ozMint dst v = some t') : t'.WF := by
  unfold ozMint at h
  split_ifs at h
  exact WF_ozUpdate hw h

theorem WF_ozBurn {t t' : Token A} {src : A} {v : ℕ} (hw : t.WF)
    (h : t.ozBurn src v = some t') : t'.WF := by
  unfold ozBurn at h
  split_ifs at h
  exact WF_ozUpdate hw h

theorem WF_ozApprove {t t' : Token A} {o s : A} {v : ℕ} (hw : t.WF)
    (h : t.ozApprove o s v = some t') : t'.WF := by
  unfold ozApprove at h
  split_ifs at h
  cases h; exact hw

theorem WF_ozSpend {t t' : Token A} {o s : A} {v : ℕ} (hw : t.WF)
    (h : t.ozSpend o s v = some t') : t'.WF := by
  unfold ozSpend at h
  split_ifs at h
  · exact WF_ozApprove hw h
  · cases h; exact hw

theorem WF_ozTransferFrom {t t' : Token A} {sp src dst : A} {v : ℕ} (hw : t.WF)
    (h : t.ozTransferFrom sp src dst v = some t') : t'.WF := by
  unfold ozTransferFrom at h
  obtain ⟨t1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
  exact WF_ozTransfer (WF_ozSpend hw h1) h2


/-! ## Effects of the OpenZeppelin operations -/

theorem ozTransfer_eq_some {t t' : Token A} {src dst : A} {v : ℕ}
    (h : t.ozTransfer src dst v = some t') :
    src ≠ 0 ∧ dst ≠ 0 ∧ v ≤ t.balanceOf src ∧
      t'.balanceOf = t.balanceOf - single src v + single dst v ∧
      t'.totalSupply = t.totalSupply := by
  unfold ozTransfer at h
  split_ifs at h with hs hd
  unfold ozUpdate at h
  obtain ⟨t1, h1, rfl⟩ := Option.map_eq_some_iff.1 h
  simp only [hs, hd, ↓reduceIte] at h1 ⊢
  split_ifs at h1 with hv
  cases h1
  exact ⟨hs, hd, not_lt.1 hv, rfl, rfl⟩

theorem ozMint_eq_some {t t' : Token A} {dst : A} {v : ℕ} (h : t.ozMint dst v = some t') :
    dst ≠ 0 ∧ t.totalSupply + v ≤ MAX ∧ t'.balanceOf = t.balanceOf + single dst v ∧
      t'.totalSupply = t.totalSupply + v := by
  unfold ozMint at h
  split_ifs at h with hd
  unfold ozUpdate at h
  obtain ⟨t1, h1, rfl⟩ := Option.map_eq_some_iff.1 h
  simp only [hd, ↓reduceIte] at h1 ⊢
  split_ifs at h1 with hv
  cases h1
  exact ⟨hd, not_lt.1 hv, rfl, rfl⟩

theorem ozBurn_eq_some {t t' : Token A} {src : A} {v : ℕ} (h : t.ozBurn src v = some t') :
    src ≠ 0 ∧ v ≤ t.balanceOf src ∧ t'.balanceOf = t.balanceOf - single src v ∧
      t'.totalSupply = t.totalSupply - v := by
  unfold ozBurn at h
  split_ifs at h with hs
  unfold ozUpdate at h
  obtain ⟨t1, h1, rfl⟩ := Option.map_eq_some_iff.1 h
  simp only [hs, ↓reduceIte] at h1 ⊢
  split_ifs at h1 with hv
  cases h1
  exact ⟨hs, not_lt.1 hv, rfl, rfl⟩

theorem ozSpend_eq_some {t t' : Token A} {o sp : A} {v : ℕ} (h : t.ozSpend o sp v = some t') :
    t'.balanceOf = t.balanceOf ∧ t'.totalSupply = t.totalSupply := by
  unfold ozSpend at h
  split_ifs at h
  · unfold ozApprove at h
    split_ifs at h
    cases h; exact ⟨rfl, rfl⟩
  · cases h; exact ⟨rfl, rfl⟩

theorem ozTransferFrom_eq_some {t t' : Token A} {sp src dst : A} {v : ℕ}
    (h : t.ozTransferFrom sp src dst v = some t') :
    v ≤ t.balanceOf src ∧ t'.balanceOf = t.balanceOf - single src v + single dst v ∧
      t'.totalSupply = t.totalSupply := by
  unfold ozTransferFrom at h
  obtain ⟨t1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨e1, e2⟩ := ozSpend_eq_some h1
  obtain ⟨-, -, hv, hb, hs⟩ := ozTransfer_eq_some h2
  exact ⟨e1 ▸ hv, by rw [hb, e1], hs.trans e2⟩

end Oz

end Token

end EvmLeanSpecs.Vault
