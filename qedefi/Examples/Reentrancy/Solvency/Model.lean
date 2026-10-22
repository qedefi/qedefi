import Examples.Reentrancy.Solvency.Deps
import EvmLogic.Program.Reentrancy.Value
import EvmLogic.Solidity.Layout

/-!
# Bank solvency as a world invariant

The banks of `contracts/src/reentrancy/Banks.sol` keep `mapping(address => uint256) balances`
at slot `base` and hold ether for it. `Solvent crypto base code bank w`:

* the bank's code is `code`;
* **what it owes is backed**: the sum of its balance entries is at most its ether balance;
* that sum is below `2²⁵⁶` (it fits a word);
* all ether in the world is below `2²⁵⁶` (no balance can wrap around when ether moves in).

The sum is over the **slots** of the entries (`balanceSlots`, the image of all addresses), so it
needs no Keccak non-collision hypothesis: two addresses whose entries collide share one balance,
counted once. Under injectivity it is the sum over addresses (`owed_eq_sum_addresses`).

`goodOps_solvent`: `Solvent` is closed under every world change arbitrary code can make
(`GoodOps`), so it can be the invariant of the ether-aware havoc theorem
(`EvmLogic.Program.Reentrancy.Value`). The remaining lemmas describe a bank's own writes.
-/

namespace Examples.Reentrancy.Solvency
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
  EvmLogic.Program.Reentrancy EvmLogic.Solidity

/-! ## Sums over addresses -/

/-- Updating one point of a function changes its sum by the difference. -/
theorem sum_update_add (f : Address → Nat) (a : Address) (v : Nat) :
    (∑ b, Function.update f a v b) + f a = (∑ b, f b) + v := by
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ a),
    ← Finset.add_sum_erase Finset.univ (Function.update f a v) (Finset.mem_univ a)]
  have : ∑ x ∈ Finset.univ.erase a, Function.update f a v x =
      ∑ x ∈ Finset.univ.erase a, f x :=
    Finset.sum_congr rfl fun x hx => Function.update_of_ne (Finset.ne_of_mem_erase hx) _ _
  rw [this, Function.update_self]
  omega

/-- One term is at most the sum. -/
theorem le_sum (f : Address → Nat) (a : Address) : f a ≤ ∑ b, f b :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

/-- Two terms are at most the sum. -/
theorem add_le_sum (f : Address → Nat) {a b : Address} (h : a ≠ b) : f a + f b ≤ ∑ x, f x := by
  rw [← Finset.sum_pair h]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-! ## Words -/

theorem toNat_sub_of_le {x y : Word} (h : y.toNat ≤ x.toNat) : (x - y).toNat = x.toNat - y.toNat := by
  rw [BitVec.toNat_sub]
  have := x.isLt
  rw [show 2 ^ 256 - y.toNat + x.toNat = (x.toNat - y.toNat) + 2 ^ 256 by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem toNat_add_of_lt {x y : Word} (h : x.toNat + y.toNat < 2 ^ 256) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

/-! ## Ether -/

/-- All ether in the world. -/
def supply (w : World) : Nat := ∑ a : Address, (w.balance a).toNat

/-- A self-transfer of an affordable amount changes no balance. -/
theorem balance_moveEther_self (w : World) (a : Address) {v : Word} (b : Address) :
    (moveEther w a a v).balance b = w.balance b := by
  unfold moveEther
  rw [balance_modifyState]
  have h1 := balance_modifyState w a (fun acc => { acc with balance := acc.balance - v })
  by_cases hb : b = a
  · subst hb
    simp only [ite_true] at h1 ⊢
    show (modifyState w b _).balance b + v = w.balance b
    simp only [h1, ite_true]; exact BitVec.sub_add_cancel _ _
  · simp only [hb, ite_false]
    rw [h1]; simp [hb]

theorem supply_moveEther {w : World} {src dst : Address} {v : Word}
    (hv : v.toNat ≤ (w.balance src).toNat) (hs : supply w < 2 ^ 256) :
    supply (moveEther w src dst v) = supply w := by
  by_cases hsd : src = dst
  · subst hsd; simp only [supply, balance_moveEther_self]
  have hds : dst ≠ src := fun h => hsd h.symm
  let f : Address → Nat := fun b => (w.balance b).toNat
  have h2 := add_le_sum f hsd
  have hdst : (w.balance dst).toNat + v.toNat < 2 ^ 256 := by
    simp only [supply] at hs; simp only [f] at h2; omega
  have hb : ∀ b, ((moveEther w src dst v).balance b).toNat =
      Function.update (Function.update f src (f src - v.toNat)) dst (f dst + v.toNat) b := by
    intro b
    rw [balance_moveEther w v hsd]
    by_cases h1 : b = dst
    · subst h1; simp [hds, f, toNat_add_of_lt hdst]
    · by_cases h0 : b = src
      · subst h0; simp [h1, f, toNat_sub_of_le hv]
      · simp [h0, h1, f]
  have e1 := sum_update_add (Function.update f src (f src - v.toNat)) dst (f dst + v.toNat)
  have e2 := sum_update_add f src (f src - v.toNat)
  rw [Function.update_of_ne hds] at e1
  have : supply (moveEther w src dst v) =
      ∑ b, Function.update (Function.update f src (f src - v.toNat)) dst (f dst + v.toNat) b :=
    Finset.sum_congr rfl fun b _ => hb b
  rw [this]
  simp only [supply]
  simp only [f] at e1 e2 hv ⊢
  omega

theorem supply_setAccountBalance_zero (w : World) (a : Address) :
    supply (setAccountBalance w a 0) ≤ supply w := by
  let f : Address → Nat := fun b => (w.balance b).toNat
  have hb : ∀ b, ((setAccountBalance w a 0).balance b).toNat = Function.update f a 0 b := by
    intro b
    simp only [setAccountBalance, balance_modifyState]
    by_cases h : b = a
    · subst h; simp
    · simp [h, f]
  have e := sum_update_add f a 0
  have : supply (setAccountBalance w a 0) = ∑ b, Function.update f a 0 b :=
    Finset.sum_congr rfl fun b _ => hb b
  rw [this]; simp only [supply]; simp only [f] at e ⊢; omega

theorem supply_sstore (w : World) (a : Address) (k v : Word) :
    supply (w.sstore a k v) = supply w := by
  simp [supply, World.balance_sstore]

theorem supply_incrementNonce (w : World) (a : Address) :
    supply (incrementNonce w a) = supply w := by
  simp [supply, balance_incrementNonce]

theorem balance_setCode (w : World) (a : Address) (c : ByteArray) (b : Address) :
    (setCode w a c).balance b = w.balance b := by
  simp only [setCode, balance_modifyState]
  split
  · subst_vars; rfl
  · rfl

theorem supply_setCode (w : World) (a : Address) (c : ByteArray) :
    supply (setCode w a c) = supply w := by
  simp [supply, balance_setCode]

/-! ## What a bank owes -/

/-- The slots of `balances[a]`, for every address `a`, of a mapping at slot `base`. -/
def balanceSlots (crypto : Crypto) (base : Word) : Finset Word :=
  Finset.univ.image fun a : Address => mappingSlot crypto (Word.ofAddress a) base

/-- What `bank` owes: the sum of its balance entries (each slot once). -/
def owed (crypto : Crypto) (base : Word) (bank : Address) (w : World) : Nat :=
  ∑ s ∈ balanceSlots crypto base, (w.sload bank s).toNat

theorem mem_balanceSlots (crypto : Crypto) (base : Word) (a : Address) :
    mappingSlot crypto (Word.ofAddress a) base ∈ balanceSlots crypto base :=
  Finset.mem_image_of_mem _ (Finset.mem_univ a)

/-- Under injectivity of the entries' slots, what the bank owes is the sum over addresses. -/
theorem owed_eq_sum_addresses {crypto : Crypto} {base : Word} {bank : Address} (w : World)
    (hinj : Function.Injective fun a : Address => mappingSlot crypto (Word.ofAddress a) base) :
    owed crypto base bank w =
      ∑ a : Address, (w.sload bank (mappingSlot crypto (Word.ofAddress a) base)).toNat := by
  unfold owed balanceSlots
  rw [Finset.sum_image fun x _ y _ h => hinj h]

theorem owed_keep {crypto : Crypto} {base : Word} {bank : Address} {w w' : World}
    (h : Keep bank w w') : owed crypto base bank w' = owed crypto base bank w := by
  unfold owed
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [World.sload, h.1]

theorem sload_le_owed {crypto : Crypto} {base : Word} {bank : Address} (w : World) (a : Address) :
    (w.sload bank (mappingSlot crypto (Word.ofAddress a) base)).toNat ≤ owed crypto base bank w :=
  Finset.single_le_sum (f := fun s => (w.sload bank s).toNat) (fun _ _ => Nat.zero_le _)
    (mem_balanceSlots crypto base a)

/-- Writing one balance entry changes what the bank owes by the difference. -/
theorem owed_sstore {crypto : Crypto} {base : Word} {bank : Address} (w : World) (a : Address)
    (v : Word) :
    owed crypto base bank (w.sstore bank (mappingSlot crypto (Word.ofAddress a) base) v) +
        (w.sload bank (mappingSlot crypto (Word.ofAddress a) base)).toNat =
      owed crypto base bank w + v.toNat := by
  unfold owed
  have hs := mem_balanceSlots crypto base a
  rw [← Finset.add_sum_erase _ _ hs, ← Finset.add_sum_erase _ (fun s => (w.sload bank s).toNat) hs]
  have : ∑ x ∈ (balanceSlots crypto base).erase (mappingSlot crypto (Word.ofAddress a) base),
      ((w.sstore bank (mappingSlot crypto (Word.ofAddress a) base) v).sload bank x).toNat =
      ∑ x ∈ (balanceSlots crypto base).erase (mappingSlot crypto (Word.ofAddress a) base),
      (w.sload bank x).toNat :=
    Finset.sum_congr rfl fun x hx => by
      rw [World.sload_sstore_ne_key _ _ _ (Finset.ne_of_mem_erase hx)]
  rw [this, World.sload_sstore_self]
  omega

/-- Writing a slot outside the balance entries does not change what the bank owes. -/
theorem owed_sstore_other {crypto : Crypto} {base : Word} {bank : Address} (w : World) {k : Word}
    (hk : k ∉ balanceSlots crypto base) (v : Word) :
    owed crypto base bank (w.sstore bank k v) = owed crypto base bank w := by
  unfold owed
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [World.sload_sstore_ne_key _ _ _ (fun h => hk (by rw [← h]; exact hs))]

/-! ## Solvency -/

/-- **The bank is solvent**: its code is `code`, what it owes is backed by its ether and fits a
word, and all ether fits a word. -/
structure Solvent (crypto : Crypto) (base : Word) (code : ByteArray) (bank : Address) (w : World) :
    Prop where
  /-- The bank's code. -/
  code : w.code bank = code
  /-- What it owes is backed by its ether. -/
  backed : owed crypto base bank w ≤ (w.balance bank).toNat
  /-- What it owes fits a word. -/
  bounded : owed crypto base bank w < 2 ^ 256
  /-- All ether fits a word. -/
  capped : supply w < 2 ^ 256

variable {crypto : Crypto} {base : Word} {code : ByteArray} {bank : Address}

/-- A world agreeing with a solvent one on the bank's storage, code and ether, with no more
ether in all, is solvent. -/
theorem Solvent.of_keep {w w' : World} (h : Solvent crypto base code bank w) (hk : Keep bank w w')
    (hb : w'.balance bank = w.balance bank) (hs : supply w' ≤ supply w) :
    Solvent crypto base code bank w' where
  code := by rw [hk.code]; exact h.code
  backed := by rw [owed_keep hk, hb]; exact h.backed
  bounded := by rw [owed_keep hk]; exact h.bounded
  capped := Nat.lt_of_le_of_lt hs h.capped

/-- **Solvency is closed under everything arbitrary code does** (`GoodOps`), for a bank whose
code is not empty and no EIP-7702 designator. -/
theorem goodOps_solvent (hsize : code.size ≠ 0) (hdel : delegatedAddress? code = none) :
    GoodOps (· = bank) (Solvent crypto base code bank) where
  code w h p hp := by subst hp; rw [h.code]; exact hsize
  deleg w h p hp := by subst hp; rw [h.code]; exact hdel
  sstore w a k v h ha :=
    h.of_keep (keep_sstore (Ne.symm ha)) (World.balance_sstore _ _ _ _ _)
      (Nat.le_of_eq (supply_sstore _ _ _ _))
  nonce w a h :=
    h.of_keep (keep_incrementNonce (by rw [h.code]; exact hsize)) (balance_incrementNonce _ _ _)
      (Nat.le_of_eq (supply_incrementNonce _ _))
  move w src dst v h hv hsrc := by
    have hk : Keep bank w (moveEther w src dst v) := keep_moveEther (by rw [h.code]; exact hsize)
    have hsup := supply_moveEther (dst := dst) hv h.capped
    by_cases hsd : src = dst
    · subst hsd
      exact h.of_keep hk (balance_moveEther_self _ _ _) (Nat.le_of_eq hsup)
    have hsb : src ≠ bank := by
      rcases hsrc with hs | hs
      · exact hs
      · exact absurd hs.symm hsd
    by_cases hdb : dst = bank
    · subst hdb
      have hbal : (moveEther w src dst v).balance dst = w.balance dst + v := by
        rw [balance_moveEther w v hsd]; simp [Ne.symm hsd]
      have h2 := add_le_sum (fun b => (w.balance b).toNat) hsd
      have hlt : (w.balance dst).toNat + v.toNat < 2 ^ 256 := by
        have := h.capped; simp only [supply] at this; omega
      refine ⟨by rw [hk.code]; exact h.code, ?_, by rw [owed_keep hk]; exact h.bounded,
        by rw [hsup]; exact h.capped⟩
      rw [owed_keep hk, hbal, toNat_add_of_lt hlt]
      exact Nat.le_add_right_of_le h.backed
    · refine h.of_keep hk ?_ (Nat.le_of_eq hsup)
      rw [balance_moveEther w v hsd]; simp [Ne.symm hsb, Ne.symm hdb]
  burn w a h ha := by
    refine h.of_keep (keep_setAccountBalance (by rw [h.code]; exact hsize)) ?_
      (supply_setAccountBalance_zero _ _)
    simp only [setAccountBalance, balance_modifyState, Ne.symm ha, ite_false]
  setCode w a c h ha :=
    h.of_keep (keep_setCode (Ne.symm ha)) (balance_setCode _ _ _ _)
      (Nat.le_of_eq (supply_setCode _ _ _))

/-! ## Conditions the banks check -/

theorem iszero_ne_zero {x : Word} (h : Word.iszero x ≠ 0) : x = 0 := by
  unfold Word.iszero Word.ofBool at h
  split at h
  · rename_i hx; simpa using hx
  · exact absurd rfl h

theorem iszero_eq_zero {x : Word} (h : Word.iszero x = 0) : x ≠ 0 := by
  intro hx; subst hx; exact absurd h (by decide)

theorem gt_eq_zero {x y : Word} (h : Word.gt x y = 0) : x.toNat ≤ y.toNat := by
  unfold Word.gt Word.ofBool at h
  split at h
  · exact absurd h (by decide)
  · rename_i hlt
    simp only [BitVec.ult, decide_eq_true_eq] at hlt
    omega

/-- The checked addition of a deposit did not overflow. -/
theorem toNat_add_of_not_gt {x v : Word} (h : (Word.gt x (v + x)).iszero ≠ 0) :
    (v + x).toNat = v.toNat + x.toNat ∧ v.toNat + x.toNat < 2 ^ 256 := by
  have h1 := gt_eq_zero (iszero_ne_zero h)
  rw [BitVec.toNat_add] at h1 ⊢
  have := v.isLt
  have := x.isLt
  by_cases hlt : v.toNat + x.toNat < 2 ^ 256
  · exact ⟨Nat.mod_eq_of_lt hlt, hlt⟩
  · rw [show v.toNat + x.toNat = (v.toNat + x.toNat - 2 ^ 256) + 2 ^ 256 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h1
    omega

/-! ## A bank's frame -/

/-- The value transfer that starts a bank's frame: the bank's storage and code are kept, its
ether grows by the value, all ether is kept. -/
theorem transferValue_in (hsize : code.size ≠ 0) {w : World} {msg : Message}
    (h : Solvent crypto base code bank w) (htgt : msg.currentTarget = bank)
    (hc : msg.caller ≠ bank) (hstv : msg.shouldTransferValue = true)
    (haff : msg.value ≠ 0 → msg.value.toNat ≤ (w.balance msg.caller).toNat) :
    Keep bank w (transferValue w msg) ∧
      ((transferValue w msg).balance bank).toNat = (w.balance bank).toNat + msg.value.toNat ∧
      supply (transferValue w msg) = supply w := by
  have hcode : (w.code bank).size ≠ 0 := by rw [h.code]; exact hsize
  unfold transferValue
  split
  · rename_i hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    have hb := haff hv.2
    refine ⟨keep_moveEther hcode, ?_, supply_moveEther hb h.capped⟩
    rw [htgt, balance_moveEther w _ hc]
    simp only [Ne.symm hc, ite_false, ite_true]
    have h2 := add_le_sum (fun b => (w.balance b).toNat) hc
    have := h.capped
    simp only [supply] at this
    exact toNat_add_of_lt (by omega)
  · rename_i hv
    simp only [hstv, Bool.true_and, decide_eq_true_eq, Classical.not_not] at hv
    exact ⟨keep_refl _ _, by rw [hv]; simp, rfl⟩

/-- **A deposit keeps the bank solvent**: the world after the transfer of `msg.value` into the
bank, with the caller's entry increased by `msg.value` (no overflow). -/
theorem solvent_deposit (hsize : code.size ≠ 0) {w : World} {msg : Message}
    (h : Solvent crypto base code bank w) (htgt : msg.currentTarget = bank)
    (hc : msg.caller ≠ bank) (hstv : msg.shouldTransferValue = true)
    (haff : msg.value ≠ 0 → msg.value.toNat ≤ (w.balance msg.caller).toNat)
    (hno : (Word.gt ((transferValue w msg).sload bank
        (mappingSlot crypto (Word.ofAddress msg.caller) base))
      (msg.value + (transferValue w msg).sload bank
        (mappingSlot crypto (Word.ofAddress msg.caller) base))).iszero ≠ 0) :
    Solvent crypto base code bank ((transferValue w msg).sstore bank
      (mappingSlot crypto (Word.ofAddress msg.caller) base)
      (msg.value + (transferValue w msg).sload bank
        (mappingSlot crypto (Word.ofAddress msg.caller) base))) := by
  obtain ⟨hk, hb, hs⟩ := transferValue_in hsize h htgt hc hstv haff
  obtain ⟨hadd, hlt⟩ := toNat_add_of_not_gt hno
  have ho := owed_sstore (crypto := crypto) (base := base) (bank := bank) (transferValue w msg)
    msg.caller (msg.value + (transferValue w msg).sload bank
      (mappingSlot crypto (Word.ofAddress msg.caller) base))
  rw [hadd, owed_keep hk] at ho
  have hbal := ((transferValue w msg).sstore bank
    (mappingSlot crypto (Word.ofAddress msg.caller) base) (msg.value + (transferValue w msg).sload
      bank (mappingSlot crypto (Word.ofAddress msg.caller) base))).balance bank |>.isLt
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [World.code_sstore, hk.code, h.code]
  · rw [World.balance_sstore, hb]; have := h.backed; omega
  · rw [World.balance_sstore] at hbal; have := h.backed; omega
  · rw [supply_sstore, hs]; exact h.capped

/-- **A withdrawal's call site**: with the caller's entry zeroed, the bank is solvent, and stays
so after sending the entry's old value to the caller. -/
theorem solvent_withdraw (hsize : code.size ≠ 0) {w : World} {a : Address}
    (h : Solvent crypto base code bank w) (ha : a ≠ bank) :
    Solvent crypto base code bank (w.sstore bank (mappingSlot crypto (Word.ofAddress a) base) 0) ∧
    ((w.sload bank (mappingSlot crypto (Word.ofAddress a) base)).toNat ≤
        ((w.sstore bank (mappingSlot crypto (Word.ofAddress a) base) 0).balance bank).toNat →
      Solvent crypto base code bank (moveEther (w.sstore bank (mappingSlot crypto
        (Word.ofAddress a) base) 0) bank a (w.sload bank (mappingSlot crypto (Word.ofAddress a)
          base)))) := by
  have ho := owed_sstore (crypto := crypto) (base := base) (bank := bank) w a 0
  rw [show (0 : Word).toNat = 0 from rfl, Nat.add_zero] at ho
  have hle := sload_le_owed (crypto := crypto) (base := base) (bank := bank) w a
  have h0 : Solvent crypto base code bank (w.sstore bank (mappingSlot crypto
      (Word.ofAddress a) base) 0) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [World.code_sstore, h.code]
    · rw [World.balance_sstore]; have := h.backed; omega
    · have := h.bounded; omega
    · rw [supply_sstore]; exact h.capped
  refine ⟨h0, fun hb => ?_⟩
  have hk : Keep bank (w.sstore bank (mappingSlot crypto (Word.ofAddress a) base) 0)
      (moveEther (w.sstore bank (mappingSlot crypto (Word.ofAddress a) base) 0) bank a
        (w.sload bank (mappingSlot crypto (Word.ofAddress a) base))) :=
    keep_moveEther (by rw [World.code_sstore, h.code]; exact hsize)
  refine ⟨by rw [hk.code]; exact h0.code, ?_, by rw [owed_keep hk]; exact h0.bounded,
    by rw [supply_moveEther hb h0.capped]; exact h0.capped⟩
  rw [owed_keep hk, balance_moveEther _ _ (Ne.symm ha)]
  simp only [ite_true]
  rw [toNat_sub_of_le hb, World.balance_sstore]
  rw [World.balance_sstore] at hb
  have := h.backed
  omega

/-! ## Writes outside the balance entries, credits -/

/-- A write outside the balance entries keeps the bank solvent. -/
theorem Solvent.sstore_other {w : World} (h : Solvent crypto base code bank w) {k : Word}
    (hk : k ∉ balanceSlots crypto base) (v : Word) :
    Solvent crypto base code bank (w.sstore bank k v) where
  code := by rw [World.code_sstore]; exact h.code
  backed := by rw [owed_sstore_other w hk, World.balance_sstore]; exact h.backed
  bounded := by rw [owed_sstore_other w hk]; exact h.bounded
  capped := by rw [supply_sstore]; exact h.capped

/-- **Crediting `v` to an entry** keeps the bank solvent when its ether already covers what it
owes plus `v` and the checked addition did not overflow. -/
theorem solvent_credit {w : World} {a : Address} {v : Word} (hcode : w.code bank = code)
    (hcap : supply w < 2 ^ 256)
    (hb : owed crypto base bank w + v.toNat ≤ (w.balance bank).toNat)
    (hno : (Word.gt (w.sload bank (mappingSlot crypto (Word.ofAddress a) base))
      (v + w.sload bank (mappingSlot crypto (Word.ofAddress a) base))).iszero ≠ 0) :
    Solvent crypto base code bank (w.sstore bank (mappingSlot crypto (Word.ofAddress a) base)
      (v + w.sload bank (mappingSlot crypto (Word.ofAddress a) base))) := by
  obtain ⟨hadd, hlt⟩ := toNat_add_of_not_gt hno
  have ho := owed_sstore (crypto := crypto) (base := base) (bank := bank) w a
    (v + w.sload bank (mappingSlot crypto (Word.ofAddress a) base))
  rw [hadd] at ho
  have hbal := (w.balance bank).isLt
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [World.code_sstore, hcode]
  · rw [World.balance_sstore]; omega
  · omega
  · rw [supply_sstore]; exact hcap

/-- The ether entering a bank's frame covers what it owes plus the value. -/
theorem backed_transferValue (hsize : code.size ≠ 0) {w : World} {msg : Message}
    (h : Solvent crypto base code bank w) (htgt : msg.currentTarget = bank)
    (hc : msg.caller ≠ bank) (hstv : msg.shouldTransferValue = true)
    (haff : msg.value ≠ 0 → msg.value.toNat ≤ (w.balance msg.caller).toNat) :
    owed crypto base bank (transferValue w msg) + msg.value.toNat ≤
      ((transferValue w msg).balance bank).toNat := by
  obtain ⟨hk, hb, -⟩ := transferValue_in hsize h htgt hc hstv haff
  rw [owed_keep hk, hb]; have := h.backed; omega

/-! ## A held lock -/

/-- While a guarded bank's lock is held: its storage and code are those of `w₀`, it holds at
least `L` wei, and all ether fits a word. -/
structure Locked (bank : Address) (w₀ : World) (L : Nat) (w : World) : Prop where
  /-- The bank's storage and code are those of `w₀`. -/
  keep : Keep bank w₀ w
  /-- The bank holds at least `L` wei. -/
  floor : L ≤ (w.balance bank).toNat
  /-- All ether fits a word. -/
  capped : supply w < 2 ^ 256

/-- **`Locked` is closed under everything arbitrary code does** (`GoodOps`). -/
theorem goodOps_locked {w₀ : World} {L : Nat} (hsize : (w₀.code bank).size ≠ 0)
    (hdel : delegatedAddress? (w₀.code bank) = none) : GoodOps (· = bank) (Locked bank w₀ L) where
  code w h p hp := by subst hp; rw [h.keep.code]; exact hsize
  deleg w h p hp := by subst hp; rw [h.keep.code]; exact hdel
  sstore w a k v h ha := ⟨h.keep.trans (keep_sstore (Ne.symm ha)),
    by rw [World.balance_sstore]; exact h.floor, by rw [supply_sstore]; exact h.capped⟩
  nonce w a h := ⟨h.keep.trans (keep_incrementNonce (by rw [h.keep.code]; exact hsize)),
    by rw [balance_incrementNonce]; exact h.floor, by rw [supply_incrementNonce]; exact h.capped⟩
  move w src dst v h hv hsrc := by
    have hk : Keep bank w (moveEther w src dst v) :=
      keep_moveEther (by rw [h.keep.code]; exact hsize)
    refine ⟨h.keep.trans hk, ?_, by rw [supply_moveEther hv h.capped]; exact h.capped⟩
    by_cases hsd : src = dst
    · subst hsd; rw [balance_moveEther_self]; exact h.floor
    have hsb : src ≠ bank := by
      rcases hsrc with hs | hs
      · exact hs
      · exact absurd hs.symm hsd
    rw [balance_moveEther w v hsd]
    by_cases hdb : bank = dst
    · subst hdb
      simp only [Ne.symm hsb, ite_false, ite_true]
      have h2 := add_le_sum (fun b => (w.balance b).toNat) hsd
      have := h.capped; simp only [supply] at this
      rw [toNat_add_of_lt (by omega)]
      exact Nat.le_add_right_of_le h.floor
    · simp only [Ne.symm hsb, hdb, ite_false]; exact h.floor
  burn w a h ha := by
    refine ⟨h.keep.trans (keep_setAccountBalance (by rw [h.keep.code]; exact hsize)), ?_,
      Nat.lt_of_le_of_lt (supply_setAccountBalance_zero _ _) h.capped⟩
    simp only [setAccountBalance, balance_modifyState, Ne.symm ha, ite_false]; exact h.floor
  setCode w a c h ha := ⟨h.keep.trans (keep_setCode (Ne.symm ha)),
    by rw [balance_setCode]; exact h.floor, by rw [supply_setCode]; exact h.capped⟩

/-- **Releasing the lock after a withdrawal**: if, at the call, the bank was backed and at
least its ether minus the entry's old value is left whatever the callee did, zeroing the entry
leaves it solvent. -/
theorem solvent_unlock {w₀ w : World} {a : Address} (hcode : w₀.code bank = code)
    (h0 : owed crypto base bank w₀ ≤ (w₀.balance bank).toNat)
    (hl : Locked bank w₀ ((w₀.balance bank).toNat -
      (w₀.sload bank (mappingSlot crypto (Word.ofAddress a) base)).toNat) w) :
    Solvent crypto base code bank (w.sstore bank (mappingSlot crypto (Word.ofAddress a) base) 0) := by
  have ho := owed_sstore (crypto := crypto) (base := base) (bank := bank) w a 0
  rw [show (0 : Word).toNat = 0 from rfl, Nat.add_zero, owed_keep hl.keep] at ho
  have hs : w.sload bank (mappingSlot crypto (Word.ofAddress a) base) =
      w₀.sload bank (mappingSlot crypto (Word.ofAddress a) base) := hl.keep.sload _
  rw [hs] at ho
  have hle := sload_le_owed (crypto := crypto) (base := base) (bank := bank) w₀ a
  have hbal := (w₀.balance bank).isLt
  have hf := hl.floor
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [World.code_sstore, hl.keep.code, hcode]
  · rw [World.balance_sstore]; omega
  · omega
  · rw [supply_sstore]; exact hl.capped

end Examples.Reentrancy.Solvency
