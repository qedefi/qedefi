import Verified.WeirdERC20.USDT.Spec.OpModel

/-!
# USDT's admin entry points satisfy `OpSpec`

`usdt_ops`: every calldata `ops` decodes (`issue`, `redeem`, `addBlackList`, `removeBlackList`,
`destroyBlackFunds`, `setParams`, without value) whose account is an actor ends as the model's
operation: it fails when the model's operation fails, and otherwise succeeds with the model's
state and only the footprint changed; static or below `g₀` it may fail. The code's conditions
(`issueOk`, …) are the model's: the owner is the model's `admin`; `require(supply + v > supply)`
is `v ≠ 0` and no overflow, and the owner's balance cannot overflow first under the actors'
supply bound; `redeem`'s `supply ≥ v` follows from the balance check under the same bound.
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open Verified.WeirdERC20.USDT.Contracts
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.Math QEDefi.ERC4626 Finsupp

/-- The low byte of a written `isBlackListed` row (`b ||| ~0xff & old`) is `b`. -/
theorem rowBool_set (b y : Word) (hb : b = 0#256 ∨ b = 1#256) :
    rowBool.get (b ||| 115792089237316195423570985008687907853269984665640564039457584007913129639680#256
      &&& y) = b := by
  rw [rowBool_get]
  have h1 : ∀ z : Word, z.div 1#256 = z := by
    intro z; apply BitVec.eq_of_toNat_eq; simp [Word.div]
  rw [h1, BitVec.and_or_distrib_left, ← BitVec.and_assoc,
    show (255#256 : Word) &&&
      115792089237316195423570985008687907853269984665640564039457584007913129639680#256 = 0#256
      by decide, BitVec.zero_and, BitVec.or_zero]
  rcases hb with h | h <;> subst h <;> decide

/-- **From an admin entry point's run to `OpSpec`'s outcome**: the code's condition `ok` fails
exactly when the model's operation does, and on success the world `W` reads as its state. -/
theorem opOut_spec {Act : Finset Address} {m mf : Machine} {o : Outcome} {e : Variant.Op Address}
    {ok : Prop} {W : World}
    (hnone : ¬ ok → M.op (pre usdtAbs Act m) e = none)
    (hsome : ok → ∃ s', M.op (pre usdtAbs Act m) e = some s' ∧
      read m.ctx.crypto Act W m.frame.msg.currentTarget = s' ∧
      FrameKeeps usdtAbs m.ctx.crypto Act m.frame.msg.currentTarget m.world W)
    (h : (Fails o ∧ m.frame.gasLeft < g₀) ∨ OpOut ok W m mf o) :
    OpMatches usdtAbs M Act e m mf o ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)) := by
  rcases h with ⟨hf, hlt⟩ | ⟨hst, hf⟩ | ⟨hn, hf⟩ | ⟨hok, ho, hwd, htr, hcr⟩
  · exact .inr ⟨hf, fun h => by omega⟩
  · exact .inr ⟨hf, fun h => by rw [h.2] at hst; cases hst⟩
  · left; unfold OpMatches; rw [hnone hn]; exact hf
  · obtain ⟨s', hop, hr, hk⟩ := hsome hok
    left; unfold OpMatches; rw [hop]
    exact ⟨ho, by rw [hwd]; exact hr, by rw [hwd]; exact hk, htr, hcr⟩

/-- The facts of a frame without value that `Start` admits. -/
theorem start_facts {Act : Finset Address} {m : Machine}
    (hs : Start USDT.runtimeCode usdtAbs M Act m) (hval : m.frame.msg.value = 0) :
    Live Act m.world m.frame.msg.currentTarget ∧
    pre usdtAbs Act m = readState m.ctx.crypto Act m.world m.frame.msg.currentTarget ∧
    QEDefi.ERC20.Spec.YAMV2.SubSupply
      (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget) := by
  obtain ⟨hlive, hpre⟩ := live_of_start hs
  have hw := world_of_start hs hval
  have hsub : QEDefi.ERC20.Spec.YAMV2.SubSupply (pre usdtAbs Act m) := hs.wf
  rw [hpre, ← hw] at hsub
  exact ⟨hw ▸ hlive, by rw [hpre, hw], hsub⟩

theorem fk_fixed {crypto : Crypto} {Act : Finset Address} {k : Word}
    (hk : k = 1 ∨ k = 3 ∨ k = 4) : footprint crypto Act k := by
  left; rw [mem_fixedSlots]; rcases hk with h | h | h <;> simp [h]

theorem supply_eq {crypto : Crypto} {Act : Finset Address} {w : World} {t : Address} :
    (readState crypto Act w t).supply = (w.sload t 1#256).toNat := rfl

section Ops

variable {crypto : Crypto} {Act : Finset Address} {w : World} {t : Address}

/-- **`issue(v)`.** -/
theorem issue_spec (hs : usdtAbs.Sound crypto Act) (hl : Live Act w t)
    (hsub : QEDefi.ERC20.Spec.YAMV2.SubSupply (readState crypto Act w t)) (c : Address)
    (v : Word) :
    (¬ issueOk crypto w t c v → M.op (readState crypto Act w t) (.mint c c v.toNat) = none) ∧
    (issueOk crypto w t c v → ∃ s', M.op (readState crypto Act w t) (.mint c c v.toNat) = some s' ∧
      read crypto Act (issueW crypto w t v) t = s' ∧
      FrameKeeps usdtAbs crypto Act t w (issueW crypto w t v)) := by
  set s := readState crypto Act w t with hs_def
  have ho : s.admin ∈ Act := hl.2.2
  have had : ownerA w t = s.admin := rfl
  have hB : (w.sload t (balKey crypto s.admin)).toNat = s.bal s.admin := (bal_eq ho).symm
  have hBS : s.bal s.admin ≤ s.supply :=
    le_trans (Token.le_total s.bal s.admin) hsub.1
  have hSM := hsub.2
  have hS : s.supply = (w.sload t 1#256).toNat := rfl
  simp only [MAX] at hSM
  rw [op_mint]
  unfold issueOk
  rw [had, lt_add_iff, lt_add_iff, hB, ← hS]
  constructor
  · intro hn
    have : ¬ (c = s.admin ∧ v.toNat ≠ 0 ∧ s.supply + v.toNat ≤ MAX) := by
      rintro ⟨h1, h2, h3⟩
      simp only [MAX] at h3
      exact hn ⟨h1, ⟨by omega, by omega⟩, by omega, by omega⟩
    simp only [this, ↓reduceIte]
  · rintro ⟨h1, ⟨h2, h3⟩, -⟩
    have hm : c = s.admin ∧ v.toNat ≠ 0 ∧ s.supply + v.toNat ≤ MAX :=
      ⟨h1, by omega, by simp only [MAX]; omega⟩
    rw [ite_eq_left hm]
    refine ⟨_, rfl, ?_⟩
    subst h1
    -- the owner's credit
    obtain ⟨hl1, hr1⟩ := read_bal_write hs ho hl (w.sload t (balKey crypto s.admin) + v)
    have hx1 : (w.sload t (balKey crypto s.admin) + v).toNat = s.bal s.admin + v.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega), hB]
    rw [hx1] at hr1
    set W1 := w.sstore t (balKey crypto s.admin) (w.sload t (balKey crypto s.admin) + v)
      with hW1
    have hs1 : W1.sload t 1#256 = w.sload t 1#256 := by
      have hs' : ActorRows crypto Act [balancesSlot, blackSlot] [allowedSlot] fixedSlots := hs
      exact World.sload_sstore_ne_key _ _ _
        (fun e => hs'.fixed1 balancesSlot (by simp) s.admin ho (by
          rw [← balKey_eq, ← e]; simp [fixedSlots, supplySlot]))
    -- the supply
    obtain ⟨hl2, hr2⟩ := write_fixed (k := 1#256) hs hl1 (.inl rfl) (W1.sload t 1#256 + v)
    have hx2 : (W1.sload t 1#256 + v).toNat = s.supply + v.toNat := by
      rw [hs1, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega), hS]
    have hW : issueW crypto w t v = W1.sstore t 1#256 (W1.sload t 1#256 + v) := rfl
    refine ⟨?_, ?_⟩
    · rw [hW, read_eq_of_live hl2, hr2, hr1, hx2]
      simp (config := { decide := true }) only [↓reduceIte]
      congr 1
      ext a
      simp only [Finsupp.update_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
      by_cases ha : a = s.admin
      · subst ha; simp
      · simp [ha, Ne.symm ha, ← hs_def]
    · rw [hW]
      exact FrameKeeps.sstore (FrameKeeps.sstore (frameKeeps_refl _ _ _ _)
        (.inr (.inl ⟨_, ho, rfl⟩)) _) (fk_fixed (.inl rfl)) _

/-- **`redeem(v)`.** -/
theorem redeem_spec (hs : usdtAbs.Sound crypto Act) (hl : Live Act w t)
    (hsub : QEDefi.ERC20.Spec.YAMV2.SubSupply (readState crypto Act w t)) (c : Address)
    (v : Word) :
    (¬ redeemOk crypto w t c v → M.op (readState crypto Act w t) (.burn c c v.toNat) = none) ∧
    (redeemOk crypto w t c v → ∃ s', M.op (readState crypto Act w t) (.burn c c v.toNat) = some s' ∧
      read crypto Act (redeemW crypto w t v) t = s' ∧
      FrameKeeps usdtAbs crypto Act t w (redeemW crypto w t v)) := by
  set s := readState crypto Act w t with hs_def
  have ho : s.admin ∈ Act := hl.2.2
  have had : ownerA w t = s.admin := rfl
  have hB : (w.sload t (balKey crypto s.admin)).toNat = s.bal s.admin := (bal_eq ho).symm
  have hBS : s.bal s.admin ≤ s.supply :=
    le_trans (Token.le_total s.bal s.admin) hsub.1
  have hS : s.supply = (w.sload t 1#256).toNat := rfl
  rw [op_burn]
  unfold redeemOk
  rw [had, hB, ← hS]
  constructor
  · intro hn
    have : ¬ (c = s.admin ∧ v.toNat ≤ s.bal c) := by
      rintro ⟨h1, h2⟩
      subst h1
      exact hn ⟨rfl, by omega, h2⟩
    simp only [this, ↓reduceIte]
  · rintro ⟨h1, h2, h3⟩
    subst h1
    have hm : s.admin = s.admin ∧ v.toNat ≤ s.bal s.admin := ⟨rfl, h3⟩
    rw [ite_eq_left hm]
    refine ⟨_, rfl, ?_⟩
    have hs' : ActorRows crypto Act [balancesSlot, blackSlot] [allowedSlot] fixedSlots := hs
    -- the supply
    obtain ⟨hl1, hr1⟩ := write_fixed (k := 1#256) hs hl (.inl rfl) (w.sload t 1#256 - v)
    have hx1 : (w.sload t 1#256 - v).toNat = s.supply - v.toNat := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega), hS]
    set W1 := w.sstore t 1#256 (w.sload t 1#256 - v) with hW1
    have hA1 : ownerA W1 t = s.admin := by
      have := congrArg VState.admin hr1
      simp only [readState] at this
      exact this
    have hb1 : W1.sload t (balKey crypto s.admin) = w.sload t (balKey crypto s.admin) :=
      World.sload_sstore_ne_key _ _ _ (fun e => hs'.fixed1 balancesSlot (by simp) s.admin ho (by
        rw [← balKey_eq, e]; simp [fixedSlots, supplySlot]))
    -- the owner's debit
    obtain ⟨hl2, hr2⟩ := read_bal_write hs ho hl1 (W1.sload t (balKey crypto s.admin) - v)
    have hx2 : (W1.sload t (balKey crypto s.admin) - v).toNat = s.bal s.admin - v.toNat := by
      rw [hb1, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega), hB]
    have hW : redeemW crypto w t v = W1.sstore t (balKey crypto (ownerA W1 t))
        (W1.sload t (balKey crypto (ownerA W1 t)) - v) := rfl
    rw [hA1] at hW
    refine ⟨?_, ?_⟩
    · rw [hW, read_eq_of_live hl2, hr2, hr1, hx2, hx1]
      simp (config := { decide := true }) only [↓reduceIte]
      congr 1
      ext a
      simp only [Finsupp.update_apply, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
      by_cases ha : a = s.admin
      · subst ha; simp
      · simp [ha, Ne.symm ha, ← hs_def]
    · rw [hW]
      exact FrameKeeps.sstore (FrameKeeps.sstore (frameKeeps_refl _ _ _ _)
        (fk_fixed (.inl rfl)) _) (.inr (.inl ⟨_, ho, rfl⟩)) _

/-- **`addBlackList(u)` / `removeBlackList(u)`.** -/
theorem blackSet_spec (hs : usdtAbs.Sound crypto Act) (hl : Live Act w t) (c : Address)
    {u : Address} (hu : u ∈ Act) (b : Bool) :
    (¬ c = ownerA w t →
      M.op (readState crypto Act w t) (.setBlacklisted c u b) = none) ∧
    (c = ownerA w t → ∃ s', M.op (readState crypto Act w t) (.setBlacklisted c u b) = some s' ∧
      read crypto Act (blackSetW crypto w t u (if b then 1#256 else 0#256)) t = s' ∧
      FrameKeeps usdtAbs crypto Act t w (blackSetW crypto w t u (if b then 1#256 else 0#256))) := by
  have had : ownerA w t = (readState crypto Act w t).admin := rfl
  rw [op_setBlacklisted, had]
  constructor
  · intro hn; simp only [hn, ↓reduceIte]
  · intro h1
    rw [ite_eq_left h1]
    refine ⟨_, rfl, ?_, ?_⟩
    · obtain ⟨hl1, hr1⟩ := write_black hs hl hu
        ((if b then 1#256 else 0#256) |||
          115792089237316195423570985008687907853269984665640564039457584007913129639680#256 &&&
            w.sload t (blackKey crypto u))
      unfold blackSetW
      rw [read_eq_of_live hl1, hr1, rowBool_set _ _ (by cases b <;> simp)]
      cases b <;> rfl
    · exact FrameKeeps.sstore (frameKeeps_refl _ _ _ _) (.inr (.inr (.inr ⟨u, hu, rfl⟩))) _

/-- **`destroyBlackFunds(u)`.** -/
theorem destroy_spec (hs : usdtAbs.Sound crypto Act) (hl : Live Act w t)
    (hsub : QEDefi.ERC20.Spec.YAMV2.SubSupply (readState crypto Act w t)) (c : Address)
    {u : Address} (hu : u ∈ Act) :
    (¬ destroyOk crypto w t c u →
      M.op (readState crypto Act w t) (.destroyBlackFunds c u) = none) ∧
    (destroyOk crypto w t c u → ∃ s',
      M.op (readState crypto Act w t) (.destroyBlackFunds c u) = some s' ∧
      read crypto Act (destroyW crypto w t u) t = s' ∧
      FrameKeeps usdtAbs crypto Act t w (destroyW crypto w t u)) := by
  set s := readState crypto Act w t with hs_def
  have had : ownerA w t = s.admin := rfl
  have hbu : (w.sload t (balKey crypto u)).toNat = s.bal u := (bal_eq hu).symm
  have hBS : s.bal u ≤ s.supply := le_trans (Token.le_total s.bal u) hsub.1
  have hS : s.supply = (w.sload t 1#256).toNat := rfl
  have hbl : s.blacklisted u = true ↔ blackW crypto w t u ≠ 0#256 := blacklisted_iff hu
  rw [op_destroy]
  unfold destroyOk
  rw [had, ← hbl]
  constructor
  · intro hn; simp only [hn, ↓reduceIte]
  · intro h1
    rw [ite_eq_left h1]
    refine ⟨_, rfl, ?_⟩
    have hs' : ActorRows crypto Act [balancesSlot, blackSlot] [allowedSlot] fixedSlots := hs
    obtain ⟨hl1, hr1⟩ := read_bal_write hs hu hl 0#256
    set W1 := w.sstore t (balKey crypto u) 0#256 with hW1
    have hs1 : W1.sload t 1#256 = w.sload t 1#256 :=
      World.sload_sstore_ne_key _ _ _ (fun e => hs'.fixed1 balancesSlot (by simp) u hu (by
        rw [← balKey_eq, ← e]; simp [fixedSlots, supplySlot]))
    obtain ⟨hl2, hr2⟩ := write_fixed (k := 1#256) hs hl1 (.inl rfl)
      (W1.sload t 1#256 - w.sload t (balKey crypto u))
    have hx2 : (W1.sload t 1#256 - w.sload t (balKey crypto u)).toNat = s.supply - s.bal u := by
      rw [hs1, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega), hS, hbu]
    have hW : destroyW crypto w t u =
        W1.sstore t 1#256 (W1.sload t 1#256 - w.sload t (balKey crypto u)) := rfl
    refine ⟨?_, ?_⟩
    · rw [hW, read_eq_of_live hl2, hr2, hr1, hx2]
      simp (config := { decide := true }) only [↓reduceIte]
      congr 1
      ext a
      simp only [Finsupp.update_apply, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
      by_cases ha : a = u
      · subst ha; simp
      · simp [ha, Ne.symm ha, ← hs_def]
    · rw [hW]
      exact FrameKeeps.sstore (FrameKeeps.sstore (frameKeeps_refl _ _ _ _)
        (.inr (.inl ⟨_, hu, rfl⟩)) _) (fk_fixed (.inl rfl)) _

/-- **`setParams(b, x)`.** -/
theorem params_spec (hs : usdtAbs.Sound crypto Act) (hl : Live Act w t) (c : Address)
    (b x : Word) :
    (¬ paramsOk w t c b x →
      M.op (readState crypto Act w t) (.setParams c b.toNat x.toNat) = none) ∧
    (paramsOk w t c b x → ∃ s',
      M.op (readState crypto Act w t) (.setParams c b.toNat x.toNat) = some s' ∧
      read crypto Act (paramsW w t b x) t = s' ∧
      FrameKeeps usdtAbs crypto Act t w (paramsW w t b x)) := by
  have had : ownerA w t = (readState crypto Act w t).admin := rfl
  rw [op_setParams]
  unfold paramsOk
  rw [had]
  constructor
  · intro hn; simp only [hn, ↓reduceIte]
  · intro h1
    rw [ite_eq_left h1]
    refine ⟨_, rfl, ?_⟩
    obtain ⟨-, -, hx⟩ := h1
    obtain ⟨hl1, hr1⟩ := write_fixed (k := 3#256) hs hl (.inr (.inl rfl)) b
    obtain ⟨hl2, hr2⟩ := write_fixed (k := 4#256) hs hl1 (.inr (.inr rfl)) (x * 1000000#256)
    have hxm : (x * 1000000#256).toNat = x.toNat * 10 ^ 6 := by
      rw [BitVec.toNat_mul, show (1000000#256 : Word).toNat = 10 ^ 6 from rfl,
        Nat.mod_eq_of_lt (by omega)]
    refine ⟨?_, ?_⟩
    · show read crypto Act ((w.sstore t 3#256 b).sstore t 4#256 (x * 1000000#256)) t = _
      rw [read_eq_of_live hl2, hr2, hr1, hxm]
      simp (config := { decide := true }) only [↓reduceIte]
    · exact FrameKeeps.sstore (FrameKeeps.sstore (frameKeeps_refl _ _ _ _)
        (fk_fixed (.inr (.inl rfl))) _) (fk_fixed (.inr (.inr rfl))) _

end Ops

/-- The address mask on a word: its address. -/
theorem mask_and (x : Word) :
    1461501637330902918203684832716283019655932542975#256 &&& x =
      Word.ofAddress (Word.toAddress x) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,
    show (1461501637330902918203684832716283019655932542975#256 : Word).toNat = 2 ^ 160 - 1
      from rfl, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
  simp only [Word.ofAddress, Word.toAddress, BitVec.toNat_setWidth]
  omega

/-- **`OpSpec` for USDT's admin entry points.** -/
theorem usdt_ops : OpSpec USDT.runtimeCode usdtAbs M g₀ ops opAddrs := by
  intro Act m e hs hop hA
  unfold ops at hop
  by_cases hbad : m.frame.msg.value.toNat ≠ 0 ∨ m.frame.msg.data.size < 4
  · simp only [hbad, ↓reduceIte] at hop; cases hop
  simp only [hbad, ↓reduceIte] at hop
  push Not at hbad
  obtain ⟨hv0, hsz⟩ := hbad
  have hval : m.frame.msg.value = 0 := BitVec.eq_of_toNat_eq (by simpa using hv0)
  obtain ⟨hl, hpre, hsub⟩ := start_facts hs hval
  have hg : g₀ ≤ m.frame.gasLeft + (g₀ - m.frame.gasLeft) := by omega
  split_ifs at hop with h1 h2 h3 h4 h5 h6
  · obtain rfl := Option.some.inj hop
    have hu : argAddr m.frame.msg.data 0 ∈ Act := hA _ (by simp [opAddrs])
    obtain ⟨hn, hsm⟩ := blackSet_spec (w := m.world) (t := m.frame.msg.currentTarget) hs.sound hl
      m.frame.msg.caller hu true
    simp only [↓reduceIte] at hsm
    refine (halts_of_high hs.fresh (Post := OpOut _ _ m) (fun _ _ _ h => opOut_halt h)
      (fun _ _ h => h) (blackSet_high m hs.fresh _ (argWord m.frame.msg.data 0)
        (argAddr m.frame.msg.data 0) 1#256 hg (.inl ⟨h1, rfl⟩) hsz hs.size rfl
        (mask_and _) hval)).mono fun mf o _ h => ?_
    exact opOut_spec (by rw [hpre]; exact hn) (by rw [hpre]; exact hsm) h
  · obtain rfl := Option.some.inj hop
    have hu : argAddr m.frame.msg.data 0 ∈ Act := hA _ (by simp [opAddrs])
    obtain ⟨hn, hsm⟩ := blackSet_spec (w := m.world) (t := m.frame.msg.currentTarget) hs.sound hl
      m.frame.msg.caller hu false
    simp only [Bool.false_eq_true, ↓reduceIte] at hsm
    refine (halts_of_high hs.fresh (Post := OpOut _ _ m) (fun _ _ _ h => opOut_halt h)
      (fun _ _ h => h) (blackSet_high m hs.fresh _ (argWord m.frame.msg.data 0)
        (argAddr m.frame.msg.data 0) 0#256 hg (.inr ⟨h2, rfl⟩) hsz hs.size rfl
        (mask_and _) hval)).mono fun mf o _ h => ?_
    exact opOut_spec (by rw [hpre]; exact hn) (by rw [hpre]; exact hsm) h
  · obtain rfl := Option.some.inj hop
    have hu : argAddr m.frame.msg.data 0 ∈ Act := hA _ (by simp [opAddrs])
    obtain ⟨hn, hsm⟩ := destroy_spec (w := m.world) (t := m.frame.msg.currentTarget) hs.sound hl
      hsub m.frame.msg.caller hu
    refine (halts_of_high hs.fresh (Post := OpOut _ _ m) (fun _ _ _ h => opOut_halt h)
      (fun _ _ h => h) (destroy_high m hs.fresh _ (argWord m.frame.msg.data 0)
        (argAddr m.frame.msg.data 0) hg h3 hsz hs.size rfl (mask_and _) hval
        (dep_of_start hs hval))).mono fun mf o _ h => ?_
    exact opOut_spec (by rw [hpre]; exact hn) (by rw [hpre]; exact hsm) h
  · obtain rfl := Option.some.inj hop
    obtain ⟨hn, hsm⟩ := params_spec (w := m.world) (t := m.frame.msg.currentTarget) hs.sound hl
      m.frame.msg.caller (argWord m.frame.msg.data 0) (argWord m.frame.msg.data 1)
    refine (halts_of_high hs.fresh (Post := OpOut _ _ m) (fun _ _ _ h => opOut_halt h)
      (fun _ _ h => h) (params_high m hs.fresh _ (argWord m.frame.msg.data 0)
        (argWord m.frame.msg.data 1) hg h4 hsz hs.size rfl rfl hl.2.1 hval)).mono
      fun mf o _ h => ?_
    exact opOut_spec (by rw [hpre]; exact hn) (by rw [hpre]; exact hsm) h
  · obtain rfl := Option.some.inj hop
    obtain ⟨hn, hsm⟩ := issue_spec (w := m.world) (t := m.frame.msg.currentTarget) hs.sound hl
      hsub m.frame.msg.caller (argWord m.frame.msg.data 0)
    refine (halts_of_high hs.fresh (Post := OpOut _ _ m) (fun _ _ _ h => opOut_halt h)
      (fun _ _ h => h) (issue_high m hs.fresh _ (argWord m.frame.msg.data 0) hg h5 hsz hs.size
        rfl hval)).mono fun mf o _ h => ?_
    exact opOut_spec (by rw [hpre]; exact hn) (by rw [hpre]; exact hsm) h
  · obtain rfl := Option.some.inj hop
    obtain ⟨hn, hsm⟩ := redeem_spec (w := m.world) (t := m.frame.msg.currentTarget) hs.sound hl
      hsub m.frame.msg.caller (argWord m.frame.msg.data 0)
    refine (halts_of_high hs.fresh (Post := OpOut _ _ m) (fun _ _ _ h => opOut_halt h)
      (fun _ _ h => h) (redeem_high m hs.fresh _ (argWord m.frame.msg.data 0) hg h6 hsz hs.size
        rfl hval)).mono fun mf o _ h => ?_
    exact opOut_spec (by rw [hpre]; exact hn) (by rw [hpre]; exact hsm) h

end Verified.WeirdERC20.USDT.Spec
