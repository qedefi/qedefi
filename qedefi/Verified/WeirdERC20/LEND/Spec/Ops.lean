import Verified.WeirdERC20.LEND.Spec.Fallback

/-!
# LEND under the spec: the sale and administration entry points

In the final sale state (the model's invariant) every purchase (`buyTokens()`,
`buyTokensPresale()`, `buyTokensICO()`) and every `setState(x)` reverts: the purchases require
`currentState` to be a sale state, `setState` requires the caller to be the manager and the
state not to be `ICOFinished`. The model says the same (`stepOp` is `none`), so for these only
the any-gas run is needed: the frame fails, whatever its gas. `setTokenManager(mgr)` by the
manager writes the low 160 bits of slot 5 (keeping the others), and reverts for anyone else.
-/

namespace Verified.WeirdERC20.LEND.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.LEND.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas

/-- A frame that can only fail, for any gas. -/
theorem halts_fails {m : Machine} (h : LowHalts m fun _ _ => False) : Halts m fun _ o => Fails o :=
  h _ ⟨fun _ _ => trivial, fun _ _ => trivial⟩ fun _ _ h => h.elim

/-- The manager as the code reads it (`slot5 / 256⁰ & mask & mask`). -/
theorem mask_div_one (x : Word) :
    1461501637330902918203684832716283019655932542975#256 &&&
      (1461501637330902918203684832716283019655932542975#256 &&& Word.div x 1#256) =
      Word.ofAddress (Word.toAddress x) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, Word.div, BitVec.toNat_udiv, BitVec.toNat_ofNat,
    Word.ofAddress, Word.toAddress, BitVec.toNat_setWidth]
  rw [show (1 : Nat) % 2 ^ 256 = 1 by decide, Nat.div_one,
    show (1461501637330902918203684832716283019655932542975 : Nat) % 2 ^ 256 = 2 ^ 160 - 1 by
      decide, ← Nat.and_assoc, Nat.and_self, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
  exact (Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))).symm

/-- The manager slot after `tokenManager = mgr`: its low 160 bits are `mgr`. -/
theorem toAddress_setManager (a : Address) (x : Word) :
    Word.toAddress (Word.ofAddress a * 1#256 |||
      115792089237316195423570985007226406215939081747436879206741300988257197096960#256 &&& x) =
      a := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  simp only [Word.toAddress, Word.ofAddress, BitVec.toNat_setWidth, BitVec.toNat_or,
    BitVec.toNat_and, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.or_mod_two_pow, Nat.and_mod_two_pow]
  rw [show (115792089237316195423570985007226406215939081747436879206741300988257197096960 : Nat) %
    2 ^ 256 % 2 ^ 160 = 0 by decide, Nat.zero_and, Nat.or_zero]
  have h1 : a.toNat % 2 ^ 256 = a.toNat := Nat.mod_eq_of_lt (by omega)
  simp only [h1, show (1 : Nat) % 2 ^ 256 = 1 by decide, Nat.mul_one, Nat.mod_eq_of_lt ha]

/-! ## Runs -/

set_option maxHeartbeats 0 in
/-- The purchases revert in the final state, at any gas. -/
theorem buy_low (m : Machine) (hf : Fresh LEND.runtimeCode m)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (h4 : 4 ≤ m.frame.msg.data.size)
    (hk : Abi.selectorOf m.frame.msg.data = 0xd0febe4c ∨
      Abi.selectorOf m.frame.msg.data = 0x1d511879 ∨ Abi.selectorOf m.frame.msg.data = 0xd7b91bcc)
    (hph : 255#256 &&& Word.div (m.world.sload m.frame.msg.currentTarget 3#256) 1#256 = 5#256) :
    LowHalts m fun _ _ => False := by
  intro H hF _
  apply WP.halts_of_false
  have hsel' := BNB.Spec.div_selector m.frame.msg.data
  have hz := BNB.Spec.calldatasize_ne (n := m.frame.msg.data.size) h4 hsz
  rcases hk with hk | hk | hk <;> rw [hk] at hsel' <;> solady_fresh_intro <;>
    hwp_steps [hsel', hz, hph]

set_option maxHeartbeats 0 in
/-- `setState(x)` reverts in the final state, at any gas. -/
theorem setState_low (m : Machine) (hf : Fresh LEND.runtimeCode m)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (h4 : 4 ≤ m.frame.msg.data.size)
    (hk : Abi.selectorOf m.frame.msg.data = 0x56de96db)
    (hph : 255#256 &&& Word.div (m.world.sload m.frame.msg.currentTarget 3#256) 1#256 = 5#256) :
    LowHalts m fun _ _ => False := by
  intro H hF _
  apply WP.halts_of_false
  have hsel' := BNB.Spec.div_selector m.frame.msg.data
  rw [hk] at hsel'
  have hz := BNB.Spec.calldatasize_ne (n := m.frame.msg.data.size) h4 hsz
  solady_fresh_intro
  hwp_steps [hsel', hz, hph, mask_div_one]

/-- `setTokenManager(a)`'s code-level end: anyone but the manager reverts; the manager's call
writes `a` into the low 160 bits of slot 5 and stops. -/
def TMPost (m : Machine) (a : Address) (mf : Machine) (o : Outcome) : Prop :=
  (m.frame.msg.caller ≠ Word.toAddress (m.world.sload m.frame.msg.currentTarget 5#256) →
    ∃ out, o = .revert out) ∧
  (m.frame.msg.caller = Word.toAddress (m.world.sload m.frame.msg.currentTarget 5#256) →
    m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧ (∃ out, o = .success out) ∧
    mf.world = m.world.sstore m.frame.msg.currentTarget 5#256 (Word.ofAddress a * 1#256 |||
      115792089237316195423570985007226406215939081747436879206741300988257197096960#256 &&&
        m.world.sload m.frame.msg.currentTarget 5#256) ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts)

theorem eq_addr_of {c d : Address} (h : (Word.eq (Word.ofAddress c) (Word.ofAddress d)).iszero.iszero ≠ 0) :
    c = d := by
  by_contra hne
  have : Word.ofAddress c ≠ Word.ofAddress d := fun e => hne (Word.ofAddress_injective e)
  exact h (by simp [Word.eq, Word.ofBool, Word.iszero]; exact this)

theorem eq_addr_zero {c d : Address} (h : c ≠ d) : Word.eq (Word.ofAddress c) (Word.ofAddress d) = 0 := by
  have : Word.ofAddress c ≠ Word.ofAddress d := fun e => h (Word.ofAddress_injective e)
  simp [Word.eq, Word.ofBool]; exact this

set_option maxHeartbeats 0 in
theorem setTokenManager_low (m : Machine) (a : Address) (hf : Fresh LEND.runtimeCode m)
    (hd : Args m.frame.msg.data 0x7cb2b79c [Word.ofAddress a])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (TMPost m a) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, Nat.mul_zero,
    Nat.add_zero] at hsize harg0
  have hsel' := BNB.Spec.div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := BNB.Spec.calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, mask_div_one, ofAddress_and_addressMask, addressMask_and_ofAddress]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  have hc := eq_addr_of (c := m_msg.caller)
    (d := Word.toAddress (m_world.sload m_msg.currentTarget 5#256)) (by with_reducible assumption)
  exact pwp_stop (by pcode_fact) (hok _ _ ⟨fun h => absurd hc h, fun _ =>
    ⟨hv, ‹_›, ⟨_, rfl⟩, rfl, rfl, rfl⟩⟩)

set_option maxHeartbeats 0 in
theorem setTokenManager_high (m : Machine) (a : Address) (hf : Fresh LEND.runtimeCode m)
    (hd : Args m.frame.msg.data 0x7cb2b79c [Word.ofAddress a])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (TMPost m a) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, Nat.mul_zero,
    Nat.add_zero] at hsize harg0
  have hsel' := BNB.Spec.div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := BNB.Spec.calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  by_cases hc : m_msg.caller = Word.toAddress (m_world.sload m_msg.currentTarget 5#256)
  · have he : Word.eq (Word.ofAddress m_msg.caller)
        (Word.ofAddress (Word.toAddress (m_world.sload m_msg.currentTarget 5#256))) = 1#256 := by
      rw [← hc]; exact eq_self _
    pwp_steps [hval, hst, hsel', hz, harg0, mask_div_one, he, ofAddress_and_addressMask,
      addressMask_and_ofAddress]
    exact pwp_stop (by pcode_fact) ⟨fun h => absurd hc h, fun _ =>
      ⟨hval, hst, ⟨_, rfl⟩, rfl, rfl, rfl⟩⟩
  · have he := eq_addr_zero hc
    pwp_steps [hval, hst, hsel', hz, harg0, mask_div_one, he, ofAddress_and_addressMask,
      addressMask_and_ofAddress]
    exact ⟨fun _ => ⟨_, rfl⟩, fun h => absurd h hc⟩

/-! ## The obligation -/

/-- What the decoder accepts. -/
theorem ops_cases {c : Address} {d : ByteArray} {v : ℕ} {e : LEND.Op Address}
    (h : ops c d v = some e) :
    4 ≤ d.size ∧
      ((Abi.selectorOf d = 0xd0febe4c ∧ e = .buyTokens c v) ∨
       (Abi.selectorOf d = 0x1d511879 ∧ e = .buyTokensPresale c v) ∨
       (Abi.selectorOf d = 0xd7b91bcc ∧ e = .buyTokensICO c v) ∨
       (v = 0 ∧ 36 ≤ d.size ∧ Abi.selectorOf d = 0x56de96db ∧
         e = .setState c (argWord d 0).toNat) ∨
       (v = 0 ∧ 36 ≤ d.size ∧ Abi.selectorOf d = 0x7cb2b79c ∧
         Word.ofAddress (Word.toAddress (argWord d 0)) = argWord d 0 ∧
         e = .setTokenManager c (Word.toAddress (argWord d 0)))) := by
  unfold ops at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 <;> cases h
  · exact ⟨by omega, .inl ⟨h2, rfl⟩⟩
  · exact ⟨by omega, .inr (.inl ⟨h3, rfl⟩)⟩
  · exact ⟨by omega, .inr (.inr (.inl ⟨h4, rfl⟩))⟩
  · simp only [not_or, not_not, not_lt] at h5
    exact ⟨by omega, .inr (.inr (.inr (.inl ⟨h5.1, h5.2, h6.1, rfl⟩)))⟩
  · simp only [not_or, not_not, not_lt] at h5
    exact ⟨by omega, .inr (.inr (.inr (.inr ⟨h5.1, h5.2, h7.1, h7.2, rfl⟩)))⟩

/-- A frame that only fails meets `OpSpec` for an operation the model refuses. -/
theorem op_fails {Act : Finset Address} {m : Machine} {e : LEND.Op Address}
    (hn : M.op (pre abs Act m) e = none) (h : LowHalts m fun _ _ => False) :
    Halts m fun mf o => OpMatches abs M Act e m mf o ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)) :=
  (halts_fails h).mono fun mf o _ ho => .inl (by unfold OpMatches; rw [hn]; exact ho)

/-- A write to the manager slot through the abstraction. -/
theorem read_sstore_manager {crypto : Crypto} {Act : Finset Address} {w : World} {t : Address}
    (hS : abs.Sound crypto Act) (y : Word) :
    read crypto Act (w.sstore t 5#256 y) t = { read crypto Act w t with manager := Word.toAddress y } := by
  have hk : (5#256 : Word) ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8] : List Word) := by decide
  simp only [read, readSlot]
  rw [BNB.Spec.readMap_sstore_fixed (base := balancesSlot) hS hk (by simp),
    BNB.Spec.readMap2_sstore_fixed (base := allowedSlot) hS hk (by simp),
    World.sload_sstore_ne_key _ _ _ (show supplySlot ≠ 5#256 by decide),
    World.sload_sstore_ne_key _ _ _ (show stateSlot ≠ 5#256 by decide),
    World.sload_sstore_ne_key _ _ _ (show presaleSlot ≠ 5#256 by decide),
    World.sload_sstore_ne_key _ _ _ (show icoSlot ≠ 5#256 by decide),
    World.sload_sstore_ne_key _ _ _ (show totalSoldSlot ≠ 5#256 by decide),
    show managerSlot = 5#256 from rfl, World.sload_sstore_self]

theorem op_setTokenManager (Act : Finset Address) (m : Machine)
    (hs : Start LEND.runtimeCode abs M Act m) (a : Address)
    (hd : Args m.frame.msg.data 0x7cb2b79c [Word.ofAddress a]) (hval : m.frame.msg.value = 0) :
    Halts m fun mf o => OpMatches abs M Act (.setTokenManager m.frame.msg.caller a) m mf o ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)) := by
  have hpre := pre_eq hs
  have hman : (pre abs Act m).manager =
      Word.toAddress (m.world.sload m.frame.msg.currentTarget 5#256) := by
    rw [hpre]; rfl
  refine halts_split' (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => setTokenManager_high m a hs.fresh hd hs.size hval hG.2 hG.1)
    (setTokenManager_low m a hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  unfold OpMatches
  simp only [M, QEDefi.ERC20.Spec.LEND.model, QEDefi.ERC20.Spec.LEND.stepOp, hman]
  by_cases hc : m.frame.msg.caller = Word.toAddress (m.world.sload m.frame.msg.currentTarget 5#256)
  · rw [ite_pos' hc]
    obtain ⟨-, -, ho, hw, ht, hcr⟩ := hok hc
    left
    refine ⟨ho, ?_, ?_, ht, hcr⟩
    · show read _ _ _ _ = _
      rw [hw, read_sstore_manager hs.sound, toAddress_setManager, ← hpre]
    · rw [hw]
      exact BNB.Spec.FrameKeeps.sstore' (.inl (by simp [managerSlot]))
        BNB.Spec.frameKeeps_refl'
  · rw [ite_neg' hc]
    obtain ⟨out, rfl⟩ := hrev hc
    exact .inl trivial

/-- **The sale and administration entry points.** -/
theorem ops_spec : OpSpec LEND.runtimeCode abs M g₀ ops opAddrs := by
  intro Act m e hs hop _
  obtain ⟨h4, hc⟩ := ops_cases hop
  have hph := phase_word hs
  have hp : (pre abs Act m).phase = 5 := hs.wf.1
  rcases hc with ⟨hk, rfl⟩ | ⟨hk, rfl⟩ | ⟨hk, rfl⟩ | ⟨-, -, hk, rfl⟩ | ⟨hv, h36, hk, hcl, rfl⟩
  · exact op_fails (by simp [M, QEDefi.ERC20.Spec.LEND.model, QEDefi.ERC20.Spec.LEND.stepOp,
      QEDefi.ERC20.Spec.LEND.buy, hp]) (buy_low m hs.fresh hs.size h4 (.inl hk) hph)
  · exact op_fails (by simp [M, QEDefi.ERC20.Spec.LEND.model, QEDefi.ERC20.Spec.LEND.stepOp,
      QEDefi.ERC20.Spec.LEND.buyPresale, hp]) (buy_low m hs.fresh hs.size h4 (.inr (.inl hk)) hph)
  · exact op_fails (by simp [M, QEDefi.ERC20.Spec.LEND.model, QEDefi.ERC20.Spec.LEND.stepOp,
      QEDefi.ERC20.Spec.LEND.buyICO, hp]) (buy_low m hs.fresh hs.size h4 (.inr (.inr hk)) hph)
  · exact op_fails (by simp [M, QEDefi.ERC20.Spec.LEND.model, QEDefi.ERC20.Spec.LEND.stepOp, hp])
      (setState_low m hs.fresh hs.size h4 hk hph)
  · have hval : m.frame.msg.value = 0 := BitVec.eq_of_toNat_eq (by simpa using hv)
    refine op_setTokenManager Act m hs _ ⟨hk, by simpa using h36, fun i hi => ?_⟩ hval
    obtain rfl : i = 0 := by simpa using hi
    simpa [argWord] using hcl.symm

end Verified.WeirdERC20.LEND.Spec
