import Examples.Time.VestingWallet.Basic

/-!
# `VestingWallet`: the vesting schedule at the bytecode level

`vested_wp`: the internal `vestedAmount(uint64)` (`_vestingSchedule(address(this).balance +
released(), timestamp)`) against the model's `vestedAmount`, including the checked `+`, `-`,
`*` and the division. The external `vestedAmount(uint64)`, `releasable()` and `release()` all
call it.
-/

namespace Examples.Time.VestingWallet
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Tactic
open Examples.Time.Contracts QEDefi.Vesting

set_option maxHeartbeats 0 in
/-- **`vestedAmount(timestamp)` as an internal function** (entry `0x2a5`, stack
`ts :: r :: rest`), proved once for a symbolic `ts` and symbolic immutables: it returns to `r`
with `vestedAmount (sched i) (ts mod 2⁶⁴)` of the wallet's balance and `_released`, or reverts
(`Panic`) exactly when the model does, changing nothing. The schedule's three branches
(before, after, linear) are the code's own `JUMPI`s; nothing is enumerated. -/
theorem vested_wp {i : VestingWallet.Immutables} (m : Machine) {ts r : Word} {rest : List Word}
    (hv : WalletFrame i m) (hpc : m.frame.pc = 0x2a5) (hs : m.frame.stack = ts :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hg : 5000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64)
    (hmsz : m.frame.memory.size = 96) :
    WP m (fun m' => ∃ v g, vestedAmount (sched i) (ts.toNat % 2 ^ 64)
          (state m.world m.frame.msg.currentTarget) = some v ∧
        m' = m.resumeWith r.toNat (BitVec.ofNat 256 v :: rest) m.frame.memory g
          m.frame.returnData (m.frame.sub.warmKey m.frame.msg.currentTarget 1#256) ∧
        g ≤ m.frame.gasLeft ∧ m.frame.gasLeft ≤ g + 3000)
      (fun mf o => vestedAmount (sched i) (ts.toNat % 2 ^ 64)
          (state m.world m.frame.msg.currentTarget) = none ∧ (∃ out, o = .revert out) ∧
        mf.world = m.world) := by
  obtain ⟨hc, hj⟩ := hv
  have hagree := jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  generalize hspec : vestedAmount (sched i) (ts.toNat % 2 ^ 64) (state m_world m_msg.currentTarget) = spec
  have htot : (state m_world m_msg.currentTarget).total =
      (m_world.balance m_msg.currentTarget).toNat + (m_world.sload m_msg.currentTarget 1#256).toNat := rfl
  pwp_steps
  by_cases hadd : (m_world.balance m_msg.currentTarget).toNat + (m_world.sload m_msg.currentTarget 1#256).toNat < 2 ^ 256
  · rw [checkedAdd_ok hadd]
    pwp_steps [readBytes_code_1198, Bytes.toWord_ofWord]
    by_cases h1 : ts.toNat % 2 ^ 64 < start i
    · rw [iszero_lt_eq_zero (by rw [toNat_mask_and, toNat_and_mask]; exact h1)]
      pwp_steps
      refine WP.ret ⟨0, _, ?_, rfl, ?_⟩
      · rw [← hspec]; exact vestedAmount_before (by rw [htot]; exact hadd) h1
      · exact ⟨by evm_gas, by evm_gas⟩
    · rw [iszero_lt_eq_one (by rw [toNat_mask_and, toNat_and_mask]; unfold start at h1; omega)]
      pwp_steps [readBytes_code_1236, readBytes_code_1198, Bytes.toWord_ofWord]
      rw [checkedAdd_ok (by rw [toNat_mask_and, toNat_and_mask]; omega)]
      pwp_steps
      by_cases h2 : start i + duration i ≤ ts.toNat % 2 ^ 64
      · rw [lt_eq_zero' (by rw [toNat_end, toNat_mask_and]; unfold start duration at h2; omega)]
        pwp_steps
        refine WP.ret ⟨_, _, ?_, by rw [Machine.resumeWith, ofNat_add_toNat _ _ hadd], ?_⟩
        · rw [← hspec]
          exact vestedAmount_after (by rw [htot]; exact hadd) (by show start i ≤ _; omega) h2
        · exact ⟨by evm_gas, by evm_gas⟩
      · rw [lt_eq_one' (by rw [toNat_end, toNat_mask_and]; unfold start duration at h2; omega)]
        pwp_steps [readBytes_code_1458, readBytes_code_1198, Bytes.toWord_ofWord]
        rw [checkedSub_ok (by rw [toNat_and_mask, toNat_and_mask]; unfold start at h1; omega)]
        pwp_steps
        have hd : ((ts &&& 18446744073709551615#256) - (i.start &&& 18446744073709551615#256)).toNat =
            ts.toNat % 2 ^ 64 - start i := by
          rw [toNat_sub_of_le' (by rw [toNat_and_mask, toNat_and_mask]; unfold start at h1; omega),
            toNat_and_mask, toNat_and_mask]; rfl
        have hT : (m_world.sload m_msg.currentTarget 1#256 + m_world.balance m_msg.currentTarget).toNat =
            (state m_world m_msg.currentTarget).total := by
          rw [htot, toNat_add_of_lt' (by omega)]; omega
        by_cases h3 : (state m_world m_msg.currentTarget).total * (ts.toNat % 2 ^ 64 - start i) < 2 ^ 256
        · rw [checkedMul_ok (by rw [hd, hT, Nat.mul_comm]; exact h3)]
          have hdur : (18446744073709551615#256 &&& i.duration) ≠ 0 := by
            intro h0
            have := congrArg BitVec.toNat h0
            rw [toNat_mask_and] at this
            simp only [start, duration] at h1 h2
            simp at this
            omega
          pwp_steps [hdur]
          have hdu : (18446744073709551615#256 &&& i.duration).toNat = duration i := toNat_mask_and _
          have hval : Word.div (((ts &&& 18446744073709551615#256) - (i.start &&& 18446744073709551615#256)) *
              (m_world.sload m_msg.currentTarget 1#256 + m_world.balance m_msg.currentTarget))
                (18446744073709551615#256 &&& i.duration) =
              BitVec.ofNat 256 ((state m_world m_msg.currentTarget).total * (ts.toNat % 2 ^ 64 - start i) /
                duration i) := by
            apply BitVec.eq_of_toNat_eq
            rw [toNat_div', BitVec.toNat_mul, hd, hT, hdu, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by rw [Nat.mul_comm]; exact h3), Nat.mul_comm,
              Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h3)]
          rw [hval]
          refine WP.ret ⟨_, _, ?_, rfl, ?_⟩
          · rw [← hspec]
            exact vestedAmount_mid (by rw [htot]; exact hadd) (by show start i ≤ _; omega)
              (by show _ < start i + duration i; omega) h3
          · exact ⟨by evm_gas, by evm_gas⟩
        · rw [checkedMul_overflow (by rw [hd, hT, Nat.mul_comm]; omega)]
          pwp_steps [hmsz]
          refine ⟨?_, ⟨_, rfl⟩, rfl⟩
          rw [← hspec]
          exact vestedAmount_mid_overflow (by rw [htot]; exact hadd)
            (by show start i ≤ _; omega) (by show _ < start i + duration i; omega)
            (by show 2 ^ 256 ≤ (state m_world m_msg.currentTarget).total * (_ - start i); omega)
  · rw [checkedAdd_overflow (by omega)]
    pwp_steps [hmsz]
    exact ⟨by rw [← hspec]; exact vestedAmount_overflow (by rw [htot]; show 2 ^ 256 ≤ _; omega), ⟨_, rfl⟩, rfl⟩

end Examples.Time.VestingWallet
