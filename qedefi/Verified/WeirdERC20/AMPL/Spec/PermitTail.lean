import Verified.WeirdERC20.AMPL.Spec.PermitRules
import Verified.WeirdERC20.AMPL.Spec.PermitModel

/-!
# AMPL's `permit` after `name()`, at any gas

From the return of `name()` into `DOMAIN_SEPARATOR()` (pc `2689`), with the name's length word
at memory `352`, its bytes at `384` and the free memory pointer `F` (any `F ≥ 384`: the copy
of a long name moves it), to the end of `permit`. The run computes the domain separator, the
digest and the call to `ecrecover`, compares the signer with the owner, increments the nonce
with `SafeMath`, writes the allowance and logs `Approval`. `tail_low`: at any gas, the frame
fails or ends as `hsucc` says.

The free pointer is symbolic, so the run keeps every memory offset in the form `c + F`
(`BitVec.ofNat_add_ofNat` and the facts `hFm`… on `F`), which lets the reads of the free
pointer skip the stores above it (`loadWord64_store`).
-/

set_option linter.unusedSimpArgs false

namespace Verified.WeirdERC20.AMPL.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open EvmLogic.Program.Nested
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC4626 Verified.WeirdERC20.AMPL.Contracts
open Verified.WeirdERC20.AMPL.Spec Verified.Solady.Spec.AnyGas

theorem loadWord64_store {M : Memory} {off : Nat} {w : Word} (h : 96 ≤ off) :
    (M.storeWord off w).loadWord 64 = M.loadWord 64 :=
  Memory.loadWord_storeWord_of_disjoint _ _ _ _ (.inl (by omega))

theorem loadWord_store_shift {M : Memory} {F a b : Nat} {w : Word} (h : a + 32 ≤ b ∨ b + 32 ≤ a) :
    (M.storeWord (b + F) w).loadWord (a + F) = M.loadWord (a + F) :=
  Memory.loadWord_storeWord_of_disjoint _ _ _ _ (by omega)

theorem read_128_loadWords (M : Memory) (off : Nat) :
    M.read off 128 = Bytes.ofWord (M.loadWord off) ++ (Bytes.ofWord (M.loadWord (off + 32)) ++
      (Bytes.ofWord (M.loadWord (off + 64)) ++ Bytes.ofWord (M.loadWord (off + 96)))) := by
  rw [Memory.read_128]
  simp only [Memory.loadWord]
  rw [Bytes.ofWord_toWord (by simp [Memory.read, Bytes.size_readPadded]),
    Bytes.ofWord_toWord (by simp [Memory.read, Bytes.size_readPadded]),
    Bytes.ofWord_toWord (by simp [Memory.read, Bytes.size_readPadded]),
    Bytes.ofWord_toWord (by simp [Memory.read, Bytes.size_readPadded])]

theorem loadWord_storeWord_eq {M : Memory} {off off' : Nat} {w : Word} (h : off = off') :
    (M.storeWord off w).loadWord off' = w := by
  subst h; exact Memory.loadWord_storeWord _ _ _

theorem read32_storeWord_eq {M : Memory} {off off' : Nat} {w : Word} (h : off = off') :
    (M.storeWord off w).read off' 32 = Bytes.ofWord w := by
  subst h; exact Memory.read_storeWord _ _ _

theorem read_storeWord_prefix_eq {M : Memory} {off off' n : Nat} {w : Word} (h : off = off')
    (hn : n ≤ 32) : (M.storeWord off w).read off' n = (Bytes.ofWord w).extract 0 n := by
  subst h; exact Memory.read_storeWord_prefix _ _ _ _ hn

theorem extract_ofWord_32 (w : Word) : (Bytes.ofWord w).extract 0 32 = Bytes.ofWord w := by
  rw [show (32 : Nat) = (Bytes.ofWord w).size from (Bytes.size_ofWord w).symm,
    ByteArray.extract_zero_size]

theorem addr_of_eq_ne {a b : Address} (h : (Word.ofAddress a).eq (Word.ofAddress b) ≠ 0) :
    a = b := by
  by_contra hne
  apply h
  have : Word.ofAddress a ≠ Word.ofAddress b := fun e => hne (Word.ofAddress_injective e)
  have h' : (Word.ofAddress a == Word.ofAddress b) = false := by simpa using this
  simp [Word.eq, Word.ofBool, h']

/-- The first two bytes of `0x1901 << 240`: EIP-712's `"\x19\x01"`. -/
theorem prefix_eq :
    (Bytes.ofWord 11309588061646438093662687302255421419811724423900836950936401294474059186176#256).extract
      0 2 = eip712Prefix := by
  kernel_decide

/-- The domain separator computed from the name bytes in memory. -/
def dsOfMem (m : Machine) (Lw : Word) : Word :=
  m.ctx.crypto.keccak256 (Bytes.ofWord DOMAIN_TYPEHASH ++
    (Bytes.ofWord (m.ctx.crypto.keccak256 (m.frame.memory.read 384 Lw.toNat)) ++
      (Bytes.ofWord VERSION_HASH ++ (Bytes.ofWord (ofNat m.ctx.block.chainId) ++
        Bytes.ofWord (Word.ofAddress m.frame.msg.currentTarget)))))

set_option maxHeartbeats 0 in
/-- **`permit` from the return of `name()`, at any gas.** -/
theorem tail_low {H : Machine → Outcome → Prop} (hF : FailH H) (m : Machine)
    (F : Nat) (Lw : Word) (sh nonce s r v dl val : Word) (o sp : Address)
    (hc : m.frame.code = AMPL.runtimeCode) (hj : JumpTable m.frame.jumpDests AMPL.runtimeCode)
    (hpc : m.frame.pc = 2689)
    (hs : m.frame.stack = [352#256, DOMAIN_TYPEHASH, ofNat m.ctx.block.chainId, 0#256,
      5041#256, 0#256, sh, nonce, s, r, v, dl, val, Word.ofAddress sp, Word.ofAddress o, 974#256,
      3573918927#256])
    (hM352 : m.frame.memory.loadWord 352 = Lw)
    (hM64 : m.frame.memory.loadWord 64 = BitVec.ofNat 256 F)
    (hF1 : 384 ≤ F) (hF2 : F + 3000 < 2 ^ 256)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hsucc : ∀ (mf : Machine),
      m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit → m.frame.msg.isStatic = false →
      (ecrecoverAddress? m.ctx.crypto (digest m.ctx.crypto (dsOfMem m Lw) sh)
        (255#256 &&& v) r s).getD 0 = o →
      (Word.lt (1#256 + nonce) nonce).iszero ≠ 0 →
      mf.world = (m.world.sstore m.frame.msg.currentTarget
          (m.ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress o) ++ Bytes.ofWord 160#256))
          (1#256 + nonce)).sstore m.frame.msg.currentTarget
        (m.ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress sp) ++
          Bytes.ofWord (m.ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress o) ++
            Bytes.ofWord 159#256)))) val →
      mf.transient = m.transient → mf.createdAccounts = m.createdAccounts →
      mf.frame.sub.logs = m.frame.sub.logs.push (approvalLog m.frame.msg.currentTarget o sp val) →
      H mf (.success .empty)) :
    WP m (fun _ => False) H := by
  have hFm : ∀ c, c ≤ 1000 → (c + F) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = c + F :=
    fun c _ => Nat.mod_eq_of_lt (by omega)
  have hF96 : ∀ c, 96 ≤ c + F := fun c => by omega
  have hF0 : F % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      F := Nat.mod_eq_of_lt (by omega)
  have hF96' : 96 ≤ F := by omega
  have hFa : ∀ a b, a ≤ 1000 → b ≤ 1000 → (a + (b + F)) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      a + b + F := fun a b _ _ => by rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hFb : ∀ a b, a ≤ 1000 → b ≤ 1000 → (a + F + b) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      a + b + F := fun a b _ _ => by rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hR : ∀ a b, a + F + b = a + b + F := fun a b => by omega
  have hC : ∀ b, F + b = b + F := fun b => by omega
  have hS1 : ∀ a b, b ≤ a → a ≤ 1000 →
      BitVec.ofNat 256 (a + F) - BitVec.ofNat 256 (b + F) = BitVec.ofNat 256 (a - b) := by
    intro a b hab ha
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; rw [Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega)]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have hS2 : ∀ a, 32 ≤ a → a ≤ 1000 →
      BitVec.ofNat 256 (a + F) - 32#256 = BitVec.ofNat 256 (a - 32 + F) := by
    intro a ha ha'
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; rw [Nat.mod_eq_of_lt (by omega)]; omega)]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hc hpc hs hstd
  hwp_steps stop_at [5175] [hM352, hM64, DOMAIN_TYPEHASH, BitVec.ofNat_add_ofNat, hFm, hF96, hF0,
    hF96', loadWord64_store, BitVec.toNat_ofNat, hFa, hFb, Nat.reducePow, Nat.reduceMod,
    Nat.reduceAdd, BitVec.sub_self, BitVec.add_zero, ← Nat.add_assoc, hR, hC, hS1, hS2]
  refine wp_staticcall_one hF (by pcode_fact) rfl (by simp) rfl hdel (read_128_loadWords _ _)
    (fun _ _ _ _ => ?_) (fun hdep _ _ hlogs => ?_)
  · dsimp only
    hwp_steps []
    refine pwp_returndatacopy hF (by pcode_fact) rfl fun _ _ => ?_
    dsimp only
    hwp_steps []
  · dsimp only
    rw [returnMemory_ecrecoverOutput]
    split
    · rename_i a hrec
      hwp_steps [hM352, hM64, DOMAIN_TYPEHASH, BitVec.ofNat_add_ofNat, hFm, hF96, hF0,
        hF96', loadWord64_store, BitVec.toNat_ofNat, hFa, hFb, Nat.reducePow, Nat.reduceMod,
        Nat.reduceAdd, BitVec.sub_self, BitVec.add_zero, ← Nat.add_assoc, hR, hC, hS1, hS2,
        loadWord_store_shift, mask_lit_and, and_mask_lit, Word.toAddress_ofAddress, callMemory]
      simp (disch := omega) only [Memory.loadWord_expand, Memory.read_expand,
        loadWord_storeWord_eq, Memory.loadWord_storeWord_of_disjoint, read32_storeWord_eq,
        Memory.read_storeWord_of_disjoint, Memory.read_66, Memory.read_160,
        read_storeWord_prefix_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, callMemory,
        extract_ofWord_32, prefix_eq] at hrec
      have hoa : o = a := addr_of_eq_ne ‹(Word.ofAddress o).eq (Word.ofAddress a) ≠ 0›
      refine pwp_stop (by pcode_fact) (hsucc _ hdep (by assumption) ?_ (by assumption) rfl rfl rfl ?_)
      · simp only [digest, dsOfMem, DOMAIN_TYPEHASH, VERSION_HASH]
        rw [hrec, hoa]; rfl
      · logs_simp [hlogs]
        rw [logEntry_eq_eventLog (data := [val])]
        · rfl
        · simp (disch := omega) only [Memory.read_expand, read32_storeWord_eq,
            Memory.read_storeWord_of_disjoint, encodeArgs_one, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt]
    · rename_i hrec
      hwp_steps [hM352, hM64, DOMAIN_TYPEHASH, BitVec.ofNat_add_ofNat, hFm, hF96, hF0,
        hF96', loadWord64_store, BitVec.toNat_ofNat, hFa, hFb, Nat.reducePow, Nat.reduceMod,
        Nat.reduceAdd, BitVec.sub_self, BitVec.add_zero, ← Nat.add_assoc, hR, hC, hS1, hS2,
        loadWord_store_shift, mask_lit_and, and_mask_lit, Word.toAddress_ofAddress, callMemory]
      simp (disch := omega) only [Memory.loadWord_expand, Memory.read_expand,
        loadWord_storeWord_eq, Memory.loadWord_storeWord_of_disjoint, read32_storeWord_eq,
        Memory.read_storeWord_of_disjoint, Memory.read_66, Memory.read_160,
        read_storeWord_prefix_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, callMemory,
        extract_ofWord_32, prefix_eq] at hrec
      have ho0 : o = 0 := addr_of_eq_ne (b := 0) ‹(Word.ofAddress o).eq 0#256 ≠ 0›
      refine pwp_stop (by pcode_fact) (hsucc _ hdep (by assumption) ?_ (by assumption) rfl rfl rfl ?_)
      · simp only [digest, dsOfMem, DOMAIN_TYPEHASH, VERSION_HASH]
        rw [hrec, ho0]; rfl
      · logs_simp [hlogs]
        rw [logEntry_eq_eventLog (data := [val])]
        · rfl
        · simp (disch := omega) only [Memory.read_expand, read32_storeWord_eq,
            Memory.read_storeWord_of_disjoint, encodeArgs_one, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt]

end Verified.WeirdERC20.AMPL.Spec.Malformed
