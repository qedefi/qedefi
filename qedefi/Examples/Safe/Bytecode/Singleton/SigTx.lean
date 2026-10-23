import Examples.Safe.Bytecode.Singleton.CopyLoop
import Examples.Safe.Bytecode.Singleton.Digest
import Examples.Actor.Bytecode.MiniSafeLoop

/-!
# The signature loop in `execTransaction`: fewer than `thr` signers never pass

The loop of `checkNSignatures` (head pc `6820`) checking the digest `dh` of this Safe against the
threshold `thr`. Invariant (`TxL`): the counter `i` is at most the number of owners in `O ∩ T` up
to `lastOwner` (`cnt`), the free memory pointer is bounded, and the signatures' length is kept.
Each iteration that passes recovers an owner in `T` above `lastOwner`: an `eth_sign` or plain
ECDSA signature by `Signers`, an approval by `msg.sender` (active, so a signer if an owner) or by
an approval set before (the non-signers have none, `SafeOk.approvals`), a contract signature by
the owner's code (idle owners have none). So `i < thr` holds forever: the loop never exits.
-/

namespace EvmLean.Memory
open EvmLogic EvmLean.Bytes
/-- The 60 bytes `abi.encodePacked("\x19Ethereum Signed Message:\n32", d)` solc leaves at `n`. -/
theorem read_ethSign (M : Memory) (n : Nat) (d : Word) :
    ((((M.expand n 32).storeWord n
      11430537079145650693387304458692941425836787954612963690241153482819318579200#256).expand
      (28 + n) 32).storeWord (28 + n) d).read n 60 =
      Examples.Safe.Guard.ethSignPrefix ++ ofWord d := by
  generalize hX : ((((M.expand n 32).storeWord n
      11430537079145650693387304458692941425836787954612963690241153482819318579200#256).expand
      (28 + n) 32).storeWord (28 + n) d) = X
  have h1 : X.read n 28 = Examples.Safe.Guard.ethSignPrefix := by
    have h := read_storeWord_inner (M.expand n 32) n 0 28
      11430537079145650693387304458692941425836787954612963690241153482819318579200#256
      (by omega)
    simp only [Nat.add_zero] at h
    rw [← hX, read_storeWord_of_disjoint _ _ _ _ _ (.inl (by omega)), read_expand, h]
    decide +kernel
  have h2 : X.read (n + 28) 32 = ofWord d := by
    rw [← hX, show n + 28 = 28 + n by omega, read_storeWord]
  rw [show (60 : Nat) = 28 + 32 from rfl, read_add, h1, h2]
end EvmLean.Memory

namespace EvmLogic.Program
open EvmLean
/-- Return data copied to `[off, off + n)` leaves the words outside unchanged. -/
theorem loadWord_returnMemory_of_disjoint (mem : Memory) (off n : Nat) (out : ByteArray) (o : Nat)
    (h : o + 32 ≤ off ∨ off + n ≤ o) : (returnMemory mem off n out).loadWord o = mem.loadWord o := by
  unfold returnMemory
  split
  · rfl
  · have hn : (out.extract 0 (min n out.size)).size ≤ n := by
      simp only [ByteArray.size_extract]; omega
    rw [Memory.loadWord, Memory.loadWord, Memory.read_write_of_disjoint _ _ _ _ _ (by omega)]
end EvmLogic.Program

namespace Examples.Safe.Guard

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested
open Examples.Safe.Contracts Examples.Actor.MiniSafeOwn

namespace Dep

variable (D : Dep) {O T : Finset Address} {thr : Nat} {h₀ : Word} {msg : Message}
  {ctx : Context} {w : World} {m : Machine}

/-- The address mask. -/
abbrev amask : Word := 1461501637330902918203684832716283019655932542975#256

theorem amask_and (x : Word) : amask &&& x = Word.ofAddress (Word.toAddress x) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show amask.toNat = 2 ^ 160 - 1 from rfl, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod]
  simp only [Word.ofAddress, Word.toAddress, BitVec.toNat_setWidth]
  omega

/-- **The loop states of `execTransaction`'s check**. -/
def TxL (msg : Message) (ctx : Context) (O T : Finset Address) (rest : List Word)
    (req sig dh ex ret L : Word) (P0 : Nat) (x : Machine) : Prop :=
  ∃ i sv rv vv cur last mem w p,
    Fr (fix msg ctx) x 6820 (i :: sv :: rv :: vv :: cur :: last :: req :: sig :: dh :: ex :: ret ::
      rest) mem w ∧
    mem.loadWord 64 = p ∧ mem.loadWord sig.toNat = L ∧ 128 ≤ p.toNat ∧
    p.toNat ≤ P0 + 256 * i.toNat ∧ sig.toNat + 32 + L.toNat ≤ p.toNat ∧
    i.toNat ≤ cnt (O ∩ T) (amask &&& last)

theorem amask_amask (x : Word) :
    amask &&& (amask &&& x) = Word.ofAddress (Word.toAddress x) := by
  rw [amask_and, amask_and]; simp

theorem eq_zero_iff' {x y : Word} : Word.eq x y = 0 ↔ x ≠ y := by
  unfold Word.eq; rw [← not_iff_not, ← ne_eq, ofBool_ne_zero]; simp

theorem eq_ne_zero_iff' {x y : Word} : Word.eq x y ≠ 0 ↔ x = y := by
  rw [ne_eq, eq_zero_iff', not_not]

/-- An owner slot read nonzero (`owners[a] != address(0)`): `a` is an owner. -/
theorem owner_mem {w' : World} {x : Word}
    (hR : ∃ m₀ : Machine, m₀.world = w' ∧ D.Rsf ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m₀)
    (ht : msg.currentTarget = D.sf)
    (h : (amask &&& (amask &&& (w'.sload msg.currentTarget (ctx.crypto.keccak256
      (Bytes.ofWord (amask &&& (amask &&& x)) ++ Bytes.ofWord 2#256))).div 1#256)).eq 0#256 = 0) :
    Word.toAddress x ∈ O := by
  obtain ⟨m₀, hw, hG, -⟩ := hR
  rw [hw] at hG
  rw [eq_zero_iff', amask_amask x] at h
  refine hG.2.2.owners _ fun h0 => h ?_
  have : w'.sload msg.currentTarget (ownerSlot ctx.crypto (Word.toAddress x)) = 0 := by
    rw [ht]; exact h0
  simp only [ownerSlot, mapSlot] at this
  rw [show (2#256 : Word) = 2 from rfl, this]; decide

/-- An approval read nonzero for the digest: not by an owner outside `T`. -/
theorem approval_T {w' : World} {x dh : Word} {sh : ByteArray}
    (hR : ∃ m₀ : Machine, m₀.world = w' ∧ D.Rsf ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m₀)
    (ht : msg.currentTarget = D.sf) (hsh : sh.size = 32)
    (hdh : dh = safeDigest ctx.crypto ctx.block.chainId D.sf sh) (hO : Word.toAddress x ∈ O)
    (h : ((w'.sload msg.currentTarget (ctx.crypto.keccak256 (Bytes.ofWord dh ++ Bytes.ofWord
      (ctx.crypto.keccak256 (Bytes.ofWord (amask &&& (amask &&& x)) ++ Bytes.ofWord 8#256))))).eq
        0#256).iszero ≠ 0) :
    Word.toAddress x ∈ T := by
  obtain ⟨m₀, hw, hG, -⟩ := hR
  rw [hw] at hG
  rw [iszero_ne_zero, eq_zero_iff'] at h
  by_contra hT
  apply h
  have := hG.2.2.approvals _ hO hT sh hsh
  rw [amask_amask, ht, hdh]
  exact this

/-- The executor (`msg.sender`) approves: it is active, so a signer if an owner. -/
theorem executor_T {ex x : Word} (hC : D.SgCtx O T thr h₀ msg ctx)
    (hex : ex = Word.ofAddress msg.caller) (hO : Word.toAddress x ∈ O)
    (h : ((amask &&& ex).eq (amask &&& x)).iszero.iszero ≠ 0) : Word.toAddress x ∈ T := by
  rw [iszero_ne_zero, iszero_eq_zero, eq_ne_zero_iff', hex, amask_and, amask_and] at h
  simp only [Word.toAddress_ofAddress] at h
  have hc : msg.caller = Word.toAddress x := Word.ofAddress_injective h
  by_contra hT
  exact hC.active (.inr ⟨hc ▸ hO, hc ▸ hT⟩)

/-- **One more signer**: the counter stays below the count of owners in `T` up to the new
last owner. -/
theorem step_cnt {i last x : Word} (hO : Word.toAddress x ∈ O) (hT : Word.toAddress x ∈ T)
    (hgt : ((amask &&& x).gt (amask &&& last)).iszero = 0)
    (hi : i.toNat ≤ cnt (O ∩ T) (amask &&& last)) :
    (1#256 + i).toNat ≤ cnt (O ∩ T) (amask &&& x) := by
  rw [iszero_eq_zero, gt_ne_zero] at hgt
  have hc := cnt_lt (Finset.mem_inter.2 ⟨hO, hT⟩) (x := amask &&& last) (y := amask &&& x)
    (by rw [← amask_and]; exact hgt) (by rw [← amask_and])
  have := cnt_le (O ∩ T) (amask &&& last)
  have := card_le (O ∩ T)
  rw [toNat_add_of_lt (by simp; omega)]
  simp; omega

theorem cnt_lt_thr {i : Word} {x : Word} (hC : D.SgCtx O T thr h₀ msg ctx)
    (h : i.toNat ≤ cnt (O ∩ T) x) : i.toNat < thr :=
  Nat.lt_of_le_of_lt (h.trans (cnt_le _ _)) hC.card

end Dep

end Examples.Safe.Guard
