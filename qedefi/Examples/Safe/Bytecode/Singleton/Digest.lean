import Examples.Safe.Bytecode.Singleton.Ctx

/-!
# The transaction digest in memory

The memory shapes solc and Safe's assembly leave before hashing: the domain separator
(`keccak256(abi.encode(DOMAIN_SEPARATOR_TYPEHASH, chainid, this))`) and the EIP-712 digest
(`keccak256(0x1901 ‖ domainSeparator ‖ safeTxHash)`, read from byte `30` of the word `0x1901`).
-/

namespace EvmLean.Memory
open EvmLogic EvmLean.Bytes

theorem read_storeWord_inner (m : Memory) (off i n : Nat) (w : Word) (hn : i + n ≤ 32) :
    (m.storeWord off w).read (off + i) n = (ofWord w).extract i (i + n) := by
  apply ext_getD (by rw [read, size_readPadded, ByteArray.size_extract, size_ofWord]; omega)
  intro j hj
  rw [read, size_readPadded] at hj
  have h : off ≤ off + i + j ∧ off + i + j < off + (ofWord w).size := by rw [size_ofWord]; omega
  simp only [read, getD_readPadded, hj, ↓reduceIte, storeWord, getD_bytes_write, h, and_self,
    getD_extract]
  simp only [show i + j < i + n by omega, ↓reduceIte]
  congr 1
  omega

theorem read_storeWord' (m : Memory) {off off' : Nat} (w : Word) (h : off' = off) :
    (m.storeWord off w).read off' 32 = ofWord w := by
  subst h; exact read_storeWord m off' w

theorem loadWord_storeWord' (m : Memory) {off off' : Nat} (w : Word) (h : off' = off) :
    (m.storeWord off w).loadWord off' = w := by
  subst h; exact loadWord_storeWord m off' w

/-- The 128 bytes of four consecutive words. -/
theorem read_128' (m : Memory) (off : Nat) : m.read off 128 =
    m.read off 32 ++ (m.read (off + 32) 32 ++ (m.read (off + 64) 32 ++ m.read (off + 96) 32)) := by
  rw [show (128 : Nat) = 32 + 96 from rfl, read_add, show (96 : Nat) = 32 + 64 from rfl,
    read_add, show (64 : Nat) = 32 + 32 from rfl, read_add, Nat.add_assoc]

/-- The 96 bytes `abi.encode(a, b, c)` writes after its length word. -/
theorem read_encode3 (M : Memory) (n : Nat) (a b c : Word) :
    (((((((M.expand 64 32).expand (32 + n) 32).storeWord (32 + n) a).expand (32 + (32 + n))
      32).storeWord (32 + (32 + n)) b).expand (32 + (32 + (32 + n))) 32).storeWord
      (32 + (32 + (32 + n))) c).read (32 + n) 96 = ofWord a ++ ofWord b ++ ofWord c := by
  generalize hX : (((((((M.expand 64 32).expand (32 + n) 32).storeWord (32 + n) a).expand
    (32 + (32 + n)) 32).storeWord (32 + (32 + n)) b).expand (32 + (32 + (32 + n))) 32).storeWord
    (32 + (32 + (32 + n))) c) = X
  have h1 : X.read (32 + n) 32 = ofWord a := by
    rw [← hX, read_storeWord_of_disjoint _ _ _ _ _ (.inl (by omega)), read_expand,
      read_storeWord_of_disjoint _ _ _ _ _ (.inl (by omega)), read_expand, read_storeWord]
  have h2 : X.read (32 + n + 32) 32 = ofWord b := by
    rw [← hX, read_storeWord_of_disjoint _ _ _ _ _ (.inl (by omega)), read_expand,
      show 32 + n + 32 = 32 + (32 + n) by omega, read_storeWord]
  have h3 : X.read (32 + n + 32 + 32) 32 = ofWord c := by
    rw [← hX, show 32 + n + 32 + 32 = 32 + (32 + (32 + n)) by omega, read_storeWord]
  rw [show (96 : Nat) = 32 + 64 from rfl, read_add, read_64, h1, h2, h3, ByteArray.append_assoc]

/-- The 66 bytes `0x1901 ‖ d ‖ x` Safe hashes into a transaction digest. -/
theorem read_digest (M : Memory) (n : Nat) (d : Word) :
    ((((M.expand n 32).storeWord n 6401#256).expand (n + 32) 32).storeWord (n + 32) d).read
      (n + 30) 66 = ⟨#[0x19, 0x01]⟩ ++ ofWord d ++ M.read (n + 64) 32 := by
  generalize hX : ((((M.expand n 32).storeWord n 6401#256).expand (n + 32) 32).storeWord
    (n + 32) d) = X
  have h1 : X.read (n + 30) 2 = ⟨#[0x19, 0x01]⟩ := by
    rw [← hX, read_storeWord_of_disjoint _ _ _ _ _ (.inl (by omega)), read_expand,
      read_storeWord_inner _ _ _ _ _ (by omega)]
    decide +kernel
  have h2 : X.read (n + 30 + 2) 32 = ofWord d := by
    rw [← hX, show n + 30 + 2 = n + 32 by omega, read_storeWord]
  have h3 : X.read (n + 30 + 2 + 32) 32 = M.read (n + 64) 32 := by
    rw [← hX, show n + 30 + 2 + 32 = n + 64 by omega,
      read_storeWord_of_disjoint _ _ _ _ _ (.inr (by omega)), read_expand,
      read_storeWord_of_disjoint _ _ _ _ _ (.inr (by omega)), read_expand]
  rw [show (66 : Nat) = 2 + 64 from rfl, read_add, read_64, h1, h2, h3, ByteArray.append_assoc]

end EvmLean.Memory

namespace Examples.Safe.Guard

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested
open Examples.Safe.Contracts

namespace Dep

variable (D : Dep) {O T : Finset Address} {thr : Nat} {h₀ : Word} {msg : Message}
  {ctx : Context} {w : World} {m : Machine}

theorem domainTypehash_eq :
    domainTypehash =
      32523383700587834770323112271211932718128200013265661849047136999858837557784#256 := by
  decide

theorem len_encode3 (p : Word) :
    BitVec.toNat (32#256 + (32#256 + (32#256 + (32#256 + p))) - p - 32#256) = 96 := by
  have : 32#256 + (32#256 + (32#256 + (32#256 + p))) - p - 32#256 = 96#256 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [this]; rfl

set_option maxHeartbeats 40000000 in
/-- **`getTransactionHash`** (body at pc `12738`, returning to `9580`): the hash it returns is a
digest of this Safe on this chain; the free memory pointer moves by `128` (the domain
separator's encoding), and the memory between the scratch words and it is kept. -/
theorem tx_hash {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 p : Word} {rest : List Word} {mem : Memory}
    {B : Machine → Prop} (htgt : msg.currentTarget = D.sf)
    (hp : mem.loadWord 64 = p) (hpb : p.toNat < 2 ^ 40) (hp0 : 128 ≤ p.toNat)
    (hF : Fr (fix msg ctx) m 12738
      (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: 9580#256 :: rest) mem w)
    (hk : ∀ (m' : Machine) (dh : Word) (mem' : Memory), Fr (fix msg ctx) m' 9580 (dh :: rest) mem' w →
      (∃ sh : ByteArray, sh.size = 32 ∧ dh = safeDigest ctx.crypto ctx.block.chainId D.sf sh) →
      mem'.loadWord 64 = p + 128#256 →
      (∀ o, 96 ≤ o → o + 32 ≤ p.toNat → mem'.loadWord o = mem.loadWord o) →
      OwnB True (fun _ => True) (D.Rsf ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork)
        (Own.SstoreOk (Kw ctx.crypto)) D.Csf Dsim Doomed B m') :
    OwnB True (fun _ => True) (D.Rsf ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork)
      (Own.SstoreOk (Kw ctx.crypto)) D.Csf Dsim Doomed B m := by
  sg_explore [9580] using [hp, toNat_add_of_lt, len_encode3, Memory.read_encode3,
    Memory.read_digest]
  refine hk _ _ _ hF ?_ ?_ ?_
  · refine ⟨Bytes.ofWord ?x, Bytes.size_ofWord _, ?_⟩
    swap
    rw [htgt]
    unfold safeDigest domainSeparator
    rw [domainTypehash_eq]
  · simp (disch := first | omega | simp) only [Memory.loadWord_expand,
      Memory.loadWord_storeWord_of_disjoint, Own.loadWord_copyIn_of_disjoint,
      Memory.loadWord_storeWord]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · intro o h1 h2
    simp (disch := first | omega | simp) only [Memory.loadWord_expand,
      Memory.loadWord_storeWord_of_disjoint, Own.loadWord_copyIn_of_disjoint]

end Dep

end Examples.Safe.Guard
