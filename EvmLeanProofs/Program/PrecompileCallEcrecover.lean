import EvmLeanProofs.Program.PrecompileCall
import EvmLeanProofs.Solidity.Abi
import EvmLeanProofs.Program.Memory

/-!
# `ECRECOVER` on a four-word input

solc calls `ecrecover(hash, v, r, s)` by `STATICCALL`ing address `0x01` with the four words
`hash ‖ v ‖ r ‖ s` as input. For such an input, and any `Crypto`, the precompile
(`Precompile.ecrecover`) is described by `ecrecoverAddress?`:

* `ecrecoverAddress? crypto hash v r s`: the recovered signer, as the precompile computes it
  (`v ∈ {27, 28}`, `0 < r, s < n`, then `crypto.ecrecover` and the low 20 bytes of the Keccak
  of the public key), or `none` for an invalid signature;
* `ecrecover_words`: with at least 3000 gas the call succeeds, costs 3000 gas, and returns the
  signer as one ABI word, or empty output (`none`).

Nothing here is a cryptographic claim: `crypto.ecrecover` is an arbitrary function.
-/

namespace EvmLean.Program

open Bytes

/-- The signer `ECRECOVER` recovers from `(hash, v, r, s)` (see `Precompile.ecrecover`), or
`none` for an invalid signature. -/
def ecrecoverAddress? (crypto : Crypto) (hash v r s : Word) : Option Address :=
  if v.toNat ≠ 27 ∧ v.toNat ≠ 28 then none
  else if r.toNat = 0 ∨ Secp256k1.n ≤ r.toNat ∨ s.toNat = 0 ∨ Secp256k1.n ≤ s.toNat then none
  else (crypto.ecrecover (Bytes.ofWord hash) (v.toNat - 27) r.toNat s.toNat).map
    fun pub => Word.toAddress (crypto.keccak256 pub)

/-- Byte `j` of a big-endian encoding. -/
theorem getD_ofNatBE (len n j : Nat) :
    getD (ofNatBE len n) j = if j < len then (n >>> (8 * (len - 1 - j))).toUInt8 else 0 := by
  unfold getD
  split
  · rename_i h
    have h' : j < len := by rw [size_ofNatBE] at h; exact h
    simp only [h', ↓reduceIte, ofNatBE, ByteArray.getElem_eq_getElem_data, Array.getElem_ofFn]
  · rename_i h
    have h' : ¬ j < len := by rw [size_ofNatBE] at h; exact h
    simp only [h', ↓reduceIte]

/-- The precompile's output encoding of an address: the low 20 bytes of a word, left-padded
to 32 bytes, are the ABI word of the address. -/
theorem leftPad32_extract_ofWord (k : Word) :
    Precompile.leftPad32 ((ofWord k).extract 12 32) = ofWord (Word.ofAddress (Word.toAddress k)) := by
  have hsz : ((ofWord k).extract 12 32).size = 20 := by
    rw [ByteArray.size_extract, size_ofWord]; rfl
  unfold Precompile.leftPad32
  rw [hsz]
  apply ext_getD (by rw [ByteArray.size_append, size_zeros, hsz, size_ofWord])
  intro j hj
  rw [ByteArray.size_append, size_zeros, hsz] at hj
  have hv : (Word.ofAddress (Word.toAddress k)).toNat = k.toNat % 2 ^ 160 := by
    simp [Word.ofAddress, Word.toAddress, BitVec.toNat_setWidth]; omega
  rw [getD_append, size_zeros,
    show ofWord (Word.ofAddress (Word.toAddress k)) = ofNatBE 32 (Word.ofAddress (Word.toAddress k)).toNat
      from rfl, getD_ofNatBE, hv]
  simp only [show j < 32 from hj, ↓reduceIte]
  by_cases hj12 : j < 32 - 20
  · simp only [hj12, ↓reduceIte, getD_zeros]
    have hs : 160 ≤ 8 * (32 - 1 - j) := by omega
    have : (k.toNat % 2 ^ 160) >>> (8 * (32 - 1 - j)) = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      apply Nat.div_eq_of_lt
      exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
        (Nat.pow_le_pow_right (by decide) hs)
    rw [this]; rfl
  · simp only [hj12, ↓reduceIte, getD_extract, ofWord]
    rw [getD_ofNatBE]
    have hj32 : j < 32 := by omega
    simp only [show 12 + (j - (32 - 20)) = j by omega, hj32, ↓reduceIte]
    apply UInt8.toNat.inj
    simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow]
    have hs : 8 * (32 - 1 - j) + 8 ≤ 160 := by omega
    obtain ⟨t, ht⟩ : ∃ t, 160 = 8 * (32 - 1 - j) + 8 + t := ⟨160 - (8 * (32 - 1 - j) + 8), by omega⟩
    rw [ht, Nat.pow_add, Nat.pow_add, Nat.mul_assoc, Nat.mod_mul_right_div_self,
      Nat.mod_mul_right_mod]

/-- The four-word input of `ECRECOVER`, as reads of it see it. -/
theorem readPadded_words (a b c d : Word) :
    readPadded (ofWord a ++ (ofWord b ++ (ofWord c ++ ofWord d))) 0 32 = ofWord a ∧
    readPadded (ofWord a ++ (ofWord b ++ (ofWord c ++ ofWord d))) 32 32 = ofWord b ∧
    readPadded (ofWord a ++ (ofWord b ++ (ofWord c ++ ofWord d))) 64 32 = ofWord c ∧
    readPadded (ofWord a ++ (ofWord b ++ (ofWord c ++ ofWord d))) 96 32 = ofWord d := by
  have s := size_ofWord
  have e0 := Solidity.readPadded_append_of_le (ofWord a) (ofWord b ++ (ofWord c ++ ofWord d)) 0 32
    (by simp [s])
  have e1 := Solidity.readPadded_append_shift (ofWord a) (ofWord b ++ (ofWord c ++ ofWord d)) 0 32
  have e1' := Solidity.readPadded_append_of_le (ofWord b) (ofWord c ++ ofWord d) 0 32 (by simp [s])
  have e2 := Solidity.readPadded_append_shift (ofWord a) (ofWord b ++ (ofWord c ++ ofWord d)) 32 32
  have e2' := Solidity.readPadded_append_shift (ofWord b) (ofWord c ++ ofWord d) 0 32
  have e2'' := Solidity.readPadded_append_of_le (ofWord c) (ofWord d) 0 32 (by simp [s])
  have e3 := Solidity.readPadded_append_shift (ofWord a) (ofWord b ++ (ofWord c ++ ofWord d)) 64 32
  have e3' := Solidity.readPadded_append_shift (ofWord b) (ofWord c ++ ofWord d) 32 32
  have e3'' := Solidity.readPadded_append_shift (ofWord c) (ofWord d) 0 32
  simp only [s, Nat.add_zero] at e0 e1 e1' e2 e2' e2'' e3 e3' e3''
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e0, ← s a, readPadded_zero_size]
  · rw [e1, e1', ← s b, readPadded_zero_size]
  · rw [show (64 : Nat) = 32 + 32 from rfl, e2, e2', e2'', ← s c, readPadded_zero_size]
  · rw [show (96 : Nat) = 32 + 64 from rfl, e3, show (64 : Nat) = 32 + 32 from rfl, e3', e3'',
      ← s d, readPadded_zero_size]

/-- **`ECRECOVER` on `hash ‖ v ‖ r ‖ s`**: with at least 3000 gas it succeeds, costs 3000, and
returns the recovered signer as an ABI word, or nothing for an invalid signature. Holds for
every `Crypto`. -/
theorem ecrecover_words (crypto : Crypto) (hash v r s : Word) {gas : Nat} (h : 3000 ≤ gas) :
    Precompile.ecrecover crypto (ofWord hash ++ (ofWord v ++ (ofWord r ++ ofWord s))) gas =
      { success := true, gasLeft := gas - 3000,
        output := match ecrecoverAddress? crypto hash v r s with
          | some a => ofWord (Word.ofAddress a)
          | none => .empty } := by
  obtain ⟨h0, h1, h2, h3⟩ := readPadded_words hash v r s
  unfold Precompile.ecrecover ecrecoverAddress?
  simp only [Nat.not_lt.mpr h, ↓reduceIte, Precompile.readWord, h0, h1, h2, h3, toNat_ofWord]
  by_cases hv : v.toNat ≠ 27 ∧ v.toNat ≠ 28
  · simp [hv]
  · have hv' : ¬ (v.toNat ≠ 27 && v.toNat ≠ 28) = true := by simpa using hv
    simp only [hv, hv', ↓reduceIte]
    by_cases hr : r.toNat = 0 ∨ Secp256k1.n ≤ r.toNat ∨ s.toNat = 0 ∨ Secp256k1.n ≤ s.toNat
    · have hr' : (r.toNat = 0 || r.toNat ≥ Secp256k1.n || s.toNat = 0 ||
          s.toNat ≥ Secp256k1.n) = true := by
        simp only [ge_iff_le, Bool.or_eq_true, decide_eq_true_eq]; omega
      simp only [hr, hr', ↓reduceIte]
      simp
    · have hr' : ¬ (r.toNat = 0 || r.toNat ≥ Secp256k1.n || s.toNat = 0 ||
          s.toNat ≥ Secp256k1.n) = true := by
        simp only [ge_iff_le, Bool.or_eq_true, decide_eq_true_eq]; omega
      simp only [hr, hr', ↓reduceIte]
      cases crypto.ecrecover (ofWord hash) (v.toNat - 27) r.toNat s.toNat with
      | none => simp
      | some pub => simp [Option.map_some, leftPad32_extract_ofWord]

/-! ## The call -/

open Interpreter

/-- The calldata of a child message is the input window of the caller's memory. -/
theorem childMsg_data (m : Machine) (caller to codeAddress : Address) (value : Word) (gas : Nat)
    (stv st : Bool) (inOff inSize outOff outSize : Word) :
    (childMsg m caller to codeAddress value gas stv st inOff inSize outOff outSize).data =
      m.frame.memory.read inOff.toNat inSize.toNat := by
  simp only [childMsg, callMemory, readBytes_bytes, Memory.read_expand]

/-- What `ECRECOVER` writes back: the signer's ABI word, or nothing. -/
def ecrecoverOutput (crypto : Crypto) (hash v r s : Word) : ByteArray :=
  match ecrecoverAddress? crypto hash v r s with
  | some a => ofWord (Word.ofAddress a)
  | none => .empty

/-- The caller's memory after `ECRECOVER` returned into a one-word output window: the signer's
word stored there, or unchanged. -/
theorem returnMemory_ecrecoverOutput (mem : Memory) (off : Nat) (crypto : Crypto)
    (hash v r s : Word) :
    returnMemory mem off 32 (ecrecoverOutput crypto hash v r s) =
      match ecrecoverAddress? crypto hash v r s with
      | some a => mem.storeWord off (Word.ofAddress a)
      | none => mem := by
  unfold ecrecoverOutput
  cases ecrecoverAddress? crypto hash v r s with
  | some a => exact returnMemory_ofWord mem off _
  | none =>
    unfold returnMemory
    have : (ByteArray.empty.extract 0 (min 32 ByteArray.empty.size)).size = 0 := by simp
    simp only [this, ↓reduceIte]

variable {m : Machine} {gas inOff outOff : Word} {rest : List Word}

/-- **`ecrecover(hash, v, r, s)` as solc calls it**: `STATICCALL(gas, 0x01, inOff, 128, outOff,
32)` with the four words at `inOff`, under the standard precompiles of the machine's context
(any `Crypto`). If the forwarded gas covers the precompile's 3000, the caller continues with
`1` pushed, `3000` gas spent beyond the call's own charges, the signer's word written at
`outOff` (or memory unchanged for an invalid signature, `returnMemory_ecrecoverOutput`) and
kept as return data. -/
theorem WP.staticcall_ecrecover {Q : Machine → Prop} {H : Machine → Outcome → Prop}
    {hash v r s : Word}
    (hcode : m.frame.code[m.frame.pc]? = some 0xfa)
    (hstk : m.frame.stack = gas :: 1#256 :: inOff :: 128#256 :: outOff :: 32#256 :: rest)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hgas : callCost m gas 0 1 0 0 inOff 128#256 outOff 32#256 ≤ m.frame.gasLeft)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hin : m.frame.memory.read inOff.toNat 128 =
      ofWord hash ++ (ofWord v ++ (ofWord r ++ ofWord s)))
    (hsub : 3000 ≤ (callGas m gas 0 1 0 0 inOff 128#256 outOff 32#256).subCall)
    (k : WP { m with frame := { callerFrame m rest (callCost m gas 0 1 0 0 inOff 128#256 outOff
          32#256) 1 inOff 128#256 outOff 32#256 with
        gasLeft := m.frame.gasLeft - callCost m gas 0 1 0 0 inOff 128#256 outOff 32#256 +
          ((callGas m gas 0 1 0 0 inOff 128#256 outOff 32#256).subCall - 3000)
        sub := mergeSub (m.frame.sub.warmAddr 1)
          (Substate.ofMessage (childMsg m m.frame.msg.currentTarget 1 1 0
            (callGas m gas 0 1 0 0 inOff 128#256 outOff 32#256).subCall true true inOff 128#256
            outOff 32#256)) m.world 1
        returnData := ecrecoverOutput m.ctx.crypto hash v r s
        stack := 1 :: rest
        memory := returnMemory (callMemory m inOff 128#256 outOff 32#256) outOff.toNat 32
          (ecrecoverOutput m.ctx.crypto hash v r s)
        pc := m.frame.pc + 1 } } Q H) :
    WP m Q H := by
  have hto : Word.toAddress (1#256) = 1 := by decide
  have hpre : m.precompiles.isPrecompile (Word.toAddress 1#256) = true := by
    rw [hstd, hto]; exact isPrecompile_one _
  refine WP.staticcall_precompile hcode hstk (by rw [hto]; exact hdel) (by rw [hto]; exact hgas)
    hdepth hpre ?_
  have hrun : ∀ msg : Message, msg.data = ofWord hash ++ (ofWord v ++ (ofWord r ++ ofWord s)) →
      3000 ≤ msg.gas → m.precompiles.run 1 msg.data msg.gas =
        { success := true, gasLeft := msg.gas - 3000,
          output := ecrecoverOutput m.ctx.crypto hash v r s } := by
    intro msg hd hg
    rw [hstd, hd]
    exact (run_one _ _ _ _).trans (ecrecover_words _ _ _ _ _ hg)
  rw [hto]
  have hd := childMsg_data m m.frame.msg.currentTarget 1 1 0
    (callGas m gas 0 1 0 0 inOff 128#256 outOff 32#256).subCall true true inOff 128#256 outOff
    32#256
  rw [BitVec.toNat_ofNat, show 128 % 2 ^ 256 = 128 by decide, hin] at hd
  have hr := hrun _ hd hsub
  rw [resume_precompile_success (by rw [hr])]
  rw [hr]
  exact k

end EvmLean.Program
