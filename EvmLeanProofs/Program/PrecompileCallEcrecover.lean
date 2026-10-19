import EvmLeanProofs.Program.PrecompileCall
import EvmLeanProofs.Solidity.Abi

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

end EvmLean.Program
