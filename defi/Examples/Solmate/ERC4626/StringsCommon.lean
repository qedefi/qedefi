import Examples.Solmate.ERC4626.Views
import EvmLogic.Tactic.Mcopy
import EvmLogic.Solidity.Strings

/-!
# String getters: shared definitions

The postcondition and precondition of a `string` getter's frame (`StringPost`, `StringPre`), its
top-level result (`StringResult`, `string_call`, `stringPre_start`) and memory facts used by both
the vault's and the asset's getters (`Strings.lean` in `ERC4626/` and `ERC20/`).
-/

section

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts EvmLean.Bytes

/-- What a `string` getter ends with: the world unchanged, and the ABI encoding of the string
`s` when the slot decodes to `some s`, a revert when it is inconsistent. -/
def StringPost (m : Machine) (r : Option ByteArray) (mf : Machine) (o : Outcome) : Prop :=
  mf.world = m.world ∧
    match r with
    | some s => o = .success (Abi.encodeString s)
    | none => ∃ out, o = .revert out

theorem read_encodeShort (M : Memory) {L : Nat} {data : ByteArray} (hL1 : 1 ≤ L) (hL : L ≤ 31)
    (hd : M.read 160 L = data)
    (hh : M.read 192 64 = ofWord 32#256 ++ ofWord (BitVec.ofNat 256 L)) :
    (((M.mcopy 256 160 L).expand (L + 256) 32).storeWord (L + 256) 0#256).read 192 96 =
      Abi.encodeString data := by
  have hsz : data.size = L := by rw [← hd, Memory.size_read]
  generalize hM2 : ((M.mcopy 256 160 L).expand (L + 256) 32).storeWord (L + 256) 0#256 = M2
  have e1 : M2.read 192 96 = M2.read 192 64 ++ (M2.read 256 L ++ M2.read (L + 256) (32 - L)) := by
    rw [show (96 : Nat) = 64 + (L + (32 - L)) by omega, Memory.read_add, Memory.read_add,
      show 192 + 64 = 256 from rfl, show 256 + L = L + 256 by omega]
  rw [e1, ← hM2, Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega),
    Memory.read_expand, Memory.read_mcopy_of_disjoint _ _ _ _ _ _ (by omega), hh,
    Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand, Memory.read_mcopy,
    hd, Memory.read_storeWord_prefix (hn := by omega), extract_ofWord_zero (by omega)]
  simp only [Abi.encodeString, hsz, show (L + 31) / 32 * 32 - L = 32 - L by omega,
    ByteArray.append_assoc]

theorem add_one_ptr (h : Word) (k : Nat) :
    1#256 + (h + BitVec.ofNat 256 k) = h + BitVec.ofNat 256 (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem Memory.read_prefix (M : Memory) {off a b : Nat} (h : a ≤ b) :
    M.read off a = (M.read off b).extract 0 a := by
  apply ext_getD (by simp only [Memory.size_read, ByteArray.size_extract]; omega)
  intro j hj
  rw [Memory.size_read] at hj
  simp only [Memory.read, getD_readPadded, getD_extract, hj, ↓reduceIte, Nat.zero_add,
    show j < b by omega]

/-- The start of a string getter's frame: fresh, no value, gas `Str.getterGas` of the stored
length (below `2⁶⁴`), calldata below `2⁶⁴` bytes. -/
structure StringPre (code : ByteArray) (slot : Word) (m : Machine) : Prop where
  fresh : Fresh code m
  value : m.frame.msg.value = 0
  gas : Str.getterGas (Str.slotLen (m.world.sload m.frame.msg.currentTarget slot)) ≤
    m.frame.gasLeft
  gasLt : m.frame.gasLeft < 2 ^ 64
  sizeLt : m.frame.msg.data.size < 2 ^ 64

theorem getterGas_le {L g : Nat} (h : Str.getterGas L ≤ g) (c : Nat) (hc : c ≤ 3000) :
    5000 + 2400 * ((L + 31) / 32) + Gas.memoryCost (256 + 64 * ((L + 31) / 32)) ≤ g - c := by
  unfold Str.getterGas at h; omega

/-- What a top-level call of a string getter returns: success with `Abi.encodeString s` for
`some s`, a revert for `none`. -/
def StringResult (res : MessageResult) (r : Option ByteArray) : Prop :=
  match r with
  | some s => res.success = true ∧ res.output = Abi.encodeString s
  | none => res.success = false ∧ res.reverted = true

variable {ctx : Context} {w : World} {tr : TransientStorage} {vault asset caller : Address}
  {data : ByteArray} {gas : Nat} {wa : AddressSet} {wk : StorageKeySet}

theorem string_call {code : ByteArray} {a : Address} {r : Option ByteArray}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hdel : delegatedAddress? code = none) (hpre : Precompile.isPrecompile ctx.fork a = false)
    (h : Halts (startMachine ctx w tr (callMsg code a caller data gas wa wk))
      (StringPost (startMachine ctx w tr (callMsg code a caller data gas wa wk)) r)) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg code a caller data gas wa wk) = .ok res ∧ res.world = w ∧ StringResult res r := by
  obtain ⟨n, hn⟩ := processMessageCall_of_halts (a := a)
    (msg := callMsg code a caller data gas wa wk) hdeleg hdel rfl rfl hpre rfl rfl h
  refine ⟨n, fun fuel hle => ?_⟩
  obtain ⟨mf, o, ⟨hw, ho⟩, hs, hrun⟩ := hn fuel hle
  have hk : mf.frame.kind = .call 0 0 := hs.kind
  refine ⟨_, hrun, ?_⟩
  cases r with
  | some v =>
    simp only at ho
    subst ho
    obtain ⟨h1, h2, h3, -⟩ := topLevelResult_success_call
      (t := (callMsg code a caller data gas wa wk).target) (out := Abi.encodeString v) hk
    exact ⟨h3.trans hw, h1, h2⟩
  | none =>
    obtain ⟨out, ho⟩ := ho
    subst ho
    have hsnap : mf.frame.snapshot.1 = w := by rw [hs.snapshot]; rfl
    simp only [frameResult_revert, topLevelResult_world, topLevelResult_success,
      topLevelResult_reverted, StringResult, ChildResult.success, hsnap]
    decide

theorem stringPre_start {code : ByteArray} {a : Address} {slot : Word}
    (hgas : Str.getterGas (Str.slotLen (w.sload a slot)) ≤ gas) (hgas' : gas < 2 ^ 64)
    (hsize : data.size < 2 ^ 64) :
    StringPre code slot (startMachine ctx w tr (callMsg code a caller data gas wa wk)) where
  fresh := fresh_startMachine ctx w tr (callMsg code a caller data gas wa wk)
  value := rfl
  gas := hgas
  gasLt := hgas'
  sizeLt := hsize

end Examples.Solmate.ERC4626

end
