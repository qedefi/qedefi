import EvmLeanProofs.Program.Tactic
import EvmLeanProofs.Program.Call

namespace EvmLean.Program.Examples.TwoContracts

open Interpreter

/-- Runtime code of `B` (solc 0.8.28, `--optimize --optimize-runs 200 --evm-version cancun`). -/
def codeB : ByteArray := ⟨#[
  0x60, 0x80, 0x60, 0x40, 0x52, 0x34, 0x80, 0x15, 0x60, 0x0e, 0x57, 0x5f, 0x5f, 0xfd, 0x5b, 0x50,
  0x60, 0x04, 0x36, 0x10, 0x60, 0x26, 0x57, 0x5f, 0x35, 0x60, 0xe0, 0x1c, 0x80, 0x63, 0x6d, 0x4c,
  0xe6, 0x3c, 0x14, 0x60, 0x2a, 0x57, 0x5b, 0x5f, 0x5f, 0xfd, 0x5b, 0x5f, 0x54, 0x60, 0x40, 0x51,
  0x90, 0x81, 0x52, 0x60, 0x20, 0x01, 0x60, 0x40, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3, 0xfe, 0xa2,
  0x64, 0x69, 0x70, 0x66, 0x73, 0x58, 0x22, 0x12, 0x20, 0xcf, 0x57, 0x00, 0xee, 0xe4, 0x91, 0x14,
  0x99, 0xb3, 0xe0, 0xca, 0x7f, 0xdd, 0xd9, 0x16, 0xb7, 0xe2, 0x6f, 0x3d, 0x63, 0xae, 0xed, 0x62,
  0x9f, 0x4d, 0xd9, 0xbd, 0xb3, 0x09, 0xac, 0x84, 0xc1, 0x64, 0x73, 0x6f, 0x6c, 0x63, 0x43, 0x00,
  0x08, 0x1c, 0x00, 0x33]⟩

/-- Runtime code of `A`. -/
def codeA : ByteArray := ⟨#[
  0x60, 0x80, 0x60, 0x40, 0x52, 0x34, 0x80, 0x15, 0x60, 0x0e, 0x57, 0x5f, 0x5f, 0xfd, 0x5b, 0x50,
  0x60, 0x04, 0x36, 0x10, 0x60, 0x26, 0x57, 0x5f, 0x35, 0x60, 0xe0, 0x1c, 0x80, 0x63, 0x26, 0x12,
  0x1f, 0xf0, 0x14, 0x60, 0x2a, 0x57, 0x5b, 0x5f, 0x5f, 0xfd, 0x5b, 0x60, 0x30, 0x60, 0x42, 0x56,
  0x5b, 0x60, 0x40, 0x51, 0x90, 0x81, 0x52, 0x60, 0x20, 0x01, 0x60, 0x40, 0x51, 0x80, 0x91, 0x03,
  0x90, 0xf3, 0x5b, 0x5f, 0x61, 0xbe, 0xef, 0x60, 0x01, 0x60, 0x01, 0x60, 0xa0, 0x1b, 0x03, 0x16,
  0x63, 0x6d, 0x4c, 0xe6, 0x3c, 0x60, 0x40, 0x51, 0x81, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x60,
  0xe0, 0x1b, 0x81, 0x52, 0x60, 0x04, 0x01, 0x60, 0x20, 0x60, 0x40, 0x51, 0x80, 0x83, 0x03, 0x81,
  0x86, 0x5a, 0xfa, 0x15, 0x80, 0x15, 0x60, 0x80, 0x57, 0x3d, 0x5f, 0x5f, 0x3e, 0x3d, 0x5f, 0xfd,
  0x5b, 0x50, 0x50, 0x50, 0x50, 0x60, 0x40, 0x51, 0x3d, 0x60, 0x1f, 0x19, 0x60, 0x1f, 0x82, 0x01,
  0x16, 0x82, 0x01, 0x80, 0x60, 0x40, 0x52, 0x50, 0x81, 0x01, 0x90, 0x60, 0xa2, 0x91, 0x90, 0x60,
  0xa7, 0x56, 0x5b, 0x90, 0x50, 0x90, 0x56, 0x5b, 0x5f, 0x60, 0x20, 0x82, 0x84, 0x03, 0x12, 0x15,
  0x60, 0xb6, 0x57, 0x5f, 0x5f, 0xfd, 0x5b, 0x50, 0x51, 0x91, 0x90, 0x50, 0x56, 0xfe, 0xa2, 0x64,
  0x69, 0x70, 0x66, 0x73, 0x58, 0x22, 0x12, 0x20, 0x2c, 0x93, 0x6e, 0xcd, 0xdd, 0x6c, 0xe7, 0x5f,
  0xe2, 0x13, 0x3e, 0x3c, 0xa5, 0x0f, 0x2b, 0xa2, 0xfd, 0xd1, 0x57, 0xa0, 0xff, 0xb1, 0xfb, 0x91,
  0x0a, 0x4d, 0x82, 0xe3, 0xf6, 0x84, 0xa6, 0x54, 0x64, 0x73, 0x6f, 0x6c, 0x63, 0x43, 0x00, 0x08,
  0x1c, 0x00, 0x33]⟩

/-- `a < b` is false as a word comparison when `b ≤ a < 2²⁵⁶`. -/
theorem lt_ofNat_eq_zero {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 256) :
    Word.lt (ofNat a) (BitVec.ofNat 256 b) = 0 := by
  rw [Word.lt_eq_zero_iff]
  simp only [ofNat, BitVec.toNat_ofNat]
  omega

/-! ## `B.get()` -/

/-- Memory after solc's prologue `mstore(0x40, 0x80)`. -/
def fmpMemory : Memory := (({} : Memory).expand 64 32).storeWord 64 128#256

/-- Precondition of `B.get()`: no value, calldata starting with the selector `0x6d4ce63c`,
at least 3000 gas. -/
def getPre (m : Machine) : Prop :=
  m.frame.msg.value = 0 ∧ 4 ≤ m.frame.msg.data.size ∧ m.frame.msg.data.size < 2 ^ 256 ∧
    selectorOf m.frame.msg.data = 0x6d4ce63c#256 ∧ 3000 ≤ m.frame.gasLeft

/-- The machine at the entry of `get`'s body. -/
def getEntry (m m' : Machine) : Prop :=
  m' = { m with frame := { m.frame with
    pc := 0x2a, stack := [0x6d4ce63c#256], memory := fmpMemory, gasLeft := m.frame.gasLeft - 96 } }

/-- Postcondition of `B.get()`: returns slot 0 of the executing account, changes no state,
uses at most 2400 gas, emits no logs. -/
def getPost (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord (m.world.sload m.frame.msg.currentTarget 0)) ∧
    mf.world = m.world ∧ mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    m.frame.gasLeft ≤ mf.frame.gasLeft + 2400 ∧ mf.frame.sub.logs = m.frame.sub.logs

set_option maxHeartbeats 0 in
/-- `B`'s dispatcher reaches `get`. -/
theorem get_dispatch (m : Machine) (hf : Fresh codeB m) (hpre : getPre m) :
    WP m (fun m' => m'.frame.pc = 0x2a ∧ getEntry m m') (getPost m) := by
  obtain ⟨hc, hj, hpc, hs, hmem, -, -⟩ := hf.frame
  obtain ⟨hval, hsize, hsize', hsel, hg⟩ := hpre
  simp only [selectorOf] at hsel
  wp_intro m
  wp_run_to 0x2a [hval, hsel, lt_ofNat_eq_zero hsize hsize']
  exact WP.ret ⟨rfl, by simp only [getEntry, fmpMemory]⟩

set_option maxHeartbeats 0 in
/-- The body of `get`. -/
theorem get_body (m m' : Machine) (hf : Fresh codeB m) (hpre : getPre m) (hs : SameFrame m m')
    (he : getEntry m m') : Halts m' (getPost m) := by
  obtain ⟨hc, hj, -, -, -, -, -⟩ := hf.frame
  obtain ⟨-, -, -, -, hg⟩ := hpre
  subst he
  apply WP.halts_of_false
  wp_intro m
  wp_steps [fmpMemory]
  simp only [getPost, outputMachine, true_and]
  refine ⟨rfl, ?_, rfl⟩
  evm_gas

/-- `B.get()` as a function summary. -/
def getSummary : FunctionSummary codeB where
  entry := 0x2a
  pre := getPre
  atEntry := getEntry
  post := getPost
  dispatch := get_dispatch
  body m m' hf hpre hs _ he := get_body m m' hf hpre hs he

/-! ## `A.f()` -/

/-- `B`'s address in `A`. -/
def addrB : Address := 0xbeef

theorem toAddress_beef : Word.toAddress 48879#256 = addrB := by decide

/-- `B`'s code is not a delegation designator. -/
theorem delegatedAddress?_codeB : delegatedAddress? codeB = none := by decide +kernel

/-- Postcondition of `A.f()`: returns `B`'s slot 0, world unchanged. -/
def fPost (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord (m.world.sload addrB 0)) ∧ mf.world = m.world

set_option maxHeartbeats 0 in
theorem f_halts (m : Machine) (hf : Fresh codeA m) (hval : m.frame.msg.value = 0)
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 256)
    (hsel : selectorOf m.frame.msg.data = 0x26121ff0#256) (hg : 20000 ≤ m.frame.gasLeft)
    (hg' : m.frame.gasLeft < 2 ^ 64) (hcodeB : m.world.code addrB = codeB)
    (hpre : m.precompiles.isPrecompile addrB = false)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit) :
    Halts m (fPost m) := by
  apply WP.halts_of_false
  obtain ⟨hc, hj, hpc, hs, hmem, -, -⟩ := hf.frame
  simp only [selectorOf] at hsel
  wp_intro m
  wp_run_to 0x72 [hval, hsel, lt_ofNat_eq_zero hsize hsize']
  have hacc := accessCost_le (m_sub.accessedAddresses.contains addrB)
  have hmod : (m_gasLeft - 203) % 2 ^ 256 = m_gasLeft - 203 := Nat.mod_eq_of_lt (by omega)
  refine WP.staticcall (by code_fact) rfl ?_ ?_ ?_ ?_ (getSummary.halts ?_ ?_) ?_
  · exact .inr (by dsimp only; rw [toAddress_beef, hcodeB]; exact delegatedAddress?_codeB)
  · simp only [callCost, callGas, callExt, toAddress_beef, ofNat, BitVec.toNat_ofNat, hmod,
      Nat.reducePow, Nat.reduceMod]
    rw [messageCallGas_zero (by evm_gas)]
    simp only [Gas.maxMessageCallGas]
    evm_gas
  · exact hdepth
  · rw [toAddress_beef]; exact hpre
  · exact ⟨_, _, _, rfl, by dsimp only [childMsg]; rw [toAddress_beef]; exact hcodeB⟩
  · dsimp only [getPre]
    dsimp only [Frame.init, childMsg, callMemory]
    refine ⟨rfl, by simp, by simp, ?_, ?_⟩
    · simp only [readBytes_bytes, Memory.read_expand, BitVec.reduceToNat,
        Memory.read_storeWord_prefix _ _ 4 _ (by decide)]
      decide +kernel
    show 3000 ≤ (callGas _ (ofNat (m_gasLeft - 203)) 0 _ 0 0 _ _ _ _).subCall
    simp only [callGas, callExt, toAddress_beef, ofNat, BitVec.toNat_ofNat, hmod,
      Nat.reducePow, Nat.reduceMod]
    rw [messageCallGas_zero (by evm_gas)]
    simp only [Gas.maxMessageCallGas]
    evm_gas
  · intro mf o ⟨ho, hw, ht, hca, hgasB, hlogs⟩ hsame
    have hk : mf.frame.kind = .call 128 32 := hsame.kind
    subst ho
    rw [resumeAfter_success hk]
    dsimp only [callerFrame, callMemory, Frame.init, childMsg] at hgasB ⊢
    simp only [toAddress_beef, returnMemory_ofWord, callCost, callGas, callExt, ofNat,
      BitVec.toNat_ofNat, hmod, Nat.reducePow, Nat.reduceMod] at hgasB ⊢
    rw [messageCallGas_zero (by evm_gas)] at hgasB ⊢
    simp only [Gas.maxMessageCallGas] at hgasB ⊢
    wp_steps
    exact ⟨rfl, hw⟩

/-- `A`'s code is not a delegation designator. -/
theorem delegatedAddress?_codeA : delegatedAddress? codeA = none := by decide +kernel

/-- **`A.f()` returns `B`'s storage slot 0**, for every `Crypto`, context without EIP-7702
authorizations (or before Prague), world in which `addrB` holds `B`'s code, transient storage,
caller, calldata selecting `f`, and gas in `[20000, 2⁶⁴)`; the world is unchanged. `B`'s
behaviour enters only through its summary `getSummary` (via `WP.staticcall`). -/
theorem f_processMessageCall {ctx : Context} {w : World} {tr : TransientStorage}
    {msg : Message} {a : Address}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork a = false)
    (hpreB : Precompile.isPrecompile ctx.fork addrB = false) (hcodeB : w.code addrB = codeB)
    (htarget : msg.target = some a) (hca : msg.codeAddress = some a) (hcode : msg.code = codeA)
    (hval : msg.value = 0) (hdepth : msg.depth = 0) (hsize : 4 ≤ msg.data.size)
    (hsize' : msg.data.size < 2 ^ 256) (hsel : selectorOf msg.data = 0x26121ff0#256)
    (hgas : 20000 ≤ msg.gas) (hgas' : msg.gas < 2 ^ 64) :
    ∃ N, ∀ fuel, N ≤ fuel → ∃ r, processMessageCall fuel ctx w tr msg = .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord (w.sload addrB 0) ∧ r.world = w := by
  have hf := fresh_startMachine ctx w tr msg
  rw [hcode] at hf
  obtain ⟨-, -, -, -, -, hg, -⟩ := hf.frame
  obtain ⟨N, hN⟩ := processMessageCall_of_halts hdeleg (hcode ▸ delegatedAddress?_codeA) htarget
    hca hpre hval hdepth (f_halts _ hf hval hsize hsize' hsel (hg ▸ hgas) (hg ▸ hgas') hcodeB
      hpreB (by simp only [startMachine, Frame.init, hdepth, Gas.stackDepthLimit]; omega))
  refine ⟨N, fun fuel hle => ?_⟩
  obtain ⟨mf, o, ⟨rfl, hw⟩, hsame, hrun⟩ := hN fuel hle
  have hk : mf.frame.kind = .call 0 0 := hsame.kind
  obtain ⟨h1, h2, h3, -⟩ := topLevelResult_success_call (t := msg.target)
    (out := Bytes.ofWord (w.sload addrB 0)) hk
  exact ⟨_, hrun, h1, h2, h3.trans hw⟩

end EvmLean.Program.Examples.TwoContracts
