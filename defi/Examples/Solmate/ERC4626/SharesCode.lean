import EvmLogic.Tactic.Patched
import EvmLogic.Solidity.Dispatch
import EvmLogic.Solidity.ERC20
import Examples.Solmate.Contracts.SolmateVault
import Examples.Solmate.Contracts.Deploy
import EvmLogic.Tactic.KernelRfl

/-!
# The vault's share token: code, calldata, dispatch

Shared definitions for the share-token proofs of the compiled vault for **arbitrary immutables**
(`code i = SolmateVault.runtimeCodeWith i`), and the top-level bytecode theorems (`*_ok`,
`*_revert`) behind `Shares.lean`. Symbolic execution uses `psol_steps` with `jumpDestsAgree`.
-/

section

namespace Examples.Solmate.ERC4626.Shares

open EvmLean Examples.Solmate EvmLogic EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic
open Examples.Solmate.Contracts EvmLogic.Solidity.Dispatch

/-! ## Code -/

/-- The runtime code of the vault deployed with immutables `i`. -/
abbrev code (i : SolmateVault.Immutables) : ByteArray := SolmateVault.runtimeCodeWith i

theorem code_deployment : code SolmateVault.deployment = SolmateVault.runtimeCode :=
  SolmateVault.runtimeCodeWith_deployment

theorem code_immutablesFor (keccak256 : ByteArray → Word) (chainId : Nat) (asset self : Address) :
    code (SolmateVault.immutablesFor keccak256 chainId asset self) =
      SolmateVault.runtimeCodeFor keccak256 chainId asset self := rfl

theorem decimals_immutablesFor (keccak256 : ByteArray → Word) (chainId : Nat)
    (asset self : Address) : (SolmateVault.immutablesFor keccak256 chainId asset self).decimals = 18#256 :=
  rfl

/-- The patches only touch `PUSH32` immediates, so the jump table is the canonical one for all
immutables (kernel evaluation of the `JUMPDEST` scan, which skips the patched bytes). -/
theorem jumpDestsAgree (i : SolmateVault.Immutables) :
    JumpDestsAgree (code i) SolmateVault.runtimeCode := by
  unfold JumpDestsAgree; kernel_decide

theorem size_code (i : SolmateVault.Immutables) : (code i).size = 5248 := by
  exact (size_patchWords _ _).trans SolmateVault.size_runtimeCode

theorem delegatedAddress?_code (i : SolmateVault.Immutables) : delegatedAddress? (code i) = none :=
  delegatedAddress?_of_size (by rw [size_code]; decide)

-- The `decimals` immutable, as the `PUSH32` at 622 reads it.
theorem readBytes_code_decimals (i : SolmateVault.Immutables) :
    readBytes (code i) 623 32 = Bytes.ofWord i.decimals := by
  have hp : i.patches = [(1831, i.initialChainId), (1879, i.initialDomainSeparator),
      (688, Word.ofAddress i.asset), (1170, Word.ofAddress i.asset),
      (2014, Word.ofAddress i.asset), (2169, Word.ofAddress i.asset),
      (2668, Word.ofAddress i.asset), (2995, Word.ofAddress i.asset)] ++ (623, i.decimals) :: [] :=
    rfl
  simp only [code, SolmateVault.runtimeCodeWith, hp]
  exact readBytes_patchWords_last _ _ _ _ _ (by rw [SolmateVault.size_runtimeCode]; decide)
    (by simp)

/-! ## Calldata -/

def transferData (dst : Address) (amount : Word) : ByteArray :=
  Abi.encodeCall 0xa9059cbb [Word.ofAddress dst, amount]

def approveData (spender : Address) (amount : Word) : ByteArray :=
  Abi.encodeCall 0x095ea7b3 [Word.ofAddress spender, amount]

def transferFromData (src dst : Address) (amount : Word) : ByteArray :=
  Abi.encodeCall 0x23b872dd [Word.ofAddress src, Word.ofAddress dst, amount]

def balanceOfData (a : Address) : ByteArray := Abi.encodeCall 0x70a08231 [Word.ofAddress a]

def allowanceData (owner spender : Address) : ByteArray :=
  Abi.encodeCall 0xdd62ed3e [Word.ofAddress owner, Word.ofAddress spender]

def totalSupplyData : ByteArray := Abi.encodeCall 0x18160ddd []

def decimalsData : ByteArray := Abi.encodeCall 0x313ce567 []

theorem selectors_mem :
    ("transfer(address,uint256)", (0xa9059cbb : UInt32)) ∈ SolmateVault.selectors ∧
    ("approve(address,uint256)", (0x095ea7b3 : UInt32)) ∈ SolmateVault.selectors ∧
    ("transferFrom(address,address,uint256)", (0x23b872dd : UInt32)) ∈ SolmateVault.selectors ∧
    ("balanceOf(address)", (0x70a08231 : UInt32)) ∈ SolmateVault.selectors ∧
    ("allowance(address,address)", (0xdd62ed3e : UInt32)) ∈ SolmateVault.selectors ∧
    ("totalSupply()", (0x18160ddd : UInt32)) ∈ SolmateVault.selectors ∧
    ("decimals()", (0x313ce567 : UInt32)) ∈ SolmateVault.selectors := by
  decide

/-- A top-level, zero-value call of the vault (immutables `i`) deployed at `vault`. -/
abbrev vaultCall (i : SolmateVault.Immutables) (vault caller : Address) (data : ByteArray)
    (gas : Nat) (warmAddrs : AddressSet) (warmKeys : StorageKeySet) : Message :=
  callMsg (code i) vault caller data gas warmAddrs warmKeys

theorem processMessageCall_vaultCall {i : SolmateVault.Immutables} {ctx : Context} {w : World}
    {tr : TransientStorage} {vault caller : Address} {data : ByteArray} {gas : Nat}
    {warmAddrs : AddressSet} {warmKeys : StorageKeySet}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork vault = false) (fuel : Nat) :
    processMessageCall fuel ctx w tr (vaultCall i vault caller data gas warmAddrs warmKeys) =
      run fuel (start ctx w tr (vaultCall i vault caller data gas warmAddrs warmKeys)) :=
  processMessageCall_callMsg hdeleg (delegatedAddress?_code i) hpre fuel

/-! ## Dispatch -/

set_option maxHeartbeats 1000000 in
theorem reaches_transfer (i : SolmateVault.Immutables) : Reaches (code i) 0xa9059cbb 893 51 208 := by
  have hjd := jumpDestsAgree i
  psol_dispatch

set_option maxHeartbeats 1000000 in
theorem reaches_approve (i : SolmateVault.Immutables) : Reaches (code i) 0x095ea7b3 536 41 164 := by
  have hjd := jumpDestsAgree i
  psol_dispatch

set_option maxHeartbeats 1000000 in
theorem reaches_transferFrom (i : SolmateVault.Immutables) :
    Reaches (code i) 0x23b872dd 599 56 230 := by
  have hjd := jumpDestsAgree i
  psol_dispatch

set_option maxHeartbeats 1000000 in
theorem reaches_totalSupply (i : SolmateVault.Immutables) :
    Reaches (code i) 0x18160ddd 590 51 208 := by
  have hjd := jumpDestsAgree i
  psol_dispatch

set_option maxHeartbeats 1000000 in
theorem reaches_balanceOf (i : SolmateVault.Immutables) : Reaches (code i) 0x70a08231 804 50 207 := by
  have hjd := jumpDestsAgree i
  psol_dispatch

set_option maxHeartbeats 1000000 in
theorem reaches_allowance (i : SolmateVault.Immutables) :
    Reaches (code i) 0xdd62ed3e 1077 44 184 := by
  have hjd := jumpDestsAgree i
  psol_dispatch

set_option maxHeartbeats 1000000 in
theorem reaches_decimals (i : SolmateVault.Immutables) : Reaches (code i) 0x313ce567 618 41 164 := by
  have hjd := jumpDestsAgree i
  psol_dispatch

/-! ## Calldata facts -/

theorem encodeCall_facts (sel : Nat) (args : List Word) (hsel : sel < 2 ^ 32)
    (hn : 4 + 32 * args.length < 2 ^ 256) :
    Abi.selectorOf (Abi.encodeCall sel args) = sel ∧ 4 ≤ (Abi.encodeCall sel args).size ∧
      (Abi.encodeCall sel args).size < 2 ^ 256 := by
  rw [Abi.selectorOf_encodeCall, Abi.size_encodeCall]
  exact ⟨Nat.mod_eq_of_lt hsel, by omega, hn⟩

end Examples.Solmate.ERC4626.Shares

end

section

/-! ## `transfer`: bytecode -/

namespace Examples.Solmate.ERC4626.Shares

open EvmLean Examples.Solmate EvmLogic EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic
open Examples.Solmate.Contracts EvmLogic.Solidity.Dispatch EvmLogic.Solidity.ERC20 EvmLean.Bytes

variable {i : SolmateVault.Immutables} {ctx : Context} {w : World} {tr : TransientStorage}
  {vault caller dst : Address} {amount : Word} {gas : Nat} {warmAddrs : AddressSet}
  {warmKeys : StorageKeySet}

theorem run_start_transfer (hgas : 208 ≤ gas) (k : Nat) :
    run (k + 51) (start ctx w tr (vaultCall i vault caller (transferData dst amount) gas warmAddrs
      warmKeys)) =
      run k { start ctx w tr (vaultCall i vault caller (transferData dst amount) gas warmAddrs
          warmKeys) with
        frame := { (start ctx w tr (vaultCall i vault caller (transferData dst amount) gas warmAddrs
          warmKeys)).frame with
          pc := 893, stack := [BitVec.ofNat 256 0xa9059cbb], memory := initMemory,
          gasLeft := gas - 208 } } :=
  have h := encodeCall_facts 0xa9059cbb [Word.ofAddress dst, amount] (by decide) (by simp)
  (reaches_transfer i).run_start h.1 h.2.1 h.2.2 hgas k

set_option maxHeartbeats 10000000 in
/-- **`transfer`, success**: returns `true`, world `transferWorld`. -/
theorem transfer_ok (hgas : 100000 ≤ gas)
    (hbal : amount.toNat ≤ ((view ctx.crypto Layout.solmate w vault).balanceOf caller).toNat)
    (k : Nat) :
    ∃ r, run (k + 400) (start ctx w tr
        (vaultCall i vault caller (transferData dst amount) gas warmAddrs warmKeys)) = .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord 1 ∧
      r.world = transferWorld ctx.crypto w vault caller dst amount := by
  have hjd := jumpDestsAgree i
  have hbal' : amount.toNat ≤
      (w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
        ofWord (BitVec.ofNat 256 3)))).toNat := hbal
  rw [show k + 400 = (k + 349) + 51 by omega, run_start_transfer (by omega)]
  simp only [start, Frame.init, callMsg]
  psol_steps [transferData]
  simp only [gt_sub_self_of_le hbal']
  psol_steps [transferData]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp [ChildResult.success]
  · simp only [topLevelResult_output]
    decide +kernel
  · simp only [topLevelResult_world]
    rfl

set_option maxHeartbeats 10000000 in
/-- **`transfer`, insufficient balance**: panics; the world is unchanged. -/
theorem transfer_revert (hgas : 100000 ≤ gas)
    (hbal : ((view ctx.crypto Layout.solmate w vault).balanceOf caller).toNat < amount.toNat)
    (k : Nat) :
    ∃ r, run (k + 400) (start ctx w tr
        (vaultCall i vault caller (transferData dst amount) gas warmAddrs warmKeys)) = .ok r ∧
      r.success = false ∧ r.reverted = true ∧ r.world = w := by
  have hjd := jumpDestsAgree i
  have hbal' : (w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
      ofWord (BitVec.ofNat 256 3)))).toNat < amount.toNat := hbal
  rw [show k + 400 = (k + 349) + 51 by omega, run_start_transfer (by omega)]
  simp only [start, Frame.init, callMsg]
  psol_steps [transferData]
  simp only [gt_sub_self_of_lt hbal']
  psol_steps [transferData]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp [ChildResult.success]
  · simp
  · simp

end Examples.Solmate.ERC4626.Shares

end

section

/-! ## `approve`: bytecode -/

namespace Examples.Solmate.ERC4626.Shares

open EvmLean Examples.Solmate EvmLogic EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic
open Examples.Solmate.Contracts EvmLogic.Solidity.Dispatch EvmLogic.Solidity.ERC20 EvmLean.Bytes

variable {i : SolmateVault.Immutables} {ctx : Context} {w : World} {tr : TransientStorage}
  {vault caller spender : Address} {amount : Word} {gas : Nat} {warmAddrs : AddressSet}
  {warmKeys : StorageKeySet}

theorem run_start_approve (hgas : 164 ≤ gas) (k : Nat) :
    run (k + 41) (start ctx w tr (vaultCall i vault caller (approveData spender amount) gas
      warmAddrs warmKeys)) =
      run k { start ctx w tr (vaultCall i vault caller (approveData spender amount) gas warmAddrs
          warmKeys) with
        frame := { (start ctx w tr (vaultCall i vault caller (approveData spender amount) gas
          warmAddrs warmKeys)).frame with
          pc := 536, stack := [BitVec.ofNat 256 0x095ea7b3], memory := initMemory,
          gasLeft := gas - 164 } } :=
  have h := encodeCall_facts 0x095ea7b3 [Word.ofAddress spender, amount] (by decide) (by simp)
  (reaches_approve i).run_start h.1 h.2.1 h.2.2 hgas k

set_option maxHeartbeats 10000000 in
/-- **`approve`**: succeeds, returns `true`, world `approveWorld`. -/
theorem approve_ok (hgas : 100000 ≤ gas) (k : Nat) :
    ∃ r, run (k + 300) (start ctx w tr
        (vaultCall i vault caller (approveData spender amount) gas warmAddrs warmKeys)) = .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord 1 ∧
      r.world = approveWorld ctx.crypto w vault caller spender amount := by
  have hjd := jumpDestsAgree i
  rw [show k + 300 = (k + 259) + 41 by omega, run_start_approve (by omega)]
  simp only [start, Frame.init, callMsg]
  psol_steps [approveData]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp [ChildResult.success]
  · simp only [topLevelResult_output]
    decide +kernel
  · simp only [topLevelResult_world]
    rfl

end Examples.Solmate.ERC4626.Shares

end

section

/-! ## `transferFrom`: bytecode, success -/

namespace Examples.Solmate.ERC4626.Shares

open EvmLean Examples.Solmate EvmLogic EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic
open Examples.Solmate.Contracts EvmLogic.Solidity.Dispatch EvmLogic.Solidity.ERC20 EvmLean.Bytes

variable {i : SolmateVault.Immutables} {ctx : Context} {w : World} {tr : TransientStorage}
  {vault caller src dst : Address} {amount : Word} {gas : Nat} {warmAddrs : AddressSet}
  {warmKeys : StorageKeySet}

theorem run_start_transferFrom (hgas : 230 ≤ gas) (k : Nat) :
    run (k + 56) (start ctx w tr (vaultCall i vault caller (transferFromData src dst amount) gas
      warmAddrs warmKeys)) =
      run k { start ctx w tr (vaultCall i vault caller (transferFromData src dst amount) gas
          warmAddrs warmKeys) with
        frame := { (start ctx w tr (vaultCall i vault caller (transferFromData src dst amount) gas
          warmAddrs warmKeys)).frame with
          pc := 599, stack := [BitVec.ofNat 256 0x23b872dd], memory := initMemory,
          gasLeft := gas - 230 } } :=
  have h := encodeCall_facts 0x23b872dd [Word.ofAddress src, Word.ofAddress dst, amount]
    (by decide) (by simp)
  (reaches_transferFrom i).run_start h.1 h.2.1 h.2.2 hgas k

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
/-- **`transferFrom`, success**: returns `true`, world `transferFromWorld`. -/
theorem transferFrom_ok (hgas : 100000 ≤ gas)
    (hal : (view ctx.crypto Layout.solmate w vault).allowance src caller = maxWord ∨
      amount.toNat ≤ ((view ctx.crypto Layout.solmate w vault).allowance src caller).toNat)
    (hbal : amount.toNat ≤ ((spendWorld ctx.crypto w vault src caller amount).sload vault
      (balanceSlot ctx.crypto Layout.solmate src)).toNat) (k : Nat) :
    ∃ r, run (k + 500) (start ctx w tr
        (vaultCall i vault caller (transferFromData src dst amount) gas warmAddrs warmKeys)) = .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord 1 ∧
      r.world = transferFromWorld ctx.crypto w vault caller src dst amount := by
  have hjd := jumpDestsAgree i
  rw [show k + 500 = (k + 444) + 56 by omega, run_start_transferFrom (by omega)]
  simp only [start, Frame.init, callMsg]
  psol_steps [transferFromData]
  by_cases hmax : (view ctx.crypto Layout.solmate w vault).allowance src caller = maxWord
  · have hmax' : w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
        ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord (BitVec.ofNat 256 4))))) =
        maxWord := hmax
    simp only [eq_maxWord_of_eq hmax']
    psol_steps [transferFromData]
    have hbal' : amount.toNat ≤ (w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++
        ofWord (BitVec.ofNat 256 3)))).toNat := by
      simp only [spendWorld, show w.sload vault (allowanceSlot ctx.crypto Layout.solmate src caller) =
        maxWord from hmax, ↓reduceIte] at hbal
      exact hbal
    simp only [gt_sub_self_of_le hbal']
    psol_steps [transferFromData]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · simp only [topLevelResult_success]; rfl
    · simp only [topLevelResult_output]
      decide +kernel
    · simp only [topLevelResult_world, transferFromWorld, spendWorld,
        show w.sload vault (allowanceSlot ctx.crypto Layout.solmate src caller) = maxWord from hmax,
        ↓reduceIte]
      rfl
  · have hmax' : w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
        ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord (BitVec.ofNat 256 4))))) ≠
        maxWord := hmax
    have hal' : amount.toNat ≤ (w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
        ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++
          ofWord (BitVec.ofNat 256 4)))))).toNat := hal.resolve_left hmax
    simp only [eq_maxWord_of_ne hmax']
    psol_steps [transferFromData]
    simp only [gt_sub_self_of_le hal']
    psol_steps [transferFromData]
    have hbal' : amount.toNat ≤ ((w.sstore vault (ctx.crypto.keccak256
        (ofWord (Word.ofAddress caller) ++ ofWord (ctx.crypto.keccak256
          (ofWord (Word.ofAddress src) ++ ofWord (BitVec.ofNat 256 4)))))
        (w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
          ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++
            ofWord (BitVec.ofNat 256 4))))) - amount)).sload vault
        (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord (BitVec.ofNat 256 3)))).toNat := by
      simp only [spendWorld, show ¬ w.sload vault (allowanceSlot ctx.crypto Layout.solmate src caller) =
        maxWord from hmax, ↓reduceIte] at hbal
      exact hbal
    simp only [gt_sub_self_of_le hbal']
    psol_steps [transferFromData]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · simp only [topLevelResult_success]; rfl
    · simp only [topLevelResult_output]
      decide +kernel
    · simp only [topLevelResult_world, transferFromWorld, spendWorld,
        show ¬ w.sload vault (allowanceSlot ctx.crypto Layout.solmate src caller) = maxWord from hmax,
        ↓reduceIte]
      rfl

end Examples.Solmate.ERC4626.Shares

end

section

/-! ## `transferFrom`: bytecode, reverts (world unchanged) -/

namespace Examples.Solmate.ERC4626.Shares

open EvmLean Examples.Solmate EvmLogic EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic
open Examples.Solmate.Contracts EvmLogic.Solidity.Dispatch EvmLogic.Solidity.ERC20 EvmLean.Bytes

variable {i : SolmateVault.Immutables} {ctx : Context} {w : World} {tr : TransientStorage}
  {vault caller src dst : Address} {amount : Word} {gas : Nat} {warmAddrs : AddressSet}
  {warmKeys : StorageKeySet}

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
/-- **`transferFrom`, insufficient allowance.** -/
theorem transferFrom_revert_allowance (hgas : 100000 ≤ gas)
    (hmax : (view ctx.crypto Layout.solmate w vault).allowance src caller ≠ maxWord)
    (hlt : ((view ctx.crypto Layout.solmate w vault).allowance src caller).toNat < amount.toNat)
    (k : Nat) :
    ∃ r, run (k + 500) (start ctx w tr
        (vaultCall i vault caller (transferFromData src dst amount) gas warmAddrs warmKeys)) =
        .ok r ∧
      r.success = false ∧ r.reverted = true ∧ r.world = w := by
  have hjd := jumpDestsAgree i
  rw [show k + 500 = (k + 444) + 56 by omega, run_start_transferFrom (by omega)]
  simp only [start, Frame.init, callMsg]
  psol_steps [transferFromData]
  have hmax' : w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
      ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord (BitVec.ofNat 256 4))))) ≠
      maxWord := hmax
  have hlt' : (w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
      ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++
        ofWord (BitVec.ofNat 256 4)))))).toNat < amount.toNat := hlt
  simp only [eq_maxWord_of_ne hmax']
  psol_steps [transferFromData]
  simp only [gt_sub_self_of_lt hlt']
  psol_steps [transferFromData]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp only [topLevelResult_success]; rfl
  · simp only [topLevelResult_reverted]
  · simp only [topLevelResult_world]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
/-- **`transferFrom`, insufficient balance.** -/
theorem transferFrom_revert_balance (hgas : 100000 ≤ gas)
    (hal : (view ctx.crypto Layout.solmate w vault).allowance src caller = maxWord ∨
      amount.toNat ≤ ((view ctx.crypto Layout.solmate w vault).allowance src caller).toNat)
    (hbal : ((spendWorld ctx.crypto w vault src caller amount).sload vault
      (balanceSlot ctx.crypto Layout.solmate src)).toNat < amount.toNat) (k : Nat) :
    ∃ r, run (k + 500) (start ctx w tr
        (vaultCall i vault caller (transferFromData src dst amount) gas warmAddrs warmKeys)) =
        .ok r ∧
      r.success = false ∧ r.reverted = true ∧ r.world = w := by
  have hjd := jumpDestsAgree i
  rw [show k + 500 = (k + 444) + 56 by omega, run_start_transferFrom (by omega)]
  simp only [start, Frame.init, callMsg]
  psol_steps [transferFromData]
  by_cases hmax : (view ctx.crypto Layout.solmate w vault).allowance src caller = maxWord
  · have hmax' : w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
        ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord (BitVec.ofNat 256 4))))) =
        maxWord := hmax
    simp only [eq_maxWord_of_eq hmax']
    psol_steps [transferFromData]
    have hbal' : (w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++
        ofWord (BitVec.ofNat 256 3)))).toNat < amount.toNat := by
      simp only [spendWorld, show w.sload vault (allowanceSlot ctx.crypto Layout.solmate src caller) =
        maxWord from hmax, ↓reduceIte] at hbal
      exact hbal
    simp only [gt_sub_self_of_lt hbal']
    psol_steps [transferFromData]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · simp only [topLevelResult_success]; rfl
    · simp only [topLevelResult_reverted]
    · simp only [topLevelResult_world]
  · have hmax' : w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
        ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord (BitVec.ofNat 256 4))))) ≠
        maxWord := hmax
    have hal' : amount.toNat ≤ (w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
        ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++
          ofWord (BitVec.ofNat 256 4)))))).toNat := hal.resolve_left hmax
    simp only [eq_maxWord_of_ne hmax']
    psol_steps [transferFromData]
    simp only [gt_sub_self_of_le hal']
    psol_steps [transferFromData]
    have hbal' : ((w.sstore vault (ctx.crypto.keccak256
        (ofWord (Word.ofAddress caller) ++ ofWord (ctx.crypto.keccak256
          (ofWord (Word.ofAddress src) ++ ofWord (BitVec.ofNat 256 4)))))
        (w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
          ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++
            ofWord (BitVec.ofNat 256 4))))) - amount)).sload vault
        (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++
          ofWord (BitVec.ofNat 256 3)))).toNat < amount.toNat := by
      simp only [spendWorld, show ¬ w.sload vault (allowanceSlot ctx.crypto Layout.solmate src caller) =
        maxWord from hmax, ↓reduceIte] at hbal
      exact hbal
    simp only [gt_sub_self_of_lt hbal']
    psol_steps [transferFromData]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · simp only [topLevelResult_success]; rfl
    · simp only [topLevelResult_reverted]
    · simp only [topLevelResult_world]

end Examples.Solmate.ERC4626.Shares

end

section

/-! ## Share-token views: bytecode -/

namespace Examples.Solmate.ERC4626.Shares

open EvmLean Examples.Solmate EvmLogic EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic
open Examples.Solmate.Contracts EvmLogic.Solidity.Dispatch EvmLogic.Solidity.ERC20 EvmLean.Bytes

variable {i : SolmateVault.Immutables} {ctx : Context} {w : World} {tr : TransientStorage}
  {vault caller a owner spender : Address} {gas : Nat} {warmAddrs : AddressSet}
  {warmKeys : StorageKeySet}

set_option maxHeartbeats 10000000 in
/-- **`totalSupply()`** returns `totalSupply`. -/
theorem totalSupply_ok (hgas : 10000 ≤ gas) (k : Nat) :
    ∃ r, run (k + 100) (start ctx w tr
        (vaultCall i vault caller totalSupplyData gas warmAddrs warmKeys)) = .ok r ∧
      r.success = true ∧
      r.output = Bytes.ofWord (view ctx.crypto Layout.solmate w vault).totalSupply ∧
      r.world = w := by
  have hjd := jumpDestsAgree i
  have h := encodeCall_facts 0x18160ddd [] (by decide) (by simp)
  rw [show k + 100 = (k + 49) + 51 by omega,
    (reaches_totalSupply i).run_start (data := totalSupplyData) h.1 h.2.1 h.2.2 (by omega)]
  simp only [start, Frame.init, callMsg]
  psol_steps [totalSupplyData]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp only [topLevelResult_success]; rfl
  · simp only [topLevelResult_output]; rfl
  · simp only [topLevelResult_world]

set_option maxHeartbeats 10000000 in
/-- **`balanceOf(a)`** returns `balanceOf[a]`. -/
theorem balanceOf_ok (hgas : 10000 ≤ gas) (k : Nat) :
    ∃ r, run (k + 200) (start ctx w tr
        (vaultCall i vault caller (balanceOfData a) gas warmAddrs warmKeys)) = .ok r ∧
      r.success = true ∧
      r.output = Bytes.ofWord ((view ctx.crypto Layout.solmate w vault).balanceOf a) ∧
      r.world = w := by
  have hjd := jumpDestsAgree i
  have h := encodeCall_facts 0x70a08231 [Word.ofAddress a] (by decide) (by simp)
  rw [show k + 200 = (k + 150) + 50 by omega,
    (reaches_balanceOf i).run_start (data := balanceOfData a) h.1 h.2.1 h.2.2 (by omega)]
  simp only [start, Frame.init, callMsg]
  psol_steps [balanceOfData]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp only [topLevelResult_success]; rfl
  · simp only [topLevelResult_output]; rfl
  · simp only [topLevelResult_world]

set_option maxHeartbeats 10000000 in
/-- **`allowance(owner, spender)`** returns `allowance[owner][spender]`. -/
theorem allowance_ok (hgas : 10000 ≤ gas) (k : Nat) :
    ∃ r, run (k + 200) (start ctx w tr
        (vaultCall i vault caller (allowanceData owner spender) gas warmAddrs warmKeys)) = .ok r ∧
      r.success = true ∧
      r.output = Bytes.ofWord ((view ctx.crypto Layout.solmate w vault).allowance owner spender) ∧
      r.world = w := by
  have hjd := jumpDestsAgree i
  have h := encodeCall_facts 0xdd62ed3e [Word.ofAddress owner, Word.ofAddress spender] (by decide)
    (by simp)
  rw [show k + 200 = (k + 156) + 44 by omega,
    (reaches_allowance i).run_start (data := allowanceData owner spender) h.1 h.2.1 h.2.2 (by omega)]
  simp only [start, Frame.init, callMsg]
  psol_steps [allowanceData]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp only [topLevelResult_success]; rfl
  · simp only [topLevelResult_output]; rfl
  · simp only [topLevelResult_world]

set_option maxHeartbeats 10000000 in
/-- **`decimals()`** returns the `decimals` immutable as a `uint8`. -/
theorem decimals_ok (hgas : 10000 ≤ gas) (k : Nat) :
    ∃ r, run (k + 100) (start ctx w tr
        (vaultCall i vault caller decimalsData gas warmAddrs warmKeys)) = .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord (i.decimals &&& 255#256) ∧ r.world = w := by
  have hjd := jumpDestsAgree i
  have h := encodeCall_facts 0x313ce567 [] (by decide) (by simp)
  rw [show k + 100 = (k + 59) + 41 by omega,
    (reaches_decimals i).run_start (data := decimalsData) h.1 h.2.1 h.2.2 (by omega)]
  simp only [start, Frame.init, callMsg]
  psol_steps [decimalsData, readBytes_code_decimals]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp only [topLevelResult_success]; rfl
  · simp only [topLevelResult_output]
  · simp only [topLevelResult_world]

end Examples.Solmate.ERC4626.Shares

end
