import Verified.OpenZeppelin.Constructor.ProxyDefs
import Verified.OpenZeppelin.Contracts.ActorImpl
import Verified.OpenZeppelin.Constructor.ActorSet
import Verified.Solmate.ERC4626.Convert
import Verified.OpenZeppelin.Constructor.AdminCtor
import Verified.OpenZeppelin.Constructor.Create
import Verified.OpenZeppelin.Constructor.ProxyCode
import EvmLogic.Tactic.StepExt

/-!
# The `TransparentUpgradeableProxy` constructor, instruction by instruction

`proxy_seg1` runs the constructor frame of `initCodeFor logic o` from its first instruction to
its `RETURN`: it decodes `abi.encode(logic, o, set(1))`, checks that `logic` has code, writes the
implementation slot and emits `Upgraded`, delegatecalls `set(1)` into `logic` (`actorSet_halts`),
creates the `ProxyAdmin` with `CREATE` (`WP.create`, `admin_ctor_halts`) at
`createAddress self 1`, writes the admin slot and emits `AdminChanged`, then copies the runtime
code, stores the admin immutable into it and returns it (`proxy_output_eq`).
-/

namespace Verified.OpenZeppelin.Constructor
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Tactic
open Verified.OpenZeppelin.Contracts Verified.Solmate.Constructor Verified.Solmate.ERC4626

theorem setData_selector : Abi.selectorOf (Bytes.ofWord OzTransparentProxy.dataWord0 ++
    (Bytes.ofWord OzTransparentProxy.dataWord1).extract 0 4) = 0x60fe47b1 := by decide +kernel

theorem setData_arg : Bytes.toWord (readBytes (Bytes.ofWord OzTransparentProxy.dataWord0 ++
    (Bytes.ofWord OzTransparentProxy.dataWord1).extract 0 4) 4 32) = 1#256 := by decide +kernel

theorem setData_size : (Bytes.ofWord OzTransparentProxy.dataWord0 ++
    (Bytes.ofWord OzTransparentProxy.dataWord1).extract 0 4).size = 36 := by decide +kernel

/-- The `ProxyAdmin` creation code embedded in the proxy's init code. -/
theorem readBytes_initCode_admin :
    readBytes OzTransparentProxy.initCode 2107 1200 = OzProxyAdmin.creationCode := by
  rw [OzTransparentProxy.initCode_eq, readBytes_append_of_le _ _ _ _
    (by rw [OzTransparentProxy.size_creationCode]; omega)]
  apply eq_of_data_toList_eq
  rw [readBytes_toList _ _ _ (by rw [OzTransparentProxy.size_creationCode]; omega)
    (by rw [OzTransparentProxy.size_creationCode]; omega)]
  decide +kernel

theorem iszero_ofAddress' {a : Address} (h : a ≠ 0) : Word.iszero (Word.ofAddress a) = 0#256 := by
  apply EvmLogic.Solidity.iszero_of_ne
  intro he; apply h
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat he
  simp only [Word.ofAddress, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
  have hlt := a.isLt
  rw [Nat.mod_eq_of_lt (by omega)] at this
  exact this

theorem getElem_adminRuntime_zero : OzProxyAdmin.runtimeCode[0]? = some 0x60 := by decide +kernel

theorem delegatedAddress?_actor : delegatedAddress? ActorImpl.runtimeCode = none :=
  delegatedAddress?_of_size (by rw [ActorImpl.size_runtimeCode]; decide)

/-- **What the proxy constructor leaves in the world** (`w` before, `w'` after; `px` the proxy,
`pa` the `ProxyAdmin` it creates): the implementation and admin slots of the proxy hold `logic`
and `pa`, `pa` holds the `ProxyAdmin` runtime code and is owned by `o`, the proxy's code is
untouched (it is deposited when the constructor returns), and no other account changes. -/
structure ProxyCtorPost (w : World) (px logic o pa : Address) (w' : World) : Prop where
  impl : w'.sload px OzTransparentProxy.implementationSlot = Word.ofAddress logic
  admin : w'.sload px OzTransparentProxy.adminSlot = Word.ofAddress pa
  codePa : w'.code pa = OzProxyAdmin.runtimeCode
  owner : w'.sload pa 0#256 = Word.ofAddress o
  codeSelf : w'.code px = w.code px
  other : ∀ a, a ≠ px → a ≠ pa → w'.account a = w.account a

set_option maxHeartbeats 0 in
/-- **The proxy constructor frame**, for any frame starting the init code of a proxy to `logic`
owned by `o`, with no value, not static, room for one more call level, nonce 1 (the creation
has incremented it), both ERC-1967 slots empty, `logic` holding `ActorImpl` and not a
precompile, the `ProxyAdmin`'s address `createAddress self 1` deployable and non-zero, `o ≠ 0`
(else `ProxyAdmin` reverts) and at least 1 000 000 gas: it returns the runtime code with the
admin immutable, leaves `ProxyCtorPost`, and uses at most 500 000 gas. -/
theorem proxy_seg1 (logic o : Address) (m : Machine)
    (hf : Fresh (OzTransparentProxy.initCodeFor logic o) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false)
    (hlogic : m.world.code logic = ActorImpl.runtimeCode)
    (hpreL : m.precompiles.isPrecompile logic = false)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hn1 : (m.world.account m.frame.msg.currentTarget).nonce = 1)
    (hpaDep : accountDeployable m.world
      (createAddress m.ctx.crypto.keccak256 m.frame.msg.currentTarget 1) = true)
    (ho : Word.ofAddress o ≠ 0#256)
    (hpa0 : createAddress m.ctx.crypto.keccak256 m.frame.msg.currentTarget 1 ≠ 0)
    (hsAdmin : m.world.sload m.frame.msg.currentTarget OzTransparentProxy.adminSlot = 0#256)
    (hsImpl : m.world.sload m.frame.msg.currentTarget OzTransparentProxy.implementationSlot = 0#256)
    (hg : 1000000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun _ => False) (fun mf out =>
      out = .success (OzTransparentProxy.runtimeCodeWith
        ⟨createAddress m.ctx.crypto.keccak256 m.frame.msg.currentTarget 1⟩) ∧
      ProxyCtorPost m.world m.frame.msg.currentTarget logic o
        (createAddress m.ctx.crypto.keccak256 m.frame.msg.currentTarget 1) mf.world ∧
      m.frame.gasLeft ≤ mf.frame.gasLeft + 500000) := by
  obtain ⟨hc, hj, hpc, hs, hmem, -, -⟩ := hf.frame
  clear hf
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  wp_hide_jump_tables
  subst hs hpc hc hmem
  have hJ := OzTransparentProxy.jumpTable_initCodeFor hj
  pwp_xsteps 400 [hval, OzTransparentProxy.size_initCodeFor]
  rw [write_args (by simp only [Memory.size_expand, Memory.size_storeWord,
    Memory.size_empty, Memory.wordsAfter, Memory.words]; decide)]
  wp_abstract_mem M0 with hM0
  have h160 : M0.loadWord 160 = Word.ofAddress logic := by subst hM0; mem_fact
  have h192 : M0.loadWord 192 = Word.ofAddress o := by subst hM0; mem_fact
  have h224 : M0.loadWord 224 = 0x60#256 := by subst hM0; mem_fact
  have h256 : M0.loadWord 256 = 0x24#256 := by subst hM0; mem_fact
  have h288 : M0.read 288 36 =
      Bytes.ofWord OzTransparentProxy.dataWord0 ++ (Bytes.ofWord OzTransparentProxy.dataWord1).extract 0 4 := by
    subst hM0
    rw [show (36 : Nat) = 32 + 4 from rfl, Memory.read_add]
    mem_fact [Memory.ofWord_extract_zero_32]
  clear hM0
  pwp_xsteps 400 [M0_size, M0_fp, h160, h192, h224, h256, h288, Memory.mcopy_eq,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self,
    Memory.read_storeWord_prefix, Memory.read_write_of_size, Memory.read_write_of_disjoint,
    Memory.loadWord_write_of_disjoint, ByteArray.size_extract, Memory.size_write,
    Bytes.size_zeros, ByteArray.size_append, Bytes.size_ofWord]
  wp_abstract_mem M1 with hM1
  try simp only [ByteArray.size_append, Bytes.size_ofWord, ByteArray.size_extract, Nat.min_def,
    Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMul,
    Nat.reduceEqDiff, Nat.sub_zero] at M1_size
  have g64 : M1.loadWord 64 = 448#256 := by subst hM1; mem_fact
  have g352 : M1.loadWord 352 = 0x24#256 := by subst hM1; mem_fact
  have g192 : M1.loadWord 192 = Word.ofAddress o := by subst hM1; mem_fact [h192]
  have g384 : M1.read 384 36 =
      Bytes.ofWord OzTransparentProxy.dataWord0 ++ (Bytes.ofWord OzTransparentProxy.dataWord1).extract 0 4 := by
    subst hM1
    rw [Memory.read_expand, Memory.read_storeWord_of_disjoint _ 420 384 36 _ (.inl (by decide)),
      Memory.read_expand, Memory.read_write_of_size _ _ _ _ setData_size]
  clear hM1
  have hto : Word.toAddress (Word.ofAddress logic) = logic := Word.toAddress_ofAddress _
  pwp_xsteps 400 [M1_size, hto, Word.toAddress_ofAddress, hlogic, ActorImpl.size_runtimeCode]
  simp only [hto, hlogic, ActorImpl.size_runtimeCode, ofNat,
    BitVec.reduceSub]
  have hacc := accessCost_le (m_sub.accessedAddresses.contains logic)
  simp only [OzTransparentProxy.implementationSlot] at hsImpl
  pwp_xrun_to 766 [M1_size, g64, g352, g192, g384, hsImpl, BitVec.and_zero, BitVec.or_zero,
    addressMask_and_ofAddress, ofAddress_and_addressMask]
  wp_abstract gas g1 hg1
  have hg1' : m_gasLeft ≤ g1 + 50000 := by subst hg1; evm_gas
  have hg1'' : g1 ≤ m_gasLeft := by subst hg1; omega
  clear hg1
  pwp_xsteps 1
  have hmod : (g1 - 2) % 2 ^ 256 = g1 - 2 := Nat.mod_eq_of_lt (by omega)
  refine WP.delegatecall (by pcode_fact) rfl ?_ ?_ ?_ ?_
    (actorSet_halts (v := 1#256) _ ?_ hval (by dsimp only [childMsg, Frame.init]; simp [hstatic]) ?_ ?_ ?_) ?_
  · exact .inr (by dsimp only; rw [hto, World.code_sstore, hlogic]; exact delegatedAddress?_actor)
  · simp only [callCost, callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, hmod, Nat.reducePow,
      Nat.reduceMod]
    rw [messageCallGas_zero (by evm_gas)]
    simp only [Gas.maxMessageCallGas]
    evm_gas
  · exact hdepth
  · rw [hto]; exact hpreL
  · exact ⟨_, _, _, rfl, by dsimp only [childMsg]; rw [hto, World.code_sstore, hlogic]⟩
  · dsimp only [Frame.init, childMsg, callMemory]
    simp only [BitVec.reduceToNat, readBytes_bytes, Memory.read_expand, g384]
    exact ⟨setData_selector, by rw [setData_size]; exact Nat.le_refl _, setData_arg⟩
  · dsimp only [Frame.init, childMsg, callMemory]
    simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
    decide
  · dsimp only [Frame.init, childMsg]
    simp only [callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, hmod, Nat.reducePow,
      Nat.reduceMod]
    rw [messageCallGas_zero (by evm_gas)]
    simp only [Gas.maxMessageCallGas]
    evm_gas
  · intro mf o' ⟨ho', hw', hgasB⟩ hsame
    have hk : mf.frame.kind = .call 0 0 := hsame.kind
    subst ho'
    rw [resumeAfter_success hk]
    dsimp only at hw' hgasB
    have hs1' : mf.ctx = m_ctx := hsame.ctx
    have hs2 : mf.precompiles = m_pre := hsame.precompiles
    have hs3 : mf.originalWorld = m_originalWorld := hsame.originalWorld
    simp only [hw', hs1', hs2, hs3]
    dsimp only [delegateCaller, delegateChild, callerFrame, callMemory, Frame.init, childMsg] at hgasB ⊢
    simp only [hto, callCost, callGas, callExt, ofNat, BitVec.toNat_ofNat, hmod, Nat.reducePow,
      Nat.reduceMod] at hgasB ⊢
    rw [messageCallGas_zero (by evm_gas)] at hgasB ⊢
    simp only [Gas.maxMessageCallGas] at hgasB ⊢
    wp_abstract sub S1 hS1
    clear hS1
    wp_generalize_gas g2 hg2
    have hg2' : m_gasLeft ≤ g2 + 80000 := by
      subst hg2
      access_bounds
      evm_gas
    clear hg2 hgasB
    have hret : ∀ mem : Memory, returnMemory mem 0 0 ByteArray.empty = mem := fun mem => by
      simp [returnMemory]
    simp only [hret]
    pwp_xsteps 400 [M1_size, g64, g352, g192, hto, hlogic, ActorImpl.size_runtimeCode,
      ByteArray.size_empty, World.code_sstore, ofAddress_and_addressMask, addressMask_and_ofAddress,
      size_readBytes]
    wp_abstract_mem M2 with hM2
    simp only [size_readBytes, ↓reduceIte, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMul,
      Nat.reduceLeDiff, Nat.reduceEqDiff] at M2_size
    have k64 : M2.loadWord 64 = 480#256 := by
      subst hM2; mem_fact [Memory.loadWord_write_of_disjoint, size_readBytes]
    have k480 : M2.read 480 1200 = OzProxyAdmin.creationCode := by
      rw [← hM2, Memory.read_write_of_size _ _ _ _ (size_readBytes _ _ _), readBytes_initCode_admin]
    clear hM2
    pwp_xrun_to 117 [M2_size, k64]
    -- the creation of the `ProxyAdmin`
    have hpaNe : createAddress m_ctx.crypto.keccak256 m_msg.currentTarget 1 ≠ m_msg.currentTarget := by
      intro he
      rw [he] at hpaDep
      simp only [accountDeployable, hn1, Bool.and_eq_true, decide_eq_true_eq] at hpaDep
      omega
    wp_abstract gas g3 hg3
    have hg3' : m_gasLeft ≤ g3 + 120000 := by subst hg3; gen_access; evm_gas
    clear hg3
    refine WP.create (by pcode_fact) rfl ?_
      (by show 1232 ≤ Gas.maxInitCodeSize m_ctx.fork; cases m_ctx.fork <;> decide) hstatic (by simp) ?_ hdepth ?_
      (admin_ctor_halts o _ ?_ rfl rfl ho ?_ ?_) ?_
    · simp only [createCharge, memoryCost, Gas.createCost, Gas.createBase, Gas.initCodeCost,
        Gas.codeInitPerWord, Gas.words]
      evm_gas
    · simp only [account_sstore, ↓reduceIte, hn1, Gas.maxNonce]; decide
    · simp only [createTarget, accountDeployable, account_sstore, hn1]
      simp only [accountDeployable] at hpaDep
      simpa [hpaNe] using hpaDep
    · refine ⟨_, _, _, rfl, ?_⟩
      simp only [createMsg, readBytes_bytes, BitVec.reduceToNat, Memory.read_expand]
      rw [show (1232 : Nat) = 1200 + 32 from rfl, Memory.read_add,
        Memory.read_storeWord_of_disjoint _ 1680 480 1200 _ (.inl (by decide)), Memory.read_expand,
        k480, show 480 + 1200 = 1680 from rfl, Memory.read_storeWord, OzProxyAdmin.initCodeFor_eq]
    · simp only [launchCreate, beginCreate, createMsg, createCaller, createTarget, transferValue,
        account_sstore, hn1, ↓reduceIte, ne_eq]
      apply sload_incrementNonce_of_deployable
      simp only [accountDeployable, account_incrementNonce, account_sstore, hpaNe, ↓reduceIte]
      simpa only [accountDeployable] using hpaDep
    · simp only [launchCreate, beginCreate, Frame.init, createMsg, createGas, createCharge,
        memoryCost, Gas.createCost, Gas.createBase, Gas.initCodeCost, Gas.codeInitPerWord, Gas.words,
        Gas.maxMessageCallGas]
      evm_gas
    · rintro mf2 o2 ⟨ho2, hw2, hgas2⟩ hsame2
      subst ho2
      have hk2 : mf2.frame.kind = .create := hsame2.kind
      have hmsg2 : mf2.frame.msg = _ := hsame2.msg
      have hctx2 : mf2.ctx = _ := hsame2.ctx
      have hdep2 := depositCode_ok (fork := mf2.ctx.fork) (g := mf2.frame.gasLeft)
        (out := OzProxyAdmin.runtimeCode) (by rw [getElem_adminRuntime_zero]; decide)
        (by
          rw [OzProxyAdmin.size_runtimeCode]
          simp only [launchCreate, beginCreate, Frame.init, createMsg, createGas, createCharge,
            memoryCost, Gas.createCost, Gas.createBase, Gas.initCodeCost, Gas.codeInitPerWord,
            Gas.words, Gas.maxMessageCallGas] at hgas2
          evm_gas)
        (by rw [OzProxyAdmin.size_runtimeCode]; cases mf2.ctx.fork <;> decide)
      rw [resumeAfter_create_success hk2 hdep2]
      wp_abstract sub S2 hS2
      clear hS2
      wp_abstract world W2 hW2
      wp_abstract gas g4 hg4
      have hg4' : m_gasLeft ≤ g4 + 450000 := by
        subst hg4
        simp only [launchCreate, beginCreate, Frame.init, createMsg, createCaller, createGas,
          createCharge, memoryCost, Gas.createCost, Gas.createBase, Gas.initCodeCost,
          Gas.codeInitPerWord, Gas.words, Gas.maxMessageCallGas,
          OzProxyAdmin.size_runtimeCode] at hgas2 ⊢
        evm_gas
      clear hg4 hgas2 hdep2
      have hs1 : mf2.precompiles = _ := hsame2.precompiles
      have hs3 : mf2.originalWorld = _ := hsame2.originalWorld
      simp only [hctx2, hs1, hs3, hmsg2]
      simp only [launchCreate, beginCreate, createMsg, createCaller, createTarget, account_sstore,
        hn1, ↓reduceIte, Frame.init]
      have hz := iszero_ofAddress' hpa0
      have hpaW : Word.ofAddress (createAddress m_ctx.crypto.keccak256 m_msg.currentTarget 1) ≠
          0#256 := by
        intro h; have := iszero_ofAddress' hpa0; rw [h] at this; exact absurd this (by decide)
      have hA : W2.sload m_msg.currentTarget
          81955473079516046949633743016697847541294818689821282749996681496272635257091#256 =
          0#256 := by
        have h00 : ((0#256 : Word) = 0) = True := by simp
        rw [← hW2, hmsg2, hw2]
        simp only [launchCreate, beginCreate, createMsg, createCaller, createTarget, account_sstore,
          hn1, ↓reduceIte, Frame.init, transferValue, ne_eq, h00, not_true_eq_false, decide_false,
          Bool.and_false, Bool.false_eq_true]
        have hne1 : (81955473079516046949633743016697847541294818689821282749996681496272635257091#256 : Word) ≠ 0#256 := by decide
        have hne2 : (81955473079516046949633743016697847541294818689821282749996681496272635257091#256 : Word) ≠
            24440054405305269366569402256811496959409073762505157381672968839269610695612#256 := by decide
        simp only [World.sload, account_setCode _ _ _ (by rw [OzProxyAdmin.size_runtimeCode]; decide),
          account_sstore, account_incrementNonce, Ne.symm hpaNe, ↓reduceIte, Storage.get_set, hne1,
          hne2]
        exact hsAdmin
      pwp_xrun_to 708 [hz, hpaW, hA, ofAddress_and_addressMask, addressMask_and_ofAddress,
        Solidity.eq_self]
      wp_abstract_mem M3 with hM3
      have k128 : M3.loadWord 128 =
          Word.ofAddress (createAddress m_ctx.crypto.keccak256 m_msg.currentTarget 1) := by
        subst hM3; mem_fact
      clear hM3
      pwp_xsteps 40 [hpaW, M3_size, M3_fp, k128, hA]
      apply WP.of_step
      case h =>
        apply EvmLean.Interpreter.step_sstore
        case hcode => pcode_fact
        case hstk => exact rfl
        case hstatic => exact hstatic
        case hstipend => dsimp only; evm_gas
        case hgas => dsimp only; evm_gas
      case hs => same_frame
      pwp_norm [hpaW, M3_size, M3_fp, k128, hA, addressMask_and_ofAddress, BitVec.or_zero]
      pwp_xsteps 60 [hpaW, M3_size, M3_fp, k128]
      wp_abstract sub S3 hS3
      clear hS3
      wp_abstract_mem M4 with hM4
      have hM : ∀ j < 1005, Bytes.getD M4.bytes j =
          Bytes.getD (readBytes OzTransparentProxy.initCode 1102 1005) j := fun j hj => by
        rw [← hM4]; exact getD_write_proxyRuntime _ j hj
      simp only [size_readBytes] at M4_size
      clear hM4
      pwp_xsteps 20 [M4_size]
      refine ⟨by rw [proxy_output_eq M4 hM], ?_, by dsimp only [outputMachine]; evm_gas⟩
      dsimp only [outputMachine]
      have h00 : ((0#256 : Word) = 0) = True := by simp
      have hsI : m_world.sload m_msg.currentTarget
          24440054405305269366569402256811496959409073762505157381672968839269610695612#256 =
          0#256 := hsImpl
      have hkI : OzTransparentProxy.implementationSlot =
          24440054405305269366569402256811496959409073762505157381672968839269610695612#256 := rfl
      have hkA : OzTransparentProxy.adminSlot =
          81955473079516046949633743016697847541294818689821282749996681496272635257091#256 := rfl
      have hsz : OzProxyAdmin.runtimeCode.size ≠ 0 := by rw [OzProxyAdmin.size_runtimeCode]; decide
      subst hW2
      rw [hmsg2, hw2]
      simp only [launchCreate, beginCreate, createMsg, createCaller, createTarget, account_sstore,
        hn1, ↓reduceIte, Frame.init, transferValue, ne_eq, h00, not_true_eq_false, decide_false,
        Bool.and_false, Bool.false_eq_true]
      have hneAI : (81955473079516046949633743016697847541294818689821282749996681496272635257091#256 : Word) ≠
          24440054405305269366569402256811496959409073762505157381672968839269610695612#256 := by decide
      have hne0I : (0#256 : Word) ≠
          24440054405305269366569402256811496959409073762505157381672968839269610695612#256 := by decide
      have hne0A : (0#256 : Word) ≠
          81955473079516046949633743016697847541294818689821282749996681496272635257091#256 := by decide
      rw [hsI, BitVec.and_zero, BitVec.or_zero]
      constructor
      · rw [hkI]
        simp only [World.sload, account_sstore, account_setCode _ _ _ hsz, account_incrementNonce,
          Ne.symm hpaNe, ↓reduceIte, Storage.get_set, hneAI.symm, hne0I.symm]
      · rw [hkA]
        simp only [World.sload, account_sstore, ↓reduceIte, Storage.get_set]
      · simp only [World.code, account_sstore, account_setCode _ _ _ hsz, hpaNe, ↓reduceIte]
      · simp only [World.sload, account_sstore, account_setCode _ _ _ hsz, hpaNe, ↓reduceIte,
          Storage.get_set]
      · simp only [World.code, account_sstore, account_setCode _ _ _ hsz, account_incrementNonce,
          Ne.symm hpaNe, ↓reduceIte]
      · intro a h1 h2
        simp only [account_sstore, account_setCode _ _ _ hsz, account_incrementNonce, h1, h2,
          ↓reduceIte]

end Verified.OpenZeppelin.Constructor
