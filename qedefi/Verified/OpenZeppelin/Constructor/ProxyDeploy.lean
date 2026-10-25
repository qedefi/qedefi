import Verified.OpenZeppelin.Constructor.ProxySeg1

/-!
# Deploying the `TransparentUpgradeableProxy`

`proxy_ctor_halts`: the constructor frame (init code `initCodeFor logic o`, i.e.
`creationCode ++ abi.encode(logic, o, set(1))`) delegatecalls `set(1)` into `logic`, creates its
`ProxyAdmin` (owned by `o`) at `createAddress self 1`, records the implementation and the admin
in their ERC-1967 slots and returns the runtime code with the admin as immutable.

`proxy_create`: a top-level creation (`processMessageCall` of a message with `target = none`)
of that init code at a deployable address, with `logic` holding `ActorImpl`, succeeds; its world
is described by `ProxyDeployed`.
-/

namespace Verified.OpenZeppelin.Constructor
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Solidity
open Verified.OpenZeppelin.Contracts Verified.Solmate.Constructor

/-- **The `TransparentUpgradeableProxy` constructor** as a frame summary (`proxy_seg1`). -/
theorem proxy_ctor_halts (logic o : Address) (m : Machine)
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
    Halts m (fun mf out =>
      out = .success (OzTransparentProxy.runtimeCodeWith
        ⟨createAddress m.ctx.crypto.keccak256 m.frame.msg.currentTarget 1⟩) ∧
      ProxyCtorPost m.world m.frame.msg.currentTarget logic o
        (createAddress m.ctx.crypto.keccak256 m.frame.msg.currentTarget 1) mf.world ∧
      m.frame.gasLeft ≤ mf.frame.gasLeft + 500000) :=
  WP.halts_of_false (proxy_seg1 logic o m hf hval hstatic hlogic hpreL hdepth hn1 hpaDep ho hpa0
    hsAdmin hsImpl hg hg')

/-- **A deployed proxy** at `px` with admin `pa` over `logic`, owner `o`, in `w'`, deployed from
`w`: the two contracts' code, the two ERC-1967 slots, the `ProxyAdmin`'s owner, and every other
account as in `w`. -/
structure ProxyDeployed (w : World) (px logic o pa : Address) (w' : World) : Prop where
  codePx : w'.code px = OzTransparentProxy.runtimeCodeWith ⟨pa⟩
  codePa : w'.code pa = OzProxyAdmin.runtimeCode
  impl : w'.sload px OzTransparentProxy.implementationSlot = Word.ofAddress logic
  admin : w'.sload px OzTransparentProxy.adminSlot = Word.ofAddress pa
  owner : w'.sload pa 0#256 = Word.ofAddress o
  other : ∀ a, a ≠ px → a ≠ pa → w'.account a = w.account a

theorem delegatedAddress?_proxyInit (logic o : Address) :
    delegatedAddress? (OzTransparentProxy.creationCode ++
      OzTransparentProxy.constructorArgsFor logic o) = none := by
  rw [← OzTransparentProxy.initCodeFor_eq]
  simp only [delegatedAddress?, isValidDelegation, OzTransparentProxy.size_initCodeFor]
  rfl

theorem getElem_proxyRuntimeCodeWith_zero (i : OzTransparentProxy.Immutables) :
    (OzTransparentProxy.runtimeCodeWith i)[0]? = some 0x60 := by
  rw [OzTransparentProxy.runtimeCodeWith, getElem?_patchWords_of_offsets _ _ 0 [16] rfl
    (by decide)]
  decide +kernel

theorem size_proxyRuntimeCodeWith (i : OzTransparentProxy.Immutables) :
    (OzTransparentProxy.runtimeCodeWith i).size = 1005 := by
  rw [OzTransparentProxy.runtimeCodeWith, size_patchWords, OzTransparentProxy.size_runtimeCode]

theorem ofAddress_ne_zero {a : Address} (h : a ≠ 0) : Word.ofAddress a ≠ 0#256 := by
  intro he; apply h
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat he
  simp only [Word.ofAddress, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
  have hlt := a.isLt
  rw [Nat.mod_eq_of_lt (by omega)] at this
  exact this

/-- **Deploying the proxy.** A top-level creation running `creationCode ++ abi.encode(logic, o,
set(1))` at an address `px` with no code, nonce 0 and empty storage (`accountDeployable`;
otherwise it fails with an address collision), sent with no value, not static, at depth 0, with
at least 1 000 000 and fewer than `2⁶⁴` gas, before Prague or without EIP-7702 authorizations,
terminates successfully and leaves a `ProxyDeployed` world, with the `ProxyAdmin` at
`pa = createAddress px 1`. Hypotheses: `logic` holds `ActorImpl` and is not a precompile (the
constructor delegatecalls the initialization data into it); `o ≠ 0` (the `ProxyAdmin` rejects a
zero owner); `pa` is deployable, differs from `px` and is not the zero address (the nested
`CREATE` succeeds; the last two fail only on a keccak collision). -/
theorem proxy_create {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    {logic o : Address}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (htarget : msg.target = none)
    (hcode : msg.code = OzTransparentProxy.creationCode ++
      OzTransparentProxy.constructorArgsFor logic o)
    (hval : msg.value = 0) (hdepth : msg.depth = 0) (hstatic : msg.isStatic = false)
    (hd : accountDeployable w msg.currentTarget = true)
    (hlogic : w.code logic = ActorImpl.runtimeCode)
    (hpre : Precompile.isPrecompile ctx.fork logic = false)
    (ho : o ≠ 0)
    (hpaDep : accountDeployable w (createAddress ctx.crypto.keccak256 msg.currentTarget 1) = true)
    (hpaSelf : createAddress ctx.crypto.keccak256 msg.currentTarget 1 ≠ msg.currentTarget)
    (hpa0 : createAddress ctx.crypto.keccak256 msg.currentTarget 1 ≠ 0)
    (hg : 1000000 ≤ msg.gas) (hg' : msg.gas < 2 ^ 64) :
    ∃ r : MessageResult, (∃ n, ∀ fuel, n ≤ fuel → processMessageCall fuel ctx w tr msg = .ok r) ∧
      r.success = true ∧ ProxyDeployed w msg.currentTarget logic o
        (createAddress ctx.crypto.keccak256 msg.currentTarget 1) r.world := by
  have hf : Fresh (OzTransparentProxy.initCodeFor logic o) (createMachine ctx w tr msg) := by
    have := fresh_createMachine ctx w tr msg
    rwa [hcode, ← OzTransparentProxy.initCodeFor_eq] at this
  have hd' := hd
  simp only [accountDeployable, Bool.and_eq_true, decide_eq_true_eq] at hd'
  have hh := proxy_ctor_halts logic o (createMachine ctx w tr msg) hf hval hstatic
    (by simp only [createMachine]; rw [code_incrementNonce']; exact hlogic) hpre
    (by simp only [createMachine, Frame.init, hdepth, Gas.stackDepthLimit]; decide)
    (by simp only [createMachine, Frame.init, account_incrementNonce, ↓reduceIte, hd'.1.1])
    (by
      simp only [createMachine, Frame.init, accountDeployable, account_incrementNonce, hpaSelf,
        ↓reduceIte]
      simpa only [accountDeployable] using hpaDep)
    (ofAddress_ne_zero ho) hpa0
    (sload_incrementNonce_of_deployable _ hd) (sload_incrementNonce_of_deployable _ hd)
    hg hg'
  obtain ⟨n, mf, out, ⟨hout, hpost, hgf⟩, hsf, hr⟩ := processMessageCall_create_of_halts hdeleg
    (hcode ▸ delegatedAddress?_proxyInit logic o) htarget hd hval hdepth hh
  have hk : mf.frame.kind = .create := hsf.kind
  have hmsg : mf.frame.msg = msg := hsf.msg
  dsimp only [createMachine, Frame.init] at hout hpost hgf
  subst hout
  have hdep := depositCode_ok (fork := mf.ctx.fork) (g := mf.frame.gasLeft)
    (out := OzTransparentProxy.runtimeCodeWith
      ⟨createAddress ctx.crypto.keccak256 msg.currentTarget 1⟩)
    (by rw [getElem_proxyRuntimeCodeWith_zero]; decide)
    (by rw [size_proxyRuntimeCodeWith]; omega)
    (by rw [size_proxyRuntimeCodeWith]; cases mf.ctx.fork <;> decide)
  obtain ⟨hs, hw⟩ := topLevelResult_create hk hdep
  refine ⟨_, ⟨n, fun fuel hle => (hr fuel hle).trans (by rw [htarget])⟩, hs, ?_⟩
  rw [hw, hmsg]
  have hsz := size_proxyRuntimeCodeWith
    ⟨createAddress ctx.crypto.keccak256 msg.currentTarget 1⟩
  have hsz' : (OzTransparentProxy.runtimeCodeWith
      ⟨createAddress ctx.crypto.keccak256 msg.currentTarget 1⟩).size ≠ 0 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [World.code, account_setCode _ _ _ hsz', ↓reduceIte]
  · simp only [World.code, account_setCode _ _ _ hsz', hpaSelf, ↓reduceIte]
    exact hpost.codePa
  · simp only [World.sload, account_setCode _ _ _ hsz', ↓reduceIte]
    exact hpost.impl
  · simp only [World.sload, account_setCode _ _ _ hsz', ↓reduceIte]
    exact hpost.admin
  · simp only [World.sload, account_setCode _ _ _ hsz', hpaSelf, ↓reduceIte]
    exact hpost.owner
  · intro a h1 h2
    simp only [account_setCode _ _ _ hsz', h1, ↓reduceIte]
    rw [hpost.other a h1 h2, account_incrementNonce]
    simp only [h1, ↓reduceIte]

end Verified.OpenZeppelin.Constructor
