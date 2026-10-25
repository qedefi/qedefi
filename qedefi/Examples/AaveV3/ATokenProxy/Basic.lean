import Examples.AaveV3.ATokenProxy.Code
import Examples.Solmate.ERC20.BalanceOf
import EvmLogic.Tactic.Abstract
import EvmLogic.Tactic.Mcopy

/-!
# Aave V3 aToken proxy: shared vocabulary

Every aToken (and variable-debt-token) address runs `ATokenProxy.runtimeCode`, the deployed
`InitializableImmutableAdminUpgradeabilityProxy`: its five own functions (`admin()`,
`implementation()`, `upgradeTo`, `upgradeToAndCall` for the admin, `initialize` once) and a
fallback that, for anyone but the admin, runs OpenZeppelin's `_delegate` on the implementation in
the EIP-1967 slot:

```
calldatacopy(0, 0, calldatasize())                                          // pc 1129
let result := delegatecall(gas(), implementation, 0, calldatasize(), 0, 0)  // pc 1138
returndatacopy(0, 0, returndatasize())                                      // pc 1143
switch result case 0 { revert(0, returndatasize()) } default { return(0, returndatasize()) }
```

This file fixes the admin (`admin`, the PoolConfigurator), the slot (`implSlot`,
`implementation`), how the implementation's frame relates to the proxy's (`DelegatedFrom`), how
the proxy's frame ends after it (`Forwarded`, `Reverted`), and the dispatcher facts for calldata
selecting none of the proxy's functions (`proxySelectors`, `dispatch_facts`).
-/

namespace Examples.AaveV3.ATokenProxy
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Examples.AaveV3.Contracts

/-- The proxy admin, the value of the immutable `_admin` (the PoolConfigurator). -/
def admin : Address := 0x64b761d848206f447fe2dd461b0c635ec39ebb27

theorem ofAddress_admin :
    Word.ofAddress admin = 574988636942314518095395226888196325637651086119#256 := by decide

/-- solc's `msg.sender == _admin` fails for any other caller. -/
theorem adminWord_eq_caller {c : Address} (h : c ≠ admin) :
    Word.eq 574988636942314518095395226888196325637651086119#256 (Word.ofAddress c) = 0#256 := by
  rw [← ofAddress_admin]
  exact eq_of_ne fun e => h (Word.ofAddress_injective e).symm

/-- The EIP-1967 implementation slot, `keccak256("eip1967.proxy.implementation") - 1`. -/
def implSlot : Word := 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc

/-- The implementation the proxy at `a` delegates to: the address in its implementation slot. -/
def implementation (w : World) (a : Address) : Address := Word.toAddress (w.sload a implSlot)

/-- The output of a frame outcome (empty after an exceptional halt). -/
def outputOf : Outcome → ByteArray
  | .success out => out
  | .revert out => out
  | .halt _ => .empty

/-- `mc` is the implementation's frame the proxy frame `M` delegates to: same transaction
constants, world, transient storage and created accounts; same caller, address, value, calldata
and static flag; one level deeper. -/
structure DelegatedFrom (M mc : Machine) : Prop where
  ctx : mc.ctx = M.ctx
  precompiles : mc.precompiles = M.precompiles
  originalWorld : mc.originalWorld = M.originalWorld
  world : mc.world = M.world
  transient : mc.transient = M.transient
  created : mc.createdAccounts = M.createdAccounts
  caller : mc.frame.msg.caller = M.frame.msg.caller
  target : mc.frame.msg.currentTarget = M.frame.msg.currentTarget
  value : mc.frame.msg.value = M.frame.msg.value
  data : mc.frame.msg.data = M.frame.msg.data
  isStatic : mc.frame.msg.isStatic = M.frame.msg.isStatic
  depth : mc.frame.msg.depth = M.frame.msg.depth + 1

/-- How the proxy frame (started at `M`) ends at `mf` with `o` after the implementation's frame
started at `mc` and ended at `mcf` with `oc`: success and revert data are passed through, an
exceptional halt becomes an empty revert; after success the world, transient storage and logs
are the implementation's, otherwise the proxy's; the proxy itself uses at most `K` gas besides
what the implementation used. -/
def Forwarded (M : Machine) (K : Nat) (mc mcf : Machine) (oc : Outcome) (mf : Machine)
    (o : Outcome) : Prop :=
  match oc with
  | .success out => o = .success out ∧ mf.world = mcf.world ∧ mf.transient = mcf.transient ∧
      mf.createdAccounts = mcf.createdAccounts ∧
      mf.frame.sub.logs = M.frame.sub.logs ++ mcf.frame.sub.logs ∧
      M.frame.gasLeft + mcf.frame.gasLeft ≤ mf.frame.gasLeft + K + mc.frame.gasLeft
  | .revert out => o = .revert out ∧ mf.world = M.world ∧ mf.transient = M.transient ∧
      mf.createdAccounts = mcf.createdAccounts ∧ mf.frame.sub.logs = M.frame.sub.logs ∧
      M.frame.gasLeft + mcf.frame.gasLeft ≤ mf.frame.gasLeft + K + mc.frame.gasLeft
  | .halt _ => o = .revert .empty ∧ mf.world = M.world ∧ mf.transient = M.transient ∧
      mf.createdAccounts = mcf.createdAccounts ∧ mf.frame.sub.logs = M.frame.sub.logs ∧
      M.frame.gasLeft ≤ mf.frame.gasLeft + K + mc.frame.gasLeft

theorem failSub_logs (p c : Substate) (w : World) (t : Address) :
    (failSub p c w t).logs = p.logs := by
  unfold failSub; split <;> rfl

/-- The memory of the proxy after `mstore(0x40, 0x80)`. -/
abbrev mem0 : Memory := ({ } : Memory).expand 64 32 |>.storeWord 64 128#256

/-- The selectors of the proxy's own functions: `admin()`, `implementation()`,
`initialize(address,bytes)`, `upgradeTo(address)`, `upgradeToAndCall(address,bytes)`. -/
def proxySelectors : List Nat := [0xf851a440, 0x5c60da1b, 0xd1f57894, 0x3659cfe6, 0x4f1ef286]

/-- They are the selectors of the verified ABI. -/
theorem proxySelectors_abi : proxySelectors.map (fun n => n.toUInt32) =
    ATokenProxy.selectors.map Prod.snd := by
  decide

theorem DelegatedFrom.of_eq {M M' mc : Machine} (h : DelegatedFrom M' mc)
    (h1 : M'.ctx = M.ctx) (h2 : M'.precompiles = M.precompiles)
    (h3 : M'.originalWorld = M.originalWorld) (h4 : M'.world = M.world)
    (h5 : M'.transient = M.transient) (h6 : M'.createdAccounts = M.createdAccounts)
    (h7 : M'.frame.msg = M.frame.msg) : DelegatedFrom M mc :=
  ⟨h.ctx.trans h1, h.precompiles.trans h2, h.originalWorld.trans h3, h.world.trans h4,
    h.transient.trans h5, h.created.trans h6, h7 ▸ h.caller, h7 ▸ h.target, h7 ▸ h.value,
    h7 ▸ h.data, h7 ▸ h.isStatic, h7 ▸ h.depth⟩

theorem Forwarded.of_le {M M' mc mcf mf : Machine} {oc o : Outcome} {K K' d : Nat}
    (h : Forwarded M' K mc mcf oc mf o) (hw : M'.world = M.world)
    (ht : M'.transient = M.transient) (hl : M'.frame.sub.logs = M.frame.sub.logs)
    (hg : M.frame.gasLeft ≤ M'.frame.gasLeft + d) (hK : K + d ≤ K') :
    Forwarded M K' mc mcf oc mf o := by
  cases oc with
  | success out =>
    obtain ⟨a, b, c, e, f, g⟩ := h
    exact ⟨a, b, c, e, by rw [f, hl], by omega⟩
  | revert out =>
    obtain ⟨a, b, c, e, f, g⟩ := h
    exact ⟨a, b.trans hw, c.trans ht, e, f.trans hl, by omega⟩
  | halt _ =>
    obtain ⟨a, b, c, e, f, g⟩ := h
    exact ⟨a, b.trans hw, c.trans ht, e, f.trans hl, by omega⟩

theorem lt_size_four_one {n : Nat} (h : n < 4) : Word.lt (ofNat n) (BitVec.ofNat 256 4) = 1 := by
  rw [Word.lt_eq_one_iff]; simp only [ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact h

theorem selectorOf_lt (data : ByteArray) : Abi.selectorOf data < 2 ^ 32 := by
  have := Bytes.toNat_lt (readBytes data 0 4)
  rw [size_readBytes] at this
  exact this

theorem eq_selector_of_ne {s c : Nat} (hs : s < 2 ^ 32) (hc : c < 2 ^ 32) (h : c ≠ s) :
    Word.eq (BitVec.ofNat 256 c) (BitVec.ofNat 256 s) = 0#256 :=
  eq_of_ne fun e => h (by
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this)

/-- The dispatcher's comparisons for a selector that is none of the proxy's. -/
theorem dispatch_facts {data : ByteArray} (h : Abi.selectorOf data ∉ proxySelectors) :
    Word.eq (BitVec.ofNat 256 0xf851a440) (BitVec.ofNat 256 (Abi.selectorOf data)) = 0#256 ∧
    Word.eq (BitVec.ofNat 256 0x5c60da1b) (BitVec.ofNat 256 (Abi.selectorOf data)) = 0#256 ∧
    Word.eq (BitVec.ofNat 256 0xd1f57894) (BitVec.ofNat 256 (Abi.selectorOf data)) = 0#256 ∧
    Word.eq (BitVec.ofNat 256 0x3659cfe6) (BitVec.ofNat 256 (Abi.selectorOf data)) = 0#256 ∧
    Word.eq (BitVec.ofNat 256 0x4f1ef286) (BitVec.ofNat 256 (Abi.selectorOf data)) = 0#256 := by
  have hs32 := selectorOf_lt data
  simp only [proxySelectors, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨n1, n2, n3, n4, n5⟩ := h
  exact ⟨eq_selector_of_ne hs32 (by decide) (Ne.symm n1),
    eq_selector_of_ne hs32 (by decide) (Ne.symm n2),
    eq_selector_of_ne hs32 (by decide) (Ne.symm n3),
    eq_selector_of_ne hs32 (by decide) (Ne.symm n4),
    eq_selector_of_ne hs32 (by decide) (Ne.symm n5)⟩

theorem gt_one_of_lt {a b : Word} (h : b.toNat < a.toNat) : Word.gt a b = 1#256 :=
  (Word.gt_eq_one_iff a b).2 h

theorem gt_zero_of_le {a b : Word} (h : a.toNat ≤ b.toNat) : Word.gt a b = 0#256 := by
  unfold Word.gt Word.ofBool
  simp [BitVec.ult, Nat.not_lt.mpr h]

/-- The dispatcher's first comparison (`0x5c60da1b > selector`) for a selector below it. -/
theorem gt_selector_lt {data : ByteArray} (h : Abi.selectorOf data < 0x5c60da1b) :
    Word.gt (BitVec.ofNat 256 0x5c60da1b) (BitVec.ofNat 256 (Abi.selectorOf data)) = 1#256 :=
  gt_one_of_lt (by have := selectorOf_lt data; simp only [BitVec.toNat_ofNat]; omega)

/-- The dispatcher's first comparison for a selector at least `0x5c60da1b`. -/
theorem gt_selector_ge {data : ByteArray} (h : ¬ Abi.selectorOf data < 0x5c60da1b) :
    Word.gt (BitVec.ofNat 256 0x5c60da1b) (BitVec.ofNat 256 (Abi.selectorOf data)) = 0#256 :=
  gt_zero_of_le (by have := selectorOf_lt data; simp only [BitVec.toNat_ofNat]; omega)

/-- The frame reverted (with some data) having changed nothing observable (world, transient
storage, created accounts, logs), using at most `g` gas. -/
def Reverted (g : Nat) (m mf : Machine) (o : Outcome) : Prop :=
  (∃ out, o = .revert out) ∧ mf.world = m.world ∧ mf.transient = m.transient ∧
    mf.createdAccounts = m.createdAccounts ∧ mf.frame.sub.logs = m.frame.sub.logs ∧
    m.frame.gasLeft ≤ mf.frame.gasLeft + g

theorem adminWord_eq_admin :
    Word.eq 574988636942314518095395226888196325637651086119#256 (Word.ofAddress admin) =
      1#256 := by
  rw [← ofAddress_admin]; exact eq_self _

end Examples.AaveV3.ATokenProxy
