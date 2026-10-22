import Examples.AaveV3.AToken.State
import Examples.AaveV3.ATokenProxy.Basic
import Examples.Reentrancy.Solvency.Deps
import EvmLogic.Program.Reentrancy.AnyCaller

/-!
# The aEthWETH ledger as a world invariant

The protected accounts are the aEthWETH proxy (`proxy`, mainnet `0x4d5F…14E8`) and the AToken
implementation it delegates to (`impl`, `0xadC4…7AdA`), `Prot`. `Good crypto w`:

* the proxy runs the deployed proxy code, the implementation the deployed AToken code, and the
  proxy's EIP-1967 slot holds the implementation;
* at **both** accounts (the implementation is a contract of its own that anyone may call; its
  own storage is a second, independent ledger) `TokenOk`: `lastInitializedRevision ≥ 5` and
  `initializing = false` (so `initialize` reverts), and **the sum of the scaled balances (the low
  120 bits of every `_userState` slot) equals `_totalSupply`** (slot 54), in `ℕ`.

The sum is over the **slots** of the `_userState` entries (`userSlots`, the image of all
addresses), so it needs no Keccak injectivity: two addresses whose entries collide share one
balance, counted once. The only Keccak hypotheses (`SlotsOk`) say that the finite families of
slots the code writes — `_userState[a]`, `_allowances[o][s]`, `_nonces[a]` — are pairwise
disjoint and avoid the fixed slots `0`, `1`, `54` and the EIP-1967 slot.

`goodOps_good`: `Good` depends only on the storage and code of the two protected accounts, which
hold non-delegated code, so it is closed under every world change arbitrary code makes
(`GoodOps`).
-/

namespace Examples.AaveV3.AToken.Havoc
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
  EvmLogic.Program.Reentrancy EvmLogic.Solidity Examples.AaveV3.Contracts

/-! ## Normal forms for the prefix executor -/

/-- solc's address mask of any word is an address. -/
theorem mask_and_eq (x : Word) :
    1461501637330902918203684832716283019655932542975#256 &&& x =
      Word.ofAddress (Word.toAddress x) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Word.ofAddress, Word.toAddress, BitVec.toNat_and, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by decide : 1461501637330902918203684832716283019655932542975 < 2 ^ 256),
    show (1461501637330902918203684832716283019655932542975 : Nat) = 2 ^ 160 - 1 by decide,
    Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]

/-- solc's address mask of any word, operands swapped. -/
theorem and_mask_eq (x : Word) :
    x &&& 1461501637330902918203684832716283019655932542975#256 =
      Word.ofAddress (Word.toAddress x) := by
  rw [BitVec.and_comm]; exact mask_and_eq x

/-- A Keccak of two words is a mapping slot. -/
theorem keccak_mappingSlot (crypto : Crypto) (k b : Word) :
    crypto.keccak256 (Bytes.ofWord k ++ Bytes.ofWord b) = mappingSlot crypto k b := rfl

/-! ## Accounts and slots -/

/-- The aEthWETH proxy. -/
abbrev proxy : Address := ATokenProxy.address
/-- The AToken implementation. -/
abbrev impl : Address := AToken.address

theorem proxy_ne_impl : proxy ≠ impl := by decide

/-- The protected accounts: the proxy and its implementation. -/
def Prot (a : Address) : Prop := a = proxy ∨ a = impl

/-- The slot of `_userState[a]` (mapping at slot 52), as the code computes it. -/
abbrev userSlot (crypto : Crypto) (a : Address) : Word :=
  mappingSlot crypto (Word.ofAddress a) 52#256

/-- The slots of `_userState[a]`, for all addresses `a`. -/
def userSlots (crypto : Crypto) : Finset Word := Finset.univ.image (userSlot crypto)

/-- The slots of `_allowances[o][s]` (nested mapping at slot 53), for all `o`, `s`. -/
def allowanceSlots (crypto : Crypto) : Finset Word :=
  Finset.univ.image fun p : Address × Address =>
    mappingSlot crypto (Word.ofAddress p.2) (mappingSlot crypto (Word.ofAddress p.1) 53#256)

/-- The slots of `_nonces[a]` (mapping at slot 58), for all addresses `a`. -/
def nonceSlots (crypto : Crypto) : Finset Word :=
  Finset.univ.image fun a : Address => mappingSlot crypto (Word.ofAddress a) 58#256

/-- The fixed slots the invariant reads: `lastInitializedRevision`, `initializing`,
`_totalSupply`, the EIP-1967 implementation slot. -/
def fixedSlots : Finset Word := {0#256, 1#256, 54#256, ATokenProxy.implSlot}

/-- **The Keccak hypotheses**: the slot families the code writes are pairwise disjoint and avoid
the fixed slots. Statements about finite families of slots, not injectivity of Keccak. -/
structure SlotsOk (crypto : Crypto) : Prop where
  allow : Disjoint (allowanceSlots crypto) (userSlots crypto)
  nonce : Disjoint (nonceSlots crypto) (userSlots crypto)
  userFixed : Disjoint (userSlots crypto) fixedSlots
  allowFixed : Disjoint (allowanceSlots crypto) fixedSlots
  nonceFixed : Disjoint (nonceSlots crypto) fixedSlots

theorem mem_userSlots (crypto : Crypto) (a : Address) : userSlot crypto a ∈ userSlots crypto :=
  Finset.mem_image_of_mem _ (Finset.mem_univ a)

theorem mem_allowanceSlots (crypto : Crypto) (o s : Address) :
    mappingSlot crypto (Word.ofAddress s) (mappingSlot crypto (Word.ofAddress o) 53#256) ∈
      allowanceSlots crypto :=
  Finset.mem_image.2 ⟨(o, s), Finset.mem_univ _, rfl⟩

theorem mem_nonceSlots (crypto : Crypto) (a : Address) :
    mappingSlot crypto (Word.ofAddress a) 58#256 ∈ nonceSlots crypto :=
  Finset.mem_image_of_mem _ (Finset.mem_univ a)

/-! ## The invariant -/

/-- The scaled balance held in a `_userState` word: its low 120 bits. -/
def low120 (x : Word) : Nat := x.toNat % 2 ^ 120

/-- The sum of the scaled balances at `t`, over the `_userState` slots. -/
def ledgerSum (crypto : Crypto) (w : World) (t : Address) : Nat :=
  ∑ s ∈ userSlots crypto, low120 (w.sload t s)

/-- The token state at `t` is initialized and its scaled ledger balanced. -/
structure TokenOk (crypto : Crypto) (w : World) (t : Address) : Prop where
  /-- `lastInitializedRevision ≥ 5` (`ATOKEN_REVISION`). -/
  rev : 5 ≤ (w.sload t 0#256).toNat
  /-- `initializing = false` (byte 0 of slot 1). -/
  init : (w.sload t 1#256).toNat % 256 = 0
  /-- **Σ scaled balances = scaled total supply.** -/
  ledger : ledgerSum crypto w t = (w.sload t 54#256).toNat

/-- **The invariant** (see the module docstring). -/
structure Good (crypto : Crypto) (w : World) : Prop where
  proxyCode : w.code proxy = ATokenProxy.runtimeCode
  implCode : w.code impl = AToken.runtimeCode
  implSlot : w.sload proxy ATokenProxy.implSlot = Word.ofAddress impl
  proxyOk : TokenOk crypto w proxy
  implOk : TokenOk crypto w impl

/-- The transaction hashes with `crypto`. -/
abbrev Ctx (crypto : Crypto) : Context → Prop := fun c => c.crypto = crypto

/-! ## Closure under arbitrary code -/

theorem TokenOk.keep {crypto : Crypto} {w w' : World} {t : Address} (h : TokenOk crypto w t)
    (hk : Keep t w w') : TokenOk crypto w' t := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hk.sload]; exact h.rev
  · rw [hk.sload]; exact h.init
  · unfold ledgerSum; simp only [hk.sload]; exact h.ledger

theorem Good.keep {crypto : Crypto} {w w' : World} (h : Good crypto w)
    (hk : KeepP Prot w w') : Good crypto w' := by
  have hp := hk proxy (.inl rfl)
  have hi := hk impl (.inr rfl)
  exact ⟨by rw [hp.code]; exact h.proxyCode, by rw [hi.code]; exact h.implCode,
    by rw [hp.sload]; exact h.implSlot, h.proxyOk.keep hp, h.implOk.keep hi⟩

theorem size_proxyCode : ATokenProxy.runtimeCode.size ≠ 0 := by
  rw [ATokenProxy.size_runtimeCode]; decide

theorem size_implCode : AToken.runtimeCode.size ≠ 0 := by
  rw [AToken.size_runtimeCode]; decide

theorem deleg_proxyCode : delegatedAddress? ATokenProxy.runtimeCode = none := by decide +kernel

theorem deleg_implCode : delegatedAddress? AToken.runtimeCode = none := by decide +kernel

theorem Good.code_size {crypto : Crypto} {w : World} (h : Good crypto w) :
    ∀ p, Prot p → (w.code p).size ≠ 0 := by
  rintro p (rfl | rfl)
  · rw [h.proxyCode]; exact size_proxyCode
  · rw [h.implCode]; exact size_implCode

/-- **`Good` is closed under everything arbitrary code does.** -/
theorem goodOps_good (crypto : Crypto) : GoodOps Prot (Good crypto) where
  code := fun _ h => h.code_size
  deleg w h p hp := by
    rcases hp with rfl | rfl
    · rw [h.proxyCode]; exact deleg_proxyCode
    · rw [h.implCode]; exact deleg_implCode
  sstore w a k v h ha := h.keep fun p hp => keep_sstore fun e => ha (e ▸ hp)
  nonce w a h := h.keep fun p hp => keep_incrementNonce (h.code_size p hp)
  move w src dst v h _ _ := h.keep fun p hp => keep_moveEther (h.code_size p hp)
  burn w a h ha := h.keep fun p hp => keep_setAccountBalance (h.code_size p hp)
  setCode w a c h ha := h.keep fun p hp => keep_setCode fun e => ha (e ▸ hp)

end Examples.AaveV3.AToken.Havoc
