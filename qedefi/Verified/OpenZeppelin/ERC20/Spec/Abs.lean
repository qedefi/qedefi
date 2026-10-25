import Verified.OpenZeppelin.ERC20.CalleeTransferFrom
import QEDefi.ERC20.Spec.Storage
import QEDefi.ERC20.Spec.Instances.Oz
import QEDefi.ERC20.RepOz

/-!
# `OzAsset`'s storage as `Variant.oz` states, for a set of actors

`ozAbs` reads `Layout.oz` (balances at slot 0, allowances at slot 1, the supply at slot 2) into
a `VState`: the actors' balances and allowances (`readMap`, `readMap2`), the supply, and
constants for every field `Variant.oz` never changes (`self` is the token's address). Its
`Sound` is `ActorRows` for the two mappings and slot 2: the actors' rows are pairwise distinct
and are not slot 2.

`actorView` is the word-level `ERC20.State` the actors see (zero outside them), which
represents `ozRead`'s ledger exactly (`rep_actorView`); under `ozSound` the compiled code's
storage writes (`moveWorld`, `allowanceWorld`, `ozTransferFromWorld`, `mintWorld`, `burnWorld`)
act on it as the word-level `ERC20.Model.oz*` operations do (`actorView_*`), and change nothing
outside the footprint (`frameKeeps_*`).
-/

namespace Verified.OpenZeppelin.ERC20.Spec
open EvmLean EvmLogic EvmLogic.Solidity EvmLogic.Solidity.ERC20 QEDefi.ERC20 QEDefi.ERC20.Spec
open QEDefi.Math EvmLean.Interpreter EvmLogic.Program

/-! ## The abstraction -/

/-- **The token at `token` in `w`, as the actors `Act` see it.** -/
noncomputable def ozRead (crypto : Crypto) (Act : Finset Address) (w : World) (token : Address) :
    VState Address where
  self := token
  bal := readMap crypto Act w token Layout.oz.balances
  supply := readSlot w token Layout.oz.totalSupply
  allowance := readMap2 crypto Act w token Layout.oz.allowances
  scale := 1
  admin := 0
  paused := false
  blacklisted := fun _ => false
  feeBps := 0
  feeMax := 0
  ether := 0
  frozen := 0
  nonces := 0

/-- The slots `ozRead` reads: the supply and the actors' rows. -/
def ozFootprint (crypto : Crypto) (Act : Finset Address) (k : Word) : Prop :=
  k = Layout.oz.totalSupply ∨ MapSlots crypto Act Layout.oz.balances k ∨
    Map2Slots crypto Act Layout.oz.allowances k

/-- **The hash hypothesis**: the actors' balance and allowance rows are pairwise distinct and
none is the supply slot (`ActorRows`; a finite set of Keccak values). -/
def ozSound (crypto : Crypto) (Act : Finset Address) : Prop :=
  ActorRows crypto Act [Layout.oz.balances] [Layout.oz.allowances] [Layout.oz.totalSupply]

theorem ozRead_congr (crypto : Crypto) (Act : Finset Address) (w w' : World) (token : Address)
    (h : ∀ k, ozFootprint crypto Act k → w'.sload token k = w.sload token k) :
    ozRead crypto Act w' token = ozRead crypto Act w token := by
  have h1 := readMap_congr (crypto := crypto) (Act := Act) (w := w) (w' := w') (token := token)
    (base := Layout.oz.balances) fun k hk => h k (.inr (.inl hk))
  have h2 := readMap2_congr (crypto := crypto) (Act := Act) (w := w) (w' := w') (token := token)
    (base := Layout.oz.allowances) fun k hk => h k (.inr (.inr hk))
  have h3 := readSlot_congr (w := w) (w' := w') (token := token) (h _ (.inl rfl))
  simp only [ozRead, h1, h2, h3]

/-- **`OzAsset`'s storage abstraction.** -/
noncomputable def ozAbs : TokenAbs (VState Address) where
  read := ozRead
  footprint := ozFootprint
  read_congr := fun crypto Act w w' token h _ => ozRead_congr crypto Act w w' token h
  Sound := ozSound

@[simp] theorem ozAbs_read : ozAbs.read = ozRead := rfl
@[simp] theorem ozAbs_footprint : ozAbs.footprint = ozFootprint := rfl
@[simp] theorem ozAbs_sound : ozAbs.Sound = ozSound := rfl

/-! ## The word-level view of the actors -/

/-- The word-level state the actors see: their balances and allowances, zero elsewhere. -/
def actorView (crypto : Crypto) (Act : Finset Address) (w : World) (token : Address) : State where
  totalSupply := w.sload token Layout.oz.totalSupply
  balanceOf a := if a ∈ Act then w.sload token (balanceSlot crypto Layout.oz a) else 0
  allowance o sp := if o ∈ Act ∧ sp ∈ Act then
    w.sload token (allowanceSlot crypto Layout.oz o sp) else 0

variable {crypto : Crypto} {Act : Finset Address} {w w' : World} {token : Address}

theorem actorView_balanceOf {a : Address} (ha : a ∈ Act) :
    (actorView crypto Act w token).balanceOf a = w.sload token (balanceSlot crypto Layout.oz a) := by
  simp only [actorView, ha, ↓reduceIte]

theorem actorView_allowance {o sp : Address} (ho : o ∈ Act) (hs : sp ∈ Act) :
    (actorView crypto Act w token).allowance o sp =
      w.sload token (allowanceSlot crypto Layout.oz o sp) := by
  simp only [actorView, ho, hs, and_self, ↓reduceIte]

/-- `actorView` represents the ledger `ozRead` reads. -/
theorem rep_actorView : Rep (actorView crypto Act w token) (ozRead crypto Act w token).toToken := by
  refine ⟨rfl, fun a => ?_, fun o sp _ => ?_⟩
  · show _ = readMap crypto Act w token Layout.oz.balances a
    by_cases ha : a ∈ Act
    · rw [readMap_of_mem ha, actorView_balanceOf ha]; rfl
    · rw [readMap_of_not_mem ha]; simp [actorView, ha]
  · show _ = readMap2 crypto Act w token Layout.oz.allowances o sp
    by_cases h : o ∈ Act ∧ sp ∈ Act <;> simp [readMap2, actorView, h, allowanceSlot]

/-- **Reading a represented ledger**: if `actorView` of `w'` represents `t`, the token in
`w'` is the token in `w` with the ledger `t`. -/
theorem ozRead_of_rep {t : Token Address} (hr : Rep (actorView crypto Act w' token) t) :
    ozRead crypto Act w' token = (ozRead crypto Act w token).withToken t := by
  have hb : readMap crypto Act w' token Layout.oz.balances = t.balanceOf := by
    ext a
    have := hr.balanceOf a
    by_cases ha : a ∈ Act
    · rw [readMap_of_mem ha, ← this, actorView_balanceOf ha]; rfl
    · rw [readMap_of_not_mem ha, ← this]; simp [actorView, ha]
  have hs : readSlot w' token Layout.oz.totalSupply = t.totalSupply := hr.totalSupply
  have ha : readMap2 crypto Act w' token Layout.oz.allowances = t.allowance := by
    funext o sp
    have := hr.allowance o sp trivial
    rw [← this]
    by_cases h : o ∈ Act ∧ sp ∈ Act <;> simp [readMap2, actorView, h, allowanceSlot]
  simp only [ozRead, VState.withToken, hb, hs, ha]

/-! ## Slots of the actors -/

section Slots

variable (hR : ozSound crypto Act)
include hR

theorem bal_inj {a b : Address} (ha : a ∈ Act) (hb : b ∈ Act)
    (h : balanceSlot crypto Layout.oz a = balanceSlot crypto Layout.oz b) : a = b :=
  (hR.inj1 _ (List.mem_singleton_self _) _ (List.mem_singleton_self _) a ha b hb h).1

theorem allow_inj {o sp o' sp' : Address} (ho : o ∈ Act) (hs : sp ∈ Act) (ho' : o' ∈ Act)
    (hs' : sp' ∈ Act)
    (h : allowanceSlot crypto Layout.oz o sp = allowanceSlot crypto Layout.oz o' sp') :
    o = o' ∧ sp = sp' :=
  let h' := hR.inj2 _ (List.mem_singleton_self _) _ (List.mem_singleton_self _) o ho sp hs o' ho'
    sp' hs' h
  ⟨h'.1, h'.2.1⟩

theorem bal_ne_allow {a o sp : Address} (ha : a ∈ Act) (ho : o ∈ Act) (hs : sp ∈ Act) :
    balanceSlot crypto Layout.oz a ≠ allowanceSlot crypto Layout.oz o sp :=
  hR.disj _ (List.mem_singleton_self _) _ (List.mem_singleton_self _) a ha o ho sp hs

theorem bal_ne_supply {a : Address} (ha : a ∈ Act) :
    balanceSlot crypto Layout.oz a ≠ Layout.oz.totalSupply := fun h =>
  hR.fixed1 _ (List.mem_singleton_self _) a ha (h ▸ List.mem_singleton_self _)

theorem allow_ne_supply {o sp : Address} (ho : o ∈ Act) (hs : sp ∈ Act) :
    allowanceSlot crypto Layout.oz o sp ≠ Layout.oz.totalSupply := fun h =>
  hR.fixed2 _ (List.mem_singleton_self _) o ho sp hs (h ▸ List.mem_singleton_self _)

/-- Writing an actor's balance row. -/
theorem actorView_sstore_bal {a : Address} (ha : a ∈ Act) (v : Word) :
    actorView crypto Act (w.sstore token (balanceSlot crypto Layout.oz a) v) token =
      (actorView crypto Act w token).setBalance a v := by
  simp only [actorView, State.setBalance, State.mk.injEq]
  refine ⟨World.sload_sstore_ne_key _ _ _ (bal_ne_supply hR ha).symm, ?_, ?_⟩
  · funext b
    by_cases hb : b ∈ Act
    · by_cases hba : b = a
      · subst hba; simp [hb]
      · simp only [hb, ↓reduceIte, hba]
        exact World.sload_sstore_ne_key _ _ _ fun h => hba (bal_inj hR hb ha h)
    · have : b ≠ a := fun h => hb (h ▸ ha)
      simp [hb, this]
  · funext o sp
    split
    · rename_i h
      exact World.sload_sstore_ne_key _ _ _ (bal_ne_allow hR ha h.1 h.2).symm
    · rfl

/-- Writing an allowance row of two actors. -/
theorem actorView_sstore_allow {o sp : Address} (ho : o ∈ Act) (hs : sp ∈ Act) (v : Word) :
    actorView crypto Act (w.sstore token (allowanceSlot crypto Layout.oz o sp) v) token =
      (actorView crypto Act w token).setAllowance o sp v := by
  simp only [actorView, State.setAllowance, State.mk.injEq]
  refine ⟨World.sload_sstore_ne_key _ _ _ (allow_ne_supply hR ho hs).symm, ?_, ?_⟩
  · funext b
    split
    · rename_i hb
      exact World.sload_sstore_ne_key _ _ _ (bal_ne_allow hR hb ho hs)
    · rfl
  · funext o' sp'
    by_cases h : o' ∈ Act ∧ sp' ∈ Act
    · by_cases he : o' = o ∧ sp' = sp
      · obtain ⟨rfl, rfl⟩ := he; simp [h]
      · simp only [h, and_self, ↓reduceIte, he]
        exact World.sload_sstore_ne_key _ _ _ fun hk => he (allow_inj hR h.1 h.2 ho hs hk)
    · have : ¬ (o' = o ∧ sp' = sp) := fun he => h (he.1 ▸ he.2 ▸ ⟨ho, hs⟩)
      simp [h, this]

/-- Writing the supply slot. -/
theorem actorView_sstore_supply (v : Word) :
    actorView crypto Act (w.sstore token Layout.oz.totalSupply v) token =
      { actorView crypto Act w token with totalSupply := v } := by
  simp only [actorView, State.mk.injEq, World.sload_sstore_self, true_and]
  refine ⟨?_, ?_⟩
  · funext b
    split
    · rename_i hb
      exact World.sload_sstore_ne_key _ _ _ (bal_ne_supply hR hb)
    · rfl
  · funext o sp
    split
    · rename_i h
      exact World.sload_sstore_ne_key _ _ _ (allow_ne_supply hR h.1 h.2)
    · rfl

/-! ## The compiled code's writes, through the view -/

/-- `_update` between two actors is `Model.ozTransfer`. -/
theorem actorView_moveWorld {c d : Address} {amount : Word} {s' : State} (hc : c ∈ Act)
    (hd : d ∈ Act) (hm : Model.ozTransfer (actorView crypto Act w token) c d amount = some s') :
    actorView crypto Act (moveWorld crypto Layout.oz w token c d amount) token = s' := by
  unfold Model.ozTransfer at hm
  split at hm
  · cases hm
  split at hm
  · cases hm
  unfold Model.transfer at hm
  split at hm
  · cases hm
    have e2 : ∀ v, (w.sstore token (balanceSlot crypto Layout.oz c) v).sload token
        (balanceSlot crypto Layout.oz d) =
        (actorView crypto Act (w.sstore token (balanceSlot crypto Layout.oz c) v) token).balanceOf d :=
      fun v => (actorView_balanceOf hd).symm
    simp only [moveWorld]
    rw [e2, actorView_sstore_bal hR hd, actorView_sstore_bal hR hc, ← actorView_balanceOf hc,
      BitVec.add_comm]
  · cases hm

/-- One allowance write between two actors is `Model.approve`. -/
theorem actorView_allowanceWorld {o sp : Address} {amount : Word} (ho : o ∈ Act)
    (hs : sp ∈ Act) :
    actorView crypto Act (allowanceWorld crypto Layout.oz w token o sp amount) token =
      Model.approve (actorView crypto Act w token) o sp amount :=
  actorView_sstore_allow hR ho hs amount

/-- `_spendAllowance` between two actors is `Model.ozSpend`. -/
theorem actorView_ozSpendWorld {o sp : Address} {amount : Word} {s₁ : State} (ho : o ∈ Act)
    (hs : sp ∈ Act) (hm : Model.ozSpend (actorView crypto Act w token) o sp amount = some s₁) :
    actorView crypto Act (ozSpendWorld crypto Layout.oz w token o sp amount) token = s₁ := by
  unfold Model.ozSpend at hm
  rw [actorView_allowance ho hs] at hm
  simp only [ozSpendWorld]
  split
  · rename_i hmax
    simp only [hmax, ↓reduceIte, Option.some.injEq] at hm
    exact hm
  · rename_i hmax
    simp only [hmax, ↓reduceIte] at hm
    split at hm
    · unfold Model.ozApprove at hm
      split at hm
      · cases hm
      · split at hm
        · cases hm
        · cases hm
          rw [actorView_allowanceWorld hR ho hs]
    · cases hm

/-- `transferFrom` between actors is `Model.ozTransferFrom`. -/
theorem actorView_ozTransferFromWorld {sp src dst : Address} {amount : Word} {s' : State}
    (hsp : sp ∈ Act) (hs : src ∈ Act) (hd : dst ∈ Act)
    (hm : Model.ozTransferFrom (actorView crypto Act w token) sp src dst amount = some s') :
    actorView crypto Act (ozTransferFromWorld crypto Layout.oz w token sp src dst amount) token =
      s' := by
  unfold Model.ozTransferFrom at hm
  obtain ⟨s₁, h1, h2⟩ := Option.bind_eq_some_iff.1 hm
  have e1 := actorView_ozSpendWorld hR hs hsp h1
  rw [← e1] at h2
  exact actorView_moveWorld hR hs hd h2

/-- `_mint` to an actor is `Model.ozMint`. -/
theorem actorView_mintWorld {d : Address} {amount : Word} {s' : State} (hd : d ∈ Act)
    (hm : Model.ozMint (actorView crypto Act w token) d amount = some s') :
    actorView crypto Act (mintWorld crypto Layout.oz w token d amount) token = s' := by
  unfold Model.ozMint at hm
  split at hm
  · cases hm
  split at hm
  · cases hm
    have e2 : ∀ v, (w.sstore token Layout.oz.totalSupply v).sload token
        (balanceSlot crypto Layout.oz d) =
        (actorView crypto Act (w.sstore token Layout.oz.totalSupply v) token).balanceOf d :=
      fun v => (actorView_balanceOf hd).symm
    simp only [mintWorld]
    rw [e2, actorView_sstore_bal hR hd, actorView_sstore_supply hR]
    rfl
  · cases hm

/-- `_burn` from an actor is `Model.ozBurn`. -/
theorem actorView_burnWorld {src : Address} {amount : Word} {s' : State} (hs : src ∈ Act)
    (hm : Model.ozBurn (actorView crypto Act w token) src amount = some s') :
    actorView crypto Act (burnWorld crypto Layout.oz w token src amount) token = s' := by
  unfold Model.ozBurn at hm
  split at hm
  · cases hm
  split at hm
  · cases hm
    have e2 : ∀ v, (w.sstore token (balanceSlot crypto Layout.oz src) v).sload token
        Layout.oz.totalSupply =
        (actorView crypto Act (w.sstore token (balanceSlot crypto Layout.oz src) v)
          token).totalSupply := fun v => rfl
    simp only [burnWorld]
    rw [e2, actorView_sstore_supply hR, actorView_sstore_bal hR hs, ← actorView_balanceOf hs]
  · cases hm

end Slots

/-! ## What the writes keep -/

theorem frameKeeps_refl : FrameKeeps ozAbs crypto Act token w w :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem frameKeeps_trans {w₁ w₂ : World} (h₁ : FrameKeeps ozAbs crypto Act token w w₁)
    (h₂ : FrameKeeps ozAbs crypto Act token w₁ w₂) : FrameKeeps ozAbs crypto Act token w w₂ :=
  ⟨fun k hk => (h₂.own k hk).trans (h₁.own k hk), h₂.code.trans h₁.code,
    h₂.nonce.trans h₁.nonce, h₂.balance.trans h₁.balance,
    fun b hb => (h₂.others b hb).trans (h₁.others b hb)⟩

/-- One write inside the footprint. -/
theorem frameKeeps_sstore {k : Word} (hk : ozFootprint crypto Act k) (v : Word) :
    FrameKeeps ozAbs crypto Act token w (w.sstore token k v) := by
  refine ⟨fun k' hk' => World.sload_sstore_ne_key _ _ _ (fun h => hk' (h ▸ hk)),
    World.code_sstore _ _ _ _ _, ?_, World.balance_sstore _ _ _ _ _,
    fun b hb => World.account_modify_ne _ _ hb⟩
  simp [World.sstore]

theorem fp_bal {a : Address} (ha : a ∈ Act) :
    ozFootprint crypto Act (balanceSlot crypto Layout.oz a) := .inr (.inl ⟨a, ha, rfl⟩)

theorem fp_allow {o sp : Address} (ho : o ∈ Act) (hs : sp ∈ Act) :
    ozFootprint crypto Act (allowanceSlot crypto Layout.oz o sp) :=
  .inr (.inr ⟨o, ho, sp, hs, rfl⟩)

theorem fp_supply : ozFootprint crypto Act Layout.oz.totalSupply := .inl rfl

theorem frameKeeps_moveWorld {c d : Address} {amount : Word} (hc : c ∈ Act) (hd : d ∈ Act) :
    FrameKeeps ozAbs crypto Act token w (moveWorld crypto Layout.oz w token c d amount) :=
  frameKeeps_trans (frameKeeps_sstore (fp_bal hc) _) (frameKeeps_sstore (fp_bal hd) _)

theorem frameKeeps_allowanceWorld {o sp : Address} {amount : Word} (ho : o ∈ Act)
    (hs : sp ∈ Act) :
    FrameKeeps ozAbs crypto Act token w (allowanceWorld crypto Layout.oz w token o sp amount) :=
  frameKeeps_sstore (fp_allow ho hs) _

theorem frameKeeps_ozTransferFromWorld {sp src dst : Address} {amount : Word} (hsp : sp ∈ Act)
    (hs : src ∈ Act) (hd : dst ∈ Act) :
    FrameKeeps ozAbs crypto Act token w
      (ozTransferFromWorld crypto Layout.oz w token sp src dst amount) := by
  refine frameKeeps_trans ?_ (frameKeeps_moveWorld hs hd)
  simp only [ozSpendWorld]
  split
  · exact frameKeeps_refl
  · exact frameKeeps_allowanceWorld hs hsp

theorem frameKeeps_mintWorld {d : Address} {amount : Word} (hd : d ∈ Act) :
    FrameKeeps ozAbs crypto Act token w (mintWorld crypto Layout.oz w token d amount) :=
  frameKeeps_trans (frameKeeps_sstore fp_supply _) (frameKeeps_sstore (fp_bal hd) _)

theorem frameKeeps_burnWorld {src : Address} {amount : Word} (hs : src ∈ Act) :
    FrameKeeps ozAbs crypto Act token w (burnWorld crypto Layout.oz w token src amount) :=
  frameKeeps_trans (frameKeeps_sstore (fp_bal hs) _) (frameKeeps_sstore fp_supply _)

end Verified.OpenZeppelin.ERC20.Spec
