import Examples.Safe.Bytecode.Defs

/-!
# The singleton's frames: context

A frame of the Safe v1.5.0 singleton's code at the Safe `sf` (delegated from `SafeProxy`):
`Jsg` is the frame judgment it satisfies from its start (`OwnG`: every own path ends the frame,
each `SSTORE` writes the nonce or an approval, requests satisfy `Iss sf` except at
`simulateAndRevert`'s `DELEGATECALL`, after which the frame is doomed). `SgCtx` collects what
the proof uses about the frame and the transaction.
-/

namespace Examples.Safe.Guard

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested
open Examples.Safe.Contracts

/-! ## Word facts -/

theorem ofBool_ne_zero {b : Bool} : Word.ofBool b ≠ 0 ↔ b = true := by
  cases b <;> decide

theorem iszero_ne_zero {x : Word} : Word.iszero x ≠ 0 ↔ x = 0 := by
  unfold Word.iszero; rw [ofBool_ne_zero, beq_iff_eq]

theorem iszero_eq_zero {x : Word} : Word.iszero x = 0 ↔ x ≠ 0 := by
  rw [← not_iff_not, not_not, ← ne_eq, iszero_ne_zero]

theorem lt_ne_zero {x y : Word} : Word.lt x y ≠ 0 ↔ x.toNat < y.toNat := by
  unfold Word.lt; rw [ofBool_ne_zero]; simp [BitVec.ult]

theorem lt_eq_zero {x y : Word} : Word.lt x y = 0 ↔ y.toNat ≤ x.toNat := by
  rw [← not_iff_not, ← ne_eq, lt_ne_zero, Nat.not_le]

theorem gt_ne_zero {x y : Word} : Word.gt x y ≠ 0 ↔ y.toNat < x.toNat := by
  unfold Word.gt; rw [ofBool_ne_zero]; simp [BitVec.ult]

theorem gt_eq_zero {x y : Word} : Word.gt x y = 0 ↔ x.toNat ≤ y.toNat := by
  rw [← not_iff_not, ← ne_eq, gt_ne_zero, Nat.not_le]

theorem toNat_add_of_lt {x y : Word} (h : x.toNat + y.toNat < 2 ^ 256) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

namespace Dep

variable (D : Dep)

/-- The frame judgment of the singleton's frames at the Safe. -/
abbrev Jsg (crypto : Crypto) (chainId : Nat) (O T : Finset Address) (thr : Nat) (h₀ : Word)
    (fork : Fork) : Machine → Prop :=
  OwnG True (fun _ => True) (D.Rsf crypto chainId O T thr h₀ fork) (Own.SstoreOk (Kw crypto))
    D.Csf Dsim Doomed

/-- The tracked constants of a singleton frame. -/
abbrev fix (msg : Message) (ctx : Context) : Fix :=
  ⟨msg, ctx, PrecompileImpl.standard ctx, SafeSingleton.runtimeCode⟩

/-- What a singleton frame at the Safe uses: who runs it, the transaction's signers and owners,
the fallback handler. -/
structure SgCtx (O T : Finset Address) (thr : Nat) (h₀ : Word) (msg : Message) (ctx : Context) :
    Prop where
  target : msg.currentTarget = D.sf
  caller : msg.caller ≠ D.sf
  active : ¬ X ctx.fork O T msg.caller
  thr_lt : thr < 2 ^ 256
  card : (O ∩ T).card < thr
  signers : Signers ctx.crypto ctx.block.chainId D.sf O T
  handler : h₀ = 0 ∨ ¬ D.Rl (Word.toAddress h₀)

/-- The free memory pointer after the singleton's prologue (`mstore(0x40, 0x80)`). -/
abbrev mem0 : Memory := (({ } : Memory).expand 64 32).storeWord 64 128#256

theorem not_dsim {k : Fix} {m : Machine} {pc : Nat} {st : List Word} {mem : Memory} {w : World}
    (hF : Fr k m pc st mem w) (h : pc ≠ 11184) : ¬ Dsim m := fun hd => h (hF.pc.symm.trans hd)

theorem eq_ofAddress_of_ne {a b : Address} (h : a ≠ b) :
    Word.eq (Word.ofAddress a) (Word.ofAddress b) = 0 := by
  have : (Word.ofAddress a == Word.ofAddress b) = false := by
    simpa using fun e => h (Word.ofAddress_injective e)
  simp [Word.eq, this, Word.ofBool]

/-- The singleton frame is not a self-call: `authorized` functions revert. -/
theorem SgCtx.eq_caller {O T : Finset Address} {thr : Nat} {h₀ : Word} {msg : Message}
    {ctx : Context} (hC : D.SgCtx O T thr h₀ msg ctx) :
    Word.eq (Word.ofAddress msg.caller) (Word.ofAddress msg.currentTarget) = 0 :=
  eq_ofAddress_of_ne (by rw [hC.target]; exact hC.caller)

theorem handlerSlot_eq :
    handlerSlot = 49122629484629529244014240937346711770925847994644146912111677022347558721749#256 :=
  rfl

/-! ## Side conditions of calls -/

theorem pre_one (msg : Message) (ctx : Context) :
    (fix msg ctx).pre.isPrecompile (Word.toAddress 1#256) = true := by
  show Precompile.isPrecompile ctx.fork (Word.toAddress 1#256) = true
  exact isPrecompile_one _

/-- After Prague, `1` is idle: no code, so no delegation designator. -/
theorem del_one {crypto : Crypto} {chainId : Nat} {O T : Finset Address} {thr : Nat} {h₀ : Word}
    {msg : Message} {ctx : Context} {m : Machine} {w : World} (hw : m.world = w) :
    D.Rsf crypto chainId O T thr h₀ ctx.fork m →
      (fix msg ctx).ctx.fork < .prague ∨ delegatedAddress? (w.code (Word.toAddress 1#256)) = none := by
  rintro ⟨-, hI, -⟩
  by_cases hf : ctx.fork < .prague
  · exact .inl hf
  · right
    have h0 := (hI 1 (.inl ⟨rfl, Nat.le_of_not_lt hf⟩)).1
    rw [hw] at h0
    cases hd : delegatedAddress? (w.code (Word.toAddress 1#256)) with
    | none => rfl
    | some d => exact absurd h0 (delegated_size hd)

/-- A static request satisfies the Safe's issuance. -/
theorem csf_static {m : Machine} {req : CallRequest} (h : req.msg.isStatic = true) : D.Csf m req :=
  .inr (.inl ⟨rfl, .inl h⟩)

end Dep

/-- Close a doom-point goal away from `simulateAndRevert`'s `DELEGATECALL`. -/
macro "sg_nodoom" : tactic =>
  `(tactic| exact fun hd => absurd hd (Dep.not_dsim (by assumption) (by decide)))

/-- Close the side conditions of the singleton's static calls (`ecrecover`, `isValidSignature`)
and of calls away from the doom point. -/
macro "sg_side" : tactic => `(tactic| first
  | sg_nodoom
  | exact Dep.not_dsim (by assumption) (by decide)
  | exact Dep.pre_one _ _
  | exact Dep.del_one _ (Fr.world (by assumption))
  | exact fun _ _ hs => Dep.csf_static _ hs
  | exact fun _ _ _ hm => Dep.csf_static _ (OwnB.callMsg_static hm))

/-- `own_explore` with the normalization of solc's memory idioms (mapping-slot preimages in
scratch space, the free memory pointer) and address masks. -/
syntax "sg_explore" (" [" num,* "]")? (&" using" " [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| sg_explore $[[$pcs,*]]? $[using [$extra,*]]?) => do
    let pcs := (pcs.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| own_explore [$pcs,*] using [readBytes_bytes, Memory.read_64, Memory.read_expand,
      Memory.read_storeWord, Memory.read_storeWord_of_disjoint,
      Memory.loadWord_storeWord_of_disjoint, EvmLogic.Solidity.ofAddress_and_addressMask,
      EvmLogic.Solidity.addressMask_and_ofAddress, $extra,*])

end Examples.Safe.Guard
