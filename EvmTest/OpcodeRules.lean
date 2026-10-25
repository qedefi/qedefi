import EvmLogic.Tactic.WpStep
import EvmLogic.Tactic.PrefixStep
import EvmTest.InterpreterUtil
import EvmLogic.Program.Create
import EvmLogic.Program.CallCode
import EvmLogic.Program.Selfdestruct
import EvmLogic.Program.Reentrancy.Create

/-!
# The step lemmas and WP rules of `TLOAD`/`TSTORE`, `CREATE*`, `SELFDESTRUCT`, `CALLCODE` fire

Small concrete machines. For an arbitrary `Crypto`, `evm_steps`, `wp_steps` and `apwp_steps`
execute `TSTORE`/`TLOAD` (and evaluate the read-after-write). With the test `fakeCrypto`,
`step_tstore_static` halts a static frame, and the `CREATE`, `CREATE2`, `SELFDESTRUCT` and
`CALLCODE` lemmas (and `WP.create_havoc`) apply to literal machines with their side conditions
decided, including the freshness of the hashed `CREATE`/`CREATE2` address. The checks are kernel
proofs, run at build time.
-/

namespace EvmTest.OpcodeRules

open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmTest.InterpreterUtil

/-- A top-level frame running `code` at `contract`, with `gas`, at `pc` with `stack`. -/
def machine (crypto : Crypto) (code : ByteArray) (isStatic : Bool := false) (pc : Nat := 0)
    (stack : List Word := []) (gas : Nat := 100000) : Machine :=
  let w : World := (∅ : World).insert contract { nonce := 1, code := code }
  let msg : Message :=
    { caller := 0xCA11, target := some contract, currentTarget := contract, gas := gas,
      value := 0, data := .empty, codeAddress := some contract, code := code, depth := 0,
      shouldTransferValue := false, isStatic := isStatic, accessedAddresses := ∅,
      accessedStorageKeys := ∅ }
  { ctx := { crypto }, precompiles := PrecompileImpl.standard { crypto }, world := w,
    transient := ∅, originalWorld := w, createdAccounts := ∅,
    frame := { Frame.init msg (.call 0 0) (w, ∅) with pc := pc, stack := stack },
    parents := [] }

/-! ## `TLOAD` / `TSTORE` -/

/-- `PUSH1 7 PUSH1 1 TSTORE PUSH1 1 TLOAD PUSH0 SSTORE STOP`: write 7 to transient slot 1, read
it back, store it in slot 0. -/
def tcode : ByteArray := ⟨#[0x60, 0x07, 0x60, 0x01, 0x5d, 0x60, 0x01, 0x5c, 0x5f, 0x55, 0x00]⟩

/-- `evm_steps` runs the whole program (`step_tstore`, `step_tload`, read-after-write). -/
example (crypto : Crypto) (k : Nat) :
    ∃ r, run (k + 8) (machine crypto tcode) = .ok r ∧ r.world.sload contract 0 = 7 := by
  simp only [machine, Frame.init]
  evm_steps
  refine ⟨_, rfl, ?_⟩
  simp only [topLevelResult_world, World.sload_sstore_self]
  rfl

/-- `wp_steps` reaches the `TLOAD` result on the stack, for any gas `g ≥ 1000`. -/
example (crypto : Crypto) (g : Nat) (hg : 1000 ≤ g) :
    WP (machine crypto tcode (gas := g)) (fun m => m.frame.pc = 8 ∧ m.frame.stack = [7])
      (fun _ _ => False) := by
  simp only [machine, Frame.init]
  wp_steps 5
  exact WP.ret ⟨rfl, rfl⟩

/-- The any-gas prefix calculus (`apwp_steps`, rules `pwp_tstore`/`pwp_tload`) runs to the
`TLOAD` result for **any** gas: out-of-gas paths are absorbed by the `Good` snapshot. -/
example (crypto : Crypto) (g : Nat) :
    WP (machine crypto tcode (gas := g)) (fun m => m.frame.pc = 8 ∧ m.frame.stack = [7])
      (Reentrancy.FailOk (fun _ => True)) := by
  simp only [machine, Frame.init]
  have hsnap : True := trivial
  apwp_steps stop_at [8]
  exact WP.ret ⟨rfl, rfl⟩

/-- In a static frame the `TSTORE` at pc 4 halts with `writeInStaticContext`. -/
example :
    step (machine fakeCrypto tcode true 4 [1, 7]) =
      finishFrame (machine fakeCrypto tcode true 4 [1, 7]) (.halt .writeInStaticContext) :=
  step_tstore_static rfl rfl rfl (by decide)

/-! ## `CREATE` / `CREATE2` -/

/-- `PUSH0 PUSH0 PUSH0 CREATE STOP`: create a contract from empty init code, no value. -/
def ccode : ByteArray := ⟨#[0x5f, 0x5f, 0x5f, 0xf0, 0x00]⟩

/-- `PUSH0 PUSH0 PUSH0 PUSH0 CREATE2 STOP`: the same with `CREATE2` and salt 0. -/
def c2code : ByteArray := ⟨#[0x5f, 0x5f, 0x5f, 0x5f, 0xf5, 0x00]⟩

/-- `step_create` at the `CREATE` (the new address, hashed with the test `fakeCrypto`, is
free). -/
example :
    step (machine fakeCrypto ccode false 3 [0, 0, 0]) =
      .running (createChild (machine fakeCrypto ccode false 3 [0, 0, 0]) false 0 0 0 0 []) :=
  step_create rfl rfl (by decide) (by decide) rfl (Nat.zero_le _) (by decide) (by decide)
    (by decide +kernel)

/-- `step_create2` at the `CREATE2`. -/
example :
    step (machine fakeCrypto c2code false 4 [0, 0, 0, 0]) =
      .running (createChild (machine fakeCrypto c2code false 4 [0, 0, 0, 0]) true 0 0 0 0 []) :=
  step_create2 rfl rfl (by decide) (by decide) rfl (Nat.zero_le _) (by decide) (by decide)
    (by decide +kernel)

/-- The 63/64 rule: the creator keeps `⌊(100000 − 32000) / 64⌋ = 1062` gas. -/
example :
    (creatorFrame (machine fakeCrypto ccode false 3 [0, 0, 0]) false 0 0 0 []).gasLeft = 1062 := by
  simp only [creatorFrame, creatorGas_eq]
  decide

/-- With 1000 gas the `CREATE` cannot pay its charge and halts out of gas. -/
example :
    step (machine fakeCrypto ccode false 3 [0, 0, 0] 1000) =
      finishFrame (machine fakeCrypto ccode false 3 [0, 0, 0] 1000) (.halt .outOfGas) :=
  step_create_oog (b := false) (salt := 0) rfl rfl (by decide)

/-- In a static frame the `CREATE` halts with `writeInStaticContext`. -/
example :
    step (machine fakeCrypto ccode true 3 [0, 0, 0]) =
      finishFrame (machine fakeCrypto ccode true 3 [0, 0, 0]) (.halt .writeInStaticContext) :=
  step_create_static (b := false) (salt := 0) rfl rfl (by decide) (by decide) rfl

/-- Value `1` from an account with no ether: a soft failure, `0` pushed. -/
example :
    step (machine fakeCrypto ccode false 3 [1, 0, 0]) =
      .running (createSoftFail (machine fakeCrypto ccode false 3 [1, 0, 0]) false 0 0 []) :=
  step_create_soft (b := false) (salt := 0) rfl rfl (by decide) (by decide) (by decide) rfl
    (.inl (by decide))

/-- **The havoc rule fires**: with nothing protected, whatever the (empty) init code does, the
creator resumes at the `STOP` after the `CREATE`. -/
example :
    WP (machine fakeCrypto ccode false 3 [0, 0, 0]) (fun m => m.frame.pc = 4) (fun _ _ => False) :=
  Reentrancy.WP.create_havoc Reentrancy.goodOk_none (G := 100000)
    (fun _ hd => hd.danger.1.elim) rfl rfl (by decide) (by decide) rfl (Nat.zero_le _)
    (by decide) (by decide) (by decide +kernel) rfl trivial (by decide)
    (fun _ _ hs _ => WP.ret (resumeAfter_create_stack (hs.kind.trans rfl)).1)

/-- **The any-outcome havoc rule fires** with no gas, balance or freshness side condition: the
creator resumes after the `CREATE`, or the frame ends. -/
example (crypto : Crypto) (g : Nat) :
    WP (machine crypto ccode false 3 [0, 0, 0] g) (fun m => m.frame.pc = 4) (fun _ _ => True) :=
  Reentrancy.WP.create_havoc_any (b := false) (salt := 0) Reentrancy.goodOk_none
    (fun _ hd => hd.danger.1.elim) rfl rfl (by decide) rfl trivial (fun _ => trivial)
    (fun _ _ hpc _ _ => WP.ret hpc)

/-! ## `SELFDESTRUCT` -/

/-- `SELFDESTRUCT` to `0xBEEF`: the frame ends successfully; the account, not created in this
transaction, keeps its code and storage (only its balance moves). -/
example :
    step (machine fakeCrypto ⟨#[0xff]⟩ false 0 [0xBEEF]) =
      finishFrame (selfdestructMachine (machine fakeCrypto ⟨#[0xff]⟩ false 0 [0xBEEF])
        (Word.toAddress 0xBEEF) []) (.success .empty) :=
  step_selfdestruct rfl rfl rfl (by decide)

example :
    selfdestructWorld (machine fakeCrypto ⟨#[0xff]⟩ false 0 [0xBEEF]) (Word.toAddress 0xBEEF) =
      moveEther (machine fakeCrypto ⟨#[0xff]⟩ false 0 [0xBEEF]).world contract
        (Word.toAddress 0xBEEF) 0 :=
  (selfdestructWorld_of_not_created _ _ (by decide)).trans (by decide)

/-! ## `CALLCODE` -/

/-- `CALLCODE` of the code at `0xBEEF` with 50000 gas, no value. -/
example :
    step (machine fakeCrypto ⟨#[0xf2]⟩ false 0 [50000, 0xBEEF, 0, 0, 0, 0, 0]) =
      .running (callcodeChild (machine fakeCrypto ⟨#[0xf2]⟩ false 0 [50000, 0xBEEF, 0, 0, 0, 0, 0])
        50000 0xBEEF 0 0 0 0 0 []) :=
  step_callcode rfl rfl (.inl (by decide)) (by decide) (Nat.zero_le _) (by decide) (by decide)

end EvmTest.OpcodeRules
