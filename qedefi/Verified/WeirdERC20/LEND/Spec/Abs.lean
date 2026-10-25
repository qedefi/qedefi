import QEDefi.ERC20.Spec.Storage
import QEDefi.ERC20.Spec.Instances.LEND
import Verified.WeirdERC20.LEND.Contracts.LEND

/-!
# LEND: the bytecode spec statement

The data `ERC20Spec` is applied to for LEND (`contracts/mainnet/LEND/`): the storage abstraction
`abs` (layout from `storageLayout.json`, checked against mainnet in `layout-check.txt`), the
dispatcher's selectors `sel`, the decoder `ops` of the sale and administration entry points,
the gas bound `g₀`, and `lendSpec`, the statement the bytecode proofs target. The model is
`QEDefi.ERC20.Spec.LEND.model`.

Layout: `balances` 0, `allowed` 1, `supply` 2; slot 3 packs `currentState` (byte 0),
`enableTransfers` (byte 1) and `teamTokenBonus` (bytes 2–21); `escrow` 4 (never written, not
read: `FrameKeeps` pins it), `tokenManager` 5, `presaleSoldTokens` 6, `icoSoldTokens` 7,
`totalSoldTokens` 8.

`withdrawEther()` is not decoded: it sends the contract's ether to `escrow`, and `OpSpec`'s
`FrameKeeps` allows no change to the token's ether or to another account. Its obligation (and
the constant getters', which change nothing) is left to `MalformedSpec`-style statements.
-/

namespace Verified.WeirdERC20.LEND.Spec
open EvmLean EvmLogic EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec

/-- The slot of `balances`. -/
def balancesSlot : Word := 0
/-- The slot of `allowed`. -/
def allowedSlot : Word := 1
/-- The slot of `supply`. -/
def supplySlot : Word := 2
/-- The slot packing `currentState`, `enableTransfers` and `teamTokenBonus`. -/
def stateSlot : Word := 3
/-- The slot of `tokenManager`. -/
def managerSlot : Word := 5
/-- The slot of `presaleSoldTokens`. -/
def presaleSlot : Word := 6
/-- The slot of `icoSoldTokens`. -/
def icoSlot : Word := 7
/-- The slot of `totalSoldTokens`. -/
def totalSoldSlot : Word := 8

/-- LEND as the actors `Act` see it. Packed fields are read as solc 0.4.16 reads them: the
enum as byte 0, the `bool` as byte 1 being nonzero, the address as the 20 bytes from byte 2. -/
noncomputable def read (crypto : Crypto) (Act : Finset Address) (w : World) (token : Address) :
    LEND.State Address where
  bal := readMap crypto Act w token balancesSlot
  supply := readSlot w token supplySlot
  allowance := readMap2 crypto Act w token allowedSlot
  phase := (w.sload token stateSlot).toNat % 256
  enabled := decide ((w.sload token stateSlot >>> 8).toNat % 256 ≠ 0)
  team := Word.toAddress (w.sload token stateSlot >>> 16)
  manager := Word.toAddress (w.sload token managerSlot)
  presaleSold := readSlot w token presaleSlot
  icoSold := readSlot w token icoSlot
  totalSold := readSlot w token totalSoldSlot

/-- The slots `read` depends on. -/
def footprint (crypto : Crypto) (Act : Finset Address) (k : Word) : Prop :=
  k ∈ [supplySlot, stateSlot, managerSlot, presaleSlot, icoSlot, totalSoldSlot] ∨
    MapSlots crypto Act balancesSlot k ∨ Map2Slots crypto Act allowedSlot k

/-- **LEND's storage abstraction.** `Sound`: the actors' rows of `balances` and `allowed` are
pairwise distinct and none is a declared slot (`0 … 8`). -/
noncomputable def abs : TokenAbs (LEND.State Address) where
  read := read
  footprint := footprint
  read_congr := by
    intro crypto Act w w' token h _
    have hs : ∀ k ∈ [supplySlot, stateSlot, managerSlot, presaleSlot, icoSlot, totalSoldSlot],
        w'.sload token k = w.sload token k := fun k hk => h k (Or.inl hk)
    simp only [read]
    rw [readMap_congr (fun k hk => h k (Or.inr (Or.inl hk))),
      readMap2_congr (fun k hk => h k (Or.inr (Or.inr hk))), readSlot, readSlot, readSlot,
      readSlot, readSlot, readSlot, readSlot, readSlot, hs supplySlot (by simp),
      hs stateSlot (by simp), hs managerSlot (by simp), hs presaleSlot (by simp),
      hs icoSlot (by simp), hs totalSoldSlot (by simp)]
  Sound crypto Act :=
    ActorRows crypto Act [balancesSlot] [allowedSlot] [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- The dispatcher's selectors (the verified ABI). -/
def sel : List Nat := Contracts.LEND.selectors.map (·.2.toNat)

/-- The `i`-th static argument word of the calldata. -/
def argWord (data : ByteArray) (i : ℕ) : Word := Bytes.toWord (Interpreter.readBytes data (4 + 32 * i) 32)

/-- **The other entry points**, ABI-encoded with clean arguments: `buyTokens()`,
`buyTokensPresale()`, `buyTokensICO()` (payable, with the frame's value), `setState(uint8)`
(a word below `256`) and `setTokenManager(address)` (upper 96 bits clear), both without value. -/
def ops (caller : Address) (data : ByteArray) (value : ℕ) : Option (LEND.Op Address) :=
  if data.size < 4 then none
  else if Abi.selectorOf data = 0xd0febe4c then some (.buyTokens caller value)
  else if Abi.selectorOf data = 0x1d511879 then some (.buyTokensPresale caller value)
  else if Abi.selectorOf data = 0xd7b91bcc then some (.buyTokensICO caller value)
  else if value ≠ 0 ∨ data.size < 4 + 32 then none
  else if Abi.selectorOf data = 0x56de96db ∧ (argWord data 0).toNat < 256 then
    some (.setState caller (argWord data 0).toNat)
  else if Abi.selectorOf data = 0x7cb2b79c ∧
      Word.ofAddress (Word.toAddress (argWord data 0)) = argWord data 0 then
    some (.setTokenManager caller (Word.toAddress (argWord data 0)))
  else none

/-- No operation touches an account's rows other than its caller's. -/
def opAddrs : LEND.Op Address → List Address := fun _ => []

/-- The gas from which every outcome is exact: a `transferFrom` writes three rows (at most
`3 · 22100` gas) and one log; a purchase writes five slots (balance, supply and the sold
counters, at most `5 · 22100`) and one log. `150000` covers both with room for the dispatcher. -/
def g₀ : Nat := 150000

/-- **The bytecode spec of LEND**: the deployed runtime code is the LEND model through `abs`
(in the final sale state, `wf`). -/
abbrev lendSpec : Prop :=
  ERC20Spec Contracts.LEND.runtimeCode abs
    (QEDefi.ERC20.Spec.LEND.model : TokenModel (LEND.State Address) Address (LEND.Op Address))
    g₀ sel ops opAddrs

end Verified.WeirdERC20.LEND.Spec
