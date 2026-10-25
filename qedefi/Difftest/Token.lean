import Difftest.Session
import Verified.OpenZeppelin.Contracts.OzAsset
import Verified.Solady.Contracts.SoladyToken
import Verified.WETH9.Contracts.WETH9
import Verified.WeirdERC20.USDT.Contracts.USDT
import Verified.WeirdERC20.BNB.Contracts.BNB
import Verified.WeirdERC20.STA.Contracts.STA
import Verified.WeirdERC20.AMPL.Contracts.AMPL
import Verified.WeirdERC20.AMPL.Contracts.AMPLProxy
import Verified.WeirdERC20.GUSD.Contracts.GUSD
import Verified.WeirdERC20.GUSD.Contracts.GUSDImpl
import Verified.WeirdERC20.GUSD.Contracts.GUSDStore
import Verified.WeirdERC20.YAMV2.Contracts.YAMV2
import Verified.WeirdERC20.LEND.Contracts.LEND
import Verified.WeirdERC20.ZRX.Contracts.ZRX

/-!
# Token families under test

A `TokenFamily` is one token contract, either deployed through its creation code (compiled
targets) or installed as runtime code plus storage at its address (mainnet targets: the code
read from mainnet, the storage its constructor would leave, `genesisStorage`). The
generator draws from the token's whole ABI with weights, sizes amounts against the current
balances, allowances and ether, sends ether to payable functions (and sometimes to
non-payable ones) and to the fallback, and adds malformed calldata. A token may consist of
several contracts (GUSD: proxy, implementation, store), each called directly as well, and
keep its ledger in another account than the token address. In edge mode (`--edge`) the
generator favours extreme amounts, self-transfers and address arguments with dirty upper
bits.
-/

namespace Difftest

open EvmLean EvmLogic EvmLogic.Solidity Examples.Deployment Conformance

/-- A token under test. -/
structure TokenFamily where
  /-- Name used in reports and on the command line. -/
  name : String
  /-- Address of the token (canonical deployment, or mainnet address when installed). -/
  token : Address
  /-- `some init`: deploy `init` from `deployer` at nonce 0 (it must land at `token`);
  `none`: install `code` and `genesis` at `token`. -/
  init : Option ByteArray
  /-- Expected runtime code. -/
  code : ByteArray
  /-- Storage installed with the code (for `init = none`). -/
  genesis : List (Word × Word) := []
  /-- Function selectors. -/
  selectors : List (String × UInt32)
  /-- Storage slot of `balanceOf(a)`. -/
  balanceSlot : Address → Word
  /-- Storage slot of `allowance(owner, spender)`. -/
  allowanceSlot : Address → Address → Word
  /-- Storage slot of the total supply, if it is stored. -/
  supplySlot : Option Word
  /-- Relative weight of each signature (default 1). -/
  weights : List (String × Nat) := []
  /-- Signatures that accept ether. -/
  payable : List String := []
  /-- Whether the fallback accepts ether (plain transfers are generated). -/
  receivesEther : Bool := false
  /-- Ether given to every actor at setup (wei); if positive, ether balances are compared. -/
  etherFunding : Nat := 0
  /-- Addresses besides the actors that matter to the token (e.g. Permit2); also senders. -/
  extraAddresses : Array Address := #[]
  /-- A fixed scenario run before the random sequences. -/
  scenario : Array Call := #[]
  /-- Further accounts installed with code (e.g. the implementation behind a proxy). -/
  extraCode : List (Address × ByteArray) := []
  /-- `balanceOf(a)` computed from storage, when it is not the word at `balanceSlot a`
  (rebasing tokens: gons / gons-per-fragment). -/
  balanceView : Option (World → Address → Word) := none
  /-- Getters checked on the installed or deployed state: signature, address arguments and
  the expected 32-byte result (validates `genesis` against the hand-derived layout,
  including packed fields). -/
  getters : List (String × List Address × Word) := []
  /-- Storage of the accounts of `extraCode`. -/
  extraGenesis : List (Address × List (Word × Word)) := []
  /-- The account holding balances, allowances and supply, if not the token itself (GUSD's
  store). -/
  ledger : Option Address := none
  /-- Further contracts of the token called directly: address, name, selectors. -/
  others : List (Address × String × List (String × UInt32)) := []
  /-- Percentage of ABI calls that go to `others` instead of the token. -/
  othersPct : Nat := 0
  /-- Values for `uint8` arguments (signature `v`, enums). -/
  uint8Values : Array Nat := #[0, 1, 27, 28, 255]
  /-- Edge mode: more extreme amounts, self-transfers, dirty address arguments. -/
  edge : Bool := false
  /-- The token returns lock ids from request functions and takes them in `confirm*`
  functions (GUSD): reuse hash-like return values and send confirmations from alice. -/
  lockIds : Bool := false

/-- The account holding the token's ledger. -/
def TokenFamily.ledgerAddr (f : TokenFamily) : Address := f.ledger.getD f.token

/-- A human-readable name for an address. -/
def tokenAddrName (f : TokenFamily) (a : Address) : String :=
  if a = f.token then "token" else if a = 0 then "zero"
  else if a = 0x000000000022D473030F116dDEE9F6B43aC78BA3 then "permit2"
  else if a = 0xAD then "admin"
  else match actors.idxOf? a, f.others.find? (·.1 == a) with
    | some i, _ => #["alice", "bob", "carol", "dave"][i]?.getD "?"
    | none, some (_, n, _) => n
    | none, none => hexOfAddress a

/-- A call of `sig` (selector from `table`) on the token's contract `to` named `toName`. -/
def tokenCallAt (f : TokenFamily) (to : Address) (toName : String) (table : List (String × UInt32))
    (sender : Address) (sig : String) (args : List (AbiArg × String)) (value : Nat := 0) : Call :=
  let sel := (selector? table sig).getD 0
  let v := if value = 0 then "" else s!" value {value}"
  let target := if to = f.token then f.name else s!"{f.name}.{toName}"
  { sender, to, data := abiCalldata sel (args.map (·.1)), value
    kind := s!"{target}.{fnName sig}"
    desc := s!"{tokenAddrName f sender} → {target}.{fnName sig}(" ++
      ", ".intercalate (args.map (·.2)) ++ ")" ++ v }

/-- A call of `sig` on the token with the given arguments and value. -/
def tokenCall (f : TokenFamily) (sender : Address) (sig : String) (args : List (Word × String))
    (value : Nat := 0) : Call :=
  tokenCallAt f f.token f.name f.selectors sender sig (args.map fun (w, d) => (.word w, d)) value

/-- `balanceOf(a)` in the evm-lean world. -/
def TokenFamily.balance (f : TokenFamily) (w : World) (a : Address) : Nat :=
  match f.balanceView with
  | some v => (v w a).toNat
  | none => (w.sload f.ledgerAddr (f.balanceSlot a)).toNat

/-- Values worth hitting: balances, allowances among actors, total supply, ether. -/
def TokenFamily.stateValues (f : TokenFamily) (w : World) : Array Word :=
  let who := actors ++ f.extraAddresses ++ #[f.token]
  let bal := who.map fun a => w.sload f.ledgerAddr (f.balanceSlot a)
  let alw := actors.flatMap fun o => actors.map fun s => w.sload f.ledgerAddr (f.allowanceSlot o s)
  let sup := match f.supplySlot with
    | some k => #[w.sload f.ledgerAddr k]
    | none => #[]
  bal ++ alw ++ sup ++ (actors.map fun a => w.balance a) ++ #[w.balance f.token]

/-- Functions whose first address argument is the account debited. -/
def debitsFirstArg (name : String) : Bool :=
  name ∈ ["transferFrom", "burn", "burnFrom", "redeem", "destroyBlackFunds", "transferByLegacy",
    "transferWithSender", "setBalance"]

/-- An amount bounded by `ether`, likely close to it. -/
def etherAmount (ether : Nat) : Gen Nat := do
  let v := (← plausible ether).toNat
  return min v ether

/-- The next call on the token, or (with probability `othersPct` %) on another of its
contracts. -/
def genTokenCall (f : TokenFamily) (w : World) (recent : Array Word) : Gen Call := do
  let state := f.stateValues w
  let everyone := actors ++ f.extraAddresses
  let sender ← if !f.extraAddresses.isEmpty && (← below 10) = 0 then pick f.extraAddresses
    else pick actors
  let ether := (w.balance sender).toNat
  let genAddr : Gen Address := do
    let r ← below 100
    if f.edge && r < 10 then return sender
    if r < 85 then pick everyone else if r < 92 then return 0 else return f.token
  let r ← below 100
  if r < 3 then
    -- Malformed calldata.
    let (_, sel) ← pick f.selectors.toArray
    let full := calldata sel [← randWord, ← randWord, ← randWord]
    let data ← match ← below 4 with
      | 0 => pure ByteArray.empty
      | 1 => pure (full.extract 0 (← below 4))
      | 2 => pure (calldata (← next64).toUInt32 [])
      | _ => pure (full.extract 0 (4 + (← below 64)))
    return { sender, to := f.token, data, kind := s!"{f.name}.junk"
             desc := s!"{tokenAddrName f sender} → {f.name} junk {hexOfBytes data}" }
  if f.receivesEther && r < 10 then
    -- A plain ether transfer, or ether with an unknown selector (fallback).
    let value ← etherAmount ether
    let data ← if (← below 3) = 0 then pure (calldata (← next64).toUInt32 []) else pure .empty
    return { sender, to := f.token, data, value, kind := s!"{f.name}.fallback"
             desc := s!"{tokenAddrName f sender} → {f.name} fallback {hexOfBytes data} value {value}" }
  -- The target contract, then a function from its ABI, by weight.
  let (to, toName, sigs) ← if !f.others.isEmpty && (← below 100) < f.othersPct then
      pick f.others.toArray
    else pure (f.token, f.name, f.selectors)
  let table := sigs.map fun (sig, _) => (sig, (f.weights.lookup sig).getD 1)
  let total := table.foldl (fun n (_, k) => n + k) 0
  let mut x ← below total
  let mut sig := (table.headD ("", 0)).1
  for (s, k) in table do
    if x < k then sig := s; break
    x := x - k
  -- Lock ids: confirmations mostly from the custodian (alice), with hash-like recent words
  -- (ids returned by request functions) as `bytes32` arguments.
  let hashes := if f.lockIds then recent.filter (·.toNat ≥ 2 ^ 200) else #[]
  let sender ← if f.lockIds && (fnName sig).startsWith "confirm" then do
      if (← below 10) < 7 then pure (actors[0]?.getD 0) else pure sender
    else pure sender
  let mut args : List (AbiArg × String) := []
  let mut debit := sender
  let mut first := true
  let arrLen ← below 4
  let amount (debit : Address) : Gen Word := do
    if f.edge && (← below 100) < 15 then
      let b := f.balance w debit
      pick #[0, 1, BitVec.allOnes 256, BitVec.allOnes 256 - 1, BitVec.ofNat 256 (2 ^ 255),
             BitVec.ofNat 256 b, BitVec.ofNat 256 (b + 1)]
    else if (← below 2) = 0 then plausible (f.balance w debit) else genAmount state recent
  for ty in paramTypes sig do
    match ty with
    | "address" =>
      let a ← genAddr
      if first && debitsFirstArg (fnName sig) then debit := a
      first := false
      let word ← if f.edge && (← below 100) < 3 then
          pure (((← randWord) <<< 160) ||| Word.ofAddress a) else pure (Word.ofAddress a)
      let name := if word = Word.ofAddress a then tokenAddrName f a else s!"dirty {hexOfWord word}"
      args := args ++ [(.word word, name)]
    | "uint8" =>
      let v := BitVec.ofNat 256 (← pick f.uint8Values); args := args ++ [(.word v, toString v.toNat)]
    | "bytes32" =>
      let v ← if f.lockIds then do
          let r ← below 10
          if !hashes.isEmpty && r < 6 then pick hashes
          else if !recent.isEmpty && r < 8 then pick recent else randWord
        else if !recent.isEmpty && (← below 2) = 0 then pick recent else randWord
      args := args ++ [(.word v, hexOfWord v)]
    | "address[]" | "uint256[]" =>
      let n ← if (← below 10) = 0 then below 4 else pure arrLen
      let mut ws : List Word := []
      let mut names : List String := []
      for _ in [0:n] do
        if ty = "address[]" then
          let a ← genAddr; ws := ws ++ [Word.ofAddress a]; names := names ++ [tokenAddrName f a]
        else
          let v ← amount sender; ws := ws ++ [v]; names := names ++ [toString v.toNat]
      args := args ++ [(.array ws, "[" ++ ", ".intercalate names ++ "]")]
    | _ =>
      let v ← amount debit
      args := args ++ [(.word v, toString v.toNat)]
  let value ← if sig ∈ f.payable then etherAmount ether
    else if (← below 100) < 3 then etherAmount (min ether 1000) else pure 0
  return tokenCallAt f to toName sigs sender sig args value

/-- Check the storage layout against the token's own views, in evm-lean on world `w`:
`balanceOf(a)` equals the word at `balanceSlot a`, `allowance(o, s)` the word at
`allowanceSlot o s`, `totalSupply()` the word at `supplySlot` (or the token's ether balance if
the supply is not stored). The differences, if any. -/
def layoutCheck (f : TokenFamily) (w : World) : List String := Id.run do
  let view (sig : String) (args : List Address) : Option Word :=
    let sel := (selector? f.selectors sig).getD 0
    match execTx Crypto.real { gasLimit := 30_000_000 } w (actors[0]?.getD 0) (some f.token)
        (calldata sel (args.map Word.ofAddress)) gasLimit with
    | .ok (o, _) => if o.success && o.output.size = 32 then some (Bytes.toWord o.output) else none
    | .error _ => none
  let who := (actors ++ f.extraAddresses).toList
  let mut out := []
  for a in who do
    let v := view "balanceOf(address)" [a]
    let expected := match f.balanceView with
      | some bv => bv w a
      | none => w.sload f.ledgerAddr (f.balanceSlot a)
    if v != some expected then
      out := out ++ [s!"balanceOf({tokenAddrName f a}) = {v.map (·.toNat)} ≠ balance slot"]
  for o in who do
    for sp in actors.toList do
      let v := view "allowance(address,address)" [o, sp]
      if v != some (w.sload f.ledgerAddr (f.allowanceSlot o sp)) then
        out := out ++ [s!"allowance({tokenAddrName f o}, {tokenAddrName f sp}) = " ++
          s!"{v.map (·.toNat)} ≠ allowance slot"]
  let sup := match f.supplySlot with
    | some k => w.sload f.ledgerAddr k
    | none => w.balance f.token
  if view "totalSupply()" [] != some sup then out := out ++ ["totalSupply() ≠ supply slot"]
  return out

/-- The getters of `f.getters` that do not return the expected word on world `w`. -/
def getterCheck (f : TokenFamily) (w : World) : List String :=
  f.getters.filterMap fun (sig, args, expected) =>
    let sel := (selector? f.selectors sig).getD 0
    let got : Option Word :=
      match execTx Crypto.real { gasLimit := 30_000_000 } w (actors[0]?.getD 0)
          (some f.token) (calldata sel (args.map Word.ofAddress)) gasLimit with
      | .ok (o, _) => if o.success && o.output.size = 32 then some (Bytes.toWord o.output) else none
      | .error _ => none
    if got == some expected then none
    else some s!"{sig} = {got.map hexOfWord}, expected {hexOfWord expected}"

/-- Mint to two actors, approve, transfer and spend an allowance: a state in which every
storage-layout row the views read is exercised. -/
def erc20Scenario (f : TokenFamily) : Array Call :=
  let a := actors[0]?.getD 0
  let b := actors[1]?.getD 0
  let c := actors[2]?.getD 0
  let d := actors[3]?.getD 0
  let addr (x : Address) : Word × String := (Word.ofAddress x, tokenAddrName f x)
  let num (n : Nat) : Word × String := (BitVec.ofNat 256 n, toString n)
  #[tokenCall f a "mint(address,uint256)" [addr a, num (10 ^ 20)],
    tokenCall f a "mint(address,uint256)" [addr b, num 5],
    tokenCall f a "approve(address,uint256)" [addr b, num 77],
    tokenCall f c "approve(address,uint256)" [addr d, num (2 ^ 256 - 1)],
    tokenCall f a "transfer(address,uint256)" [addr c, num 3],
    tokenCall f b "transferFrom(address,address,uint256)" [addr a, addr d, num 7],
    tokenCall f b "transferFrom(address,address,uint256)" [addr a, addr d, num 71],
    tokenCall f d "transferFrom(address,address,uint256)" [addr c, addr a, num 3],
    tokenCall f a "burn(address,uint256)" [addr b, num 5]]

/-! ## Families -/

/-- `keccak(m[k])` slot of a Solidity mapping at `slot`. -/
def solSlot (slot : Nat) (a : Address) : Word := mappingSlot (Word.ofAddress a) (BitVec.ofNat 256 slot)

/-- Nested Solidity mapping slot `m[o][s]`. -/
def solSlot2 (slot : Nat) (o s : Address) : Word :=
  mappingSlot (Word.ofAddress s) (solSlot slot o)

/-- OpenZeppelin `ERC20Mock` on its own. -/
def oz20 : TokenFamily :=
  let f : TokenFamily :=
    { name := "oz20"
      token := Verified.OpenZeppelin.Contracts.OzAsset.address
      init := some (Verified.OpenZeppelin.Contracts.OzAsset.creationCode ++
        Verified.OpenZeppelin.Contracts.OzAsset.constructorArgs)
      code := Verified.OpenZeppelin.Contracts.OzAsset.runtimeCode
      selectors := Verified.OpenZeppelin.Contracts.OzAsset.selectors
      balanceSlot := solSlot 0
      allowanceSlot := solSlot2 1
      supplySlot := some 2
      weights := [("mint(address,uint256)", 4), ("burn(address,uint256)", 3),
        ("transfer(address,uint256)", 6), ("transferFrom(address,address,uint256)", 6),
        ("approve(address,uint256)", 5)] }
  { f with scenario := erc20Scenario f }

/-- Solady's balance slot: `keccak256(owner ‖ 0⁸ ‖ 0x87a211a2)` (32 bytes). -/
def soladyBalanceSlot (a : Address) : Word :=
  Crypto.real.keccak256 (Bytes.ofAddress a ++ Bytes.ofNatBE 12 0x87a211a2)

/-- Solady's allowance slot: `keccak256(owner ‖ 0⁸ ‖ 0x7f5e9f20 ‖ spender)` (52 bytes). -/
def soladyAllowanceSlot (o s : Address) : Word :=
  Crypto.real.keccak256 (Bytes.ofAddress o ++ Bytes.ofNatBE 12 0x7f5e9f20 ++ Bytes.ofAddress s)

/-- Solady `ERC20` (`SoladyToken`), with Permit2 as an extra address and sender. -/
def solady : TokenFamily :=
  let f : TokenFamily :=
    { name := "solady"
      token := Verified.Solady.Contracts.SoladyToken.address
      init := some Verified.Solady.Contracts.SoladyToken.creationCode
      code := Verified.Solady.Contracts.SoladyToken.runtimeCode
      selectors := Verified.Solady.Contracts.SoladyToken.selectors
      balanceSlot := soladyBalanceSlot
      allowanceSlot := soladyAllowanceSlot
      supplySlot := some 0x05345cdf77eb68f44c
      weights := [("mint(address,uint256)", 4), ("burn(address,uint256)", 3),
        ("transfer(address,uint256)", 6), ("transferFrom(address,address,uint256)", 6),
        ("approve(address,uint256)", 5),
        ("permit(address,address,uint256,uint256,uint8,bytes32,bytes32)", 2)]
      extraAddresses := #[0x000000000022D473030F116dDEE9F6B43aC78BA3] }
  { f with scenario := erc20Scenario f }

/-- The WETH9 deposit/transfer/withdraw round trip. -/
def wethScenario (f : TokenFamily) : Array Call :=
  let alice := actors[0]?.getD 0
  let bob := actors[1]?.getD 0
  let addr (x : Address) : Word × String := (Word.ofAddress x, tokenAddrName f x)
  let num (n : Nat) : Word × String := (BitVec.ofNat 256 n, toString n)
  let e18 := 10 ^ 18
  #[tokenCall f alice "deposit()" [] e18,
    { sender := bob, to := f.token, data := .empty, value := 2 * e18, kind := "weth9.fallback"
      desc := s!"bob → weth9 fallback value {2 * e18}" },
    tokenCall f alice "transfer(address,uint256)" [addr bob, num (e18 / 4)],
    tokenCall f bob "approve(address,uint256)" [addr alice, num (2 ^ 256 - 1)],
    tokenCall f alice "transferFrom(address,address,uint256)" [addr bob, addr alice, num e18],
    tokenCall f alice "totalSupply()" [],
    tokenCall f alice "withdraw(uint256)" [num (e18 + 3 * e18 / 4 + 1)],
    tokenCall f alice "withdraw(uint256)" [num (e18 + 3 * e18 / 4)],
    tokenCall f bob "withdraw(uint256)" [num (e18 / 2)],
    tokenCall f bob "totalSupply()" []]

/-- Mainnet WETH9: deposits and withdrawals with ether, ether balances compared. -/
def weth9 : TokenFamily :=
  let f : TokenFamily :=
    { name := "weth9"
      token := Verified.WETH9.Contracts.WETH9.address
      init := none
      code := Verified.WETH9.Contracts.WETH9.runtimeCode
      genesis := Verified.WETH9.Contracts.WETH9.genesisStorage
      selectors := Verified.WETH9.Contracts.WETH9.selectors
      balanceSlot := solSlot 3
      allowanceSlot := solSlot2 4
      supplySlot := none
      weights := [("deposit()", 6), ("withdraw(uint256)", 6), ("transfer(address,uint256)", 5),
        ("transferFrom(address,address,uint256)", 5), ("approve(address,uint256)", 4)]
      payable := ["deposit()"]
      receivesEther := true
      etherFunding := 1000 * 10 ^ 18
      getters := [("decimals()", [], 18), ("totalSupply()", [], 0)] }
  { f with scenario := wethScenario f }

/-! ### Weird ERC-20s (mainnet bytecode) -/

/-- Replace or add storage entries of a genesis state. -/
def withStorage (g : List (Word × Word)) (upd : List (Word × Word)) : List (Word × Word) :=
  g.filter (fun (k, _) => !upd.any (·.1 == k)) ++ upd

/-- A call with raw calldata. -/
def rawCall (f : TokenFamily) (sender : Address) (data : ByteArray) (desc : String)
    (value : Nat := 0) : Call :=
  { sender, to := f.token, data, value, kind := s!"{f.name}.raw",
    desc := s!"{tokenAddrName f sender} → {f.name} {desc}" }

/-- The first actor (owner and admin roles in the installed states). -/
def alice : Address := actors[0]?.getD 0
/-- The second actor. -/
def bob : Address := actors[1]?.getD 0
/-- The third actor. -/
def carol : Address := actors[2]?.getD 0
/-- The fourth actor. -/
def dave : Address := actors[3]?.getD 0

/-- An address argument. -/
def aArg (f : TokenFamily) (x : Address) : Word × String := (Word.ofAddress x, tokenAddrName f x)

/-- A number argument. -/
def nArg (n : Nat) : Word × String := (BitVec.ofNat 256 n, toString n)

/-- USDT's quirks: no return values, the approve race guard, the fee switch, pause,
blacklist and `destroyBlackFunds`, issue/redeem, the short-payload check, `INVALID` on an
insufficient balance. -/
def usdtScenario (f : TokenFamily) : Array Call :=
  let t (sender : Address) (sig : String) (args : List (Word × String)) := tokenCall f sender sig args
  #[t alice "transfer(address,uint256)" [aArg f bob, nArg (10 ^ 6)],
    t bob "approve(address,uint256)" [aArg f carol, nArg 5],
    t bob "approve(address,uint256)" [aArg f carol, nArg 0],
    t bob "approve(address,uint256)" [aArg f carol, nArg 5],
    t carol "transferFrom(address,address,uint256)" [aArg f bob, aArg f dave, nArg 5],
    t dave "transferFrom(address,address,uint256)" [aArg f alice, aArg f carol, nArg 7],
    t alice "setParams(uint256,uint256)" [nArg 10, nArg 5],
    t bob "transfer(address,uint256)" [aArg f carol, nArg (10 ^ 9)],
    t bob "transfer(address,uint256)" [aArg f carol, nArg (10 ^ 10)],
    t alice "pause()" [],
    t bob "transfer(address,uint256)" [aArg f carol, nArg 1],
    t bob "approve(address,uint256)" [aArg f dave, nArg 1],
    t alice "unpause()" [],
    t alice "addBlackList(address)" [aArg f dave],
    t dave "transfer(address,uint256)" [aArg f carol, nArg 1],
    t alice "transfer(address,uint256)" [aArg f dave, nArg 2],
    t alice "destroyBlackFunds(address)" [aArg f dave],
    t alice "issue(uint256)" [nArg (10 ^ 6)],
    t alice "issue(uint256)" [nArg 0],
    t alice "redeem(uint256)" [nArg (5 * 10 ^ 5)],
    t bob "redeem(uint256)" [nArg 1],
    rawCall f bob ((t bob "transfer(address,uint256)" [aArg f carol, nArg 1]).data.extract 0 36)
      "transfer with a 36-byte payload",
    t carol "transfer(address,uint256)" [aArg f bob, nArg (10 ^ 15)]]

/-- Mainnet USDT (`TetherToken`), fee off. -/
def usdt : TokenFamily :=
  let f : TokenFamily :=
    { name := "usdt"
      token := Verified.WeirdERC20.USDT.Contracts.USDT.address
      init := none
      code := Verified.WeirdERC20.USDT.Contracts.USDT.runtimeCode
      genesis := Verified.WeirdERC20.USDT.Contracts.USDT.genesisStorage
      selectors := Verified.WeirdERC20.USDT.Contracts.USDT.selectors
      balanceSlot := solSlot 2
      allowanceSlot := solSlot2 5
      supplySlot := some 1
      weights := [("transfer(address,uint256)", 8), ("transferFrom(address,address,uint256)", 8),
        ("approve(address,uint256)", 6), ("issue(uint256)", 2), ("redeem(uint256)", 2),
        ("setParams(uint256,uint256)", 3), ("unpause()", 2), ("removeBlackList(address)", 2),
        ("deprecate(address)", 1)]
      getters := [("owner()", [], Word.ofAddress alice), ("paused()", [], 0), ("deprecated()", [], 0),
        ("upgradedAddress()", [], 0), ("decimals()", [], 6), ("basisPointsRate()", [], 0),
        ("maximumFee()", [], 0), ("isBlackListed(address)", [dave], 0),
        ("allowance(address,address)", [alice, dave], BitVec.allOnes 256)] }
  { f with scenario := usdtScenario f }

/-- USDT with the fee switched on (0.1 %, at most 5 USDT), in the genesis state. -/
def usdtFee : TokenFamily :=
  { usdt with name := "usdtfee"
              genesis := withStorage usdt.genesis [(3, 10), (4, BitVec.ofNat 256 (5 * 10 ^ 6))]
              getters := [("basisPointsRate()", [], 10), ("maximumFee()", [], BitVec.ofNat 256 (5 * 10 ^ 6))] }

/-- BNB's quirks: zero-value reverts, `transfer` without return value, no `Approval`, the
infinite allowance decremented, freeze/unfreeze, phantom functions through the payable
fallback, `withdrawEther`. -/
def bnbScenario (f : TokenFamily) : Array Call :=
  let t (sender : Address) (sig : String) (args : List (Word × String)) := tokenCall f sender sig args
  let e18 := 10 ^ 18
  #[t alice "transfer(address,uint256)" [aArg f bob, nArg 0],
    t alice "transfer(address,uint256)" [aArg f bob, nArg e18],
    t alice "transfer(address,uint256)" [aArg f 0, nArg 1],
    t bob "approve(address,uint256)" [aArg f carol, nArg 0],
    t bob "approve(address,uint256)" [aArg f carol, nArg 7],
    t dave "transferFrom(address,address,uint256)" [aArg f alice, aArg f carol, nArg e18],
    t bob "freeze(uint256)" [nArg (1000 * e18)],
    t bob "unfreeze(uint256)" [nArg (500 * e18)],
    t carol "burn(uint256)" [nArg e18],
    rawCall f dave (calldata 0xd505accf [Word.ofAddress dave, Word.ofAddress bob, 5])
      "permit(dave, bob, 5) (not a BNB function: phantom)" e18,
    rawCall f carol .empty "plain ether" (2 * e18),
    t alice "withdrawEther(uint256)" [nArg (e18 / 2)],
    t bob "withdrawEther(uint256)" [nArg 1]]

/-- Mainnet BNB (Ethereum ERC-20 legacy). -/
def bnb : TokenFamily :=
  let f : TokenFamily :=
    { name := "bnb"
      token := Verified.WeirdERC20.BNB.Contracts.BNB.address
      init := none
      code := Verified.WeirdERC20.BNB.Contracts.BNB.runtimeCode
      genesis := Verified.WeirdERC20.BNB.Contracts.BNB.genesisStorage
      selectors := Verified.WeirdERC20.BNB.Contracts.BNB.selectors
      balanceSlot := solSlot 5
      allowanceSlot := solSlot2 7
      supplySlot := some 3
      weights := [("transfer(address,uint256)", 8), ("transferFrom(address,address,uint256)", 8),
        ("approve(address,uint256)", 6), ("burn(uint256)", 2), ("freeze(uint256)", 3),
        ("unfreeze(uint256)", 3), ("withdrawEther(uint256)", 2)]
      getters := [("owner()", [], Word.ofAddress alice), ("decimals()", [], 18),
        ("freezeOf(address)", [bob], 0), ("allowance(address,address)", [alice, dave], BitVec.allOnes 256)]
      receivesEther := true
      etherFunding := 1000 * 10 ^ 18 }
  { f with scenario := bnbScenario f }

/-- STA's quirks: 1 % burned per transfer (rounded up), two `Transfer` events, the infinite
allowance decremented, `destroy`, `INVALID` on `downAllowance` underflow. -/
def staScenario (f : TokenFamily) : Array Call :=
  let t (sender : Address) (sig : String) (args : List (Word × String)) := tokenCall f sender sig args
  #[t alice "transfer(address,uint256)" [aArg f bob, nArg 1000],
    t alice "transfer(address,uint256)" [aArg f bob, nArg 1],
    t alice "transfer(address,uint256)" [aArg f bob, nArg 0],
    t alice "transfer(address,uint256)" [aArg f alice, nArg 100],
    t dave "transferFrom(address,address,uint256)" [aArg f alice, aArg f carol, nArg 100],
    t bob "destroy(uint256)" [nArg 7],
    t carol "upAllowance(address,uint256)" [aArg f dave, nArg 5],
    t carol "downAllowance(address,uint256)" [aArg f dave, nArg 6],
    t carol "destroyFrom(address,uint256)" [aArg f bob, nArg 1],
    t alice "approve(address,uint256)" [aArg f 0, nArg 1],
    t alice "cut(uint256)" [nArg (10 ^ 18 + 1)]]

/-- Mainnet STA (Statera), a fee-on-transfer (burn) token. -/
def sta : TokenFamily :=
  let f : TokenFamily :=
    { name := "sta"
      token := Verified.WeirdERC20.STA.Contracts.STA.address
      init := none
      code := Verified.WeirdERC20.STA.Contracts.STA.runtimeCode
      genesis := Verified.WeirdERC20.STA.Contracts.STA.genesisStorage
      selectors := Verified.WeirdERC20.STA.Contracts.STA.selectors
      balanceSlot := solSlot 3
      allowanceSlot := solSlot2 4
      supplySlot := some 5
      weights := [("transfer(address,uint256)", 8), ("transferFrom(address,address,uint256)", 8),
        ("approve(address,uint256)", 5), ("destroy(uint256)", 2), ("destroyFrom(address,uint256)", 2),
        ("upAllowance(address,uint256)", 2), ("downAllowance(address,uint256)", 2)]
      getters := [("basePercent()", [], 100), ("decimals()", [], 18)] }
  { f with scenario := staScenario f }

/-- AMPL's proxy admin in the tests (not an actor; also a sender). -/
def amplAdmin : Address := 0xAD

/-- AMPL's quirks: rebases (positive and negative) changing every balance without events,
`transferAll`, the infinite allowance decremented, saturating `decreaseAllowance`, the
recipient checks, the proxy admin locked out of the token and served by the proxy. -/
def amplScenario (f : TokenFamily) : Array Call :=
  let t (sender : Address) (sig : String) (args : List (Word × String)) := tokenCall f sender sig args
  #[t alice "transfer(address,uint256)" [aArg f bob, nArg (10 ^ 9)],
    t alice "rebase(uint256,int256)" [nArg 1, nArg (10 ^ 15)],
    t bob "transferAll(address)" [aArg f carol],
    t dave "transferFrom(address,address,uint256)" [aArg f alice, aArg f carol, nArg (10 ^ 9)],
    t carol "decreaseAllowance(address,uint256)" [aArg f bob, nArg (10 ^ 30)],
    t alice "rebase(uint256,int256)" [nArg 2, (BitVec.ofNat 256 (2 ^ 256 - 2 * 10 ^ 15), "-2e15")],
    t bob "rebase(uint256,int256)" [nArg 3, nArg 1],
    t alice "transfer(address,uint256)" [aArg f f.token, nArg 1],
    t alice "transfer(address,uint256)" [aArg f 0, nArg 1],
    t amplAdmin "transfer(address,uint256)" [aArg f bob, nArg 0],
    t amplAdmin "implementation()" [],
    t bob "implementation()" [],
    t alice "scaledBalanceOf(address)" [aArg f carol]]

/-- AMPL's `balanceOf`: gon balance divided by `_gonsPerFragment` (slot 157). -/
def amplBalance (w : World) (a : Address) : Word :=
  let gpf := w.sload Verified.WeirdERC20.AMPL.Contracts.AMPLProxy.address 157
  if gpf = 0 then 0
  else w.sload Verified.WeirdERC20.AMPL.Contracts.AMPLProxy.address (solSlot 158 a) / gpf

/-- Mainnet AMPL: the zos proxy at the token address delegating to the mainnet
`UFragments` implementation, with the token state in the proxy's storage. -/
def ampl : TokenFamily :=
  let f : TokenFamily :=
    { name := "ampl"
      token := Verified.WeirdERC20.AMPL.Contracts.AMPLProxy.address
      init := none
      code := Verified.WeirdERC20.AMPL.Contracts.AMPLProxy.runtimeCode
      genesis := Verified.WeirdERC20.AMPL.Contracts.AMPLProxy.genesisStorage
      extraCode := [(Verified.WeirdERC20.AMPL.Contracts.AMPL.address,
        Verified.WeirdERC20.AMPL.Contracts.AMPL.runtimeCode)]
      selectors := Verified.WeirdERC20.AMPL.Contracts.AMPL.selectors ++
        Verified.WeirdERC20.AMPL.Contracts.AMPLProxy.selectors
      balanceSlot := solSlot 158
      allowanceSlot := solSlot2 159
      supplySlot := some 156
      balanceView := some amplBalance
      weights := [("transfer(address,uint256)", 8), ("transferFrom(address,address,uint256)", 8),
        ("approve(address,uint256)", 5), ("rebase(uint256,int256)", 4), ("transferAll(address)", 2),
        ("transferAllFrom(address,address)", 2), ("increaseAllowance(address,uint256)", 2),
        ("decreaseAllowance(address,uint256)", 2), ("upgradeTo(address)", 1),
        ("upgradeToAndCall(address,bytes)", 0), ("initialize(string,string,uint8)", 0)]
      extraAddresses := #[amplAdmin]
      getters := [("owner()", [], Word.ofAddress alice), ("monetaryPolicy()", [], Word.ofAddress alice),
        ("decimals()", [], 9), ("totalSupply()", [], BitVec.ofNat 256 (5 * 10 ^ 16)),
        ("scaledTotalSupply()", [], BitVec.ofNat 256 (2 ^ 256 - 1 - (2 ^ 256 - 1) % (5 * 10 ^ 16))),
        ("isOwner()", [], 1)] }
  { f with scenario := amplScenario f }

/-! ### Further weird ERC-20s: low and high decimals, zero-value reverts, `false` returns -/

namespace GUSDAddrs
/-- GUSD's token address (`ERC20Proxy`). -/
def proxy : Address := Verified.WeirdERC20.GUSD.Contracts.GUSD.address
/-- GUSD's `ERC20Impl` (its immutables point to the proxy and the store). -/
def impl : Address := Verified.WeirdERC20.GUSD.Contracts.GUSDImpl.address
/-- GUSD's `ERC20Store` (balances, allowances, supply). -/
def store : Address := Verified.WeirdERC20.GUSD.Contracts.GUSDStore.address
end GUSDAddrs

/-- An address-array argument. -/
def addrsArg (f : TokenFamily) (xs : List Address) : AbiArg × String :=
  (.array (xs.map Word.ofAddress), "[" ++ ", ".intercalate (xs.map (tokenAddrName f)) ++ "]")

/-- A number-array argument. -/
def numsArg (xs : List Nat) : AbiArg × String :=
  (.array (xs.map (BitVec.ofNat 256)), "[" ++ ", ".intercalate (xs.map toString) ++ "]")

/-- A static argument as an `AbiArg`. -/
def wArg (a : Word × String) : AbiArg × String := (.word a.1, a.2)

/-- GUSD's quirks: the proxy forwarding by `CALL` to the implementation, which keeps the
ledger in the store and has the proxy emit the events; 2 decimals; increase/decrease of
allowances with overflow checks; transfers to `0` rejected; `batchTransfer` (self-transfers
skipped in the ledger); custodian-only `executePrint`/`burn(owner, v)`; `requestPrint` lock ids
from `BLOCKHASH(number − 1)`; the access control between the three contracts. -/
def gusdScenario (f : TokenFamily) : Array Call :=
  let t (sender : Address) (sig : String) (args : List (Word × String)) := tokenCall f sender sig args
  let impl := Verified.WeirdERC20.GUSD.Contracts.GUSDImpl.selectors
  let store := Verified.WeirdERC20.GUSD.Contracts.GUSDStore.selectors
  let i (sender : Address) (sig : String) (args : List (AbiArg × String)) :=
    tokenCallAt f GUSDAddrs.impl "impl" impl sender sig args
  #[t alice "transfer(address,uint256)" [aArg f bob, nArg 100],
    t alice "transfer(address,uint256)" [aArg f 0, nArg 1],
    t bob "approve(address,uint256)" [aArg f 0, nArg 5],
    t bob "increaseApproval(address,uint256)" [aArg f carol, nArg (2 ^ 256 - 1)],
    t bob "decreaseApproval(address,uint256)" [aArg f carol, nArg (10 ^ 5 + 1)],
    t carol "transferFrom(address,address,uint256)" [aArg f bob, aArg f dave, nArg (10 ^ 5)],
    t dave "transferFrom(address,address,uint256)" [aArg f alice, aArg f carol, nArg 50],
    i bob "batchTransfer(address[],uint256[])" [addrsArg f [carol, bob, dave], numsArg [1, 2, 3]],
    i bob "batchTransfer(address[],uint256[])" [addrsArg f [carol], numsArg [1, 2]],
    i carol "burn(uint256)" [wArg (nArg 10)],
    i alice "executePrint(address,uint256)" [wArg (aArg f dave), wArg (nArg 1000)],
    i bob "executePrint(address,uint256)" [wArg (aArg f dave), wArg (nArg 1000)],
    i carol "requestPrint(address,uint256)" [wArg (aArg f bob), wArg (nArg 7)],
    i alice "burn(address,uint256)" [wArg (aArg f bob), wArg (nArg 1)],
    i alice "transferWithSender(address,address,uint256)" [wArg (aArg f alice), wArg (aArg f bob), wArg (nArg 1)],
    tokenCallAt f GUSDAddrs.store "store" store alice "setBalance(address,uint256)"
      [wArg (aArg f alice), wArg (nArg 0)],
    t alice "emitTransfer(address,address,uint256)" [aArg f alice, aArg f bob, nArg 1],
    t carol "requestImplChange(address)" [aArg f bob],
    t alice "totalSupply()" []]

/-- Mainnet GUSD (Gemini dollar): `ERC20Proxy` at the token address, `ERC20Impl` and
`ERC20Store` at their mainnet addresses (the implementation's immutables name them), each
with its own storage; custodian alice everywhere. -/
def gusd : TokenFamily :=
  let f : TokenFamily :=
    { name := "gusd"
      token := GUSDAddrs.proxy
      init := none
      code := Verified.WeirdERC20.GUSD.Contracts.GUSD.runtimeCode
      genesis := Verified.WeirdERC20.GUSD.Contracts.GUSD.genesisStorage
      extraCode := [(GUSDAddrs.impl, Verified.WeirdERC20.GUSD.Contracts.GUSDImpl.runtimeCode),
        (GUSDAddrs.store, Verified.WeirdERC20.GUSD.Contracts.GUSDStore.runtimeCode)]
      extraGenesis := [(GUSDAddrs.impl, Verified.WeirdERC20.GUSD.Contracts.GUSDImpl.genesisStorage),
        (GUSDAddrs.store, Verified.WeirdERC20.GUSD.Contracts.GUSDStore.genesisStorage)]
      selectors := Verified.WeirdERC20.GUSD.Contracts.GUSD.selectors
      ledger := some GUSDAddrs.store
      balanceSlot := solSlot 6
      allowanceSlot := solSlot2 7
      supplySlot := some 5
      others := [(GUSDAddrs.impl, "impl", Verified.WeirdERC20.GUSD.Contracts.GUSDImpl.selectors),
        (GUSDAddrs.store, "store", Verified.WeirdERC20.GUSD.Contracts.GUSDStore.selectors)]
      othersPct := 30
      lockIds := true
      weights := [("transfer(address,uint256)", 8), ("transferFrom(address,address,uint256)", 8),
        ("approve(address,uint256)", 5), ("increaseApproval(address,uint256)", 3),
        ("decreaseApproval(address,uint256)", 3), ("batchTransfer(address[],uint256[])", 6),
        ("burn(uint256)", 3), ("burn(address,uint256)", 2), ("executePrint(address,uint256)", 3),
        ("requestPrint(address,uint256)", 4), ("confirmPrint(bytes32)", 4),
        ("requestImplChange(address)", 1), ("confirmImplChange(bytes32)", 1),
        ("requestCustodianChange(address)", 1), ("confirmCustodianChange(bytes32)", 1)]
      getters := [("decimals()", [], 2), ("custodian()", [], Word.ofAddress alice),
        ("erc20Impl()", [], Word.ofAddress GUSDAddrs.impl), ("lockRequestCount()", [], 0),
        ("totalSupply()", [], BitVec.ofNat 256 (175 * 10 ^ 6 + 100)),
        ("allowance(address,address)", [alice, dave], BitVec.allOnes 256)] }
  { f with scenario := gusdScenario f }

/-- YAMv2's quirks: 24 decimals, OpenZeppelin 3 style string reverts, minter-only `mint`,
the allowance spent (with `Approval`) after the transfer, infinite allowances decremented. -/
def yamScenario (f : TokenFamily) : Array Call :=
  let t (sender : Address) (sig : String) (args : List (Word × String)) := tokenCall f sender sig args
  #[t alice "mint(address,uint256)" [aArg f bob, nArg (10 ^ 24)],
    t bob "mint(address,uint256)" [aArg f bob, nArg 1],
    t alice "mint(address,uint256)" [aArg f 0, nArg 1],
    t alice "mint(address,uint256)" [aArg f alice, nArg (2 ^ 256 - 1)],
    t alice "transfer(address,uint256)" [aArg f 0, nArg 1],
    t bob "transfer(address,uint256)" [aArg f carol, nArg (10 ^ 30)],
    t carol "transferFrom(address,address,uint256)" [aArg f bob, aArg f dave, nArg (10 ^ 28 + 1)],
    t carol "transferFrom(address,address,uint256)" [aArg f bob, aArg f dave, nArg (10 ^ 28)],
    t dave "transferFrom(address,address,uint256)" [aArg f alice, aArg f carol, nArg 1],
    t bob "decreaseAllowance(address,uint256)" [aArg f carol, nArg 1],
    t bob "increaseAllowance(address,uint256)" [aArg f carol, nArg (2 ^ 256 - 1)],
    t bob "increaseAllowance(address,uint256)" [aArg f carol, nArg 1],
    t alice "approve(address,uint256)" [aArg f 0, nArg 1]]

/-- Mainnet YAMv2 (24 decimals). -/
def yamv2 : TokenFamily :=
  let f : TokenFamily :=
    { name := "yamv2"
      token := Verified.WeirdERC20.YAMV2.Contracts.YAMV2.address
      init := none
      code := Verified.WeirdERC20.YAMV2.Contracts.YAMV2.runtimeCode
      genesis := Verified.WeirdERC20.YAMV2.Contracts.YAMV2.genesisStorage
      selectors := Verified.WeirdERC20.YAMV2.Contracts.YAMV2.selectors
      balanceSlot := solSlot 1
      allowanceSlot := solSlot2 2
      supplySlot := some 3
      weights := [("transfer(address,uint256)", 8), ("transferFrom(address,address,uint256)", 8),
        ("approve(address,uint256)", 5), ("mint(address,uint256)", 4),
        ("increaseAllowance(address,uint256)", 2), ("decreaseAllowance(address,uint256)", 2)]
      getters := [("decimals()", [], 24), ("minter()", [], Word.ofAddress alice),
        ("totalSupply()", [], BitVec.ofNat 256 (1750001 * 10 ^ 24))] }
  { f with scenario := yamScenario f }

/-- LEND after its ICO: zero-value transfers revert (strict `balances[to] + v > balances[to]`),
the approve race guard, infinite allowances decremented, the token manager's switches. -/
def lendScenario (f : TokenFamily) : Array Call :=
  let t (sender : Address) (sig : String) (args : List (Word × String)) := tokenCall f sender sig args
  let e18 := 10 ^ 18
  #[t alice "transfer(address,uint256)" [aArg f bob, nArg 0],
    t alice "transfer(address,uint256)" [aArg f bob, nArg e18],
    t bob "approve(address,uint256)" [aArg f carol, nArg 5],
    t bob "approve(address,uint256)" [aArg f carol, nArg 0],
    t bob "approve(address,uint256)" [aArg f carol, nArg 5],
    t carol "transferFrom(address,address,uint256)" [aArg f bob, aArg f dave, nArg 6],
    t carol "transferFrom(address,address,uint256)" [aArg f bob, aArg f dave, nArg 5],
    t dave "transferFrom(address,address,uint256)" [aArg f alice, aArg f carol, nArg e18],
    t alice "transfer(address,uint256)" [aArg f alice, nArg 1],
    t alice "transferFrom(address,address,uint256)" [aArg f bob, aArg f carol, nArg 0],
    t alice "setState(uint8)" [nArg 4],
    t bob "setTokenManager(address)" [aArg f bob],
    t alice "withdrawEther()" [],
    rawCall f carol .empty "plain ether (no sale running)" e18,
    t alice "transfer(address,uint256)" [aArg f bob, nArg (2 ^ 256 - 1)]]

/-- Mainnet LEND (EthLend), post-ICO as on mainnet. -/
def lend : TokenFamily :=
  let f : TokenFamily :=
    { name := "lend"
      token := Verified.WeirdERC20.LEND.Contracts.LEND.address
      init := none
      code := Verified.WeirdERC20.LEND.Contracts.LEND.runtimeCode
      genesis := Verified.WeirdERC20.LEND.Contracts.LEND.genesisStorage
      selectors := Verified.WeirdERC20.LEND.Contracts.LEND.selectors
      balanceSlot := solSlot 0
      allowanceSlot := solSlot2 1
      supplySlot := some 2
      weights := [("transfer(address,uint256)", 8), ("transferFrom(address,address,uint256)", 8),
        ("approve(address,uint256)", 6), ("setState(uint8)", 2), ("buyTokens()", 2),
        ("buyTokensICO()", 1), ("buyTokensPresale()", 1), ("withdrawEther()", 1),
        ("setTokenManager(address)", 1)]
      payable := ["buyTokens()", "buyTokensICO()", "buyTokensPresale()"]
      receivesEther := true
      etherFunding := 1000 * 10 ^ 18
      uint8Values := #[0, 1, 2, 3, 4, 5, 6, 255]
      getters := [("currentState()", [], 5), ("enableTransfers()", [], 1),
        ("tokenManager()", [], Word.ofAddress alice), ("escrow()", [], Word.ofAddress carol),
        ("teamTokenBonus()", [], Word.ofAddress dave), ("decimals()", [], 18),
        ("totalSupply()", [], BitVec.ofNat 256 (1750001 * 10 ^ 18))] }
  { f with scenario := lendScenario f }

/-- LEND's slot 3 (`currentState`, `enableTransfers`, `teamTokenBonus = dave`). -/
def lendSlot3 (state : Nat) (enable : Bool) : Word :=
  BitVec.ofNat 256 (dave.toNat * 2 ^ 16 + (if enable then 2 ^ 8 else 0) + state)

/-- The ICO reopened: purchases with ether through `buyTokens`/the fallback across a price
tier, the presale entry point in the wrong state, ether to the escrow by `send`, the state
machine (including out-of-range enum values) ending transfers' lock. -/
def lendIcoScenario (f : TokenFamily) : Array Call :=
  let t (sender : Address) (sig : String) (args : List (Word × String)) (value : Nat := 0) :=
    tokenCall f sender sig args value
  let e18 := 10 ^ 18
  #[t alice "transfer(address,uint256)" [aArg f bob, nArg 1],
    t bob "getPrice()" [],
    t bob "buyTokens()" [] e18,
    t bob "getPrice()" [],
    t bob "buyTokens()" [] e18,
    rawCall f carol .empty "fallback purchase" (e18 / 100),
    rawCall f carol .empty "fallback purchase below the minimum" (e18 / 100 - 1),
    t dave "buyTokensPresale()" [] e18,
    t alice "withdrawEther()" [],
    t bob "withdrawEther()" [],
    t alice "setState(uint8)" [nArg 6],
    t alice "setState(uint8)" [nArg 5],
    t alice "transfer(address,uint256)" [aArg f bob, nArg 1],
    t alice "setState(uint8)" [nArg 4]]

/-- LEND with the ICO running (`currentState = ICORunning`, transfers disabled). -/
def lendIco : TokenFamily :=
  let f : TokenFamily :=
    { lend with name := "lendico"
                genesis := withStorage lend.genesis [(3, lendSlot3 4 false)]
                getters := [("currentState()", [], 4), ("enableTransfers()", [], 0),
                  ("getPrice()", [], 27500)] }
  { f with scenario := lendIcoScenario f }

/-- ZRX's quirks: failures return `false` (no revert, no event), infinite allowances are not
spent, the shadowed `totalSupply`, no zero-address checks. -/
def zrxScenario (f : TokenFamily) : Array Call :=
  let t (sender : Address) (sig : String) (args : List (Word × String)) := tokenCall f sender sig args
  let e18 := 10 ^ 18
  #[t alice "transfer(address,uint256)" [aArg f bob, nArg e18],
    t bob "transfer(address,uint256)" [aArg f carol, nArg (10 ^ 30)],
    t carol "transferFrom(address,address,uint256)" [aArg f bob, aArg f dave, nArg (10 ^ 22 + 1)],
    t carol "transferFrom(address,address,uint256)" [aArg f bob, aArg f dave, nArg (10 ^ 22)],
    t dave "transferFrom(address,address,uint256)" [aArg f alice, aArg f carol, nArg e18],
    t alice "transfer(address,uint256)" [aArg f alice, nArg 5],
    t alice "approve(address,uint256)" [aArg f bob, nArg (2 ^ 256 - 1)],
    t bob "transferFrom(address,address,uint256)" [aArg f alice, aArg f alice, nArg 1],
    t alice "transfer(address,uint256)" [aArg f 0, nArg 1],
    t dave "transfer(address,uint256)" [aArg f bob, nArg 0],
    t dave "totalSupply()" []]

/-- Mainnet ZRX (0x Protocol Token, solc 0.4.11). -/
def zrx : TokenFamily :=
  let f : TokenFamily :=
    { name := "zrx"
      token := Verified.WeirdERC20.ZRX.Contracts.ZRX.address
      init := none
      code := Verified.WeirdERC20.ZRX.Contracts.ZRX.runtimeCode
      genesis := Verified.WeirdERC20.ZRX.Contracts.ZRX.genesisStorage
      selectors := Verified.WeirdERC20.ZRX.Contracts.ZRX.selectors
      balanceSlot := solSlot 0
      allowanceSlot := solSlot2 1
      supplySlot := some 3
      weights := [("transfer(address,uint256)", 8), ("transferFrom(address,address,uint256)", 8),
        ("approve(address,uint256)", 5)]
      getters := [("decimals()", [], 18), ("totalSupply()", [], BitVec.ofNat 256 (1750001 * 10 ^ 18)),
        ("allowance(address,address)", [alice, dave], BitVec.allOnes 256)] }
  { f with scenario := zrxScenario f }

/-- Every token family. -/
def tokenFamilies : List TokenFamily :=
  [oz20, solady, weth9, usdt, usdtFee, bnb, sta, ampl, gusd, yamv2, lend, lendIco, zrx]

/-! ## Setup and run -/

/-- Set the token up on a fresh chain on both sides (deploying or installing it, funding the
actors) and check code and installed storage. Returns the evm-lean world. -/
def setupToken (rpc : Rpc) (stats : IO.Ref Stats) (f : TokenFamily) : IO World := do
  rpc.reset
  let mut w : World := ∅
  if f.etherFunding > 0 then
    for a in actors ++ f.extraAddresses do
      rpc.setBalance a f.etherFunding
      w := w.setBalance a (BitVec.ofNat 256 f.etherFunding)
  let mut errs : List String := []
  match f.init with
  | some init =>
    let (w', o, obs, d) ← step rpc { accounts := [f.token] } w deployer none init 0 "deploy"
    stats.modify fun st => { st with calls := st.calls + 1 }
    errs := d.map (s!"deployment: " ++ ·)
    if !o.success then errs := errs ++ ["evm-lean deployment failed"]
    if obs.created != some f.token then errs := errs ++ ["anvil deployed at an unexpected address"]
    w := w'
  | none =>
    rpc.setCode f.token f.code
    w := w.modify f.token fun acc => { acc with code := f.code }
    for (a, code) in f.extraCode do
      rpc.setCode a code
      w := w.modify a fun acc => { acc with code := code }
    let stores := (f.token, f.genesis) :: f.extraGenesis
    for (a, g) in stores do
      for (k, v) in g do
        rpc.setStorageAt a k v
        w := w.sstore a k v
    let all := stores.flatMap fun (a, g) => g.map fun (k, v) => ((a, k), v)
    let vals ← rpc.storageAt (all.map (·.1)).toArray
    if vals.toList != all.map (·.2) then errs := errs ++ ["installed storage differs"]
  let theirs ← rpc.code f.token
  if w.code f.token != theirs then errs := errs ++ ["code differs between evm-lean and anvil"]
  if theirs != f.code then errs := errs ++ ["deployed code differs from the Lean constant"]
  unless errs.isEmpty do fail ("\n".intercalate errs)
  let bad := getterCheck f w
  unless bad.isEmpty do fail ("getters disagree with the installed state:\n" ++ "\n".intercalate bad)
  let how := if f.init.isSome then "deployed" else "installed"
  IO.println (s!"  {how} at {hexOfAddress f.token} ({theirs.size} B, " ++
    s!"{f.genesis.length + (f.extraGenesis.map (·.2.length)).sum} storage slots); code and storage agree, {f.getters.length} getters as expected")
  return w

/-- Test one token family: setup, the fixed scenario, `sequences` random sequences. Returns
the number of mismatching sequences. -/
def testToken (rpc : Rpc) (stats : IO.Ref Stats) (seed famIdx sequences length : Nat)
    (verbose : Bool) (f : TokenFamily) (lowGasPct : Nat := 0) : IO Nat := do
  IO.println s!"[{f.name}]"
  let world0 ← setupToken rpc stats f
  let snap ← IO.mkRef (← rpc.snapshot)
  let eth := if f.etherFunding > 0 then f.token :: (actors ++ f.extraAddresses).toList else []
  let s : Session := { rpc, name := f.name, watch := { accounts := f.token :: f.extraCode.map (·.1), eth },
                       world0, snap,
                       stats, gen := genTokenCall f, length, verbose, lowGasPct }
  let mut found := 0
  unless f.scenario.isEmpty do
    let (w, res) ← s.runFixed f.scenario
    match res with
    | some (k, diffs) =>
      found := found + 1
      s.report 0 0 (f.scenario.extract 0 (k + 1)) diffs
    | none =>
      IO.println (s!"  fixed scenario agrees ({f.scenario.size} calls); token ether balance " ++
        s!"{(w.balance f.token).toNat}")
      let bad := layoutCheck f w
      if bad.isEmpty then
        IO.println "  storage layout agrees with balanceOf/allowance/totalSupply"
      else
        found := found + 1
        IO.println "  STORAGE LAYOUT MISMATCH:"
        for b in bad do IO.println s!"    - {b}"
  found := found + (← s.fuzzMany seed famIdx sequences)
  stats.modify fun st => { st with mismatches := st.mismatches + found }
  IO.println s!"  {sequences} sequences × {length} calls: {found} mismatching sequences"
  return found

end Difftest
