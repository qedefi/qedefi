import Examples.Differential.Session
import Examples.OpenZeppelin.Contracts.OzAsset
import Examples.Solady.Contracts.SoladyToken
import Examples.WETH9.Contracts.WETH9

/-!
# Token families under test

A `TokenFamily` is one token contract, either deployed through its creation code (compiled
targets) or installed as runtime code plus storage at its address (mainnet targets: the code
read from mainnet, the storage its constructor would leave, `genesisStorage`). The
generator draws from the token's whole ABI with weights, sizes amounts against the current
balances, allowances and ether, sends ether to payable functions (and sometimes to
non-payable ones) and to the fallback, and adds malformed calldata.
-/

namespace Examples.Differential

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

/-- A human-readable name for an address. -/
def tokenAddrName (f : TokenFamily) (a : Address) : String :=
  if a = f.token then "token" else if a = 0 then "zero"
  else if a = 0x000000000022D473030F116dDEE9F6B43aC78BA3 then "permit2"
  else match actors.idxOf? a with
    | some i => #["alice", "bob", "carol", "dave"][i]?.getD "?"
    | none => hexOfAddress a

/-- A call of `sig` on the token with the given arguments and value. -/
def tokenCall (f : TokenFamily) (sender : Address) (sig : String) (args : List (Word × String))
    (value : Nat := 0) : Call :=
  let sel := (selector? f.selectors sig).getD 0
  let v := if value = 0 then "" else s!" value {value}"
  { sender, to := f.token, data := calldata sel (args.map (·.1)), value
    kind := s!"{f.name}.{fnName sig}"
    desc := s!"{tokenAddrName f sender} → {f.name}.{fnName sig}(" ++
      ", ".intercalate (args.map (·.2)) ++ ")" ++ v }

/-- `balanceOf(a)` in the evm-lean world. -/
def TokenFamily.balance (f : TokenFamily) (w : World) (a : Address) : Nat :=
  (w.sload f.token (f.balanceSlot a)).toNat

/-- Values worth hitting: balances, allowances among actors, total supply, ether. -/
def TokenFamily.stateValues (f : TokenFamily) (w : World) : Array Word :=
  let who := actors ++ f.extraAddresses ++ #[f.token]
  let bal := who.map fun a => w.sload f.token (f.balanceSlot a)
  let alw := actors.flatMap fun o => actors.map fun s => w.sload f.token (f.allowanceSlot o s)
  let sup := match f.supplySlot with
    | some k => #[w.sload f.token k]
    | none => #[]
  bal ++ alw ++ sup ++ (actors.map fun a => w.balance a) ++ #[w.balance f.token]

/-- Functions whose first address argument is the account debited. -/
def debitsFirstArg (name : String) : Bool :=
  name ∈ ["transferFrom", "burn", "burnFrom", "redeem", "destroyBlackFunds", "transferByLegacy"]

/-- An amount bounded by `ether`, likely close to it. -/
def etherAmount (ether : Nat) : Gen Nat := do
  let v := (← plausible ether).toNat
  return min v ether

/-- The next call on the token. -/
def genTokenCall (f : TokenFamily) (w : World) (recent : Array Word) : Gen Call := do
  let state := f.stateValues w
  let everyone := actors ++ f.extraAddresses
  let sender ← if !f.extraAddresses.isEmpty && (← below 10) = 0 then pick f.extraAddresses
    else pick actors
  let ether := (w.balance sender).toNat
  let genAddr : Gen Address := do
    let r ← below 100
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
  -- A function from the ABI, by weight.
  let table := f.selectors.map fun (sig, _) => (sig, (f.weights.lookup sig).getD 1)
  let total := table.foldl (fun n (_, k) => n + k) 0
  let mut x ← below total
  let mut sig := (table.headD ("", 0)).1
  for (s, k) in table do
    if x < k then sig := s; break
    x := x - k
  let mut args : List (Word × String) := []
  let mut debit := sender
  let mut first := true
  for ty in paramTypes sig do
    match ty with
    | "address" =>
      let a ← genAddr
      if first && debitsFirstArg (fnName sig) then debit := a
      first := false
      args := args ++ [(Word.ofAddress a, tokenAddrName f a)]
    | "uint8" =>
      let v := BitVec.ofNat 256 (← pick #[0, 1, 27, 28, 255]); args := args ++ [(v, toString v.toNat)]
    | "bytes32" => let v ← randWord; args := args ++ [(v, hexOfWord v)]
    | _ =>
      let v ← if (← below 2) = 0 then plausible (f.balance w debit) else genAmount state recent
      args := args ++ [(v, toString v.toNat)]
  let value ← if sig ∈ f.payable then etherAmount ether
    else if (← below 100) < 3 then etherAmount (min ether 1000) else pure 0
  return tokenCall f sender sig args value

/-! ## Families -/

/-- `keccak(m[k])` slot of a Solidity mapping at `slot`. -/
def solSlot (slot : Nat) (a : Address) : Word := mappingSlot (Word.ofAddress a) (BitVec.ofNat 256 slot)

/-- Nested Solidity mapping slot `m[o][s]`. -/
def solSlot2 (slot : Nat) (o s : Address) : Word :=
  mappingSlot (Word.ofAddress s) (solSlot slot o)

/-- OpenZeppelin `ERC20Mock` on its own. -/
def oz20 : TokenFamily where
  name := "oz20"
  token := Examples.OpenZeppelin.Contracts.OzAsset.address
  init := some (Examples.OpenZeppelin.Contracts.OzAsset.creationCode ++
    Examples.OpenZeppelin.Contracts.OzAsset.constructorArgs)
  code := Examples.OpenZeppelin.Contracts.OzAsset.runtimeCode
  selectors := Examples.OpenZeppelin.Contracts.OzAsset.selectors
  balanceSlot := solSlot 0
  allowanceSlot := solSlot2 1
  supplySlot := some 2
  weights := [("mint(address,uint256)", 4), ("burn(address,uint256)", 3),
    ("transfer(address,uint256)", 6), ("transferFrom(address,address,uint256)", 6),
    ("approve(address,uint256)", 5)]

/-- Solady's balance slot: `keccak256(owner ‖ 0⁸ ‖ 0x87a211a2)` (32 bytes). -/
def soladyBalanceSlot (a : Address) : Word :=
  Crypto.real.keccak256 (Bytes.ofAddress a ++ Bytes.ofNatBE 12 0x87a211a2)

/-- Solady's allowance slot: `keccak256(owner ‖ 0⁸ ‖ 0x7f5e9f20 ‖ spender)` (52 bytes). -/
def soladyAllowanceSlot (o s : Address) : Word :=
  Crypto.real.keccak256 (Bytes.ofAddress o ++ Bytes.ofNatBE 12 0x7f5e9f20 ++ Bytes.ofAddress s)

/-- Solady `ERC20` (`SoladyToken`), with Permit2 as an extra address and sender. -/
def solady : TokenFamily where
  name := "solady"
  token := Examples.Solady.Contracts.SoladyToken.address
  init := some Examples.Solady.Contracts.SoladyToken.creationCode
  code := Examples.Solady.Contracts.SoladyToken.runtimeCode
  selectors := Examples.Solady.Contracts.SoladyToken.selectors
  balanceSlot := soladyBalanceSlot
  allowanceSlot := soladyAllowanceSlot
  supplySlot := some 0x05345cdf77eb68f44c
  weights := [("mint(address,uint256)", 4), ("burn(address,uint256)", 3),
    ("transfer(address,uint256)", 6), ("transferFrom(address,address,uint256)", 6),
    ("approve(address,uint256)", 5),
    ("permit(address,address,uint256,uint256,uint8,bytes32,bytes32)", 2)]
  extraAddresses := #[0x000000000022D473030F116dDEE9F6B43aC78BA3]

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
    tokenCall f bob "withdraw(uint256)" [num (e18 + e18 / 4)],
    tokenCall f bob "totalSupply()" []]

/-- Mainnet WETH9: deposits and withdrawals with ether, ether balances compared. -/
def weth9 : TokenFamily :=
  let f : TokenFamily :=
    { name := "weth9"
      token := Examples.WETH9.Contracts.WETH9.address
      init := none
      code := Examples.WETH9.Contracts.WETH9.runtimeCode
      genesis := Examples.WETH9.Contracts.WETH9.genesisStorage
      selectors := Examples.WETH9.Contracts.WETH9.selectors
      balanceSlot := solSlot 3
      allowanceSlot := solSlot2 4
      supplySlot := none
      weights := [("deposit()", 6), ("withdraw(uint256)", 6), ("transfer(address,uint256)", 5),
        ("transferFrom(address,address,uint256)", 5), ("approve(address,uint256)", 4)]
      payable := ["deposit()"]
      receivesEther := true
      etherFunding := 1000 * 10 ^ 18 }
  { f with scenario := wethScenario f }

/-- Every token family. -/
def tokenFamilies : List TokenFamily := [oz20, solady, weth9]

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
    for (k, v) in f.genesis do
      rpc.setStorageAt f.token k v
      w := w.sstore f.token k v
    let vals ← rpc.storageAt (f.genesis.map fun (k, _) => (f.token, k)).toArray
    if vals.toList != f.genesis.map (·.2) then errs := errs ++ ["installed storage differs"]
  let theirs ← rpc.code f.token
  if w.code f.token != theirs then errs := errs ++ ["code differs between evm-lean and anvil"]
  if theirs != f.code then errs := errs ++ ["deployed code differs from the Lean constant"]
  unless errs.isEmpty do fail ("\n".intercalate errs)
  let how := if f.init.isSome then "deployed" else "installed"
  IO.println (s!"  {how} at {hexOfAddress f.token} ({theirs.size} B, " ++
    s!"{f.genesis.length} storage slots); code and storage agree")
  return w

/-- Test one token family: setup, the fixed scenario, `sequences` random sequences. Returns
the number of mismatching sequences. -/
def testToken (rpc : Rpc) (stats : IO.Ref Stats) (seed famIdx sequences length : Nat)
    (verbose : Bool) (f : TokenFamily) : IO Nat := do
  IO.println s!"[{f.name}]"
  let world0 ← setupToken rpc stats f
  let snap ← IO.mkRef (← rpc.snapshot)
  let eth := if f.etherFunding > 0 then f.token :: (actors ++ f.extraAddresses).toList else []
  let s : Session := { rpc, name := f.name, watch := { accounts := [f.token], eth }, world0, snap,
                       stats, gen := genTokenCall f, length, verbose }
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
  found := found + (← s.fuzzMany seed famIdx sequences)
  stats.modify fun st => { st with mismatches := st.mismatches + found }
  IO.println s!"  {sequences} sequences × {length} calls: {found} mismatching sequences"
  return found

end Examples.Differential
