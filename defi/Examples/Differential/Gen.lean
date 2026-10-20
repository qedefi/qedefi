import Examples.Differential.Family
import Conformance.Hex

/-!
# Random call sequences

Calls are drawn by a seeded SplitMix64 generator, so a run is reproducible from its seed.
Each call is generated against the current evm-lean state, which lets amounts hit the
interesting values: zero, one, `2²⁵⁶ - 1` and other near-overflow values, current balances,
total supply and total assets (± 1), and words recently returned by the contracts.

The mix: asset `mint`/`burn`/`approve`/`transfer`/`transferFrom`, donations (asset transfers
to the vault), vault `deposit`/`mint`/`withdraw`/`redeem` (with the caller sometimes not
the owner, exercising allowances), share `transfer`/`approve`/`transferFrom`, Solmate
`permit` with an invalid signature or an expired deadline, every view of either contract,
generic calls of any selector with random arguments, and malformed calldata.
-/

namespace Differential

open EvmLean EvmLean.Contracts

/-- Generator state: a SplitMix64 counter. -/
abbrev Gen := StateM UInt64

/-- The next 64 random bits (SplitMix64). -/
def next64 : Gen UInt64 := do
  let s := (← get) + 0x9E3779B97F4A7C15
  set s
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  return z ^^^ (z >>> 31)

/-- A number in `[0, n)` (`0` if `n = 0`). -/
def below (n : Nat) : Gen Nat := do
  if n = 0 then return 0 else return (← next64).toNat % n

/-- A uniformly random word. -/
def randWord : Gen Word := do
  let mut n := 0
  for _ in [0:4] do n := n * 2 ^ 64 + (← next64).toNat
  return BitVec.ofNat 256 n

/-- A random element (`default` for an empty array). -/
def pick {α : Type} [Inhabited α] (xs : Array α) : Gen α := do
  return xs[← below xs.size]?.getD default

/-- The actors sending transactions. -/
def actors : Array Address := #[0xA11CE, 0xB0B, 0xCA401, 0xDA7E]

/-- A human-readable name for an address. -/
def addrName (f : Family) (a : Address) : String :=
  if a = f.vault then "vault" else if a = f.asset then "asset" else if a = 0 then "zero"
  else match actors.idxOf? a with
    | some i => #["alice", "bob", "carol", "dave"][i]?.getD "?"
    | none => Conformance.hexOfAddress a

/-- An address argument: usually an actor, sometimes the zero address, the vault or the
asset. -/
def genAddress (f : Family) : Gen Address := do
  let r ← below 100
  if r < 85 then pick actors
  else if r < 90 then return 0
  else if r < 96 then return f.vault
  else return f.asset

/-- Values worth hitting in the current state: balances, total supply, total assets. -/
def stateValues (f : Family) (w : World) : Array Word :=
  let bal := actors.flatMap fun a =>
    #[balanceIn w f.asset f.assetBalances a, balanceIn w f.vault f.vaultBalances a,
      allowanceIn w f.vault f.vaultAllowances a (actors[0]?.getD 0)]
  bal ++ #[balanceIn w f.asset f.assetBalances f.vault,
           w.sload f.vault (BitVec.ofNat 256 f.vaultTotalSupply)]

/-- An amount: edge cases, state-derived values (± 1), recent return values, small and
medium random numbers, or a uniformly random word. -/
def genAmount (state recent : Array Word) : Gen Word := do
  let r ← below 100
  if r < 7 then return 0
  else if r < 12 then return 1
  else if r < 17 then return BitVec.allOnes 256
  else if r < 21 then
    pick #[BitVec.allOnes 256 - 1, BitVec.ofNat 256 (2 ^ 255), BitVec.ofNat 256 (2 ^ 128),
           BitVec.ofNat 256 (2 ^ 256 / 10 ^ 18), BitVec.ofNat 256 (2 ^ 256 - 10 ^ 18),
           BitVec.ofNat 256 (2 ^ 255 + 1)]
  else if r < 25 then randWord
  else if r < 50 then
    let v ← pick state
    let d ← below 3
    return if d = 0 then v else if d = 1 then v + 1 else v - 1
  else if r < 60 && !recent.isEmpty then pick recent
  else if r < 80 then return BitVec.ofNat 256 (← below 1000)
  else return BitVec.ofNat 256 ((← next64).toNat * (← below 1_000_000_000))

/-- A transaction to send. -/
structure Call where
  /-- Sender. -/
  sender : Address
  /-- Recipient contract. -/
  to : Address
  /-- Calldata. -/
  data : ByteArray
  /-- Readable description, e.g. `alice → vault.deposit(5, bob)`. -/
  desc : String
  /-- Operation name, for statistics. -/
  kind : String
  deriving Inhabited

/-- The calldata of a call with a static argument list. -/
def calldata (sel : UInt32) (args : List Word) : ByteArray :=
  Bytes.ofNatBE 4 sel.toNat ++ args.foldl (fun b w => b ++ Bytes.ofWord w) .empty

/-- The parameter types of a signature `f(t₁,…,tₙ)`. -/
def paramTypes (sig : String) : List String :=
  match sig.splitOn "(" with
  | [_, rest] =>
    let inner := (rest.dropEnd 1).toString
    if inner.isEmpty then [] else inner.splitOn ","
  | _ => []

/-- The function name of a signature. -/
def fnName (sig : String) : String := (sig.splitOn "(").headD sig

/-- An argument of the given ABI type, with its rendering. -/
def genArg (f : Family) (state recent : Array Word) (ty : String) : Gen (Word × String) := do
  match ty with
  | "address" => let a ← genAddress f; return (Word.ofAddress a, addrName f a)
  | "uint8" => let v := BitVec.ofNat 256 (← pick #[0, 1, 27, 28, 255, 256]); return (v, toString v.toNat)
  | "bytes32" => let v ← randWord; return (v, Conformance.hexOfWord v)
  | _ => let v ← genAmount state recent; return (v, toString v.toNat)

/-- A call of `sig` (looked up in `table`) on `to` with the given arguments. -/
def mkCall (f : Family) (table : List (String × UInt32)) (sender to : Address) (sig : String)
    (args : List (Word × String)) : Call :=
  let sel := (selector? table sig).getD 0
  { sender, to, data := calldata sel (args.map (·.1)), kind := s!"{addrName f to}.{fnName sig}"
    desc := s!"{addrName f sender} → {addrName f to}.{fnName sig}(" ++
      ", ".intercalate (args.map (·.2)) ++ ")" }

/-- A call of a random function of `table` with random arguments. -/
def genericCall (f : Family) (state recent : Array Word) (sender to : Address)
    (table : List (String × UInt32)) : Gen Call := do
  let (sig, _) ← pick table.toArray
  let args ← (paramTypes sig).mapM (genArg f state recent)
  return mkCall f table sender to sig args

/-- Malformed calldata: empty, a bare or truncated selector, an unknown selector, or a known
selector with a cut-off argument list. -/
def junkCall (f : Family) (sender to : Address) (table : List (String × UInt32)) : Gen Call := do
  let (_, sel) ← pick table.toArray
  let full := calldata sel [← randWord, ← randWord, ← randWord]
  let data ← match ← below 5 with
    | 0 => pure ByteArray.empty
    | 1 => pure (full.extract 0 (← below 4))
    | 2 => pure (calldata (← next64).toUInt32 [])
    | 3 => pure (full.extract 0 (4 + (← below 64)))
    | _ => pure (full ++ ⟨#[(← next64).toUInt8]⟩)
  return { sender, to, data, kind := s!"{addrName f to}.junk",
           desc := s!"{addrName f sender} → {addrName f to} junk {Conformance.hexOfBytes data}" }

/-- An amount that is likely to succeed against a bound (a balance or what it converts to):
the bound itself, a fraction of it, or the bound ± 1. -/
def plausible (bound : Nat) : Gen Word := do
  let n ← match ← below 7 with
    | 0 => pure bound
    | 1 => pure (bound / 2)
    | 2 => pure (bound / 3 + 1)
    | 3 => pure (bound + 1)
    | 4 => pure (bound - 1)
    | _ => below (bound + 1)
  return BitVec.ofNat 256 n

/-- The next call, given the current evm-lean world and recently returned words. -/
def genCall (f : Family) (w : World) (recent : Array Word) : Gen Call := do
  let state := stateValues f w
  let sender ← pick actors
  -- Amounts: half the time sized against `bound`, otherwise from `genAmount`.
  let amt (bound : Nat) : Gen Word := do
    if (← below 2) = 0 then plausible bound else genAmount state recent
  let assetBal (a : Address) := (balanceIn w f.asset f.assetBalances a).toNat
  let shares (a : Address) := (balanceIn w f.vault f.vaultBalances a).toNat
  let totalAssets := assetBal f.vault
  let totalSupply := (w.sload f.vault (BitVec.ofNat 256 f.vaultTotalSupply)).toNat
  let toAssets (s : Nat) := if totalSupply = 0 then s else s * totalAssets / totalSupply
  let toShares (x : Nat) := if totalAssets = 0 then x else x * totalSupply / totalAssets
  -- Prefer actors who can act: funded and approved depositors, share holders.
  let funded := actors.filter fun x =>
    assetBal x > 0 && (allowanceIn w f.asset f.assetAllowances x f.vault).toNat > 0
  let holders := actors.filter fun x => shares x > 0
  let prefer (xs : Array Address) : Gen Address := do
    if !xs.isEmpty && (← below 10) < 7 then pick xs else pure sender
  let a := f.assetSelectors
  let v := f.vaultSelectors
  let addr (x : Address) : Word × String := (Word.ofAddress x, addrName f x)
  let num (x : Word) : Word × String := (x, toString x.toNat)
  let r ← below 100
  if r < 10 then
    let to ← genAddress f
    let x ← if (← below 2) = 0 then pure (BitVec.ofNat 256 ((← below 1000) * 10 ^ (← below 25)))
            else genAmount state recent
    return mkCall f a sender f.asset "mint(address,uint256)" [addr to, num x]
  else if r < 16 then
    let x ← if (← below 10) < 7 then pure (BitVec.allOnes 256) else amt (assetBal sender)
    return mkCall f a sender f.asset "approve(address,uint256)" [addr f.vault, num x]
  else if r < 20 then
    return mkCall f a sender f.asset "transfer(address,uint256)"
      [addr f.vault, num (← amt (assetBal sender))]
  else if r < 30 then
    let sender ← prefer funded
    let x ← amt (assetBal sender); let to ← genAddress f
    return mkCall f v sender f.vault "deposit(uint256,address)" [num x, addr to]
  else if r < 38 then
    let sender ← prefer funded
    let x ← amt (toShares (assetBal sender)); let to ← genAddress f
    return mkCall f v sender f.vault "mint(uint256,address)" [num x, addr to]
  else if r < 56 then
    let to ← genAddress f
    let sender ← prefer holders
    let owner ← if (← below 4) < 3 then pure sender else pick actors
    if r < 47 then
      return mkCall f v sender f.vault "withdraw(uint256,address,address)"
        [num (← amt (toAssets (shares owner))), addr to, addr owner]
    else
      return mkCall f v sender f.vault "redeem(uint256,address,address)"
        [num (← amt (shares owner)), addr to, addr owner]
  else if r < 60 then
    let sender ← prefer holders
    let x ← amt (shares sender); let to ← genAddress f
    return mkCall f v sender f.vault "transfer(address,uint256)" [addr to, num x]
  else if r < 63 then
    let to ← pick actors
    let x ← if (← below 2) = 0 then pure (BitVec.allOnes 256) else amt (shares sender)
    return mkCall f v sender f.vault "approve(address,uint256)" [addr to, num x]
  else if r < 67 then
    let src ← pick actors; let to ← genAddress f
    return mkCall f v sender f.vault "transferFrom(address,address,uint256)"
      [addr src, addr to, num (← amt (shares src))]
  else if r < 69 then
    let src ← pick actors; let to ← genAddress f
    return mkCall f a sender f.asset "transferFrom(address,address,uint256)"
      [addr src, addr to, num (← amt (assetBal src))]
  else if r < 71 then
    let src ← pick actors
    return mkCall f a sender f.asset "burn(address,uint256)" [addr src, num (← amt (assetBal src))]
  else if r < 73 then
    let owner ← pick actors; let spender ← pick actors; let x ← genAmount state recent
    let deadline ← pick #[0, BitVec.allOnes 256]
    let vByte := BitVec.ofNat 256 (← pick #[27, 28, 0])
    let rr ← randWord; let ss ← randWord
    let to ← pick #[f.vault, f.asset]
    let table := if to = f.vault then v else a
    return mkCall f table sender to
      "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)"
      [addr owner, addr spender, num x, num deadline, num vByte, (rr, "r"), (ss, "s")]
  else if r < 88 then genericCall f state recent sender f.vault v
  else if r < 97 then genericCall f state recent sender f.asset a
  else
    let to ← pick #[f.vault, f.asset]
    junkCall f sender to (if to = f.vault then v else a)

end Differential
