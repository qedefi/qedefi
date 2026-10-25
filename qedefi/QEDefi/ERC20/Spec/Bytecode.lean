import QEDefi.ERC20.Spec.Laws
import QEDefi.ERC4626.Logs
import EvmLogic.Program.Summary
import EvmLogic.Solidity.Abi

/-!
# The bytecode spec of a token

`ERC20Spec code abs M g₀ sel ops` says that the runtime code `code` *is* the token model `M`:
in every fresh frame running `code` (a top-level call, or a call from any contract at any
depth), through the storage abstraction `abs`, every call ends exactly as `M` says. One
definition for every token; what differs between tokens is only the data it is applied to,
which is what a reviewer reads:

* the model `M` (for most tokens a `Variant` record and its events, `Variant.model`);
* the abstraction `abs`: which storage slots hold the model state, and the hash hypotheses
  (`TokenAbs.Sound`) under which the representation is exact;
* `g₀`, the gas from which the outcome is exact (below it, a call may fail instead);
* `sel`, the selectors the dispatcher knows (others reach the fallback);
* `ops`, the decoder of the token's other entry points (mint, burn, admin operations).

**Exactness.** A successful call returns the model's return data, leaves the model's new state
in the footprint of `abs`, appends exactly the model's events, and changes nothing else: no
other storage slot of the token, no other account, no ether, no transient storage
(`Matches`, `FrameKeeps`). A failing call fails the way the model says (`REVERT` or
`INVALID`). Because the footprint is all the token may write, a wrong model or a wrong layout
cannot be proved.

**Obligations** (fields of `ERC20Spec`, each its own theorem per token):

| Field | Calldata | Exact when |
|---|---|---|
| `calls` | `transfer`, `transferFrom`, `approve`, ABI-encoded (`Call.Encodes`) | gas ≥ `g₀`, not static, no value |
| `views` | `balanceOf`, `allowance`, `totalSupply` | gas ≥ `g₀`, no value |
| `fallback` | shorter than 4 bytes, or a selector not in `sel` | gas ≥ `g₀`, not static |
| `ops` | what `ops` decodes | gas ≥ `g₀`, not static |

Outside the "exact when" column a call may also fail (`Fails`), never do anything else.

**Not yet obligations** (stated here, proved separately per token): EIP-2612 `permit`
(`PermitSpec`, with the token's signature recovery), and calldata that is neither well formed
nor unknown (`MalformedSpec`: a known selector with short or dirty arguments; every such frame
must be explained by some model action of the caller, or fail). `ERC20Spec.Complete` is the
conjunction.

Throughout, the calldata is shorter than `2⁶⁴` bytes (it could not be paid for with `2⁶⁴`
gas; the frame-level theorems cannot see the transaction that pays for it).
-/

namespace QEDefi.ERC20.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Solidity QEDefi.ERC4626

/-! ## Storage abstraction -/

/-- **How a token's storage represents a model state.** `read` is the model state of the
token at `token` in world `w`; it may depend only on the token's storage slots in `footprint`
and on its ether balance (`read_congr`). `Sound crypto` collects the hash hypotheses under
which the representation is exact (e.g. no two mapping rows share a slot). -/
structure TokenAbs (σ : Type) where
  /-- The model state of the token at `token`. -/
  read : Crypto → World → Address → σ
  /-- The token's storage slots `read` depends on. -/
  footprint : Crypto → Word → Prop
  /-- `read` depends on nothing but the footprint and the token's ether. -/
  read_congr : ∀ crypto (w w' : World) token,
    (∀ k, footprint crypto k → w'.sload token k = w.sload token k) →
    w'.balance token = w.balance token → read crypto w' token = read crypto w token
  /-- The hash hypotheses of the representation. -/
  Sound : Crypto → Prop

/-! ## Calldata -/

/-- **ABI calldata** with selector `sel` and static word arguments `args`, as solc's decoder
reads it (trailing bytes are allowed, as the decoder ignores them). -/
structure Args (data : ByteArray) (sel : Nat) (args : List Word) : Prop where
  selector : Abi.selectorOf data = sel
  size : 4 + 32 * args.length ≤ data.size
  arg : ∀ i (h : i < args.length), Bytes.toWord (readBytes data (4 + 32 * i) 32) = args[i]

/-- A `uint256` argument. -/
def word (v : ℕ) : Word := BitVec.ofNat 256 v

/-- **`data` is the ABI encoding of the call `c`** (clean address words, amounts below
`2²⁵⁶`). Fallback and `permit` calls have their own obligations. -/
def _root_.QEDefi.ERC20.Call.Encodes (data : ByteArray) : Call Address → Prop
  | .transfer dst v => v < 2 ^ 256 ∧ Args data 0xa9059cbb [Word.ofAddress dst, word v]
  | .transferFrom src dst v =>
    v < 2 ^ 256 ∧ Args data 0x23b872dd [Word.ofAddress src, Word.ofAddress dst, word v]
  | .approve sp v => v < 2 ^ 256 ∧ Args data 0x095ea7b3 [Word.ofAddress sp, word v]
  | .other _ => False
  | .permit .. => False

/-- The three ERC-20 views. -/
inductive View where
  /-- `balanceOf(a)`. -/
  | balanceOf (a : Address)
  /-- `allowance(owner, spender)`. -/
  | allowance (owner spender : Address)
  /-- `totalSupply()`. -/
  | totalSupply

/-- `data` is the ABI encoding of the view `v`. -/
def View.Encodes (data : ByteArray) : View → Prop
  | .balanceOf a => Args data 0x70a08231 [Word.ofAddress a]
  | .allowance o sp => Args data 0xdd62ed3e [Word.ofAddress o, Word.ofAddress sp]
  | .totalSupply => Args data 0x18160ddd []

/-- What the model says the view returns. -/
def View.value {σ E : Type} (M : TokenModel σ Address E) (s : σ) : View → ℕ
  | .balanceOf a => M.balanceOf s a
  | .allowance o sp => M.allowance s o sp
  | .totalSupply => M.totalSupply s

/-! ## Outcomes -/

/-- The return data of a model result. -/
def retBytes : RetData → ByteArray
  | .empty => .empty
  | .word b => Bytes.ofWord (if b then 1#256 else 0#256)

/-- The log of a model event emitted by `token`. -/
def eventLog (token : Address) : Event Address → Log
  | .transfer src dst v => transferLog token src dst (word v)
  | .approval o sp v => approvalLog token o sp (word v)

/-- The frame failed: `REVERT` or an exceptional halt (its changes are rolled back). -/
def Fails : Outcome → Prop
  | .success _ => False
  | .revert _ => True
  | .halt _ => True

variable {σ E : Type}

/-- The model state at the start of the frame `m`: the world before its value moved (the
frame's snapshot), at the executing account. -/
def pre (abs : TokenAbs σ) (m : Machine) : σ :=
  abs.read m.ctx.crypto m.frame.snapshot.1 m.frame.msg.currentTarget

/-- **What a successful call may change**: from `w` to `w'`, the token's storage only inside
the footprint, and nothing else: no other account, and the token's code, nonce and ether. -/
structure FrameKeeps (abs : TokenAbs σ) (crypto : Crypto) (token : Address) (w w' : World) :
    Prop where
  /-- The token's storage outside the footprint. -/
  own : ∀ k, ¬ abs.footprint crypto k → w'.sload token k = w.sload token k
  /-- The token's code. -/
  code : w'.code token = w.code token
  /-- The token's nonce. -/
  nonce : (w'.account token).nonce = (w.account token).nonce
  /-- The token's ether. -/
  balance : w'.balance token = w.balance token
  /-- Every other account. -/
  others : ∀ b, b ≠ token → w'.account b = w.account b

/-- **The frame `m` ended (`mf`, `o`) as the model result `res` says**, with events `evs` on
success: the return data, the model's new state through `abs`, exactly the events appended,
nothing else changed; or the model's kind of failure. -/
def Matches (abs : TokenAbs σ) (m mf : Machine) (o : Outcome) (evs : List (Event Address)) :
    Result σ → Prop
  | .ok s' ret =>
    o = .success (retBytes ret) ∧
    abs.read m.ctx.crypto mf.world m.frame.msg.currentTarget = s' ∧
    FrameKeeps abs m.ctx.crypto m.frame.msg.currentTarget m.world mf.world ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs ++ (evs.map (eventLog m.frame.msg.currentTarget)).toArray
  | .halt .revert => ∃ out, o = .revert out
  | .halt .invalid => ∃ e, o = .halt e

/-- A frame in which a call must behave exactly: at least `g₀` gas, not static, no value. -/
def Normal (g₀ : Nat) (m : Machine) : Prop :=
  g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false ∧ m.frame.msg.value = 0

/-- The common hypotheses of every obligation: `m` is a fresh frame of `code`, started the way
the interpreter starts frames (its world is its snapshot with the value moved, as `launchCall`
and `initMachine` do), its value moved if nonzero (token code run by a `DELEGATECALL` that
carries value is out of scope), its calldata is payable, the hash hypotheses hold, and the
token is in a state its model can reach. -/
structure Start (code : ByteArray) (abs : TokenAbs σ) (M : TokenModel σ Address E) (m : Machine) :
    Prop where
  fresh : Fresh code m
  launched : m.world = transferValue m.frame.snapshot.1 m.frame.msg
  value : m.frame.msg.shouldTransferValue = true ∨ m.frame.msg.value = 0
  size : m.frame.msg.data.size < 2 ^ 64
  sound : abs.Sound m.ctx.crypto
  wf : M.wf (pre abs m)

/-! ## Obligations -/

/-- **The ERC-20 calls**: calldata encoding `c` ends as `M.call` says, with `M.events`; or,
outside `Normal`, fails. -/
def CallSpec (code : ByteArray) (abs : TokenAbs σ) (M : TokenModel σ Address E) (g₀ : Nat)
    (c : Call Address) : Prop :=
  ∀ m, Start code abs M m → c.Encodes m.frame.msg.data →
    Halts m fun mf o =>
      Matches abs m mf o (M.events (pre abs m) m.frame.msg.caller c)
        (M.call (pre abs m) m.frame.msg.caller c) ∨
      (Fails o ∧ ¬ Normal g₀ m)

/-- **The views** return the model's value (as one word, exactly) and change nothing; or,
with less than `g₀` gas or with value, fail. -/
def ViewSpec (code : ByteArray) (abs : TokenAbs σ) (M : TokenModel σ Address E) (g₀ : Nat)
    (v : View) : Prop :=
  ∀ m, Start code abs M m → v.Encodes m.frame.msg.data →
    Halts m fun mf o =>
      (∃ x : Word, o = .success (Bytes.ofWord x) ∧ x.toNat = v.value M (pre abs m) ∧
        mf.world = m.world ∧ mf.transient = m.transient ∧
        mf.createdAccounts = m.createdAccounts ∧ mf.frame.sub.logs = m.frame.sub.logs) ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0))

/-- **Unknown selectors** (and calldata shorter than a selector) end as the model's fallback
call with the frame's value; or, with less than `g₀` gas or static, fail. -/
def FallbackSpec (code : ByteArray) (abs : TokenAbs σ) (M : TokenModel σ Address E) (g₀ : Nat)
    (sel : List Nat) : Prop :=
  ∀ m, Start code abs M m →
    (m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ sel) →
    Halts m fun mf o =>
      Matches abs m mf o (M.events (pre abs m) m.frame.msg.caller (.other m.frame.msg.value.toNat))
        (M.call (pre abs m) m.frame.msg.caller (.other m.frame.msg.value.toNat)) ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false))

/-- **The other entry points**: calldata `ops caller data value` decodes to `e` ends with the
model's `M.op` state (success exactly when it succeeds), changing nothing outside the
footprint; or, outside `Normal` (value allowed when the decoder accepted it), fails. Return
data and events of these entry points are not part of this version of the spec. -/
def OpSpec (code : ByteArray) (abs : TokenAbs σ) (M : TokenModel σ Address E) (g₀ : Nat)
    (ops : Address → ByteArray → ℕ → Option E) : Prop :=
  ∀ m e, Start code abs M m →
    ops m.frame.msg.caller m.frame.msg.data m.frame.msg.value.toNat = some e →
    Halts m fun mf o =>
      (match M.op (pre abs m) e with
        | some s' => (∃ out, o = .success out) ∧
          abs.read m.ctx.crypto mf.world m.frame.msg.currentTarget = s' ∧
          FrameKeeps abs m.ctx.crypto m.frame.msg.currentTarget m.world mf.world ∧
          mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts
        | none => Fails o) ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false))

/-- **The bytecode spec of a token**: `code` is the model `M` through `abs`, exactly from gas
`g₀`, with dispatcher selectors `sel` and other entry points `ops`. -/
structure ERC20Spec (code : ByteArray) (abs : TokenAbs σ) (M : TokenModel σ Address E)
    (g₀ : Nat) (sel : List Nat) (ops : Address → ByteArray → ℕ → Option E) : Prop where
  /-- `transfer`, `transferFrom`, `approve`. -/
  calls : ∀ c, CallSpec code abs M g₀ c
  /-- `balanceOf`, `allowance`, `totalSupply`. -/
  views : ∀ v, ViewSpec code abs M g₀ v
  /-- Unknown selectors and short calldata. -/
  fallback : FallbackSpec code abs M g₀ sel
  /-- The other entry points. -/
  ops : OpSpec code abs M g₀ ops

/-! ## Obligations not yet in `ERC20Spec` -/

/-- **EIP-2612 `permit(owner, spender, value, deadline, v, r, s)`** ends as the model's
`permit` call, with `live = timestamp ≤ deadline` and the signature recovery `rec m` of the
token (its EIP-712 digest at each nonce, through `crypto.ecrecover`; a reviewed part of each
token's spec, like its model). -/
def PermitSpec (code : ByteArray) (abs : TokenAbs σ) (M : TokenModel σ Address E) (g₀ : Nat)
    (rec : Machine → ℕ → Address) : Prop :=
  ∀ m (o sp : Address) (v dl pv pr ps : Word), Start code abs M m →
    Args m.frame.msg.data 0xd505accf [Word.ofAddress o, Word.ofAddress sp, v, dl, pv, pr, ps] →
    let c : Call Address := .permit o sp v.toNat (decide (m.ctx.block.timestamp ≤ dl.toNat)) (rec m)
    Halts m fun mf out =>
      Matches abs m mf out (M.events (pre abs m) m.frame.msg.caller c)
        (M.call (pre abs m) m.frame.msg.caller c) ∨
      (Fails out ∧ ¬ Normal g₀ m)

/-- **Any calldata** is explained by some action of the caller the model allows: an ERC-20
call other than `permit`, a view (nothing changes), an entry point the decoder accepts for
some calldata of the caller, or a failure. With the exact obligations this says malformed
calldata (short or dirty arguments of a known selector) can do nothing a well-formed call
could not. -/
def MalformedSpec (code : ByteArray) (abs : TokenAbs σ) (M : TokenModel σ Address E)
    (ops : Address → ByteArray → ℕ → Option E) : Prop :=
  ∀ m, Start code abs M m →
    Halts m fun mf o =>
      Fails o ∨
      (∃ c, (∀ o sp v live rec, c ≠ .permit o sp v live rec) ∧
        Matches abs m mf o (M.events (pre abs m) m.frame.msg.caller c)
          (M.call (pre abs m) m.frame.msg.caller c)) ∨
      (mf.world = m.world ∧ mf.transient = m.transient ∧ mf.frame.sub.logs = m.frame.sub.logs) ∨
      (∃ d e s', ops m.frame.msg.caller d m.frame.msg.value.toNat = some e ∧
        M.op (pre abs m) e = some s' ∧
        abs.read m.ctx.crypto mf.world m.frame.msg.currentTarget = s' ∧
        FrameKeeps abs m.ctx.crypto m.frame.msg.currentTarget m.world mf.world)

/-- **The complete spec**: `ERC20Spec`, `permit` (for a token that has it) and malformed
calldata. -/
structure ERC20Spec.Complete (code : ByteArray) (abs : TokenAbs σ) (M : TokenModel σ Address E)
    (g₀ : Nat) (sel : List Nat) (ops : Address → ByteArray → ℕ → Option E)
    (rec : Option (Machine → ℕ → Address)) : Prop where
  spec : ERC20Spec code abs M g₀ sel ops
  permit : ∀ r, rec = some r → PermitSpec code abs M g₀ r
  malformed : MalformedSpec code abs M ops

end QEDefi.ERC20.Spec
