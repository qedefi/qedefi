import EvmLogic.Program.Summary
import EvmLogic.Solidity.Memory
import EvmLogic.Solidity.Immutables
import EvmLogic.Solidity.Steps

/-!
# Constructors: top-level creations and literal memories

A top-level creation (`processMessageCall` of a message with `target = none`) starts a frame of
kind `.create` running the init code at the new address (`createMachine`), after
`beginCreate` (the nonce of the new account incremented). When the frame returns `out`, the
code `out` is deposited (`depositCode`) and the result is `topLevelResult none …`
(`processMessageCall_create_of_halts`).

Constructors work on memory that is concrete up to a few symbolic words. Where the symbolic
executor cannot normalise a memory term, the proofs replace it by a literal `⟨b⟩` (checked by
the kernel, `Memory.eq_mk_of_toList`) and read it with `Memory.loadWord_mk` / `Memory.read_mk`,
which the code-immediate simproc then evaluates.
-/

namespace EvmLean.Memory
open EvmLean.Interpreter

theorem read_mk (b : ByteArray) (off len : Nat) : Memory.read ⟨b⟩ off len = readBytes b off len :=
  (readBytes_eq_readPadded b off len).symm

theorem loadWord_mk (b : ByteArray) (off : Nat) :
    Memory.loadWord ⟨b⟩ off = Bytes.toWord (readBytes b off 32) := by
  rw [loadWord, read_mk]

theorem size_mk (b : ByteArray) : Memory.size ⟨b⟩ = b.size := rfl

theorem bytes_mk (b : ByteArray) : (⟨b⟩ : Memory).bytes = b := rfl

theorem eq_mk_of_toList {m : Memory} {b : ByteArray} (h : m.bytes.data.toList = b.data.toList) :
    m = ⟨b⟩ := by
  obtain ⟨mb⟩ := m
  exact congrArg Memory.mk (EvmLogic.Solidity.eq_of_data_toList_eq h)

theorem ext_bytes {m m' : Memory} (h : m.bytes = m'.bytes) : m = m' := by
  cases m; cases m'; cases h; rfl

theorem expand_of_le {m : Memory} {off len : Nat} (h : off + len ≤ m.size)
    (h32 : m.size % 32 = 0) : m.expand off len = m :=
  expand_eq_self_of_le h h32

theorem size_write_of_le {m : Memory} {off : Nat} {data : ByteArray}
    (h : off + data.size ≤ m.size) (h32 : m.size % 32 = 0) : (m.write off data).size = m.size := by
  rw [size_write, expand_of_le h h32]

/-- A write inside memory (no expansion) of `a ++ b` is the write of `a`, then of `b`. -/
theorem write_append_of_le {m : Memory} {off : Nat} {a b : ByteArray}
    (h : off + a.size + b.size ≤ m.size) (h32 : m.size % 32 = 0) :
    m.write off (a ++ b) = (m.write off a).write (off + a.size) b := by
  have ha : off + a.size ≤ m.size := by omega
  have hab : off + (a ++ b).size ≤ m.size := by rw [ByteArray.size_append]; omega
  have hs1 := size_write_of_le ha h32
  apply ext_bytes
  apply Bytes.ext_getD
  · show (m.write off (a ++ b)).size = ((m.write off a).write (off + a.size) b).size
    rw [size_write_of_le hab h32, size_write_of_le (by rw [hs1]; omega) (by rw [hs1]; exact h32),
      hs1]
  · intro j _
    rw [getD_bytes_write, getD_bytes_write, getD_bytes_write, Bytes.getD_append,
      ByteArray.size_append]
    by_cases h1 : off ≤ j ∧ j < off + a.size
    · have h2 : ¬ (off + a.size ≤ j ∧ j < off + a.size + b.size) := by omega
      have h3 : off ≤ j ∧ j < off + (a.size + b.size) := by omega
      have h4 : j - off < a.size := by omega
      simp only [h1, h2, h3, h4, and_self, ↓reduceIte]
    · by_cases h2 : off + a.size ≤ j ∧ j < off + a.size + b.size
      · have h3 : off ≤ j ∧ j < off + (a.size + b.size) := by omega
        have h4 : ¬ j - off < a.size := by omega
        simp only [h2, h3, h4, and_self, ↓reduceIte]
        congr 1; omega
      · have h3 : ¬ (off ≤ j ∧ j < off + (a.size + b.size)) := by omega
        simp only [h1, h2, h3, ↓reduceIte]

theorem size_storeWord_of_le {m : Memory} {off : Nat} {w : Word} (h : off + 32 ≤ m.size)
    (h32 : m.size % 32 = 0) : (m.storeWord off w).size = m.size :=
  size_write_of_le (by rw [Bytes.size_ofWord]; exact h) h32

/-- A write inside memory of a word followed by `b` is a `storeWord`, then the write of `b`. -/
theorem write_ofWord_append_of_le {m : Memory} {off : Nat} {w : Word} {b : ByteArray}
    (h : off + 32 + b.size ≤ m.size) (h32 : m.size % 32 = 0) :
    m.write off (Bytes.ofWord w ++ b) = (m.storeWord off w).write (off + 32) b := by
  rw [write_append_of_le (by rw [Bytes.size_ofWord]; exact h) h32, Bytes.size_ofWord]
  rfl

/-- `MCOPY` as a write of the source bytes. -/
theorem mcopy_eq (mem : Memory) (dst src len : Nat) :
    mem.mcopy dst src len = ((mem.expand src len).expand dst len).write dst (mem.read src len) := by
  simp only [mcopy, read_expand]

theorem read_write_of_size (m : Memory) (off n : Nat) (data : ByteArray) (h : data.size = n) :
    (m.write off data).read off n = data := by
  subst h; exact read_write m off data

theorem loadWord_write_of_disjoint (m : Memory) (off off' : Nat) (data : ByteArray)
    (h : off' + 32 ≤ off ∨ off + data.size ≤ off') :
    (m.write off data).loadWord off' = m.loadWord off' := by
  rw [loadWord, loadWord, read_write_of_disjoint m off off' 32 data h]

theorem getD_ofWord_zero (i : Nat) : Bytes.getD (Bytes.ofWord 0) i = 0 := by
  have h : Bytes.ofWord 0 = Bytes.zeros 32 :=
    EvmLogic.Solidity.eq_of_data_toList_eq (by decide +kernel)
  rw [h, Bytes.getD_zeros]

/-- Reading a word whose tail was overwritten by a zero word: the head, then zeros. -/
theorem read_storeWord_zero_tail (m : Memory) (off off' : Nat) (h : off ≤ off')
    (h' : off' ≤ off + 32) :
    (m.storeWord off' 0).read off 32 = m.read off (off' - off) ++ Bytes.zeros (32 - (off' - off)) := by
  apply Bytes.ext_getD
  · rw [read, Bytes.size_readPadded, ByteArray.size_append, read, Bytes.size_readPadded,
      Bytes.size_zeros]
    omega
  · intro j hj
    rw [read, Bytes.size_readPadded] at hj
    simp only [read, Bytes.getD_readPadded, hj, ↓reduceIte, storeWord, getD_bytes_write,
      Bytes.getD_append, Bytes.size_readPadded, Bytes.size_ofWord, getD_ofWord_zero,
      Bytes.getD_zeros]
    by_cases h1 : j < off' - off
    · have h2 : ¬ (off' ≤ off + j ∧ off + j < off' + 32) := by omega
      simp only [h1, h2, ↓reduceIte]
    · have h2 : off' ≤ off + j ∧ off + j < off' + 32 := by omega
      simp only [h1, h2, and_self, ↓reduceIte]

/-- Reading a word whose tail was overwritten by a zero word: the head, then zeros. -/
theorem loadWord_storeWord_zero_tail (m : Memory) (off off' : Nat) (w : Word) (hw : w = 0)
    (h : off ≤ off') (h' : off' ≤ off + 32) :
    (m.storeWord off' w).loadWord off =
      Bytes.toWord (m.read off (off' - off) ++ Bytes.zeros (32 - (off' - off))) := by
  rw [loadWord, hw, read_storeWord_zero_tail m off off' h h']

/-- `loadWord_storeWord_zero_tail` for the literal `0#256` the executor produces. -/
theorem loadWord_storeWord_zero_tail' (m : Memory) (off off' : Nat) (h : off ≤ off')
    (h' : off' ≤ off + 32) :
    (m.storeWord off' 0#256).loadWord off =
      Bytes.toWord (m.read off (off' - off) ++ Bytes.zeros (32 - (off' - off))) :=
  loadWord_storeWord_zero_tail m off off' _ rfl h h'

theorem read_write_extract (m : Memory) (off n : Nat) (w : Word) (h : n ≤ 32) :
    (m.write off ((Bytes.ofWord w).extract 0 n)).read off n = (Bytes.ofWord w).extract 0 n :=
  read_write_of_size _ _ _ _ (by rw [ByteArray.size_extract, Bytes.size_ofWord]; omega)

end EvmLean.Memory

namespace EvmLogic.Program
open EvmLean EvmLean.Interpreter

/-! ## Top-level creations -/

/-- The machine of a top-level creation of `msg` in `w`: the new account's nonce incremented,
the account marked created, a `.create` frame running `msg.code`. -/
def createMachine (ctx : Context) (w : World) (tr : TransientStorage) (msg : Message) :
    Machine where
  ctx := ctx
  precompiles := PrecompileImpl.standard ctx
  world := incrementNonce w msg.currentTarget
  transient := tr
  originalWorld := w
  createdAccounts := (∅ : AddressSet).insert msg.currentTarget
  frame := Frame.init msg .create (w, tr)
  parents := []

theorem fresh_createMachine (ctx : Context) (w : World) (tr : TransientStorage) (msg : Message) :
    Fresh msg.code (createMachine ctx w tr msg) :=
  fresh_init _ msg _ _ rfl

/-- `initMachine` of a creation at a deployable address, with no value, at depth zero. -/
theorem initMachine_create {pre : PrecompileImpl} {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} (htarget : msg.target = none)
    (hd : accountDeployable w msg.currentTarget = true) (hvalue : msg.value = 0)
    (hdepth : msg.depth = 0) :
    initMachine pre ctx w tr msg = .inr
      { ctx, precompiles := pre, world := incrementNonce w msg.currentTarget, transient := tr,
        originalWorld := w, createdAccounts := (∅ : AddressSet).insert msg.currentTarget,
        frame := Frame.init msg .create (w, tr), parents := [] } := by
  simp only [initMachine, hdepth, htarget, hvalue, hd, beginCreate, transferValue,
    Gas.stackDepthLimit]
  simp

/-- **Top-level glue for creations.** A frame summary of `createMachine` gives the result of
`processMessageCall` for all large enough fuel. -/
theorem processMessageCall_create_of_halts {ctx : Context} {w : World} {tr : TransientStorage}
    {msg : Message} {H : Machine → Outcome → Prop}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hdel : delegatedAddress? msg.code = none) (htarget : msg.target = none)
    (hd : accountDeployable w msg.currentTarget = true) (hval : msg.value = 0)
    (hdepth : msg.depth = 0) (h : Halts (createMachine ctx w tr msg) H) :
    ∃ n mf o, H mf o ∧ SameFrame (createMachine ctx w tr msg) mf ∧ ∀ fuel, n ≤ fuel →
      processMessageCall fuel ctx w tr msg = .ok (topLevelResult msg.target
        (frameResult mf o).2.1 (frameResult mf o).2.2 (frameResult mf o).1) := by
  obtain ⟨n, mf, o, hH, hs, hrun⟩ := h.run rfl
  refine ⟨n, mf, o, hH, hs, fun fuel hle => ?_⟩
  rw [processMessageCall_eq_run hdeleg hdel
    (initMachine_create (pre := PrecompileImpl.standard ctx) htarget hd hval hdepth)]
  exact hrun fuel hle

/-! ## Code deposit and the result of a creation -/

theorem depositCode_ok {fork : Fork} {g : Nat} {out : ByteArray} (h0 : out[0]? ≠ some 0xef)
    (hg : 200 * out.size ≤ g) (hs : out.size ≤ Gas.maxCodeSize fork) :
    depositCode fork g out = .ok (g - 200 * out.size) := by
  have hc : Gas.codeDepositCost out.size = 200 * out.size := rfl
  simp only [depositCode, h0, ↓reduceIte, hc, Nat.not_lt.mpr hg, Nat.not_lt.mpr hs]

theorem frameResult_success_create {mf : Machine} {out : ByteArray} {g : Nat}
    (hk : mf.frame.kind = .create) (hd : depositCode mf.ctx.fork mf.frame.gasLeft out = .ok g) :
    frameResult mf (.success out) =
      ({ gasLeft := g, error := none, reverted := false, output := out, sub := mf.frame.sub,
         target := mf.frame.msg.currentTarget, kind := mf.frame.kind },
       setCode mf.world mf.frame.msg.currentTarget out, mf.transient) := by
  simp only [frameResult, hk, hd]

/-- A successful creation frame: the result of the top-level creation is successful and its
world is the frame's final world with `out` deposited at the new address. -/
theorem topLevelResult_create {mf : Machine} {out : ByteArray} {g : Nat}
    (hk : mf.frame.kind = .create) (hd : depositCode mf.ctx.fork mf.frame.gasLeft out = .ok g) :
    let r := topLevelResult none (frameResult mf (.success out)).2.1
      (frameResult mf (.success out)).2.2 (frameResult mf (.success out)).1
    r.success = true ∧ r.world = setCode mf.world mf.frame.msg.currentTarget out := by
  rw [frameResult_success_create hk hd]
  exact ⟨by simp [ChildResult.success], by simp⟩

/-! ## Worlds -/

theorem account_modifyState (w : World) (a : Address) (f : Account → Account) (b : Address)
    (he : (f (w.account a)).isEmpty = false) :
    (modifyState w a f).account b = if b = a then f (w.account a) else w.account b := by
  unfold modifyState
  dsimp only
  simp only [he, Bool.false_eq_true, ↓reduceIte]
  by_cases hb : b = a
  · subst hb; simp [World.account]
  · have hne : ¬ a = b := fun e => hb e.symm
    simp [World.account, Std.ExtTreeMap.getD_insert, hne, hb]

end EvmLogic.Program

/-! ## Bytes of patched code -/

namespace Verified.Solmate.Constructor
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Solidity EvmLogic.Program

theorem getD_eq_toList (b : ByteArray) (k : Nat) : Bytes.getD b k = (b.data.toList[k]?).getD 0 := by
  rw [← getElem?_byteArray]
  unfold Bytes.getD
  by_cases h : k < b.size
  · simp only [h, ↓reduceDIte, getElem?_pos b k h, Option.getD_some]
  · simp only [h, ↓reduceDIte, getElem?_neg b k h, Option.getD_none]

theorem readBytes_toList (a : ByteArray) (off n : Nat) (h : off + n ≤ a.size) (h' : off < a.size) :
    (readBytes a off n).data.toList = (a.data.toList.drop off).take n := by
  rw [readBytes_eq_readPadded]
  unfold Bytes.readPadded
  rw [ite_eq_left_iff.mpr (fun h'' => absurd h' h'')]
  simp [ByteArray.data_extract, Bytes.zeros, show min (off + n) a.size = off + n by omega]

theorem getD_patch_in (c : ByteArray) (ps₁ ps₂ : List (Nat × Word)) (o : Nat) (w : Word)
    (hfit : o + 32 ≤ c.size) (h₂ : ∀ o' ∈ ps₂.map Prod.fst, o + 32 ≤ o' ∨ o' + 32 ≤ o)
    (j : Nat) (h1 : o ≤ j) (h2 : j < o + 32) :
    Bytes.getD (patchWords c (ps₁ ++ (o, w) :: ps₂)) j = Bytes.getD (Bytes.ofWord w) (j - o) := by
  rw [getD_eq_toList, getD_eq_toList, data_patchWords, show j = o + (j - o) by omega,
    getElem?_patchList_last _ _ _ _ _ (by rw [Array.length_toList]; exact hfit) h₂ _ (by omega)]
  congr 2; omega

theorem getD_patch_out (c : ByteArray) (ps : List (Nat × Word)) (j : Nat)
    (h : ∀ o ∈ ps.map Prod.fst, j < o ∨ o + 32 ≤ j) :
    Bytes.getD (patchWords c ps) j = Bytes.getD c j := by
  rw [getD_eq_toList, getD_eq_toList, data_patchWords, getElem?_patchList_of_disjoint _ _ _ h]

/-! ## Patches byte by byte

`patchFn ps g j`: byte `j` after writing the words `ps` in order over the bytes `g`. Both a
patched code (`getD_patchWords`) and a memory after word stores (`getD_storeWords`) are of this
form, so a constructor's returned code is compared with `runtimeCodeWith` byte by byte. -/

/-- Byte `j` after writing the words of `ps`, in order, over `g`. -/
def patchFn : List (Nat × Word) → (Nat → UInt8) → Nat → UInt8
  | [], g, j => g j
  | p :: ps, g, j => patchFn ps (fun j => if p.1 ≤ j ∧ j < p.1 + 32 then
      Bytes.getD (Bytes.ofWord p.2) (j - p.1) else g j) j

theorem patchFn_congr (ps : List (Nat × Word)) {g g' : Nat → UInt8} {j : Nat} (h : g j = g' j) :
    patchFn ps g j = patchFn ps g' j := by
  induction ps generalizing g g' with
  | nil => exact h
  | cons p ps ih => exact ih (by simp only [h])

theorem patchWords_cons (c : ByteArray) (p : Nat × Word) (ps : List (Nat × Word)) :
    patchWords c (p :: ps) = patchWords (patchWords c [p]) ps := by
  apply eq_of_data_toList_eq
  simp only [data_patchWords, patchList, List.foldl_cons, List.foldl_nil]

theorem patchWords_nil (c : ByteArray) : patchWords c [] = c := by
  apply eq_of_data_toList_eq
  simp only [data_patchWords, patchList, List.foldl_nil]

theorem getD_patchWords_single (c : ByteArray) (o : Nat) (w : Word) (h : o + 32 ≤ c.size)
    (j : Nat) : Bytes.getD (patchWords c [(o, w)]) j =
      if o ≤ j ∧ j < o + 32 then Bytes.getD (Bytes.ofWord w) (j - o) else Bytes.getD c j := by
  split
  · rename_i hj
    exact getD_patch_in c [] [] o w h (by simp) j hj.1 hj.2
  · rename_i hj
    have ho : ∀ o' ∈ [(o, w)].map Prod.fst, j < o' ∨ o' + 32 ≤ j := by
      simp only [List.map_cons, List.map_nil, List.mem_singleton, forall_eq]; omega
    exact getD_patch_out c [(o, w)] j ho

/-- **Patched code, byte by byte** (every window inside the code). -/
theorem getD_patchWords (ps : List (Nat × Word)) (c : ByteArray)
    (h : ∀ p ∈ ps, p.1 + 32 ≤ c.size) (j : Nat) :
    Bytes.getD (patchWords c ps) j = patchFn ps (Bytes.getD c) j := by
  induction ps generalizing c with
  | nil => simp only [patchFn, patchWords_nil]
  | cons p ps ih =>
    obtain ⟨o, w⟩ := p
    rw [patchWords_cons, ih _ (fun q hq => by
      rw [size_patchWords]; exact h q (List.mem_cons_of_mem _ hq))]
    simp only [patchFn]
    apply patchFn_congr
    exact getD_patchWords_single c o w (h _ (List.mem_cons_self ..)) j

/-- Word stores at the given offsets, in order, each after the expansion `MSTORE` does. -/
def storeWords (M : Memory) (ps : List (Nat × Word)) : Memory :=
  ps.foldl (fun m p => (m.expand p.1 32).storeWord p.1 p.2) M

/-- **Memory after word stores, byte by byte.** -/
theorem getD_storeWords (ps : List (Nat × Word)) (M : Memory) (j : Nat) :
    Bytes.getD (storeWords M ps).bytes j = patchFn ps (Bytes.getD M.bytes) j := by
  induction ps generalizing M with
  | nil => simp only [storeWords, List.foldl_nil, patchFn]
  | cons p ps ih =>
    simp only [storeWords, List.foldl_cons, patchFn] at ih ⊢
    rw [ih]
    apply patchFn_congr
    simp only [Memory.storeWord, Memory.getD_bytes_write, Memory.getD_bytes_expand,
      Bytes.size_ofWord]

/-! ## Accounts -/

theorem account_incrementNonce (w : World) (a b : Address) :
    (incrementNonce w a).account b =
      if b = a then { w.account a with nonce := (w.account a).nonce + 1 } else w.account b :=
  account_modifyState w a _ b (by simp [Account.isEmpty])

theorem code_incrementNonce' (w : World) (a b : Address) :
    (incrementNonce w a).code b = w.code b := by
  simp only [World.code, incrementNonce, account_modifyState w a
    (fun acc => { acc with nonce := acc.nonce + 1 }) b (by simp [Account.isEmpty])]
  split <;> simp_all

theorem account_setCode (w : World) (a : Address) (out : ByteArray) (hs : out.size ≠ 0)
    (b : Address) :
    (setCode w a out).account b = if b = a then { w.account a with code := out } else w.account b :=
  account_modifyState w a _ b (by simp [Account.isEmpty, hs])

theorem account_sstore (w : World) (a : Address) (k v : Word) (b : Address) :
    (w.sstore a k v).account b =
      if b = a then { w.account a with storage := (w.account a).storage.set k v }
      else w.account b := by
  split
  · subst_vars; exact World.account_modify_self _ _ _
  · exact World.account_modify_ne _ _ ‹_›

theorem storage_empty_of_deployable {w : World} {a : Address} (hd : accountDeployable w a = true) :
    (w.account a).storage = ∅ := by
  simp only [accountDeployable, Bool.and_eq_true, decide_eq_true_eq] at hd
  exact Std.ExtTreeMap.isEmpty_iff.mp hd.2

theorem sload_incrementNonce_of_deployable {w : World} {a : Address} (k : Word)
    (hd : accountDeployable w a = true) : (incrementNonce w a).sload a k = 0#256 := by
  simp only [World.sload, incrementNonce, account_modifyState w a
    (fun acc => { acc with nonce := acc.nonce + 1 }) a (by simp [Account.isEmpty]), ↓reduceIte]
  simp only [accountDeployable, Bool.and_eq_true, decide_eq_true_eq] at hd
  rw [Std.ExtTreeMap.isEmpty_iff.mp hd.2]
  exact Storage.get_empty k

end Verified.Solmate.Constructor

/-- Read a word or bytes of a memory built by a chain of stores, `MCOPY`s and writes at numeral
offsets, with extra facts `hs`. -/
syntax "mem_fact" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| mem_fact $[[$hs,*]]?) => do
    let hs := (hs.map (·.getElems)).getD #[]
    `(tactic| simp (disch := first | decide | (simp (disch := decide) only [ByteArray.size_extract,
        EvmLean.Bytes.size_ofWord, EvmLean.Bytes.size_zeros, Nat.min_def] <;> decide)) only
      [EvmLean.Memory.loadWord_storeWord, EvmLean.Memory.loadWord_storeWord_of_disjoint,
      EvmLean.Memory.loadWord_expand, EvmLean.Memory.read_expand,
      EvmLean.Memory.read_storeWord_of_disjoint, EvmLean.Memory.read_storeWord_prefix,
      EvmLean.Memory.read_storeWord, EvmLean.Bytes.toWord_ofWord, EvmLean.Memory.mcopy_eq,
      EvmLean.Memory.loadWord_storeWord_zero_tail, EvmLean.Memory.read_write_of_size,
      EvmLean.Memory.read_write_of_disjoint, EvmLean.Memory.loadWord_write_of_disjoint,
      Nat.reduceSub, Nat.reduceAdd,
      $hs,*])
