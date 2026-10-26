import Verified.WeirdERC20.Common.DataExec
import Verified.Solmate.ERC20.Spec.SubCert
import Verified.OpenZeppelin.ERC20.Spec.LowGas

/-!
# The rest of a frame does not read the calldata

`data_lockstep`: a frame at a machine `ml` described by a closed abstract-interpretation table
whose recorded pcs hold no instruction reading the calldata, the gas, or starting a child
(`dataSafeB`) ends as the same frame with any other calldata, more gas, other parents and
another frame kind (`setData D (hi d x ps k ml)`) does: it fails, or it ends with the same
outcome from a machine whose image is that frame's final machine, with its created accounts
unchanged. The other frame's end is its real exit
(`Exit`), so a summary of it at the top level (where every `Halts` witness is the exit,
`exit_of_halts_top`) transfers.

For a solc 0.4/0.5 token, the table is explored from the entry of a function body, after the
dispatcher has decoded the arguments: dirty calldata (high bits in `address` words, which the
decoder masks away) and the clean calldata of the same call reach that entry with the same
stack, and from there run the same.
-/

namespace Verified.WeirdERC20.Common
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested EvmLogic.GasMono
open EvmLogic.AbsInt
open Verified.Solmate.ERC20.Spec (CertT inCertT_within inCert_recorded recorded)
open Verified.OpenZeppelin.ERC20.Spec (hi setKind exec_setKind)

/-- `ReadsData` as a Boolean. -/
def readsDataB : Opcode → Bool
  | .calldataload | .calldatasize | .calldatacopy => true
  | .gas | .call | .callcode | .delegatecall | .staticcall | .create | .create2 => true
  | _ => false

theorem readsData_iff (op : Opcode) : ReadsData op ↔ readsDataB op = true := by
  cases op <;> simp [ReadsData, readsDataB]

/-- The instruction at a byte (decoded as in the latest fork) reads no calldata, no gas and
starts no child. -/
def dataSafeB (b : UInt8) : Bool := !readsDataB (Opcode.decode .osaka b)

theorem not_readsData_of_safe (fork : Fork) {b : UInt8} (h : dataSafeB b = true) :
    ¬ ReadsData (Opcode.decode fork b) := by
  rw [readsData_iff]
  rcases decode_osaka_or_invalid fork b with h' | h' <;> rw [h']
  · simpa [dataSafeB] using h
  · simp [readsDataB]

theorem readsGasB_of_safe (fork : Fork) {b : UInt8} (h : dataSafeB b = true) :
    readsGasB (Opcode.decode fork b) = false := by
  have h' := not_readsData_of_safe fork h
  rw [readsData_iff] at h'
  cases hop : Opcode.decode fork b <;> rw [hop] at h' <;> simp_all [readsDataB, readsGasB]

/-- The image of a machine: calldata `D`, `d` more gas, message gas `x`, parents `ps`, frame
kind `k`. -/
def img (D : ByteArray) (d x : Nat) (ps : List Frame) (k : FrameKind) (m : Machine) : Machine :=
  setData D (hi d x ps k m)

@[simp] theorem img_world (D : ByteArray) (d x : Nat) (ps : List Frame) (k : FrameKind)
    (m : Machine) : (img D d x ps k m).world = m.world := rfl
@[simp] theorem img_transient (D : ByteArray) (d x : Nat) (ps : List Frame) (k : FrameKind)
    (m : Machine) : (img D d x ps k m).transient = m.transient := rfl
@[simp] theorem img_logs (D : ByteArray) (d x : Nat) (ps : List Frame) (k : FrameKind)
    (m : Machine) : (img D d x ps k m).frame.sub = m.frame.sub := rfl

/-- **One instruction does not read the calldata, the gas, the parents or the frame kind.** -/
theorem exec_img {op : Opcode} (hop : ¬ ReadsData op) {m m' : Machine} {a : Action}
    (h : (exec op).run m = .ok (a, m')) (D : ByteArray) (d x : Nat) (ps : List Frame)
    (k : FrameKind) : (exec op).run (img D d x ps k m) = .ok (a, img D d x ps k m') := by
  have hg : ¬ ReadsGas op := fun hr => hop (by
    cases op <;> simp_all [ReadsGas, ReadsData])
  exact exec_setData _ hop (exec_setKind _ hg (exec_bump _ hg h d x ps) k) D

theorem sameFrame_img {m m' : Machine} (h : SameFrame m m') (D : ByteArray) (d d' x : Nat)
    (ps : List Frame) (k : FrameKind) : SameFrame (img D d x ps k m) (img D d' x ps k m') :=
  ⟨h.ctx, h.precompiles, h.originalWorld, rfl,
    by simp [img, setData, hi, setKind, EvmLogic.Program.Nested.bump, h.msg], h.code,
    h.jumpDests, rfl, h.snapshot⟩

/-- The end of the frame from `ml` against the end (`mfh`, `oh`) of its image: a failure, or
the same outcome from a machine whose image is `mfh`, with the created accounts of `ml`. -/
def DPost (D : ByteArray) (d x : Nat) (ps : List Frame) (k : FrameKind) (ml mfh : Machine)
    (oh : Outcome) (mfl : Machine) (ol : Outcome) : Prop :=
  Failed ol ∨ (ol = oh ∧ mfh = img D d x ps k mfl ∧ mfl.createdAccounts = ml.createdAccounts)

theorem getElem?_of_getD {code : ByteArray} {q : Nat} {b : UInt8} (h : code[q]? = some b) :
    Bytes.getD code q = b := by
  obtain ⟨hlt, he⟩ := getElem?_eq_some_iff.1 h
  rw [getD_eq_getElem hlt, he]

variable {ρ : Nat → Address} {allowed : AVal → Bool} {code : ByteArray} {t : Tree}

set_option maxHeartbeats 1000000 in
/-- **The data lockstep**: from a machine of a data-safe region, the frame ends as its image
does (its real exit), or fails. -/
theorem data_lockstep (hc : CertT ρ allowed code t)
    (hsafe : ∀ q ∈ recorded t, dataSafeB (Bytes.getD code q) = true) (D : ByteArray)
    (d x : Nat) (ps : List Frame) (k : FrameKind) :
    ∀ N ml mfh oh, ml.frame.code = code → InCert ρ t ml →
      Exit (img D d x ps k ml) N mfh oh → Halts ml (DPost D d x ps k ml mfh oh) := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro ml mfh oh hcode hin hex
    obtain ⟨s, ⟨e, imm, ss, hf, hs⟩, hst⟩ := hin
    obtain ⟨b, hb, -, -⟩ := hc.ins.find hf
    rw [← hcode] at hb
    have hin : InCert ρ t ml := ⟨s, ⟨e, imm, ss, hf, hs⟩, hst⟩
    have hsb : dataSafeB b = true := by
      have := hsafe _ (inCert_recorded hin)
      rwa [← hcode, getElem?_of_getD hb] at this
    have hbh : (img D d x ps k ml).frame.code[(img D d x ps k ml).frame.pc]? = some b := hb
    have hop := not_readsData_of_safe ml.ctx.fork hsb
    cases hrun : (exec (Opcode.decode ml.ctx.fork b)).run ml with
    | error err =>
      exact Halts.of_step (step_of_exec_error hb hrun) (.refl ml) (.inl (fun out h => by cases h))
    | ok p =>
      obtain ⟨act, ml'⟩ := p
      have hrunh : (exec (Opcode.decode (img D d x ps k ml).ctx.fork b)).run
          (img D d x ps k ml) = .ok (act, img D d x ps k ml') := exec_img hop hrun D d x ps k
      have hfl := ((exec_frame _ ml).of_run hrun).1
      have hnc := (exec_noChild _ (readsGasB_of_safe ml.ctx.fork hsb) ml).of_run hrun
      cases act with
      | next =>
        have hstepl := step_of_exec_next hb hrun
        have hsteph : step (img D d x ps k ml) = .running (img D d x ps k ml') :=
          step_of_exec_next hbh hrunh
        have hst' := sameFrame_img hfl.same D d d x ps k
        obtain ⟨hN, hex'⟩ := hex.next hsteph hst'
        obtain ⟨hcode', hin'⟩ := inCertT_within hc hcode hin hb hrun (.inl ⟨rfl, rfl⟩)
        have hrec := ih (N - 1) (by omega) ml' mfh oh hcode' hin' hex'
        refine Halts.of_steps (Steps.of_step hstepl hfl.same) (hrec.mono ?_)
        rintro mfl ol - (hf | ⟨h1, h2, h3⟩)
        · exact .inl hf
        · exact .inr ⟨h1, h2, h3.trans hfl.created⟩
      | stop out =>
        have hxh := (exitOf_of_exec hbh hrunh).1 out rfl
        obtain ⟨-, rfl, rfl⟩ := (exit_zero hxh).unique hex
        exact Halts.of_step (step_of_exec_stop hb hrun) hfl.same
          (.inr ⟨rfl, rfl, hfl.created⟩)
      | revert out =>
        have hxh := (exitOf_of_exec hbh hrunh).2 out rfl
        obtain ⟨-, rfl, rfl⟩ := (exit_zero hxh).unique hex
        exact Halts.of_step (step_of_exec_revert hb hrun) hfl.same
          (.inr ⟨rfl, rfl, hfl.created⟩)
      | call req => exact hnc.elim
      | create msg => exact hnc.elim

end Verified.WeirdERC20.Common
