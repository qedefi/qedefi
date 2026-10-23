import QEDefi.Actor.Derive

/-!
# The standard action vocabulary

Capabilities `(a, p)` with `p : Action A M H` mirror EVM frames, so that a model's rules can
later be checked against bytecode (a frame at `a` that issues a call, a frame at `a` that gets
past its guard):

- `(b, call t m)`: `b` can be made to send message `m` to `t` (`msg.sender = b` at `t`);
- `(b, delegate t m)`: `b` can be made to `DELEGATECALL` `t` with `m` (`t`'s code runs on `b`'s
  storage, with `b`'s authority);
- `(o, sign h)`: `o` approves digest `h` (a signature, or approval stored on chain);
- `(t, act m)`: `t` executes `m` past its access check, i.e. performs `m`'s effect.

`M` is the system's message type (functions with arguments; a function that acts on behalf of
an account other than `msg.sender`, as in ERC-2771 or the EVC, carries that account in `M`).
A key performs every action. The rule shapes below cover the systems of
`docs/access-control.md`:

- `endpoint t may`: `t` acts on `m` from sender `b` when `may s b m` (owner, role, ward, ACL,
  bitmap, `canCall` of an authority whose answer is in the state);
- `relay c out`: when `c` acts on `m`, it issues the calls `out s m` (a Safe or timelock
  executing a transaction, a proxy forwarding to its implementation, a module calling its
  Safe);
- `quorum c Q`: `c` acts on `m` when the approvals `Q s m` are derivable (thresholds of
  signatures, weighted votes, stored approvals);
- `facts F`: capabilities a state grants without any premise (stored consent such as approved
  hashes and scheduled operations, open functions such as an uninitialised initialiser).
-/

namespace QEDefi.Actor

/-- What a principal can be made to do. -/
inductive Action (A M H : Type) where
  /-- Send message `m` to `target`. -/
  | call (target : A) (m : M)
  /-- `DELEGATECALL` `target` with message `m`. -/
  | delegate (target : A) (m : M)
  /-- Approve digest `h`. -/
  | sign (h : H)
  /-- Execute `m` past its access check (as the message's receiver). -/
  | act (m : M)
  deriving DecidableEq

variable {S A M H : Type}

/-- Rules over the standard vocabulary. -/
abbrev ARules (S A M H : Type) := Rules S A (Action A M H)

/-- **A guarded endpoint**: `t` acts on `m` sent by `b` when `may s b m`. -/
def endpoint (t : A) (may : S → A → M → Prop) : ARules S A M H := fun s q X =>
  ∃ b m, q = (t, .act m) ∧ may s b m ∧ X = {(b, .call t m)}

/-- **A relay**: acting on `m`, `c` issues the actions `out s m` (calls, delegate calls). -/
def relay (c : A) (out : S → M → Action A M H → Prop) : ARules S A M H := fun s q X =>
  ∃ m, q.1 = c ∧ out s m q.2 ∧ X = {(c, .act m)}

/-- **A quorum**: `c` acts on `m` when all of one of the approval sets `Q s m` are derivable. -/
def quorum (c : A) (Q : S → M → Set (Set (A × Action A M H))) : ARules S A M H := fun s q X =>
  ∃ m, q = (c, .act m) ∧ X ∈ Q s m

/-- **Facts**: capabilities granted by the state without premise. -/
def facts (F : S → A × Action A M H → Prop) : ARules S A M H := fun s q X => F s q ∧ X = ∅

/-- The approvals of a `k`-of-`owners` threshold on digest `h`. -/
def sigThreshold [DecidableEq A] (owners : Finset A) (k : ℕ) (h : H) :
    Set (Set (A × Action A M H)) :=
  threshold owners k (fun o => (o, .sign h))

/-! ## Deriving through each shape -/

variable {R : ARules S A M H} {s : S} {T : Set A}

theorem Derives.endpoint {t b : A} {may : S → A → M → Prop} {m : M}
    (hR : ∀ q X, QEDefi.Actor.endpoint t may s q X → R s q X) (hm : may s b m)
    (h : Derives R s T (b, .call t m)) : Derives R s T (t, .act m) :=
  Derives.single (hR _ _ ⟨b, m, rfl, hm, rfl⟩) h

theorem Derives.relay {c : A} {out : S → M → Action A M H → Prop} {m : M} {p : Action A M H}
    (hR : ∀ q X, QEDefi.Actor.relay c out s q X → R s q X) (ho : out s m p)
    (h : Derives R s T (c, .act m)) : Derives R s T (c, p) :=
  Derives.single (hR _ _ ⟨m, rfl, ho, rfl⟩) h

theorem Derives.quorum {c : A} {Q : S → M → Set (Set (A × Action A M H))} {m : M}
    {X : Set (A × Action A M H)} (hR : ∀ q X, QEDefi.Actor.quorum c Q s q X → R s q X)
    (hX : X ∈ Q s m) (h : ∀ r ∈ X, Derives R s T r) : Derives R s T (c, .act m) :=
  Derives.rule (hR _ _ ⟨m, rfl, hX⟩) h

theorem Derives.facts {F : S → A × Action A M H → Prop} {q : A × Action A M H}
    (hR : ∀ q X, QEDefi.Actor.facts F s q X → R s q X) (hF : F s q) : Derives R s T q :=
  Derives.fact (hR _ _ ⟨hF, rfl⟩)

end QEDefi.Actor
