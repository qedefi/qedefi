/-!
# Hard forks

Fork-dependent behaviour is selected by comparing against a `Fork`, e.g.
`if fork ≥ .prague then … else …`. Only forks from Cancun onward are modelled.
-/

namespace EvmLean

/-- Supported hard forks, in activation order. -/
inductive Fork where
  /-- Cancun (Dencun, March 2024): EIP-1153, 4844, 5656, 6780, 7516, 4788. -/
  | cancun
  /-- Prague (Pectra, May 2025): EIP-7702, 2537, 2935, 6110, 7002, 7251, 7623, 7685, 7691. -/
  | prague
  /-- Osaka (Fusaka, December 2025): EIP-7939 (`CLZ`), 7823, 7825, 7883, 7918, 7934, 7951, and
  the per-transaction blob limit. -/
  | osaka
  deriving DecidableEq, Repr, Inhabited

namespace Fork

/-- Position in activation order. -/
def toNat : Fork → Nat
  | cancun => 0
  | prague => 1
  | osaka => 2

instance : LE Fork := ⟨fun a b => a.toNat ≤ b.toNat⟩
instance : LT Fork := ⟨fun a b => a.toNat < b.toNat⟩
instance (a b : Fork) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.toNat ≤ b.toNat))
instance (a b : Fork) : Decidable (a < b) := inferInstanceAs (Decidable (a.toNat < b.toNat))

/-- The fork name used by the Ethereum test fixtures (`network` field). -/
def name : Fork → String
  | cancun => "Cancun"
  | prague => "Prague"
  | osaka => "Osaka"

/-- Parse a fixture `network` name. -/
def ofName? : String → Option Fork
  | "Cancun" => some cancun
  | "Prague" => some prague
  | "Osaka" => some osaka
  | _ => none

end Fork

end EvmLean
