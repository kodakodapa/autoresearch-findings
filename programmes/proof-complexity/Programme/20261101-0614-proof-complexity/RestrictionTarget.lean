import Programme.«20261031-2024-proof-complexity».NativeIter

namespace Programme.«20261101-0614-proof-complexity».RestrictionTarget
open Programme.«20261031-2024-proof-complexity».NativeIter

/-- inl is a constant; inr is a target variable. -/
abbrev Substitution := Var → Bool ⊕ Var

def literal (ρ : Substitution) (l : Lit) : Bool ⊕ Lit :=
  match ρ l.1 with
  | .inl b => .inl (b == l.2)
  | .inr v => .inr (v, l.2)

/-- None is a satisfied clause; some [] is an empty clause.
No deduplication: formal clause lengths remain visible. -/
def clause (ρ : Substitution) : Clause → Option Clause
  | [] => some []
  | l :: c => match literal ρ l with
    | .inl true => none
    | .inl false => clause ρ c
    | .inr k => (clause ρ c).map (k :: ·)

/-- An unproved target, not an assertion of the principle. -/
def TransportPrinciple : Prop :=
  ∀ (ρ : Substitution) (F G : List Clause) (d : Nat),
    (∀ c ∈ F, ∀ t, clause ρ c = some t → t ∈ G) →
    Refutes F d → Refutes G d

end Programme.«20261101-0614-proof-complexity».RestrictionTarget
