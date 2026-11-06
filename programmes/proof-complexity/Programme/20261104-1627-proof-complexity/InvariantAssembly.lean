import Programme.«20261102-0635-proof-complexity».StepSix

/-! Assembly interface only. Concrete matching reduction and its span
compatibilities remain obligations. No hole-avoidance or rank assertion is
assumed implicitly. -/
namespace Programme.«20261104-1627-proof-complexity».InvariantAssembly

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC
open Programme.«20261102-0635-proof-complexity».StepSix

theorem unit_exclusion (W : Nat → Poly Nat → Prop) (D : Nat)
    (zero : ¬ W 0 Poly.one)
    (nd : ∀ e, 1 ≤ e → e ≤ D → ∀ P, W e P → P.deg ≤ e - 1 → W (e - 1) P) :
    ¬ W D Poly.one := by
  have h : ∀ e, e ≤ D → ¬ W e Poly.one := by
    intro e
    induction e with
    | zero => intro _; exact zero
    | succ e ih =>
      intro he hu
      apply ih (by omega)
      exact nd (e + 1) (by omega) he Poly.one hu (by rw [deg_one]; omega)
  exact h D (Nat.le_refl D)

/-- Explicit compatibility obligations, not an assertion about concrete spans. -/
structure SpanRules (p D : Nat) (A : List (Poly Nat))
    (W : Nat → Poly Nat → Prop) : Prop where
  axiom_mem : ∀ P ∈ A, P.deg ≤ D → W D P
  boolean_mem : ∀ x, 2 ≤ D → W D (boolAx x)
  linear_mem : ∀ u v P Q, W D P → W D Q → W D (lc u v P Q)
  equal_mem : ∀ P Q, W D P → PEq p P Q → Q.deg ≤ D → W D Q
  multiply_mem : ∀ x P, W (D - 1) P → P.deg + 1 ≤ D → W D (P.mulVar x)

/-- Assemble StepSix from a NoDrop chain and explicit rule compatibilities. -/
def invariant {p D : Nat} {A : List (Poly Nat)}
    (W : Nat → Poly Nat → Prop) (rules : SpanRules p D A W)
    (zero : ¬ W 0 Poly.one)
    (nd : ∀ e, 1 ≤ e → e ≤ D → ∀ P, W e P → P.deg ≤ e - 1 → W (e - 1) P) :
    Invariant p D A where
  top := W D
  lower := W (D - 1)
  axiom_mem := rules.axiom_mem
  boolean_mem := rules.boolean_mem
  linear_mem := rules.linear_mem
  equal_mem := rules.equal_mem
  nodrop := by
    intro P hP hd
    by_cases hD : D = 0
    · subst D; exact hP
    · exact nd D (by omega) (Nat.le_refl D) P hP hd
  multiply_mem := rules.multiply_mem
  unit := unit_exclusion W D zero nd

theorem der_mono {p d D : Nat} {A : List (Poly Nat)} {P : Poly Nat}
    (hd : d ≤ D) (h : Der p A d P) : Der p A D P := by
  induction h with
  | ax P hA hP => exact Der.ax P hA (by omega)
  | bool x hx => exact Der.bool x (by omega)
  | lin u v P Q _ _ ihP ihQ => exact Der.lin u v P Q ihP ihQ
  | mul x P _ hP ih => exact Der.mul x P ih (by omega)
  | eq P Q _ he hQ ih => exact Der.eq P Q ih he (by omega)

theorem no_refutation_le {p D : Nat} {A : List (Poly Nat)}
    (W : Nat → Poly Nat → Prop) (rules : SpanRules p D A W)
    (zero : ¬ W 0 Poly.one)
    (nd : ∀ e, 1 ≤ e → e ≤ D → ∀ P, W e P → P.deg ≤ e - 1 → W (e - 1) P)
    {d : Nat} (hd : d ≤ D) : ¬ Refutes p A d := by
  intro h
  exact no_refutation (invariant W rules zero nd) (der_mono hd h)

end Programme.«20261104-1627-proof-complexity».InvariantAssembly

#print axioms Programme.«20261104-1627-proof-complexity».InvariantAssembly.unit_exclusion
#print axioms Programme.«20261104-1627-proof-complexity».InvariantAssembly.invariant
#print axioms Programme.«20261104-1627-proof-complexity».InvariantAssembly.der_mono
#print axioms Programme.«20261104-1627-proof-complexity».InvariantAssembly.no_refutation_le
