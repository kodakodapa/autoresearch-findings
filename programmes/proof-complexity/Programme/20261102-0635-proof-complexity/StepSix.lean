import Programme.«20261029-1156-proof-complexity».StdPC

/-! Conditional ordinary-PC induction for Proof A, step 6.
`top` and `lower` are predicates on ordinary polynomials: in the intended
application they are the inverse images of W_D and W_(D-1) under matching
reduction. No existence or concrete identification of those spaces is assumed.
Only the top-level NoDrop implication is used. -/
namespace Programme.«20261102-0635-proof-complexity».StepSix

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC

/-- Explicit hypotheses needed to pull the reduced-space argument back to
ordinary syntactic polynomial calculus. `unit` is U_D; `nodrop` is the
needed direction of ND_D. The Boolean and equality fields ensure that
reduction respects all rules of the canonical calculus. -/
structure Invariant (p D : Nat) (A : List (Poly Nat)) where
  top : Poly Nat → Prop
  lower : Poly Nat → Prop
  axiom_mem : ∀ P ∈ A, P.deg ≤ D → top P
  boolean_mem : ∀ x, 2 ≤ D → top (boolAx x)
  linear_mem : ∀ u v P Q, top P → top Q → top (lc u v P Q)
  equal_mem : ∀ P Q, top P → PEq p P Q → Q.deg ≤ D → top Q
  nodrop : ∀ P, top P → P.deg ≤ D - 1 → lower P
  multiply_mem : ∀ x P, lower P → P.deg + 1 ≤ D → top (P.mulVar x)
  unit : ¬ top Poly.one

/-- Each line is in the top space: the multiplication case first applies
NoDrop, then the lower-to-top multiplication inclusion. -/
theorem lines_mem {p D : Nat} {A : List (Poly Nat)}
    (W : Invariant p D A) {P : Poly Nat} (h : Der p A D P) : W.top P := by
  induction h with
  | ax P hA hd => exact W.axiom_mem P hA hd
  | bool x hd => exact W.boolean_mem x hd
  | lin u v P Q _ _ hP hQ => exact W.linear_mem u v P Q hP hQ
  | mul x P _ hd hP =>
      exact W.multiply_mem x P (W.nodrop P hP (by omega)) hd
  | eq P Q _ he hd hP => exact W.equal_mem P Q hP he hd

/-- ND_D, U_D and the explicit reduced-space rule compatibilities exclude
an ordinary degree-D PC refutation. This does not assert those hypotheses
for onto-FPHP or imply a semantic-PPC lower bound. -/
theorem no_refutation {p D : Nat} {A : List (Poly Nat)}
    (W : Invariant p D A) : ¬ Refutes p A D := by
  intro h
  exact W.unit (lines_mem W h)

end Programme.«20261102-0635-proof-complexity».StepSix

#print axioms Programme.«20261102-0635-proof-complexity».StepSix.lines_mem
#print axioms Programme.«20261102-0635-proof-complexity».StepSix.no_refutation
