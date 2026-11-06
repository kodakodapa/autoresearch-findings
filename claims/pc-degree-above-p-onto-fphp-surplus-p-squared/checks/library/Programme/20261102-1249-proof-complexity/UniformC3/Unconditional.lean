import Programme.«20261102-1249-proof-complexity».UniformC3.ExplicitCongruence

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Programme.«20261102-1249-proof-complexity».UniformC3.Block
open Programme.«20261027-0607-proof-complexity».Peel (IsPrime units_of_prime fact_unit)

theorem factorial_eq_library (n : Nat) : factorial n =
    Programme.«20261027-0607-proof-complexity».SJ.fact n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [factorial,Programme.«20261027-0607-proof-complexity».SJ.fact,ih]

theorem commonValue_unit {p : Nat} (hp : IsPrime p) :
    ∃ u : Int, Cong p (u * commonValue p) 1 := by
  obtain ⟨v,hv⟩ := fact_unit (units_of_prime hp) (p-1) (Nat.le_refl _)
  rw [← factorial_eq_library] at hv
  have h : Cong p (v * fac (p-1)) 1 := hv
  have hc := cong_mul (cong_mul h h) h
  refine ⟨-(v*v*v),?_⟩
  simpa [commonValue,Int.neg_mul_neg,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm] using hc

/-- An explicit elementary construction for every prime, requiring no square-lift premise.
The scalar is an inverse of the common residue -((p-1)!)^3. -/
theorem squareLiftAssumption (p : Nat) (hp : IsPrime p) : Programme.«20261102-1249-proof-complexity».UniformC3.SquareLiftAssumption p := by
  obtain ⟨u,hu⟩ := commonValue_unit hp
  have hp' : 2 ≤ p := by have := hp.1; omega
  let P := squarePartition p (by omega)
  let C : Certificate p P := {
    value := fun M => u * explicitValue p M
    unit := by
      intro M hF ht
      exact cong_trans (cong_scale (explicit_common_congruence hp' hF ht) u) hu
    row := by
      intro M hF ht i
      have h := explicit_row hp' hF ht i
      change sum3 (fun j => ((capacity p j : Int)-cc M j) * (u*explicitValue p (inc M i j))) = 0
      have he : sum3 (fun j => ((capacity p j : Int)-cc M j) * (u*explicitValue p (inc M i j))) =
          u * sum3 (fun j => ((capacity p j : Int)-cc M j) * explicitValue p (inc M i j)) := by
        simp [sum3,Int.mul_add,Int.mul_assoc,Int.mul_left_comm]
      rw [he,h,Int.mul_zero]
    col := by
      intro M hF ht j
      have h := explicit_col hp' hF ht j
      change sum3 (fun i => ((capacity p i : Int)-rc M i) * (u*explicitValue p (inc M i j))) = 0
      have he : sum3 (fun i => ((capacity p i : Int)-rc M i) * (u*explicitValue p (inc M i j))) =
          u * sum3 (fun i => ((capacity p i : Int)-rc M i) * explicitValue p (inc M i j)) := by
        simp [sum3,Int.mul_add,Int.mul_assoc,Int.mul_left_comm]
      rw [he,h,Int.mul_zero]
  }
  exact ⟨C.toIntegralLift hp' P⟩

#print axioms squareLiftAssumption
end Programme.«20261102-1249-proof-complexity».UniformC3.Block

namespace Programme.«20261102-1249-proof-complexity».UniformC3
open Programme.«20261027-0607-proof-complexity».Peel (IsPrime)
open Programme.«20261026-1402-proof-complexity».ExtLemma (Bal)
open Programme.«20261025-0459-proof-complexity».OntoFPHP (ontoFPHP PPCRefutation)
open Programme.«20261029-1156-proof-complexity».StdPC (Refutes)

/-- The general square-lift premise is now discharged. -/
theorem squareLiftAssumption (p : Nat) (hp : IsPrime p) : SquareLiftAssumption p :=
  Block.squareLiftAssumption p hp

theorem uniform_unit_design_unconditional {p : Nat} (hp : IsPrime p) (c : Nat) :
    ∃ T : List Nat → Int,
      (∀ e ≤ p-1, Bal p (2*p-1) (c*p*p) T T e) ∧ (p : Int) ∣ T [] - 1 :=
  uniform_unit_design hp (squareLiftAssumption p hp) c

theorem uniform_no_degree_p_unconditional {p : Nat} (hp : IsPrime p)
    (c n : Nat) (hn : 2*p-1 ≤ n) :
    ¬ PPCRefutation p (ontoFPHP n (c*p*p)) p :=
  uniform_no_degree_p hp (squareLiftAssumption p hp) c n hn

theorem uniform_no_standard_degree_p_unconditional {p : Nat} (hp : IsPrime p)
    (c n : Nat) (hn : 2*p-1 ≤ n) :
    ¬ Refutes p (ontoFPHP n (c*p*p)) p :=
  uniform_no_standard_degree_p hp (squareLiftAssumption p hp) c n hn

#print axioms squareLiftAssumption
#print axioms uniform_unit_design_unconditional
#print axioms uniform_no_degree_p_unconditional
#print axioms uniform_no_standard_degree_p_unconditional
end Programme.«20261102-1249-proof-complexity».UniformC3
