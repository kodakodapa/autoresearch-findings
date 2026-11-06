import Work.UniformC3.Transfer
import Work.UniformC3.FiniteLifts
import Programme.«20261029-1156-proof-complexity».StdPC

namespace Work.UniformC3
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261027-0607-proof-complexity».Peel (IsPrime)
open Programme.«20261025-0459-proof-complexity».OntoFPHP (ontoFPHP PPCRefutation)
open Programme.«20261029-1156-proof-complexity».StdPC (Refutes refutes_ppc)

/-- The single external mathematical premise, stated as existence rather than an axiom. -/
def SquareLiftAssumption (p : Nat) : Prop := Nonempty (IntegralLift p)

/-- Unit degree-p design on 2p-1 holes with surplus c*p^2.
The proof actually permits c=0 as well. -/
theorem uniform_unit_design {p : Nat} (hp : IsPrime p)
    (hLift : SquareLiftAssumption p) (c : Nat) :
    ∃ T : List Nat → Int,
      (∀ e ≤ p-1, Bal p (2*p-1) (c*p*p) T T e) ∧ (p : Int) ∣ T [] - 1 := by
  obtain ⟨H⟩ := hLift
  exact unit_design_of_rectangular_lift hp (rectangleFromSquare hp H c)

/-- General conditional PC lower bound with exactly the square-lift premise. -/
theorem uniform_no_degree_p {p : Nat} (hp : IsPrime p)
    (hLift : SquareLiftAssumption p) (c n : Nat) (hn : 2*p-1 ≤ n) :
    ¬ PPCRefutation p (ontoFPHP n (c*p*p)) p := by
  obtain ⟨H⟩ := hLift
  exact no_refutation_of_rectangular_lift hp (rectangleFromSquare hp H c) n hn

/-- The same conclusion for the library's ordinary syntactic polynomial calculus. -/
theorem uniform_no_standard_degree_p {p : Nat} (hp : IsPrime p)
    (hLift : SquareLiftAssumption p) (c n : Nat) (hn : 2*p-1 ≤ n) :
    ¬ Refutes p (ontoFPHP n (c*p*p)) p := by
  intro h
  exact uniform_no_degree_p hp hLift c n hn (refutes_ppc hp.1 h)

theorem isPrime2 : IsPrime 2 := by
  refine ⟨by decide, ?_⟩
  intro a ha
  have hb := Nat.le_of_dvd (by decide : 0 < 2) ha
  rcases (show a=0 ∨ a=1 ∨ a=2 by omega) with h | h | h <;> subst h <;> simp_all

theorem isPrime3 : IsPrime 3 := by
  refine ⟨by decide, ?_⟩
  intro a ha
  have hb := Nat.le_of_dvd (by decide : 0 < 3) ha
  rcases (show a=0 ∨ a=1 ∨ a=2 ∨ a=3 by omega) with h | h | h | h <;> subst h <;> simp_all

theorem squareLiftAssumption2 : SquareLiftAssumption 2 := ⟨integralLift2⟩
theorem squareLiftAssumption3 : SquareLiftAssumption 3 := ⟨integralLift3⟩

theorem unit_design_two (c : Nat) :
    ∃ T : List Nat → Int,
      (∀ e ≤ 1, Bal 2 3 (c*2*2) T T e) ∧ (2 : Int) ∣ T [] - 1 :=
  uniform_unit_design isPrime2 squareLiftAssumption2 c

theorem unit_design_three (c : Nat) :
    ∃ T : List Nat → Int,
      (∀ e ≤ 2, Bal 3 5 (c*3*3) T T e) ∧ (3 : Int) ∣ T [] - 1 :=
  uniform_unit_design isPrime3 squareLiftAssumption3 c

theorem no_degree_two (c n : Nat) (hn : 3 ≤ n) :
    ¬ PPCRefutation 2 (ontoFPHP n (c*2*2)) 2 :=
  uniform_no_degree_p isPrime2 squareLiftAssumption2 c n hn

theorem no_degree_three (c n : Nat) (hn : 5 ≤ n) :
    ¬ PPCRefutation 3 (ontoFPHP n (c*3*3)) 3 :=
  uniform_no_degree_p isPrime3 squareLiftAssumption3 c n hn

theorem no_standard_degree_two (c n : Nat) (hn : 3 ≤ n) :
    ¬ Refutes 2 (ontoFPHP n (c*2*2)) 2 :=
  uniform_no_standard_degree_p isPrime2 squareLiftAssumption2 c n hn

theorem no_standard_degree_three (c n : Nat) (hn : 5 ≤ n) :
    ¬ Refutes 3 (ontoFPHP n (c*3*3)) 3 :=
  uniform_no_standard_degree_p isPrime3 squareLiftAssumption3 c n hn

#print axioms uniform_unit_design
#print axioms uniform_no_degree_p
#print axioms uniform_no_standard_degree_p
#print axioms squareLiftAssumption2
#print axioms squareLiftAssumption3
#print axioms unit_design_two
#print axioms unit_design_three
#print axioms no_degree_two
#print axioms no_degree_three
#print axioms no_standard_degree_two
#print axioms no_standard_degree_three

end Work.UniformC3
