import Programme.«20261030-0634-proof-complexity».FactorUnit
import Programme.«20261027-0607-proof-complexity».VUnit
import Programme.«20261026-1402-proof-complexity».Relabel

namespace Programme.«20261102-1249-proof-complexity».UniformC3
open Programme.«20261026-1402-proof-complexity».ExtLemma

/-- Exactly the square-board integral functional required by step 1.
The top coefficients are congruent to one; all free row and column
extension sums of predecessors vanish as integers. -/
structure IntegralLift (p : Nat) where
  coeff : List Nat → Int
  unit : ∀ g, CM (2*p-1) 0 g → g.length = p → (p : Int) ∣ coeff g - 1
  harmonic : ∀ g, CM (2*p-1) 0 g → g.length = p-1 →
    (∀ i < 2*p-1, pfree (2*p-1) g i → rowS (2*p-1) 0 coeff g i = 0) ∧
    (∀ j < 2*p-1, hfree (2*p-1) g j → colS (2*p-1) 0 coeff g j = 0)

end Programme.«20261102-1249-proof-complexity».UniformC3
