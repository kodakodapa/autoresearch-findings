import Programme.«20261104-1627-proof-complexity».CCKernelThree
import Programme.«20261104-1627-proof-complexity».AnchoredOneBase

namespace Programme.«20261104-1627-proof-complexity».ZTwoCoordinates
open Programme.«20261104-1627-proof-complexity».MatchingLabels

/-- The anchored degree-two generator has a strict-order column profile. -/
theorem z_two_col (a b r : Nat) (ha : a < 3) (hb : b < 3) (hr : r < 3) :
    vectorCoeff (z 3 3 2 []) (edgeColLabel a b r) =
      if b < r then -1 else 0 := by
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  have hr' : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases ha' with ha' | ha' | ha' <;> subst a
  all_goals rcases hb' with hb' | hb' | hb' <;> subst b
  all_goals rcases hr' with hr' | hr' | hr' <;> subst r
  all_goals decide +kernel

/-- Its row profile is the dual strict-order profile. -/
theorem z_two_row (a b r : Nat) (ha : a < 3) (hb : b < 3) (hr : r < 3) :
    vectorCoeff (z 3 3 2 []) (edgeRowLabel a b r) =
      if a < r then 1 else 0 := by
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  have hr' : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases ha' with ha' | ha' | ha' <;> subst a
  all_goals rcases hb' with hb' | hb' | hb' <;> subst b
  all_goals rcases hr' with hr' | hr' | hr' <;> subst r
  all_goals decide +kernel

/-- Subtract the anchored generator with the unique middle-hole defect as weight. -/
def defect (v : Vector) (a : Nat) : Int :=
  vectorCoeff v (edgeColLabel a 2 1) - vectorCoeff v (edgeColLabel a 0 1)

def zCorrected (v : Vector) (q : Int) : Vector :=
  v ++ (z 3 3 2 []).map (fun t => (q * t.1, t.2))

theorem zCorrected_coeff (v : Vector) (q : Int) (g : Label) :
    vectorCoeff (zCorrected v q) g = vectorCoeff v g +
      q * vectorCoeff (z 3 3 2 []) g := by
  rw [zCorrected, vectorCoeff_append, Programme.«20261104-1627-proof-complexity».MixedAggregate.coeff_scale]

theorem zCorrected_defect (v : Vector) (q : Int) (a : Nat) (ha : a < 3) :
    defect (zCorrected v q) a = defect v a + q := by
  simp only [defect, zCorrected_coeff,
    z_two_col a 2 1 ha (by omega) (by omega),
    z_two_col a 0 1 ha (by omega) (by omega)]
  simp only [show ¬ (2 : Nat) < 1 by omega, show (0 : Nat) < 1 by omega, if_false, if_true, Int.mul_zero, Int.mul_neg, Int.mul_one]
  omega

theorem zCorrected_anchor_defect (v : Vector) :
    defect (zCorrected v (-defect v 0)) 0 = 0 := by
  rw [zCorrected_defect v _ 0 (by omega)]
  omega

end Programme.«20261104-1627-proof-complexity».ZTwoCoordinates
#print axioms Programme.«20261104-1627-proof-complexity».ZTwoCoordinates.z_two_col
#print axioms Programme.«20261104-1627-proof-complexity».ZTwoCoordinates.z_two_row

#print axioms Programme.«20261104-1627-proof-complexity».ZTwoCoordinates.zCorrected_anchor_defect
