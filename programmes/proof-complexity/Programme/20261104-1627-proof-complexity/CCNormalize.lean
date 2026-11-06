import Programme.«20261104-1627-proof-complexity».CCCoordinates

namespace Programme.«20261104-1627-proof-complexity».CCNormalize
open Programme.«20261104-1627-proof-complexity».MatchingLabels Programme.«20261104-1627-proof-complexity».MixedAggregate Programme.«20261104-1627-proof-complexity».MixedEliminate Programme.«20261104-1627-proof-complexity».CCCoordinates

def corrected (m : Nat) (v : Vector) : Vector :=
  v ++ (cc m [] 0 1).map (fun t => (-circulation v 0 0 1 2 * t.1, t.2))

theorem corrected_coeff (m : Nat) (v : Vector) (g : Label) :
    vectorCoeff (corrected m v) g = vectorCoeff v g -
      circulation v 0 0 1 2 * vectorCoeff (cc m [] 0 1) g := by
  rw [corrected, vectorCoeff_append, coeff_scale]
  simp [Int.neg_mul, Int.sub_eq_add_neg]

theorem corrected_circulation (m a : Nat) (v : Vector) (ha : a < m) :
    circulation (corrected m v) a 0 1 2 =
      circulation v a 0 1 2 + 2 * circulation v 0 0 1 2 := by
  simp only [circulation, corrected_coeff, cc_col]
  simp [ha]
  omega

theorem corrected_rows (m a b r : Nat) (v : Vector) :
    vectorCoeff (corrected m v) (edgeRowLabel a b r) =
      vectorCoeff v (edgeRowLabel a b r) := by
  rw [corrected_coeff, cc_row]
  omega

/-- On a three-hole board every pigeon has zero residual triangle circulation mod 3. -/
theorem corrected_triangle {m : Nat} (v : Vector) (hv : Kernel 3 m 3 2 v)
    (a : Nat) (ha : a < m) :
    (3 : Int) ∣ circulation (corrected m v) a 0 1 2 := by
  rw [corrected_circulation m a v ha]
  have h : (3 : Int) ∣ circulation v a 0 1 2 - circulation v 0 0 1 2 := by
    by_cases he : a = 0
    · subst a; simp
    · exact kernel_circulation (by omega) v hv a 0 0 1 2 ha (by omega) he
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨q,hq⟩ := h
  exact ⟨q + circulation v 0 0 1 2, by omega⟩

end Programme.«20261104-1627-proof-complexity».CCNormalize
#print axioms Programme.«20261104-1627-proof-complexity».CCNormalize.corrected_triangle
#print axioms Programme.«20261104-1627-proof-complexity».CCNormalize.corrected_rows
