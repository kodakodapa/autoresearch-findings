import Programme.«20261104-1627-proof-complexity».MixedEliminate
import Programme.«20261104-1627-proof-complexity».RowOnlyTwo

namespace Programme.«20261104-1627-proof-complexity».MixedEliminate
open Programme.«20261104-1627-proof-complexity».MatchingLabels Programme.«20261104-1627-proof-complexity».MixedAggregate

theorem residual_valid {m n : Nat} (v : Vector) (hv : valid m n 2 v) :
    valid m n 2 (residual m n v) := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hv t ht
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    obtain ⟨q, hq, hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨u, hu, he⟩ := List.mem_map.mp hs
    obtain ⟨i, hi, hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
    have hu' := rc_valid (List.mem_range.mp hi) (List.mem_range.mp hj) u hu
    cases he
    exact hu'

/-- Conditional mixed normal form: the corrected rows have precisely the
row-only rigidity. No assertion of column independence from Kernel is made. -/
theorem residual_row_rigidity {p m n : Nat} (hn : 3 ≤ n)
    (v : Vector) (hv : Kernel p m n 2 v)
    (hind : ∀ a < m, ∀ r < n, ∀ b < n, b ≠ r →
      (p : Int) ∣ vectorCoeff v (edgeColLabel a b r) -
        vectorCoeff v (edgeColLabel a (anchor r) r)) :
    (∀ a < m, ∀ i < m, a ≠ i → ∀ b < n, ∀ c < n,
      (p : Int) ∣ vectorCoeff (residual m n v) (edgeRowLabel a b i) -
        vectorCoeff (residual m n v) (edgeRowLabel a c i)) ∧
    (∀ a < m, ∀ i < m, a ≠ i →
      (p : Int) ∣ vectorCoeff (residual m n v) (edgeRowLabel a 0 i) +
        vectorCoeff (residual m n v) (edgeRowLabel i 0 a)) := by
  apply row_two_rigidity hn
  intro a ha i hi hai b hb j hj hbj
  rw [residual_rows v ha hi hb hai, residual_rows v hi ha hj (Ne.symm hai)]
  have h := kernel_two_equations (by omega) v hv a b i j ha hb hi hj hai hbj
  have hc := Int.dvd_add (hind a ha j hj b hb hbj)
    (hind i hi b hb j hj (Ne.symm hbj))
  have hh := Int.dvd_sub h hc
  have he : vectorCoeff v (edgeRowLabel a b i) + vectorCoeff v (edgeRowLabel i j a) +
      vectorCoeff v (edgeColLabel a b j) + vectorCoeff v (edgeColLabel i j b) -
      (vectorCoeff v (edgeColLabel a b j) - vectorCoeff v (edgeColLabel a (anchor j) j) +
      (vectorCoeff v (edgeColLabel i j b) - vectorCoeff v (edgeColLabel i (anchor b) b))) =
      vectorCoeff v (edgeRowLabel a b i) + vectorCoeff v (edgeColLabel i (anchor b) b) +
      (vectorCoeff v (edgeRowLabel i j a) + vectorCoeff v (edgeColLabel a (anchor j) j)) := by omega
  rwa [he] at hh

end Programme.«20261104-1627-proof-complexity».MixedEliminate
#print axioms Programme.«20261104-1627-proof-complexity».MixedEliminate.residual_valid
#print axioms Programme.«20261104-1627-proof-complexity».MixedEliminate.residual_row_rigidity
