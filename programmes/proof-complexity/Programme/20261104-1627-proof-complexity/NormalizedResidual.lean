import Programme.«20261104-1627-proof-complexity».AnchoredColumnNormalize
import Programme.«20261104-1627-proof-complexity».MixedNormalForm
import Programme.«20261104-1627-proof-complexity».ExtensionOrder

namespace Programme.«20261104-1627-proof-complexity».NormalizedResidual
open Programme.«20261104-1627-proof-complexity».MatchingLabels Programme.«20261104-1627-proof-complexity».MixedAggregate Programme.«20261104-1627-proof-complexity».MixedEliminate
open Programme.«20261029-1156-proof-complexity».StdPC

theorem rc_empty_kernel {m n i j : Nat} (p : Nat)
    (hi : i < m) (hj : j < n) : Kernel p m n 2 (rc m n [] i j) := by
  refine ⟨rc_valid hi hj, ?_⟩
  intro u
  change (p : Int) ∣ coeff (top m n (rc m n [] i j)) u - 0
  rw [rc_top_zero]
  exact ⟨0, by omega⟩

/-- Mixed subtraction preserves Kernel at every modulus and board size. -/
theorem residual_kernel {p m n : Nat} (v : Vector) (hv : Kernel p m n 2 v) :
    Kernel p m n 2 (residual m n v) := by
  apply kernel_append hv
  apply kernel_scale
  apply kernel_combine
  intro t ht
  obtain ⟨i, hi, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
  exact rc_empty_kernel p (List.mem_range.mp hi) (List.mem_range.mp hj)

def finalResidual (v : Vector) : Vector :=
  residual 3 3 (Programme.«20261104-1627-proof-complexity».AnchoredColumnNormalize.normalized (Programme.«20261104-1627-proof-complexity».CCNormalize.corrected 3 v))

/-- The explicit anchored normalization followed by mixed subtraction is
still a kernel vector, with columns zero and row-only rigidity modulo three. -/
theorem finalResidual_properties (v : Vector) (hv : Kernel 3 3 3 2 v) :
    Kernel 3 3 3 2 (finalResidual v) ∧
    (∀ a < 3, ∀ b < 3, ∀ r < 3, b ≠ r →
      (3 : Int) ∣ vectorCoeff (finalResidual v) (edgeColLabel a b r)) ∧
    (∀ a < 3, ∀ i < 3, a ≠ i → ∀ b < 3, ∀ c < 3,
      (3 : Int) ∣ vectorCoeff (finalResidual v) (edgeRowLabel a b i) -
        vectorCoeff (finalResidual v) (edgeRowLabel a c i)) ∧
    (∀ a < 3, ∀ i < 3, a ≠ i →
      (3 : Int) ∣ vectorCoeff (finalResidual v) (edgeRowLabel a 0 i) +
        vectorCoeff (finalResidual v) (edgeRowLabel i 0 a)) := by
  have hk := Programme.«20261104-1627-proof-complexity».AnchoredColumnNormalize.corrected_kernel v hv
  have hi := Programme.«20261104-1627-proof-complexity».AnchoredColumnNormalize.corrected_independent v hv
  have hr := residual_row_rigidity (by omega) _ hk hi
  exact ⟨residual_kernel _ hk,
    Programme.«20261104-1627-proof-complexity».AnchoredColumnNormalize.corrected_residual_columns v hv, hr⟩

end Programme.«20261104-1627-proof-complexity».NormalizedResidual
#print axioms Programme.«20261104-1627-proof-complexity».NormalizedResidual.residual_kernel
#print axioms Programme.«20261104-1627-proof-complexity».NormalizedResidual.finalResidual_properties
