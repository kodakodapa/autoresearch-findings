/- Hole-side counterpart of Peer.pr.IncidentSection.block_three_kernel. -/
import Programme.«20261104-1627-proof-complexity».HoleResidualSupport
namespace Programme.«20261104-1627-proof-complexity».HoleBlockThree
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261104-1627-proof-complexity».HoleProjection Programme.«20261104-1627-proof-complexity».HoleResidualSupport

theorem block_three_congruent {p n : Nat} {v : Vector}
    (ht : ∀ t ∈ v, holeBlock n t.2 ≠ 1)
    (hz : ∀ g, holeBlock n g = 2 → (p : Int) ∣ vectorCoeff v g) :
    ∀ g, (p : Int) ∣ vectorCoeff v g - vectorCoeff (splitHole n 3 v) g := by
  intro g
  rw [Programme.«20261104-1627-proof-complexity».HoleCancellation.vectorCoeff_split]
  have hcases : holeBlock n g = 1 ∨ holeBlock n g = 2 ∨ holeBlock n g = 3 := by
    unfold holeBlock
    split <;> simp_all
    split <;> simp_all
  rcases hcases with h | h | h
  · have he : vectorCoeff v g = 0 := by
      unfold vectorCoeff
      have hf : v.filter (fun t => t.2 == g) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro t ht'
        have hn := ht t ht'
        simpa only [beq_iff_eq] using (show t.2 ≠ g by intro he; exact hn (he ▸ h))
      rw [hf]; rfl
    simp [h,he]
  · simpa [h] using hz g h
  · simp [h]

theorem block_three_kernel {p m n d : Nat} {v : Vector}
    (hv : Kernel p m (n+1) d v)
    (ht : ∀ t ∈ v, holeBlock n t.2 ≠ 1)
    (hz : ∀ g, holeBlock n g = 2 → (p : Int) ∣ vectorCoeff v g) :
    Kernel p m (n+1) d (splitHole n 3 v) := by
  apply Programme.«20261104-1627-proof-complexity».ResidualSupport.kernel_of_congruent
    hv _ (block_three_congruent ht hz)
  intro t ht'
  exact hv.1 t (List.mem_filter.mp ht').1
end Programme.«20261104-1627-proof-complexity».HoleBlockThree
#print axioms Programme.«20261104-1627-proof-complexity».HoleBlockThree.block_three_congruent
#print axioms Programme.«20261104-1627-proof-complexity».HoleBlockThree.block_three_kernel
