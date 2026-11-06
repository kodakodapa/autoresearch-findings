import Programme.«20261104-1627-proof-complexity».TailCoordinateTransport
import Programme.«20261104-1627-proof-complexity».PivotFiniteCertificates
set_option maxHeartbeats 4000000
namespace Programme.«20261104-1627-proof-complexity».TailIndexedTransport
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261104-1627-proof-complexity».LprimeStages
open Programme.«20261029-1156-proof-complexity».StdPC
open Programme.«20261104-1627-proof-complexity».PivotCanonicalData Programme.«20261104-1627-proof-complexity».PivotFiniteCertificates

theorem map_indices {α β : Type} (L : List α) (fallback : α) (f : α → β) :
    ((List.range L.length).map fun j => f (L[j]?.getD fallback)) = L.map f := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    have hi : i < L.length := by simpa using h₂
    simp [List.getElem?_eq_getElem hi, hi]

def coordinates (old n : Nat) (v : Vector) (j : Nat) : Int :=
  vectorCoeff v (input old n j)

theorem top_indexed {m n : Nat} {v : Vector} (hv : valid (m+1) n 3 v)
    (hs : ∀ t ∈ v, pigeonBlock m t.2 ≠ 1) (k : Nat) :
    Programme.«20261104-1627-proof-complexity».RectangularReconstruction.dot (List.range (tails m n).length)
      (T m n k) (coordinates m n v) =
    coeff (top (m+1) n v)
      (mono n ((matchings (m+1) n 3)[k]?.getD [])) := by
  rw [Programme.«20261104-1627-proof-complexity».TailCoordinateTransport.top_grouped hv hs]
  unfold Programme.«20261104-1627-proof-complexity».RectangularReconstruction.dot T coordinates input
  rw [show ((List.range (tails m n).length).map fun j =>
      coeff (topLabel (m+1) n ((tails m n)[j]?.getD ⟨[],true,0⟩))
        (mono n ((matchings (m+1) n 3)[k]?.getD [])) *
      vectorCoeff v ((tails m n)[j]?.getD ⟨[],true,0⟩)) =
      ((tails m n).map fun g => coeff (topLabel (m+1) n g)
        (mono n ((matchings (m+1) n 3)[k]?.getD [])) * vectorCoeff v g) from
      map_indices (tails m n) (⟨[],true,0⟩ : Label) (fun g => coeff (topLabel (m+1) n g) (mono n ((matchings (m+1) n 3)[k]?.getD [])) * vectorCoeff v g)]
  congr 1
  apply List.map_congr_left
  intro g hg
  exact Int.mul_comm _ _
theorem kernel_indexed {p m n : Nat} {v : Vector}
    (hv : Kernel p (m+1) n 3 v)
    (hs : ∀ t ∈ v, pigeonBlock m t.2 ≠ 1) (k : Nat) :
    (p : Int) ∣ Programme.«20261104-1627-proof-complexity».RectangularReconstruction.dot (List.range (tails m n).length)
      (T m n k) (coordinates m n v) := by
  rw [top_indexed hv.1 hs]
  have h := hv.2 (mono n ((matchings (m+1) n 3)[k]?.getD []))
  simpa [coeff, cf] using h
end Programme.«20261104-1627-proof-complexity».TailIndexedTransport
#print axioms Programme.«20261104-1627-proof-complexity».TailIndexedTransport.top_indexed

#print axioms Programme.«20261104-1627-proof-complexity».TailIndexedTransport.kernel_indexed
