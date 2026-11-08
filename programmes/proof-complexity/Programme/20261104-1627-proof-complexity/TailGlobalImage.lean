import Programme.«20261104-1627-proof-complexity».IncidentVectorCoefficient
import Programme.«20261104-1627-proof-complexity».LprimeOne

namespace Programme.«20261104-1627-proof-complexity».IncidentSection
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261104-1627-proof-complexity».TailMatchingCoordinates

/-- Actual incident sections discharge every local-image premise of Lprime. -/
theorem tail_topImage {p m n d : Nat} (hd : 1 < d)
    (stable : 2*(d-1) < n) (localGlobal : Lprime p m n (d-1))
    {v : Vector} (hv : Kernel p (m+1) n d v)
    (ht : ∀ t ∈ v, pigeonBlock m t.2 ≠ 1) :
    TopImage p m n (d-1) (tailCoordinates m v) := by
  apply localGlobal stable
  intro h hh
  have hn : 0 < n-1 := by omega
  have he : n-1+1 = n := by omega
  have hs := tail_restriction_topImage (p:=p) (m:=m) (n:=n-1)
    (d:=d) (h:=h) hn (by omega) hd (he ▸ hv) ht
  exact hs

/-- Degree two uses the proved degree-one Lprime. -/
theorem tail_two_topImage {p m n : Nat} (hn : 2 < n)
    {v : Vector} (hv : Kernel p (m+1) n 2 v)
    (ht : ∀ t ∈ v, pigeonBlock m t.2 ≠ 1) :
    TopImage p m n 1 (tailCoordinates m v) := by
  exact tail_topImage (by omega) (by omega)
    (Programme.«20261104-1627-proof-complexity».LprimeOne.lprime_one p m n) hv ht

/-- Explicit shape of a degree-two tail's block-two coordinates. -/
theorem tail_two_row_col {p m n : Nat} (hn : 2 < n)
    {v : Vector} (hv : Kernel p (m+1) n 2 v)
    (ht : ∀ t ∈ v, pigeonBlock m t.2 ≠ 1) :
    ∃ a b : Nat → Int, ∀ i, i < m → ∀ j, j < n →
      (p : Int) ∣ vectorCoeff v ⟨[(i,j)],true,m⟩ - (a i + b j) := by
  exact (Programme.«20261104-1627-proof-complexity».LprimeOne.topImage_one_iff
    (by omega) (tailCoordinates m v)).mp (tail_two_topImage hn hv ht)

end Programme.«20261104-1627-proof-complexity».IncidentSection
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.tail_topImage
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.tail_two_topImage
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.tail_two_row_col
