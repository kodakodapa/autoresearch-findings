import Programme.«20261104-1627-proof-complexity».PivotCanonicalData
import Programme.«20261104-1627-proof-complexity».RhoCoordinateTransport
import Programme.«20261104-1627-proof-complexity».ResidualSupport
namespace Programme.«20261104-1627-proof-complexity».TailCoordinateTransport
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261104-1627-proof-complexity».LprimeStages
open Programme.«20261029-1156-proof-complexity».StdPC
open Programme.«20261104-1627-proof-complexity».PivotCanonicalData

theorem tails_nodup (m n : Nat) : (tails m n).Nodup :=
  (labels_nodup (m+1) n 3).filter _

theorem supported {m n : Nat} {v : Vector} (hv : valid (m+1) n 3 v)
    (hs : ∀ t ∈ v, pigeonBlock m t.2 ≠ 1) : ∀ t ∈ v, t.2 ∈ tails m n := by
  intro t ht
  apply List.mem_filter.mpr
  refine ⟨hv t ht, ?_⟩
  have h := hs t ht
  simp only [pigeonBlock, usesPigeon] at h
  cases he : t.2.base.any (fun e => e.1 == m) <;>
    cases hf : (t.2.isRow && t.2.mark == m) <;> simp_all

theorem top_grouped {m n : Nat} {v : Vector} (hv : valid (m+1) n 3 v)
    (hs : ∀ t ∈ v, pigeonBlock m t.2 ≠ 1) (u : List Nat) :
    coeff (top (m+1) n v) u =
      ((tails m n).map fun g => vectorCoeff v g * coeff (topLabel (m+1) n g) u).sum := by
  rw [top_coeff_sum]
  exact Programme.«20261104-1627-proof-complexity».RhoCoordinateTransport.observable_group v (tails m n) (tails_nodup m n)
    (supported hv hs) (fun g => coeff (topLabel (m+1) n g) u)
end Programme.«20261104-1627-proof-complexity».TailCoordinateTransport
#print axioms Programme.«20261104-1627-proof-complexity».TailCoordinateTransport.top_grouped
