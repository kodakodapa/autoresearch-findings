import Programme.«20261104-1627-proof-complexity».SortedSupports
namespace Programme.«20261104-1627-proof-complexity».MatchingTestPoints
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».MatchQuot
open Programme.«20261104-1627-proof-complexity».MatchingReduction

def point (s : List Nat) : Nat → Bool := fun x => decide (x ∈ s)

theorem point_good {A : List (Poly Nat)} {s : List Nat} (hs : Safe A s) :
    Good A (point s) := by
  intro u w huw h
  exact hs u (of_decide_eq_true h.1) w (of_decide_eq_true h.2) huw

theorem mono_point (s t : List Nat) :
    monoEval (point s) t = if ∀ x ∈ t, x ∈ s then 1 else 0 := by
  simp only [monoEval_all, point, decide_eq_true_eq]

theorem subset_sum_congruence {p : Nat} {A : List (Poly Nat)} {P Q : Poly Nat}
    (h : ∀ a, Good A a → (p : Int) ∣ P.eval a - Q.eval a)
    {s : List Nat} (hs : Safe A s) :
    (p : Int) ∣
      (P.terms.map (fun t => t.1 * if ∀ x ∈ t.2, x ∈ s then 1 else 0)).sum -
      (Q.terms.map (fun t => t.1 * if ∀ x ∈ t.2, x ∈ s then 1 else 0)).sum := by
  simpa only [Poly.eval, mono_point] using h (point s) (point_good hs)
end Programme.«20261104-1627-proof-complexity».MatchingTestPoints
#print axioms Programme.«20261104-1627-proof-complexity».MatchingTestPoints.point_good
#print axioms Programme.«20261104-1627-proof-complexity».MatchingTestPoints.subset_sum_congruence
