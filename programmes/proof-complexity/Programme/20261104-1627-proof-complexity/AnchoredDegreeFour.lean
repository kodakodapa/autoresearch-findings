import Programme.«20261104-1627-proof-complexity».AnchoredTwoLowering
import Programme.«20261104-1627-proof-complexity».AnchoredThree
import Programme.«20261104-1627-proof-complexity».AnchoredFour
import Programme.«20261104-1627-proof-complexity».AnchoredRhoOne
namespace Programme.«20261104-1627-proof-complexity».AnchoredDegreeFour
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261024-1633-proof-complexity».NS

theorem lowering {n k s t : Nat} {N : Matching}
    (hk : 9 ∣ k) (hs : s ≤ n) (ht : 1 ≤ t) (h4 : t ≤ 4)
    (hN : N ∈ matchings (n+k) n s) :
    NSIn 3 (ontoFPHP n k) (s+t-1) (rho n (z (n+k) n t N)).eval := by
  have cases : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by omega
  rcases cases with h | h | h | h
  · subst t
    have hw := Programme.«20261104-1627-proof-complexity».AnchoredRhoOne.anchored_identity_one (p := 3) hN
    apply nsIn_congr (Programme.«20261104-1627-proof-complexity».BoundedRelationCertificates.W_nsIn hw)
    intro a
    rw [eval_sub]
    have hc : (3 : Int) ∣ ((n+k : Nat) : Int) - n := by
      obtain ⟨b, rfl⟩ := hk
      refine ⟨3 * (b : Int), ?_⟩
      simp only [Int.natCast_add, Int.natCast_mul]
      omega
    have he : ∀ x y : Int, x-(x-y)=y := by intros; omega
    rw [he]
    simpa [Poly.eval] using Int.dvd_trans hc (Int.dvd_mul_right _ (monoEval a (mono n N)))
  · subst t
    simpa using Programme.«20261104-1627-proof-complexity».AnchoredTwoLowering.lowering_two hk hs hN
  · subst t
    simpa using Programme.«20261104-1627-proof-complexity».AnchoredThree.lowering_three hk hs hN
  · subst t
    simpa using Programme.«20261104-1627-proof-complexity».AnchoredFour.lowering_four hk hs hN

theorem level_lowering {n k d t : Nat} {N : Matching}
    (hk : 9 ∣ k) (hd : d ≤ 4) (ht : t ∈ (List.range d).map (· + 1))
    (hn : d ≤ n) (hN : N ∈ matchings (n+k) n (d-t)) :
    NSIn 3 (ontoFPHP n k) (d-1) (rho n (z (n+k) n t N)).eval := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
  have ha' : a < d := List.mem_range.mp ha
  have he : d - (a+1) + (a+1) - 1 = d-1 := by omega
  simpa only [he] using lowering hk (by omega : d-(a+1) ≤ n)
    (by omega : 1 ≤ a+1) (by omega : a+1 ≤ 4) hN
#print axioms lowering
#print axioms level_lowering
end Programme.«20261104-1627-proof-complexity».AnchoredDegreeFour
