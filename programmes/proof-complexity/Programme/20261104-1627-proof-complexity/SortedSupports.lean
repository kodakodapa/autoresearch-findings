import Programme.«20261104-1627-proof-complexity».MatchingCoverage
namespace Programme.«20261104-1627-proof-complexity».SortedSupports
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261104-1627-proof-complexity».MatchingReduction Programme.«20261104-1627-proof-complexity».MatchingCoverage

def sort (s : List Nat) : List Nat := s.mergeSort (fun x y => x ≤ y)
theorem sort_perm (s : List Nat) : (sort s).Perm s := List.mergeSort_perm s _

theorem sorted_decode_mem {n k : Nat} (s : List Nat)
    (hn : s.Nodup) (hs : Safe (ontoFPHP n k) s)
    (hb : ∀ x ∈ s, x < (n+k)*n) :
    decode n (sort s) ∈ matchings (n+k) n s.length := by
  have hp := sort_perm s
  have hm : ∀ x, x ∈ sort s ↔ x ∈ s := fun _ => hp.mem_iff
  have hle : (sort s).Pairwise (fun x y => x ≤ y) := by
    simpa only [sort, decide_eq_true_eq] using
      List.pairwise_mergeSort (le := fun x y : Nat => decide (x ≤ y))
        (by simp only [decide_eq_true_eq]; intros; omega)
        (by simp only [Bool.or_eq_true, decide_eq_true_eq]; intros; omega) s
  have hnd : (sort s).Nodup := hp.nodup_iff.mpr hn
  have hboth : (sort s).Pairwise (fun x y => x ≤ y ∧ x ≠ y) :=
    hle.and hnd
  have hrow : (sort s).Pairwise (fun x y => x/n < y/n) := by
    apply hboth.imp_of_mem
    intro x y hx hy hxy
    have hx' := (hm x).mp hx
    have hy' := (hm y).mp hy
    have hne := (Programme.«20261104-1627-proof-complexity».BoardCollisions.safe_coordinates hs hx' hy' (hb x hx') (hb y hy') hxy.2).1
    have hdiv := Nat.div_le_div_right hxy.1 (c := n)
    omega
  have h := safe_decode_mem (sort s)
    (by intro x hx y hy; exact hs x ((hm x).mp hx) y ((hm y).mp hy))
    (by intro x hx; exact hb x ((hm x).mp hx)) hrow
  simpa only [hp.length_eq] using h

theorem mono_sort (s : List Nat) (a : Nat → Bool) :
    monoEval a (sort s) = monoEval a s := by
  simp only [Programme.«20261025-0459-proof-complexity».MatchQuot.monoEval_all,
    (sort_perm s).mem_iff]
end Programme.«20261104-1627-proof-complexity».SortedSupports
#print axioms Programme.«20261104-1627-proof-complexity».SortedSupports.sorted_decode_mem
#print axioms Programme.«20261104-1627-proof-complexity».SortedSupports.mono_sort
