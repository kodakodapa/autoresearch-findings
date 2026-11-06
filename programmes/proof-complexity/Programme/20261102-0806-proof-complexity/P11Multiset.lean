import Programme.«20261026-1402-proof-complexity».ExtLemma
import Init.Data.List.Sort.Lemmas

namespace Programme.«20261102-0806-proof-complexity».P11Multiset

def sort (xs : List Nat) : List Nat := xs.mergeSort (fun a b => a ≤ b)

theorem sort_perm {xs ys : List Nat} (h : xs.Perm ys) : sort xs = sort ys := by
  apply List.Perm.eq_of_pairwise (le := fun a b : Nat => a ≤ b)
    (fun _ _ _ _ h h' => Nat.le_antisymm h h')
  · simpa only [sort, decide_eq_true_eq] using List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b)) (by simp only [decide_eq_true_eq]; intros; omega) (by simp only [Bool.or_eq_true, decide_eq_true_eq]; intros; omega) xs
  · simpa only [sort, decide_eq_true_eq] using List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b)) (by simp only [decide_eq_true_eq]; intros; omega) (by simp only [Bool.or_eq_true, decide_eq_true_eq]; intros; omega) ys
  · exact (List.mergeSort_perm xs _).trans (h.trans (List.mergeSort_perm ys _).symm)

/-- The table's three pigeon blocks have sizes ten, four, and one. -/
def ordered (a b c : List Nat) : List Nat := sort a ++ sort b ++ c

theorem ordered_perm {a a' b b' c : List Nat}
    (ha : a.Perm a') (hb : b.Perm b') :
    ordered a b c = ordered a' b' c := by
  simp only [ordered, sort_perm ha, sort_perm hb]

#print axioms sort_perm
#print axioms ordered_perm
end Programme.«20261102-0806-proof-complexity».P11Multiset
