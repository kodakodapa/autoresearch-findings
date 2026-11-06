import Programme.«20261104-1627-proof-complexity».RowRelationCertificate
import Programme.«20261104-1627-proof-complexity».ColumnRelationCertificate
namespace Programme.«20261104-1627-proof-complexity».OccupiedMarks
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».MatchQuot
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261104-1627-proof-complexity».MatchingLabels

private theorem rsum_single (N j : Nat) (hj : j < N) (f : Nat → Int)
    (hf : ∀ t < N, f t = if t = j then 1 else 0) : rsum N f = 1 := by
  have aux : ∀ s, s ≤ N → rsum s f = if j < s then 1 else 0 := by
    intro s
    induction s with
    | zero => intro _; simp [rsum]
    | succ s ih =>
      intro hs
      rw [rsum, ih (by omega), hf s (by omega)]
      by_cases h : s = j
      · subst s; simp
      · by_cases hjs : j < s <;> simp [h, hjs] <;> omega
  exact (aux N (by omega)).trans (if_pos hj)

private theorem row_unique {n k i j : Nat} (hi : i < n+k) (hj : j < n)
    {a : Nat → Bool} (ha : Good (ontoFPHP n k) a) (hx : a (var n i j) = true) :
    (sumOne (fun t => var n i t) n).eval a = 0 := by
  rw [sumOne_eval]
  have hs : rsum n (fun t => xv (var n i t) a) = 1 := by
    apply rsum_single n j hj
    intro t ht
    by_cases h : t = j
    · subst t; simp [xv, hx]
    · have hz : a (var n i t) ≠ true := by
        intro hxt
        rcases Nat.lt_or_gt_of_ne h with h | h
        · exact ha _ _ (Programme.«20261104-1627-proof-complexity».BoardCollisions.functional_mem hi ht hj h) ⟨hxt,hx⟩
        · exact ha _ _ (Programme.«20261104-1627-proof-complexity».BoardCollisions.functional_mem hi hj ht h) ⟨hx,hxt⟩
      simp [h, xv, hz]
  rw [hs]; rfl

private theorem column_unique {n k i j : Nat} (hi : i < n+k) (hj : j < n)
    {a : Nat → Bool} (ha : Good (ontoFPHP n k) a) (hx : a (var n i j) = true) :
    (sumOne (fun t => var n t j) (n+k)).eval a = 0 := by
  rw [sumOne_eval]
  have hs : rsum (n+k) (fun t => xv (var n t j) a) = 1 := by
    apply rsum_single (n+k) i hi
    intro t ht
    by_cases h : t = i
    · subst t; simp [xv, hx]
    · have hz : a (var n t j) ≠ true := by
        intro hxt
        rcases Nat.lt_or_gt_of_ne h with h | h
        · exact ha _ _ (Programme.«20261104-1627-proof-complexity».BoardCollisions.collision_mem ht hi hj h) ⟨hxt,hx⟩
        · exact ha _ _ (Programme.«20261104-1627-proof-complexity».BoardCollisions.collision_mem hi ht hj h) ⟨hx,hxt⟩
      simp [h, xv, hz]
  rw [hs]; rfl

/-- An occupied edge makes both incident axiom products vanish on Good points. -/
theorem occupied_products_zero {n k i j : Nat} (M : Matching)
    (he : (i,j) ∈ M) (hi : i < n+k) (hj : j < n)
    (a : Nat → Bool) (ha : Good (ontoFPHP n k) a) :
    monoEval a (mono n M) * (sumOne (fun t => var n i t) n).eval a = 0 ∧
    monoEval a (mono n M) * (sumOne (fun t => var n t j) (n+k)).eval a = 0 := by
  by_cases hm : monoEval a (mono n M) = 0
  · simp [hm]
  · have hall : ∀ x ∈ mono n M, a x = true := by
      by_cases h : ∀ x ∈ mono n M, a x = true
      · exact h
      · exact False.elim (hm (by rw [monoEval_all, if_neg h]))
    have hx : a (var n i j) = true := hall _ (List.mem_map.mpr ⟨(i,j),he,rfl⟩)
    rw [row_unique hi hj ha hx, column_unique hi hj ha hx]
    simp

/-- These products need no label vector: the empty NS certificate works at degree zero. -/
theorem occupied_products_nsIn {p n k i j : Nat} (M : Matching)
    (he : (i,j) ∈ M) (hi : i < n+k) (hj : j < n) :
    NSIn p (ontoFPHP n k) 0
      (fun a => monoEval a (mono n M) * (sumOne (fun t => var n i t) n).eval a) ∧
    NSIn p (ontoFPHP n k) 0
      (fun a => monoEval a (mono n M) * (sumOne (fun t => var n t j) (n+k)).eval a) := by
  constructor
  · refine ⟨[], by simp, ?_⟩
    intro a ha
    simpa only [List.map_nil, List.sum_nil, (occupied_products_zero M he hi hj a ha).1, Int.sub_self] using (show (p : Int) ∣ (0 : Int) from ⟨0, by simp⟩)
  · refine ⟨[], by simp, ?_⟩
    intro a ha
    simpa only [List.map_nil, List.sum_nil, (occupied_products_zero M he hi hj a ha).2, Int.sub_self] using (show (p : Int) ∣ (0 : Int) from ⟨0, by simp⟩)
end Programme.«20261104-1627-proof-complexity».OccupiedMarks
#print axioms Programme.«20261104-1627-proof-complexity».OccupiedMarks.occupied_products_zero
#print axioms Programme.«20261104-1627-proof-complexity».OccupiedMarks.occupied_products_nsIn
