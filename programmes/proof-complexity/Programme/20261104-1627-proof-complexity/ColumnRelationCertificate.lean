import Programme.«20261104-1627-proof-complexity».BoardCollisions
import Programme.«20261104-1627-proof-complexity».CertificateReassembly
import Programme.«20261104-1627-proof-complexity».MatchingLabels
namespace Programme.«20261104-1627-proof-complexity».ColumnRelationCertificate
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».MatchQuot
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261104-1627-proof-complexity».MatchingLabels
private theorem rsum_range (n : Nat) (f : Nat → Int) :
    rsum n f = ((List.range n).map f).sum := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rsum, List.range_succ, ih]

theorem blocked_zero {n k j i : Nat} {M : Matching}
    (hi : j < n) (fresh : ∀ e ∈ M, e.2 ≠ j)
    (bounds : ∀ e ∈ M, e.2 < n) (blocked : freeRow M i = false)
    (hj : i < n+k) {a : Nat → Bool} (ha : Good (ontoFPHP n k) a) :
    xv (i*n+j) a * monoEval a (mono n M) = 0 := by
  have ex : ∃ e ∈ M, e.1 = i := by
    classical
    by_cases h : ∃ e ∈ M, e.1 = i
    · exact h
    have hf : freeRow M i = true := by
      simp only [freeRow, List.all_eq_true, bne_iff_ne]
      intro e he heq
      exact h ⟨e, he, heq⟩
    rw [hf] at blocked
    cases blocked
  obtain ⟨e, he, hej⟩ := ex
  by_cases hx : a (i*n+j) = true
  · have hz : a (i*n+e.2) ≠ true := by
      intro hetrue
      have hne := fresh e he
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact ha _ _ (Programme.«20261104-1627-proof-complexity».BoardCollisions.functional_mem hj (bounds e he) hi h)
          ⟨by simpa [var] using hetrue, by simpa [var] using hx⟩
      · exact ha _ _ (Programme.«20261104-1627-proof-complexity».BoardCollisions.functional_mem hj hi (bounds e he) h)
          ⟨by simpa [var] using hx, by simpa [var] using hetrue⟩
    have hm : monoEval a (mono n M) = 0 := by
      rw [monoEval_all, if_neg]
      intro hall
      apply hz
      apply hall
      exact List.mem_map.mpr ⟨e, he, by simp [hej]⟩
    rw [hm, Int.mul_zero]
  · simp [xv, hx]

theorem column_relation_eval {n k j : Nat} (M : Matching)
    (hi : j < n) (fresh : ∀ e ∈ M, e.2 ≠ j)
    (bounds : ∀ e ∈ M, e.2 < n)
    (a : Nat → Bool) (ha : Good (ontoFPHP n k) a) :
    (relation (n+k) n ⟨M,false,j⟩).eval a =
      monoEval a (mono n M) * (sumOne (fun i => var n i j) (n+k)).eval a := by
  have he : ((rows (n+k) M).map (fun i => xv (i*n+j) a * monoEval a (mono n M))).sum =
      ((List.range (n+k)).map (fun i => xv (i*n+j) a * monoEval a (mono n M))).sum := by
    unfold rows
    rw [sum_filter]
    congr 1
    apply List.map_congr_left
    intro i hj
    by_cases h : freeRow M i = true
    · simp [h]
    · have hf : freeRow M i = false := by simpa using h
      simp [hf, blocked_zero hi fresh bounds hf (List.mem_range.mp hj) ha]
  rw [relation, eval_sub]
  have ht : (topLabel (n+k) n ⟨M,false,j⟩).eval a =
      ((rows (n+k) M).map (fun i => xv (i*n+j) a * monoEval a (mono n M))).sum := by
    simp [topLabel, Poly.eval, Function.comp_def, Programme.«20261025-0459-proof-complexity».MatchQuot.monoEval_cons]
  rw [ht]
  simp only [Poly.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.one_mul, Int.add_zero]
  change _ - monoEval a (mono n M) = monoEval a (mono n M) * (sumOne (fun i => var n i j) (n+k)).eval a
  rw [he, sumOne_eval, rsum_range]
  have hs : ∀ L : List Nat,
      (L.map (fun i => xv (i*n+j) a * monoEval a (mono n M))).sum =
        monoEval a (mono n M) * (L.map (fun i => xv (i*n+j) a)).sum := by
    intro L
    induction L with
    | nil => simp
    | cons i L ih => simp only [List.map_cons, List.sum_cons, ih, Int.mul_add];
                     rw [Int.mul_comm (xv (i*n+j) a)]
  rw [hs]
  simp [var, Int.mul_sub]
theorem column_relation_nsIn {p n k j : Nat} (M : Matching)
    (hi : j < n) (fresh : ∀ e ∈ M, e.2 ≠ j)
    (bounds : ∀ e ∈ M, e.2 < n) :
    NSIn p (ontoFPHP n k) (M.length+1)
      (relation (n+k) n ⟨M,false,j⟩).eval := by
  let G : Poly Nat := ⟨[(1,mono n M)]⟩
  let R := sumOne (fun i => var n i j) (n+k)
  refine ⟨[(G,R)], ?_, ?_⟩
  · intro e he
    have ee : e = (G,R) := by simpa using he
    subst e
    constructor
    · unfold R
      have hr : sumOne (fun i => var n i j) (n+k) ∈ holeAx n k :=
        List.mem_map.mpr ⟨j, List.mem_range.mpr hi, rfl⟩
      simp only [ontoFPHP, List.mem_append]
      exact Or.inl (Or.inl (Or.inr hr))
    · have hg : G.deg ≤ M.length := by
        rw [deg_le_iff]
        intro t ht
        have et : t = (1,mono n M) := by simpa [G] using ht
        subst t
        simp [mono]
      exact Nat.le_trans (Nat.add_le_add hg (sumOne_deg _ _)) (by omega)
  · intro a ha
    have he := column_relation_eval M hi fresh bounds a ha
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.add_zero]
    have hg : G.eval a = monoEval a (mono n M) := by simp [G, Poly.eval]
    rw [hg]
    change (p : Int) ∣ monoEval a (mono n M) * R.eval a - _
    rw [he]
    simp [R]

end Programme.«20261104-1627-proof-complexity».ColumnRelationCertificate
#print axioms Programme.«20261104-1627-proof-complexity».ColumnRelationCertificate.blocked_zero
#print axioms Programme.«20261104-1627-proof-complexity».ColumnRelationCertificate.column_relation_eval

#print axioms Programme.«20261104-1627-proof-complexity».ColumnRelationCertificate.column_relation_nsIn
