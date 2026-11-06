import Programme.«20261104-1627-proof-complexity».BoardCollisions
import Programme.«20261104-1627-proof-complexity».CertificateReassembly
import Programme.«20261104-1627-proof-complexity».MatchingLabels
namespace Programme.«20261104-1627-proof-complexity».RowRelationCertificate
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

theorem blocked_zero {n k i j : Nat} {M : Matching}
    (hi : i < n+k) (fresh : ∀ e ∈ M, e.1 ≠ i)
    (bounds : ∀ e ∈ M, e.1 < n+k) (blocked : freeCol M j = false)
    (hj : j < n) {a : Nat → Bool} (ha : Good (ontoFPHP n k) a) :
    xv (i*n+j) a * monoEval a (mono n M) = 0 := by
  have ex : ∃ e ∈ M, e.2 = j := by
    classical
    by_cases h : ∃ e ∈ M, e.2 = j
    · exact h
    have hf : freeCol M j = true := by
      simp only [freeCol, List.all_eq_true, bne_iff_ne]
      intro e he heq
      exact h ⟨e, he, heq⟩
    rw [hf] at blocked
    cases blocked
  obtain ⟨e, he, hej⟩ := ex
  by_cases hx : a (i*n+j) = true
  · have hz : a (e.1*n+j) ≠ true := by
      intro hetrue
      have hne := fresh e he
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact ha _ _ (Programme.«20261104-1627-proof-complexity».BoardCollisions.collision_mem (bounds e he) hi hj h)
          ⟨by simpa [var] using hetrue, by simpa [var] using hx⟩
      · exact ha _ _ (Programme.«20261104-1627-proof-complexity».BoardCollisions.collision_mem hi (bounds e he) hj h)
          ⟨by simpa [var] using hx, by simpa [var] using hetrue⟩
    have hm : monoEval a (mono n M) = 0 := by
      rw [monoEval_all, if_neg]
      intro hall
      apply hz
      apply hall
      exact List.mem_map.mpr ⟨e, he, by simp [hej]⟩
    rw [hm, Int.mul_zero]
  · simp [xv, hx]

theorem row_relation_eval {n k i : Nat} (M : Matching)
    (hi : i < n+k) (fresh : ∀ e ∈ M, e.1 ≠ i)
    (bounds : ∀ e ∈ M, e.1 < n+k)
    (a : Nat → Bool) (ha : Good (ontoFPHP n k) a) :
    (relation (n+k) n ⟨M,true,i⟩).eval a =
      monoEval a (mono n M) * (sumOne (fun j => var n i j) n).eval a := by
  have he : ((cols n M).map (fun j => xv (i*n+j) a * monoEval a (mono n M))).sum =
      ((List.range n).map (fun j => xv (i*n+j) a * monoEval a (mono n M))).sum := by
    unfold cols
    rw [sum_filter]
    congr 1
    apply List.map_congr_left
    intro j hj
    by_cases h : freeCol M j = true
    · simp [h]
    · have hf : freeCol M j = false := by simpa using h
      simp [hf, blocked_zero hi fresh bounds hf (List.mem_range.mp hj) ha]
  rw [relation, eval_sub]
  have ht : (topLabel (n+k) n ⟨M,true,i⟩).eval a =
      ((cols n M).map (fun j => xv (i*n+j) a * monoEval a (mono n M))).sum := by
    simp [topLabel, Poly.eval, Function.comp_def, Programme.«20261025-0459-proof-complexity».MatchQuot.monoEval_cons]
  rw [ht]
  simp only [Poly.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.one_mul, Int.add_zero]
  change _ - monoEval a (mono n M) = monoEval a (mono n M) * (sumOne (fun j => var n i j) n).eval a
  rw [he, sumOne_eval, rsum_range]
  have hs : ∀ L : List Nat,
      (L.map (fun j => xv (i*n+j) a * monoEval a (mono n M))).sum =
        monoEval a (mono n M) * (L.map (fun j => xv (i*n+j) a)).sum := by
    intro L
    induction L with
    | nil => simp
    | cons j L ih => simp only [List.map_cons, List.sum_cons, ih, Int.mul_add];
                     rw [Int.mul_comm (xv (i*n+j) a)]
  rw [hs]
  simp [var, Int.mul_sub]
theorem row_relation_nsIn {p n k i : Nat} (M : Matching)
    (hi : i < n+k) (fresh : ∀ e ∈ M, e.1 ≠ i)
    (bounds : ∀ e ∈ M, e.1 < n+k) :
    NSIn p (ontoFPHP n k) (M.length+1)
      (relation (n+k) n ⟨M,true,i⟩).eval := by
  let G : Poly Nat := ⟨[(1,mono n M)]⟩
  let R := sumOne (fun j => var n i j) n
  refine ⟨[(G,R)], ?_, ?_⟩
  · intro e he
    have ee : e = (G,R) := by simpa using he
    subst e
    constructor
    · unfold R
      have hr : sumOne (fun j => var n i j) n ∈ pigeonAx n k :=
        List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
      simp only [ontoFPHP, List.mem_append]
      exact Or.inl (Or.inl (Or.inl hr))
    · have hg : G.deg ≤ M.length := by
        rw [deg_le_iff]
        intro t ht
        have et : t = (1,mono n M) := by simpa [G] using ht
        subst t
        simp [mono]
      exact Nat.le_trans (Nat.add_le_add hg (sumOne_deg _ _)) (by omega)
  · intro a ha
    have he := row_relation_eval M hi fresh bounds a ha
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.add_zero]
    have hg : G.eval a = monoEval a (mono n M) := by simp [G, Poly.eval]
    rw [hg]
    change (p : Int) ∣ monoEval a (mono n M) * R.eval a - _
    rw [he]
    simp [R]

end Programme.«20261104-1627-proof-complexity».RowRelationCertificate
#print axioms Programme.«20261104-1627-proof-complexity».RowRelationCertificate.blocked_zero
#print axioms Programme.«20261104-1627-proof-complexity».RowRelationCertificate.row_relation_eval

#print axioms Programme.«20261104-1627-proof-complexity».RowRelationCertificate.row_relation_nsIn
