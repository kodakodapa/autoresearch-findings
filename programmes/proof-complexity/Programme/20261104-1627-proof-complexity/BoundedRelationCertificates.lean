import Programme.«20261104-1627-proof-complexity».RowRelationCertificate
import Programme.«20261104-1627-proof-complexity».ColumnRelationCertificate
import Programme.«20261104-1627-proof-complexity».HomogeneousLabels
namespace Programme.«20261104-1627-proof-complexity».BoundedRelationCertificates
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261104-1627-proof-complexity».BooleanReconstruction

theorem matching_bounds {m n d : Nat} {M : Matching}
    (h : M ∈ matchings m n d) : ∀ e ∈ M, e.1 < m ∧ e.2 < n := by
  induction d generalizing M with
  | zero => simp only [matchings, List.mem_singleton] at h; subst M; simp
  | succ d ih =>
    simp only [matchings, List.mem_flatMap, List.mem_map] at h
    obtain ⟨N,hN,i,hi,j,hj,rfl⟩ := h
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact ih hN e he
    · have ee : e = (i,j) := by simpa using he
      subst e
      exact ⟨List.mem_range.mp (List.mem_filter.mp (List.mem_filter.mp hi).1).1,
        List.mem_range.mp (List.mem_filter.mp hj).1⟩

theorem label_nsIn {p n k d : Nat} {g : Label}
    (hg : g ∈ labels (n+k) n d) :
    NSIn p (ontoFPHP n k) d (relation (n+k) n g).eval := by
  have hd : d ≠ 0 := by intro h; subst d; simpa [labels] using hg
  have hl := label_length hg
  unfold labels at hg
  rw [if_neg hd] at hg
  obtain ⟨M,hM,hg⟩ := List.mem_flatMap.mp hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hg
    have hb := matching_bounds hM
    have hf : ∀ e ∈ M, e.1 ≠ i := by
      simpa only [freeRow, List.all_eq_true, bne_iff_ne] using (List.mem_filter.mp hi).2
    apply nsIn_mono (Programme.«20261104-1627-proof-complexity».RowRelationCertificate.row_relation_nsIn M
      (List.mem_range.mp (List.mem_filter.mp hi).1) hf (fun e he => (hb e he).1))
    change M.length = d-1 at hl
    omega
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hg
    have hb := matching_bounds hM
    have hf : ∀ e ∈ M, e.2 ≠ j := by
      simpa only [freeCol, List.all_eq_true, bne_iff_ne] using (List.mem_filter.mp hj).2
    apply nsIn_mono (Programme.«20261104-1627-proof-complexity».ColumnRelationCertificate.column_relation_nsIn M
      (List.mem_range.mp (List.mem_filter.mp hj).1) hf (fun e he => (hb e he).2))
    change M.length = d-1 at hl
    omega

private theorem scaled_eval (c : Int) (L : List (Int × List Nat)) (a : Nat → Bool) :
    ((L.map fun t => (c*t.1,t.2)).map (fun t => t.1 * monoEval a t.2)).sum =
      c * (L.map (fun t => t.1 * monoEval a t.2)).sum := by
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons, ih, Int.mul_add, Int.mul_assoc]

theorem relations_cons_eval (m n : Nat) (t : Int × Label) (v : Vector)
    (a : Nat → Bool) :
    (relations m n (t::v)).eval a =
      t.1 * (relation m n t.2).eval a + (relations m n v).eval a := by
  simp only [relations, List.flatMap_cons, Poly.eval, List.map_append, List.sum_append]
  rw [scaled_eval]

theorem bounded_relations_nsIn {p n k D : Nat} (v : Vector)
    (hv : ∀ t ∈ v, ∃ d, d ≤ D ∧ t.2 ∈ labels (n+k) n d) :
    NSIn p (ontoFPHP n k) D (relations (n+k) n v).eval := by
  induction v with
  | nil => exact ⟨[], by simp, by simp [relations, Poly.eval]⟩
  | cons t v ih =>
    obtain ⟨d,hd,hg⟩ := hv t (by simp)
    have ht := nsIn_mono (label_nsIn (p := p) hg) hd
    have hh := nsIn_lin t.1 1 ht (ih (fun s hs => hv s (by simp [hs])))
    apply nsIn_congr hh
    intro a
    rw [relations_cons_eval]
    simp
theorem W_nsIn {p n k D : Nat} {P : Poly Nat}
    (h : W p (n+k) n D P) : NSIn p (ontoFPHP n k) D P.eval := by
  obtain ⟨v,hv,he⟩ := h
  apply nsIn_congr (bounded_relations_nsIn v hv)
  intro a
  have hh := Int.dvd_neg.mpr (Programme.«20261029-1156-proof-complexity».StdPC.peq_eval he a)
  simpa [Int.neg_sub, relations] using hh
end Programme.«20261104-1627-proof-complexity».BoundedRelationCertificates
#print axioms Programme.«20261104-1627-proof-complexity».BoundedRelationCertificates.bounded_relations_nsIn

#print axioms Programme.«20261104-1627-proof-complexity».BoundedRelationCertificates.W_nsIn
