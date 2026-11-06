import Programme.«20261104-1627-proof-complexity».BoundedRelationCertificates
import Programme.«20261104-1627-proof-complexity».OccupiedMarks
import Programme.«20261104-1627-proof-complexity».SortedSupports
namespace Programme.«20261104-1627-proof-complexity».MultiplierLabels
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261025-0459-proof-complexity».MatchQuot
open Programme.«20261104-1627-proof-complexity».BoundedRelationCertificates

theorem row_product {n k d i : Nat} {M : Matching}
    (hM : M ∈ matchings (n+k) n d) (hi : i < n+k) :
    ∃ v : Vector, (∀ t ∈ v, t.2 ∈ labels (n+k) n (d+1)) ∧
      ∀ a, Good (ontoFPHP n k) a →
      (relations (n+k) n v).eval a =
        monoEval a (mono n M) * (sumOne (fun j => var n i j) n).eval a := by
  classical
  have hb := matching_bounds hM
  by_cases hf : ∀ e ∈ M, e.1 ≠ i
  · have hg : (⟨M,true,i⟩ : Label) ∈ labels (n+k) n (d+1) := by
      simp only [labels, Nat.add_sub_cancel, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, if_false, List.mem_flatMap]
      refine ⟨M,hM,List.mem_append_left _ (List.mem_map.mpr ⟨i,?_,rfl⟩)⟩
      simpa only [rows, List.mem_filter, List.mem_range, freeRow,
        List.all_eq_true, bne_iff_ne] using And.intro hi hf
    refine ⟨[(1,⟨M,true,i⟩)], ?_, ?_⟩
    · intro t ht
      have he : t = (1,⟨M,true,i⟩) := by simpa using ht
      simpa [he] using hg
    · intro a ha
      rw [relations_cons_eval]
      simpa [relations, Poly.eval] using
        Programme.«20261104-1627-proof-complexity».RowRelationCertificate.row_relation_eval M hi hf (fun e he => (hb e he).1) a ha
  · have hex : ∃ e ∈ M, e.1 = i := by
      by_cases hx : ∃ e ∈ M, e.1 = i
      · exact hx
      · exact False.elim (hf (by intro e he hei; exact hx ⟨e,he,hei⟩))
    obtain ⟨e,he,hei⟩ := hex
    refine ⟨[],by simp,?_⟩
    intro a ha
    have hz := (Programme.«20261104-1627-proof-complexity».OccupiedMarks.occupied_products_zero M
      (show (i,e.2) ∈ M from by simpa [← hei] using he)
      hi (hb e he).2 a ha).1
    simpa [relations, Poly.eval] using hz.symm

theorem column_product {n k d j : Nat} {M : Matching}
    (hM : M ∈ matchings (n+k) n d) (hj : j < n) :
    ∃ v : Vector, (∀ t ∈ v, t.2 ∈ labels (n+k) n (d+1)) ∧
      ∀ a, Good (ontoFPHP n k) a →
      (relations (n+k) n v).eval a =
        monoEval a (mono n M) * (sumOne (fun i => var n i j) (n+k)).eval a := by
  classical
  have hb := matching_bounds hM
  by_cases hf : ∀ e ∈ M, e.2 ≠ j
  · have hg : (⟨M,false,j⟩ : Label) ∈ labels (n+k) n (d+1) := by
      simp only [labels, Nat.add_sub_cancel, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, if_false, List.mem_flatMap]
      refine ⟨M,hM,List.mem_append_right _ (List.mem_map.mpr ⟨j,?_,rfl⟩)⟩
      simpa only [cols, List.mem_filter, List.mem_range, freeCol,
        List.all_eq_true, bne_iff_ne] using And.intro hj hf
    refine ⟨[(1,⟨M,false,j⟩)], ?_, ?_⟩
    · intro t ht
      have he : t = (1,⟨M,false,j⟩) := by simpa using ht
      simpa [he] using hg
    · intro a ha
      rw [relations_cons_eval]
      simpa [relations, Poly.eval] using
        Programme.«20261104-1627-proof-complexity».ColumnRelationCertificate.column_relation_eval M hj hf (fun e he => (hb e he).2) a ha
  · have hex : ∃ e ∈ M, e.2 = j := by
      by_cases hx : ∃ e ∈ M, e.2 = j
      · exact hx
      · exact False.elim (hf (by intro e he hej; exact hx ⟨e,he,hej⟩))
    obtain ⟨e,he,hej⟩ := hex
    refine ⟨[],by simp,?_⟩
    intro a ha
    have hz := (Programme.«20261104-1627-proof-complexity».OccupiedMarks.occupied_products_zero M
      (show (e.1,j) ∈ M from by simpa [← hej] using he)
      (hb e he).1 hj a ha).2
    simpa [relations, Poly.eval] using hz.symm
theorem mono_decode (n : Nat) (s : List Nat) :
    mono n (Programme.«20261104-1627-proof-complexity».MatchingCoverage.decode n s) = s := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    simp only [Programme.«20261104-1627-proof-complexity».MatchingCoverage.decode, mono, List.map_cons] at *
    rw [ih]
    congr 1
    simpa only [Nat.mul_comm] using Nat.div_add_mod x n

theorem safe_row_product {n k i : Nat} (s : List Nat)
    (hs : Programme.«20261104-1627-proof-complexity».MatchingReduction.Safe (ontoFPHP n k) s) (hn : s.Nodup)
    (hb : ∀ x ∈ s, x < (n+k)*n) (hi : i < n+k) :
    ∃ v : Vector, (∀ t ∈ v, t.2 ∈ labels (n+k) n (s.length+1)) ∧
      ∀ a, Good (ontoFPHP n k) a →
      (relations (n+k) n v).eval a =
        monoEval a s * (sumOne (fun j => var n i j) n).eval a := by
  obtain ⟨v,hv,he⟩ := row_product (Programme.«20261104-1627-proof-complexity».SortedSupports.sorted_decode_mem s hn hs hb) hi
  refine ⟨v,hv,?_⟩
  intro a ha
  simpa only [mono_decode, Programme.«20261104-1627-proof-complexity».SortedSupports.mono_sort] using he a ha

theorem safe_column_product {n k j : Nat} (s : List Nat)
    (hs : Programme.«20261104-1627-proof-complexity».MatchingReduction.Safe (ontoFPHP n k) s) (hn : s.Nodup)
    (hb : ∀ x ∈ s, x < (n+k)*n) (hj : j < n) :
    ∃ v : Vector, (∀ t ∈ v, t.2 ∈ labels (n+k) n (s.length+1)) ∧
      ∀ a, Good (ontoFPHP n k) a →
      (relations (n+k) n v).eval a =
        monoEval a s * (sumOne (fun i => var n i j) (n+k)).eval a := by
  obtain ⟨v,hv,he⟩ := column_product (Programme.«20261104-1627-proof-complexity».SortedSupports.sorted_decode_mem s hn hs hb) hj
  refine ⟨v,hv,?_⟩
  intro a ha
  simpa only [mono_decode, Programme.«20261104-1627-proof-complexity».SortedSupports.mono_sort] using he a ha
end Programme.«20261104-1627-proof-complexity».MultiplierLabels
#print axioms Programme.«20261104-1627-proof-complexity».MultiplierLabels.row_product
#print axioms Programme.«20261104-1627-proof-complexity».MultiplierLabels.column_product

#print axioms Programme.«20261104-1627-proof-complexity».MultiplierLabels.safe_row_product
#print axioms Programme.«20261104-1627-proof-complexity».MultiplierLabels.safe_column_product
