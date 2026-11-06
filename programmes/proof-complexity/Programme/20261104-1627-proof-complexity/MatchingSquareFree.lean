import Programme.«20261104-1627-proof-complexity».BoundedRelationCertificates
namespace Programme.«20261104-1627-proof-complexity».MatchingSquareFree
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261104-1627-proof-complexity».BoundedRelationCertificates

theorem fresh_code {m n d i j : Nat} {M : Matching}
    (hM : M ∈ matchings m n d) (hi : freeRow M i = true)
    (hj : j < n) : i*n+j ∉ mono n M := by
  intro h
  obtain ⟨e,he,eq⟩ := List.mem_map.mp h
  have hb := (matching_bounds hM e he).2
  have hn : 0 < n := by omega
  have hd : (e.1*n+e.2)/n = e.1 := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb]; omega
  have hd' : (i*n+j)/n = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hj]; omega
  have ee : e.1 = i := by rw [eq, hd'] at hd; exact hd.symm
  have hf : e.1 ≠ i := by
    exact (List.all_eq_true.mp hi) e he |> of_decide_eq_true
  exact hf ee

theorem matching_nodup {m n d : Nat} {M : Matching}
    (hM : M ∈ matchings m n d) : (mono n M).Nodup := by
  induction d generalizing M with
  | zero => simp only [matchings, List.mem_singleton] at hM; subst M; simp [mono]
  | succ d ih =>
    simp only [matchings, List.mem_flatMap, List.mem_map] at hM
    obtain ⟨N,hN,i,hi,j,hj,rfl⟩ := hM
    have hf := (List.mem_filter.mp (List.mem_filter.mp hi).1).2
    have hb := List.mem_range.mp (List.mem_filter.mp hj).1
    have hx := fresh_code hN hf hb
    simp only [mono, List.map_append, List.map_cons, List.map_nil]
    change ((mono n N) ++ [i*n+j]).Nodup
    apply List.nodup_append.mpr
    refine ⟨ih hN, by simp, ?_⟩
    intro a ha b hb
    have eb : b = i*n+j := by simpa using hb
    subst b
    intro ee
    exact hx (ee ▸ ha)
theorem label_squarefree {m n d : Nat} {g : Label}
    (hg : g ∈ labels m n d) :
    ∀ t ∈ (relation m n g).terms, t.2.Nodup := by
  have hd : d ≠ 0 := by intro h; subst d; simpa [labels] using hg
  unfold labels at hg
  rw [if_neg hd] at hg
  obtain ⟨M,hM,hg⟩ := List.mem_flatMap.mp hg
  have hm := matching_nodup hM
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hg
    intro t ht
    simp only [relation, topLabel, Programme.«20261024-1633-proof-complexity».NS.Poly.sub,
      List.mem_append, Bool.false_eq_true, ite_true, ite_false, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with ht | ht
    · obtain ⟨j,hj,rfl⟩ := ht
      exact List.nodup_cons.mpr ⟨fresh_code hM (List.mem_filter.mp hi).2
        (List.mem_range.mp (List.mem_filter.mp hj).1),hm⟩
    · obtain ⟨u,hu,rfl⟩ := ht
      have : u = (1,mono n M) := by simpa using hu
      subst u; exact hm
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hg
    intro t ht
    simp only [relation, topLabel, Programme.«20261024-1633-proof-complexity».NS.Poly.sub,
      List.mem_append, Bool.false_eq_true, ite_true, ite_false, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with ht | ht
    · obtain ⟨i,hi,rfl⟩ := ht
      exact List.nodup_cons.mpr ⟨fresh_code hM (List.mem_filter.mp hi).2
        (List.mem_range.mp (List.mem_filter.mp hj).1),hm⟩
    · obtain ⟨u,hu,rfl⟩ := ht
      have : u = (1,mono n M) := by simpa using hu
      subst u; exact hm
theorem bounded_squarefree {m n D : Nat} (v : Vector)
    (hv : ∀ z ∈ v, ∃ d, d ≤ D ∧ z.2 ∈ labels m n d) :
    ∀ t ∈ (relations m n v).terms, t.2.Nodup := by
  intro t ht
  obtain ⟨z,hz,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨u,hu,eq⟩ := List.mem_map.mp ht
  obtain ⟨d,hd,hg⟩ := hv z hz
  have hh := label_squarefree hg u hu
  subst t
  exact hh
end Programme.«20261104-1627-proof-complexity».MatchingSquareFree
#print axioms Programme.«20261104-1627-proof-complexity».MatchingSquareFree.matching_nodup
#print axioms Programme.«20261104-1627-proof-complexity».MatchingSquareFree.label_squarefree
#print axioms Programme.«20261104-1627-proof-complexity».MatchingSquareFree.bounded_squarefree
