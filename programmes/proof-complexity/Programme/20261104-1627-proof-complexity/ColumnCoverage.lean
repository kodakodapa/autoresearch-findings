import Programme.«20261104-1627-proof-complexity».MatchingDeletion

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels

/-- A nonempty finite edge list contains an edge of maximal column. -/
theorem maximal_column (M : Matching) (hne : M ≠ []) :
    ∃ x ∈ M, ∀ a ∈ M, a.2 ≤ x.2 := by
  induction M with
  | nil => exact False.elim (hne rfl)
  | cons x M ih =>
    by_cases he : M = []
    · subst M; exact ⟨x, by simp, by simp⟩
    · obtain ⟨y, hy, hm⟩ := ih he
      by_cases hxy : x.2 ≤ y.2
      · refine ⟨y, by simp [hy], ?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hxy
        · exact hm a ha
      · refine ⟨x, by simp, ?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact Nat.le_refl _
        · have := hm a ha; omega

def columnExtensions (m n d : Nat) (N : Matching) : List Matching :=
  ((matchings m n d).filter (compatible N)).flatMap fun E =>
    ((cols n (N ++ E)).filter (fun j => E.all fun e => e.2 < j)).flatMap
      fun j => (rows m (N ++ E)).map fun i => ordered (E ++ [(i,j)])

theorem column_extensions_coverage (m n d : Nat) (N M : Matching) :
    M ∈ columnExtensions m n d N ↔
      M ∈ (matchings m n (d+1)).filter (compatible N) := by
  constructor
  · intro h
    simp only [columnExtensions, List.mem_flatMap, List.mem_filter, List.mem_map] at h
    obtain ⟨E, ⟨hE,hNE⟩, j, ⟨hj,_⟩, i, hi, rfl⟩ := h
    have hr : i ∈ rows m E := by
      simp only [rows, List.mem_filter, freeRow, List.all_append,
        Bool.and_eq_true] at hi ⊢
      exact ⟨hi.1, hi.2.2⟩
    have hc : j ∈ cols n E := by
      simp only [cols, List.mem_filter, freeCol, List.all_append,
        Bool.and_eq_true] at hj ⊢
      exact ⟨hj.1, hj.2.2⟩
    refine List.mem_filter.mpr ⟨ordered_extension_mem hE hr hc, ?_⟩
    have hp := List.mergeSort_perm (E ++ [(i,j)]) (fun a b => a.1 ≤ b.1)
    apply List.all_eq_true.mpr
    intro a ha
    have ha' := hp.mem_iff.mp ha
    rcases List.mem_append.mp ha' with ha' | ha'
    · exact List.all_eq_true.mp hNE a ha'
    · simp only [List.mem_singleton] at ha'
      subst a
      simp only [rows, cols, List.mem_filter, freeRow, freeCol, List.all_append,
        Bool.and_eq_true] at hi hj
      simp only [Bool.and_eq_true]
      exact ⟨hi.2.1, hj.2.1⟩
  · intro h
    obtain ⟨hM,hN⟩ := List.mem_filter.mp h
    have hn : M ≠ [] := by
      intro he; have := matching_length hM; simp [he] at this
    obtain ⟨x,hx,hm⟩ := maximal_column M hn
    exact column_max_preimage hM hx hN hm

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.maximal_column
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.column_extensions_coverage
