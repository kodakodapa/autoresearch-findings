import Programme.«20261104-1627-proof-complexity».OmissionEnumeration

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels

theorem matching_pull_mem {m n d h : Nat} (hh : h ≤ n) (M : Matching)
    (hM : M ∈ matchings m (n+1) d) (ha : ∀ e ∈ M, e.2 ≠ h) :
    pullMatching h M ∈ matchings m n d := by
  induction d generalizing M with
  | zero =>
    simp only [matchings, List.mem_singleton] at hM ⊢
    subst M
    rfl
  | succ d ih =>
    simp only [matchings, List.mem_flatMap, List.mem_map] at hM ⊢
    obtain ⟨N, hN, i, hi, j, hj, rfl⟩ := hM
    have haN : ∀ e ∈ N, e.2 ≠ h := by
      intro e he
      exact ha e (List.mem_append_left _ he)
    have hjh : j ≠ h := ha (i,j) (by simp)
    refine ⟨pullMatching h N, ih N hN haN, i, ?_, closeHole h j, ?_, ?_⟩
    · simpa [rows, freeRow, pullMatching, List.all_map, Function.comp_def] using hi
    · simp only [cols, List.mem_filter, List.mem_range] at hj ⊢
      refine ⟨?_, ?_⟩
      · unfold closeHole
        split <;> omega
      · rw [freeCol, List.all_eq_true] at hj
        simp only [freeCol, pullMatching, List.all_map, List.all_eq_true]
        intro e he
        apply Bool.eq_iff_iff.mpr
        simp only [Function.comp_apply, bne_iff_ne]
        constructor
        · intro _; trivial
        · intro _ heq
          have heh := haN e he
          have eqj := congrArg (omitHole h) heq
          rw [omit_close h e.2 heh, omit_close h j hjh] at eqj
          have := hj.2 e he
          simp only [bne_iff_ne] at this
          exact this eqj
    · simp [pullMatching]

theorem matching_omission_coverage {m n d h : Nat} (hh : h ≤ n)
    (M : Matching) (hM : M ∈ matchings m (n+1) d)
    (ha : ∀ e ∈ M, e.2 ≠ h) :
    ∃ N ∈ matchings m n d, pushMatching h N = M := by
  exact ⟨pullMatching h M, matching_pull_mem hh M hM ha, push_pull h M ha⟩

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.matching_pull_mem
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.matching_omission_coverage
