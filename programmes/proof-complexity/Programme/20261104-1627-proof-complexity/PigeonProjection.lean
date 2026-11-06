import Programme.«20261104-1627-proof-complexity».PigeonSplit

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels

theorem matching_drop_last {m n d : Nat} (M : Matching)
    (hM : M ∈ matchings (m+1) n d) (ha : ∀ e ∈ M, e.1 ≠ m) :
    M ∈ matchings m n d := by
  induction d generalizing M with
  | zero => simpa only [matchings] using hM
  | succ d ih =>
    simp only [matchings, List.mem_flatMap, List.mem_map] at hM ⊢
    obtain ⟨N, hN, i, hi, j, hj, rfl⟩ := hM
    have haN : ∀ e ∈ N, e.1 ≠ m := by
      intro e he
      exact ha e (List.mem_append_left _ he)
    have him : i ≠ m := ha (i,j) (by simp)
    refine ⟨N, ih N hN haN, i, ?_, j, hj, rfl⟩
    simp only [List.mem_filter, rows, List.mem_range] at hi ⊢
    exact ⟨⟨by omega, hi.1.2⟩, hi.2⟩

theorem matching_add_last {m n d : Nat} (M : Matching)
    (hM : M ∈ matchings m n d) : M ∈ matchings (m+1) n d := by
  induction d generalizing M with
  | zero => simpa only [matchings] using hM
  | succ d ih =>
    simp only [matchings, List.mem_flatMap, List.mem_map] at hM ⊢
    obtain ⟨N, hN, i, hi, j, hj, rfl⟩ := hM
    refine ⟨N, ih N hN, i, ?_, j, hj, rfl⟩
    simp only [List.mem_filter, rows, List.mem_range] at hi ⊢
    exact ⟨⟨by omega, hi.1.2⟩, hi.2⟩

theorem matching_rows_lt {m n d : Nat} {M : Matching}
    (hM : M ∈ matchings m n d) : ∀ e ∈ M, e.1 < m := by
  induction d generalizing M with
  | zero => simp only [matchings, List.mem_singleton] at hM; subst M; simp
  | succ d ih =>
    simp only [matchings, List.mem_flatMap, List.mem_map] at hM
    obtain ⟨N, hN, i, hi, j, hj, rfl⟩ := hM
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact ih hN e he
    · simp only [List.mem_singleton] at he
      subst e
      exact (List.mem_range.mp (List.mem_filter.mp (List.mem_filter.mp hi).1).1)

theorem label_drop_last {m n d : Nat} (g : Label)
    (hg : g ∈ labels (m+1) n d) (hb : pigeonBlock m g = 1) :
    g ∈ labels m n d := by
  have hu : usesPigeon m g = false := by
    unfold pigeonBlock at hb
    split at hb <;> simp_all
  have ha : ∀ e ∈ g.base, e.1 ≠ m := by
    intro e he heq
    have : usesPigeon m g = true := by
      simp only [usesPigeon, List.any_eq_true]
      exact ⟨e, he, by simp [heq]⟩
    simp_all
  have hm : g.isRow = true → g.mark ≠ m := by
    intro hr heq
    simp [pigeonBlock, hu, hr, heq] at hb
  unfold labels at hg ⊢
  split at hg
  · contradiction
  · rename_i hd
    rw [if_neg hd]
    simp only [List.mem_flatMap, List.mem_append, List.mem_map] at hg ⊢
    obtain ⟨M, hM, hg⟩ := hg
    rcases hg with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
    · refine ⟨M, matching_drop_last M hM ha, Or.inl ⟨i, ?_, rfl⟩⟩
      simp only [rows, List.mem_filter, List.mem_range] at hi ⊢
      exact ⟨by have := hm rfl; simp only at this; omega, hi.2⟩
    · exact ⟨M, matching_drop_last M hM ha, Or.inr ⟨j, hj, rfl⟩⟩

theorem splitPigeon_one_valid {m n d : Nat} {v : Vector}
    (hv : valid (m+1) n d v) : valid m n d (splitPigeon m 1 v) := by
  intro t ht
  obtain ⟨ht, hb⟩ := List.mem_filter.mp ht
  exact label_drop_last t.2 (hv t ht) (by simpa using hb)

theorem label_add_last {m n d : Nat} (g : Label)
    (hg : g ∈ labels m n d) :
    g ∈ labels (m+1) n d ∧ pigeonBlock m g = 1 := by
  unfold labels at hg
  split at hg
  · contradiction
  · rename_i hd
    simp only [List.mem_flatMap, List.mem_append, List.mem_map] at hg
    obtain ⟨M, hM, hg⟩ := hg
    have hu : usesPigeon m (⟨M,true,0⟩ : Label) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨e, he, hm⟩ := List.any_eq_true.mp h
      have he' := matching_rows_lt hM e he
      simp only [beq_iff_eq] at hm
      omega
    have hu' (b : Bool) (i : Nat) : usesPigeon m (⟨M,b,i⟩ : Label) = false := hu
    rcases hg with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
    · have him : i < m := List.mem_range.mp (List.mem_filter.mp hi).1
      constructor
      · simp only [labels, hd, ↓reduceIte, List.mem_flatMap, List.mem_append, List.mem_map]
        refine ⟨M, matching_add_last M hM, Or.inl ⟨i, ?_, rfl⟩⟩
        simp only [rows, List.mem_filter, List.mem_range] at hi ⊢
        exact ⟨by omega, hi.2⟩
      · simp [pigeonBlock, hu', show i ≠ m by omega]
    · constructor
      · simp only [labels, hd, ↓reduceIte, List.mem_flatMap, List.mem_append, List.mem_map]
        exact ⟨M, matching_add_last M hM, Or.inr ⟨j, hj, rfl⟩⟩
      · simp [pigeonBlock, hu']

/-- The first block is precisely the original smaller-board label set. -/
theorem label_first_block_iff {m n d : Nat} (g : Label) :
    (g ∈ labels (m+1) n d ∧ pigeonBlock m g = 1) ↔
      g ∈ labels m n d := by
  exact ⟨fun h => label_drop_last g h.1 h.2, label_add_last g⟩

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.label_first_block_iff
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.matching_drop_last
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.label_drop_last
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.splitPigeon_one_valid
