import Programme.«20261101-0614-proof-complexity».OnehotRestriction

namespace Programme.«20261101-0614-proof-complexity».OnehotReproof
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity».RestrictionTarget
open Programme.«20261101-0614-proof-complexity».Composition

theorem clause_fixed (ρ : Substitution) : ∀ c : Clause,
    (∀ l ∈ c, ρ l.1 = .inr l.1) → clause ρ c = some c := by
  intro c
  induction c with
  | nil => intro _; rfl
  | cons l c ih =>
    intro h
    have h1 := h l (by simp)
    have h2 := ih (fun m hm => h m (by simp [hm]))
    obtain ⟨v, b⟩ := l
    simp only [clause, literal] at h1 ⊢
    rw [h1]; simp only; rw [h2]; rfl

theorem clause_true (ρ : Substitution) : ∀ c : Clause,
    (∃ l ∈ c, literal ρ l = .inl true) → clause ρ c = none := by
  intro c
  induction c with
  | nil => intro ⟨l, hl, _⟩; simp at hl
  | cons m c ih =>
    rintro ⟨l, hl, hlt⟩
    simp only [clause]
    rcases List.mem_cons.mp hl with rfl | hl'
    · rw [hlt]
    · cases hm : literal ρ m with
      | inr k => simp [ih ⟨l, hl', hlt⟩]
      | inl b => cases b
                 · exact ih ⟨l, hl', hlt⟩
                 · rfl

theorem fixed (ρ : Substitution) (v : Nat → Var) (n : Nat)
    (h : ∀ i < n, ρ (v i) = .inr (v i)) :
    ∀ c ∈ onehot n v, clause ρ c = some c := by
  intro c hc
  apply clause_fixed
  intro l hl
  by_cases hn : n = 1
  · simp [onehot, hn] at hc
  · simp only [onehot, if_neg hn, List.mem_append, List.mem_singleton,
      List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range] at hc
    rcases hc with rfl | ⟨i, hi, k, ⟨hk, _⟩, rfl⟩
    · simp only [List.mem_map, List.mem_range] at hl
      obtain ⟨i, hi, rfl⟩ := hl
      exact h i hi
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact h i hi
      · exact h k hk

theorem selected (ρ : Substitution) (v : Nat → Var) (n j : Nat)
    (hj : j < n) (h : ∀ i < n, ρ (v i) = .inl (i == j)) :
    ∀ c ∈ onehot n v, clause ρ c = none := by
  intro c hc
  apply clause_true
  by_cases hn : n = 1
  · simp [onehot, hn] at hc
  · simp only [onehot, if_neg hn, List.mem_append, List.mem_singleton,
      List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range] at hc
    rcases hc with rfl | ⟨i, hi, k, ⟨hk, hik⟩, rfl⟩
    · refine ⟨pos (v j), by simp [List.mem_map]; exact ⟨j, hj, rfl⟩, ?_⟩
      simp [literal, pos, h j hj]
    · have hik' : i < k := of_decide_eq_true hik
      by_cases hij : i = j
      · subst hij
        refine ⟨minus (v k), by simp, ?_⟩
        have : (k == i) = false := beq_eq_false_iff_ne.mpr (by omega)
        simp [literal, minus, h k hk, this]
      · refine ⟨minus (v i), by simp, ?_⟩
        have : (i == j) = false := beq_eq_false_iff_ne.mpr hij
        simp [literal, minus, h i hi, this]

#print axioms fixed
#print axioms selected
end Programme.«20261101-0614-proof-complexity».OnehotReproof
