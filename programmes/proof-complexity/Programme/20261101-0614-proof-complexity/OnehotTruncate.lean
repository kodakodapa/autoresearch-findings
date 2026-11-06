import Programme.«20261101-0614-proof-complexity».OnehotRestriction
namespace Programme.«20261101-0614-proof-complexity».Composition
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity».RestrictionTarget

theorem domain_truncate (ρ : Substitution) (v : Nat → Var) (n : Nat)
    (h : ∀ i < n, ρ (v i) = .inr (v i)) (hn : ρ (v n) = .inl false) :
    clause ρ ((List.range (n+1)).map (fun i => pos (v i))) =
      some ((List.range n).map (fun i => pos (v i))) := by
  rw [List.range_succ, List.map_append, clause_append, domain_fixed ρ v n h]
  simp [clause, literal, pos, hn]

theorem onehot_truncate (ρ : Substitution) (v : Nat → Var) (n : Nat)
    (hn : 2 ≤ n) (h : ∀ i < n, ρ (v i) = .inr (v i))
    (hlast : ρ (v n) = .inl false) :
    ∀ c ∈ onehot (n+1) v, ∀ t, clause ρ c = some t → t ∈ onehot n v := by
  intro c hc t ht
  have hne : n ≠ 1 := by omega
  have hne' : n+1 ≠ 1 := by omega
  simp only [onehot, if_neg hne', List.mem_append, List.mem_singleton,
    List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range] at hc
  rcases hc with rfl | ⟨i, hi, j, ⟨hj, hij⟩, rfl⟩
  · rw [domain_truncate ρ v n h hlast] at ht
    cases ht
    simp [onehot, hne]
  · have hij' : i < j := of_decide_eq_true hij
    have hin : i < n := by omega
    by_cases hjn : j < n
    · have he : t = [minus (v i), minus (v j)] := by
        simpa [clause, literal, minus, h i hin, h j hjn] using ht.symm
      subst t
      simp only [onehot, if_neg hne, List.mem_append, List.mem_singleton,
        List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range]
      exact Or.inr ⟨i, hin, j, ⟨hjn, hij⟩, rfl⟩
    · have he : j = n := by omega
      subst j
      simp [clause, literal, minus, h i hin, hlast] at ht
theorem onehot_reduce (ρ : Substitution) (v : Nat → Var) (n : Nat)
    (hn : 1 ≤ n)
    (h : ∀ i < n, ρ (v i) = if n = 1 then .inl true else .inr (v i))
    (hlast : ρ (v n) = .inl false) :
    ∀ c ∈ onehot (n+1) v, ∀ t, clause ρ c = some t → t ∈ onehot n v := by
  by_cases he : n = 1
  · subst n
    have hs : ∀ i < 2, ρ (v i) = .inl (i == 0) := by
      intro i hi
      have hc : i = 0 ∨ i = 1 := by omega
      rcases hc with rfl | rfl
      · simpa using h 0 (by omega)
      · simpa using hlast
    intro c hc t ht
    have ht' := onehot_selected ρ v 2 0 (by omega) hs c hc
    rw [ht'] at ht
    contradiction
  · exact onehot_truncate ρ v n (by omega)
      (fun i hi => by simpa [he] using h i hi) hlast
#print axioms onehot_reduce
#print axioms onehot_truncate
end Programme.«20261101-0614-proof-complexity».Composition
