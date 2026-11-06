import Programme.«20261101-0614-proof-complexity».OnehotReproof

namespace Programme.«20261101-0614-proof-complexity».OnehotReduceReproof
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity».RestrictionTarget
open Programme.«20261101-0614-proof-complexity».Composition

theorem app (ρ : Substitution) : ∀ (c d : Clause) (c' : Clause),
    clause ρ c = some c' → clause ρ (c ++ d) = (clause ρ d).map (c' ++ ·) := by
  intro c
  induction c with
  | nil => intro d c' h; simp [clause] at h; subst h; cases hd : clause ρ d <;> simp [clause, hd]
  | cons l c ih =>
    intro d c' h
    rw [List.cons_append]
    simp only [clause] at h ⊢
    cases hl : literal ρ l with
    | inl b =>
      simp only [hl] at h
      cases b
      · exact ih d c' h
      · simp at h
    | inr k =>
      simp only [hl] at h
      cases hc : clause ρ c with
      | none => simp [hc] at h
      | some c2 =>
        simp [hc] at h; subst h
        have := ih d c2 hc
        rw [this]
        cases clause ρ d <;> simp

theorem dom (ρ : Substitution) (v : Nat → Var) (n : Nat)
    (h : ∀ i < n, ρ (v i) = .inr (v i)) (hl : ρ (v n) = .inl false) :
    clause ρ ((List.range (n+1)).map (fun i => pos (v i))) =
      some ((List.range n).map (fun i => pos (v i))) := by
  have hf := Programme.«20261101-0614-proof-complexity».OnehotReproof.clause_fixed ρ ((List.range n).map (fun i => pos (v i))) (by
    intro l hl'
    simp only [List.mem_map, List.mem_range] at hl'
    obtain ⟨i, hi, rfl⟩ := hl'
    exact h i hi)
  rw [List.range_succ, List.map_append, app ρ _ _ _ hf]
  simp [clause, literal, pos, hl]

theorem reduce (ρ : Substitution) (v : Nat → Var) (n : Nat)
    (hn : 1 ≤ n)
    (h : ∀ i < n, ρ (v i) = if n = 1 then .inl true else .inr (v i))
    (hlast : ρ (v n) = .inl false) :
    ∀ c ∈ onehot (n+1) v, ∀ t, clause ρ c = some t → t ∈ onehot n v := by
  intro c hc t ht
  by_cases he : n = 1
  · subst he
    have h0 : ρ (v 0) = .inl true := by simpa using h 0 (by omega)
    simp only [onehot, if_neg (show 1+1 ≠ 1 by omega), if_pos rfl, List.mem_append, List.mem_singleton,
      List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range] at hc
    rcases hc with rfl | ⟨i, hi, j, ⟨hj, hij⟩, rfl⟩
    · simp [List.range_succ, clause, literal, pos, h0] at ht
    · have hij' : i < j := of_decide_eq_true hij
      have : j = 1 := by omega
      have hi0 : i = 0 := by omega
      subst this; subst hi0
      simp [clause, literal, minus, h0, hlast] at ht
  · have hne : n+1 ≠ 1 := by omega
    have hn2 : ∀ i < n, ρ (v i) = .inr (v i) := fun i hi => by simpa [he] using h i hi
    simp only [onehot, if_neg hne, List.mem_append, List.mem_singleton,
      List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range] at hc
    rcases hc with rfl | ⟨i, hi, j, ⟨hj, hij⟩, rfl⟩
    · rw [dom ρ v n hn2 hlast] at ht
      cases ht
      simp [onehot, he]
    · have hij' : i < j := of_decide_eq_true hij
      have hin : i < n := by omega
      by_cases hjn : j < n
      · have : t = [minus (v i), minus (v j)] := by
          simpa [clause, literal, minus, hn2 i hin, hn2 j hjn] using ht.symm
        subst this
        simp only [onehot, if_neg he, List.mem_append, List.mem_singleton,
          List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range]
        exact Or.inr ⟨i, hin, j, ⟨hjn, hij⟩, rfl⟩
      · have : j = n := by omega
        subst this
        simp [clause, literal, minus, hlast, hn2 i hin] at ht

#print axioms reduce
end Programme.«20261101-0614-proof-complexity».OnehotReduceReproof
