import Programme.«20261101-0614-proof-complexity».CompositionTransport
namespace Programme.«20261101-0614-proof-complexity».Composition
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity».RestrictionTarget

theorem domain_fixed (ρ : Substitution) (v : Nat → Var) (n : Nat)
    (h : ∀ i < n, ρ (v i) = .inr (v i)) :
    clause ρ ((List.range n).map (fun i => pos (v i))) =
      some ((List.range n).map (fun i => pos (v i))) := by
  apply fixed_clause
  intro l hl
  rcases List.mem_map.mp hl with ⟨i, hi, rfl⟩
  exact h i (List.mem_range.mp hi)

theorem onehot_selected (ρ : Substitution) (v : Nat → Var) (n j : Nat)
    (hj : j < n) (h : ∀ i < n, ρ (v i) = .inl (i == j)) :
    ∀ c ∈ onehot n v, clause ρ c = none := by
  intro c hc
  by_cases hn : n = 1
  · simp [onehot, hn] at hc
  · simp only [onehot, if_neg hn, List.mem_append, List.mem_singleton,
      List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range] at hc
    rcases hc with rfl | ⟨i, hi, k, ⟨hk, hik⟩, rfl⟩
    · have aux : ∀ (xs : List Nat), j ∈ xs → (∀ i ∈ xs, i < n) →
          clause ρ (xs.map (fun i => pos (v i))) = none := by
        intro xs
        induction xs with
        | nil => simp
        | cons i xs ih =>
          intro hm hb
          simp only [List.map_cons, clause, literal, pos, h i (hb i (by simp))]
          by_cases he : i = j
          · subst i; simp
          · have hjx : j ∈ xs := by simpa [Ne.symm he] using hm
            have heq : (i == j) = false := beq_eq_false_iff_ne.mpr he
            rw [heq]
            exact ih hjx (fun a ha => hb a (by simp [ha]))
      exact aux _ (List.mem_range.mpr hj) (fun i hi => List.mem_range.mp hi)
    · have hikNat : i < k := of_decide_eq_true hik
      by_cases hi' : i = j
      · have hk' : k ≠ j := by omega
        have hki : (k == j) = false := beq_eq_false_iff_ne.mpr hk'
        subst i
        simp [clause, literal, minus, h j hi, h k hk, hki]
      · have hii : (i == j) = false := beq_eq_false_iff_ne.mpr hi'
        simp [clause, literal, minus, h i hi, hii]

theorem onehot_fixed (ρ : Substitution) (v : Nat → Var) (n : Nat)
    (h : ∀ i < n, ρ (v i) = .inr (v i)) :
    ∀ c ∈ onehot n v, clause ρ c = some c := by
  intro c hc
  by_cases hn : n = 1
  · simp [onehot, hn] at hc
  · simp only [onehot, if_neg hn, List.mem_append, List.mem_singleton,
      List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range] at hc
    rcases hc with rfl | ⟨i, hi, k, ⟨hk, _⟩, rfl⟩
    · exact domain_fixed ρ v n h
    · simp [clause, literal, minus, h i hi, h k hk]
#print axioms onehot_selected
#print axioms onehot_fixed
end Programme.«20261101-0614-proof-complexity».Composition
