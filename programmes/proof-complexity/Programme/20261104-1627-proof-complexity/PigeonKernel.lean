import Programme.«20261104-1627-proof-complexity».PigeonProjection

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC

theorem matching_cols_lt {m n d : Nat} {M : Matching}
    (hM : M ∈ matchings m n d) : ∀ e ∈ M, e.2 < n := by
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
      exact List.mem_range.mp (List.mem_filter.mp hj).1

private theorem cf_zero_bad (L : List (Int × List Nat)) (u : List Nat) (B : Nat)
    (hu : ∀ x ∈ u, x < B)
    (hL : ∀ t ∈ L, ∃ x ∈ t.2, B ≤ x) : cf L u = 0 := by
  have hf : L.filter (fun t => decide (t.2.Perm u)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht hp
    obtain ⟨x, hx, hb⟩ := hL t ht
    have hh := hu x ((of_decide_eq_true hp).mem_iff.mp hx)
    omega
  simp [cf, hf]

private theorem rows_succ (m : Nat) (M : Matching) :
    rows (m+1) M = rows m M ++ if freeRow M m then [m] else [] := by
  simp only [rows, List.range_succ, List.filter_append]
  cases h : freeRow M m <;> simp [h]

private theorem topLabel_first_coeff {m n : Nat} (g : Label)
    (u : List Nat) (hu : ∀ x ∈ u, x < m*n) :
    coeff (topLabel (m+1) n g) u = coeff (topLabel m n g) u := by
  cases g with
  | mk M r a =>
    cases r
    · simp only [topLabel, Bool.false_eq_true, ↓reduceIte, rows_succ,
        List.map_append, coeff, cf_append]
      have hz : cf ((if freeRow M m then [m] else []).map
          fun i => (1, (i*n+a)::mono n M)) u = 0 := by
        apply cf_zero_bad _ u (m*n) hu
        intro t ht
        split at ht
        · simp only [List.map_cons, List.map_nil, List.mem_singleton] at ht
          subst t
          exact ⟨m*n+a, by simp, by omega⟩
        · simp at ht
      rw [hz, Int.add_zero]
    · rfl

private theorem topLabel_nonfirst_zero {m n d : Nat} {g : Label}
    (hg : g ∈ labels (m+1) n d) (hb : pigeonBlock m g ≠ 1)
    (u : List Nat) (hu : ∀ x ∈ u, x < m*n) :
    coeff (topLabel (m+1) n g) u = 0 := by
  apply cf_zero_bad _ u (m*n) hu
  intro t ht
  by_cases huse : usesPigeon m g = true
  · obtain ⟨e, he, hem⟩ := List.any_eq_true.mp huse
    have hem : e.1 = m := by simpa using hem
    have hx : m*n+e.2 ∈ mono n g.base := by
      exact List.mem_map.mpr ⟨e, he, by simp [hem]⟩
    unfold topLabel at ht
    split at ht <;> obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht <;>
      exact ⟨m*n+e.2, List.mem_cons_of_mem _ hx, by omega⟩
  · have hu' : usesPigeon m g = false := Bool.eq_false_iff.mpr huse
    have hr : g.isRow = true ∧ g.mark = m := by
      simpa [pigeonBlock, hu', Bool.and_eq_true] using hb
    simp only [topLabel, hr.1, ↓reduceIte] at ht
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
    exact ⟨g.mark*n+j, by simp, by rw [hr.2]; omega⟩

private theorem cf_scaled' (a : Int) (L : List (Int × List Nat)) (u : List Nat) :
    cf (L.map fun b => (a*b.1,b.2)) u = a * cf L u := by
  induction L with
  | nil => simp [cf]
  | cons b L ih =>
    by_cases h : b.2.Perm u <;> simp [cf, h] at ih ⊢ <;> simp_all [Int.mul_add]

/-- Exact coefficient projection onto monomials avoiding the last pigeon. -/
theorem splitPigeon_one_coeff {m n d : Nat} (v : Vector)
    (hv : valid (m+1) n d v) (u : List Nat)
    (hu : ∀ x ∈ u, x < m*n) :
    coeff (top m n (splitPigeon m 1 v)) u = coeff (top (m+1) n v) u := by
  induction v with
  | nil => simp [splitPigeon, top, coeff, cf]
  | cons t v ih =>
    have ht := hv t List.mem_cons_self
    have hi := ih (fun a ha => hv a (List.mem_cons_of_mem t ha))
    by_cases hb : pigeonBlock m t.2 = 1
    · simp only [splitPigeon, List.filter_cons, hb, beq_self_eq_true, ↓reduceIte]
      change cf (_ ++ _) u = cf (_ ++ _) u
      rw [cf_append, cf_append, cf_scaled', cf_scaled']
      rw [show cf (topLabel (m+1) n t.2).terms u =
        cf (topLabel m n t.2).terms u from topLabel_first_coeff t.2 u hu]
      exact congrArg (fun x => t.1 * cf (topLabel m n t.2).terms u + x) hi
    · simp only [splitPigeon, List.filter_cons, show (pigeonBlock m t.2 == 1) = false by simp [hb], ↓reduceIte]
      change _ = cf (_ ++ _) u
      rw [cf_append, cf_scaled', show cf (topLabel (m+1) n t.2).terms u = 0 from
        topLabel_nonfirst_zero ht hb u hu]
      simpa only [Int.mul_zero, Int.zero_add, coeff, top, splitPigeon, List.flatMap, Bool.false_eq_true, ite_false] using hi

/-- Every variable occurring in a smaller-board top term lies on that board. -/
theorem top_terms_board {m n d : Nat} {v : Vector} (hv : valid m n d v) :
    ∀ t ∈ (top m n v).terms, ∀ x ∈ t.2, x < m*n := by
  intro t ht
  obtain ⟨a, ha, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
  have hg := hv a ha
  unfold labels at hg
  split at hg
  · contradiction
  · obtain ⟨M, hM, hg⟩ := List.mem_flatMap.mp hg
    have hm := matching_rows_lt hM
    have hn := matching_cols_lt hM
    have hbase : ∀ x ∈ mono n M, x < m*n := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      have hi := hm e he
      have hj := hn e he
      have hstep : e.1*n+e.2 < (e.1+1)*n := by
        rw [Nat.add_mul, Nat.one_mul]; omega
      exact Nat.lt_of_lt_of_le hstep (Nat.mul_le_mul_right n (by omega))
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨i, hi, heq⟩ := List.mem_map.mp hg
      have hi' := List.mem_range.mp (List.mem_filter.mp hi).1
      rw [← heq] at hb
      simp only [topLabel, ↓reduceIte] at hb
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · have hj' := List.mem_range.mp (List.mem_filter.mp hj).1
        have hs : i*n+j < (i+1)*n := by rw [Nat.add_mul, Nat.one_mul]; omega
        exact Nat.lt_of_lt_of_le hs (Nat.mul_le_mul_right n (by omega))
      · exact hbase x hx
    · obtain ⟨j, hj, heq⟩ := List.mem_map.mp hg
      have hj' := List.mem_range.mp (List.mem_filter.mp hj).1
      rw [← heq] at hb
      simp only [topLabel, Bool.false_eq_true, ↓reduceIte] at hb
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · have hi' := List.mem_range.mp (List.mem_filter.mp hi).1
        have hs : i*n+j < (i+1)*n := by rw [Nat.add_mul, Nat.one_mul]; omega
        exact Nat.lt_of_lt_of_le hs (Nat.mul_le_mul_right n (by omega))
      · exact hbase x hx

/-- The G1 projection of a kernel vector is a kernel vector on one fewer pigeon. -/
theorem splitPigeon_one_kernel {p m n d : Nat} {v : Vector}
    (hv : Kernel p (m+1) n d v) :
    Kernel p m n d (splitPigeon m 1 v) := by
  have hvalid := splitPigeon_one_valid hv.1
  refine ⟨hvalid, fun u => ?_⟩
  have hz : coeff (⟨[]⟩ : Poly Nat) u = 0 := by simp [coeff, cf]
  rw [hz]
  by_cases hu : ∀ x ∈ u, x < m*n
  · rw [splitPigeon_one_coeff v hv.1 u hu]
    simpa [coeff, cf] using hv.2 u
  · have hcoeff : coeff (top m n (splitPigeon m 1 v)) u = 0 := by
      have hf : (top m n (splitPigeon m 1 v)).terms.filter
          (fun t => decide (t.2.Perm u)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro t ht hp
        apply hu
        intro x hx
        exact top_terms_board hvalid t ht x ((of_decide_eq_true hp).mem_iff.mpr hx)
      simp [coeff, cf, hf]
    simp [hcoeff]

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.splitPigeon_one_coeff

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.splitPigeon_one_kernel
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.top_terms_board
