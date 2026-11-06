import Programme.«20261024-1110-proof-complexity».HakenUpper
/-!
# The ordering principle `GT n` has polynomial-size resolution refutations (core Lean 4)

The negative control of target A, in the `Refutation` type of the Haken lower bound
(`Work.Haken.haken`): for every `n ≥ 1` we construct a resolution refutation of the ordering
principle `GT n` with at most `n + 3 n³` clauses (Stålmarck 1996; cf. Bonet–Galesi 2001, whose
width lower bound shows that `GT n` has large width but, by this theorem, polynomial size).

Variables `(i, j)`, `i ≠ j < n`, mean "`i` precedes `j`". Clauses:
* antisymmetry `¬x_{ij} ∨ ¬x_{ji}` for `i ≠ j`;
* transitivity `¬x_{ij} ∨ ¬x_{jk} ∨ x_{ik}` for pairwise distinct `i, j, k`;
* no minimum `⋁_{i ≠ j} x_{ij}` for every `j`.
`GTtot n` adds totality `x_{ij} ∨ x_{ji}`; a refutation of `GT n` is one of `GTtot n`.

Construction: `T m j = ⋁_{i<m, i≠j} x_{ij}` ("`j` is not minimal among `0..m-1`"). Level `n` is
the no-minimum axioms. From level `m+1` to level `m`, for `j < m`: for each `i < m` resolve
`T (m+1) j = T m j ∨ x_{mj}` with transitivity `¬x_{im} ∨ ¬x_{mj} ∨ x_{ij}` (or antisymmetry
when `i = j`) to get `T m j ∨ ¬x_{im}`, and cut it against `T (m+1) m = ⋁_{i<m} x_{im}`.
`T 1 0` is the empty clause.
-/

namespace Programme.«20261024-1110-proof-complexity».GT

open Classical Programme.«20261024-1110-proof-complexity».Haken

def antiAx (i j : Nat) : Clause (Nat × Nat) := [neg i j, neg j i]
def transAx (i j k : Nat) : Clause (Nat × Nat) := [neg i j, neg j k, pos i k]
def nominAx (n j : Nat) : Clause (Nat × Nat) :=
  ((List.range n).filter (· ≠ j)).map fun i => pos i j
def totAx (i j : Nat) : Clause (Nat × Nat) := [pos i j, pos j i]

/-- The ordering principle (no totality axioms): antisymmetry, transitivity, no minimum. -/
def GT (n : Nat) : CNF (Nat × Nat) :=
  ((List.range n).flatMap fun i => (List.range n).flatMap fun j =>
      if i ≠ j then [antiAx i j] else []) ++
  ((List.range n).flatMap fun i => (List.range n).flatMap fun j => (List.range n).flatMap fun k =>
      if i ≠ j ∧ j ≠ k ∧ i ≠ k then [transAx i j k] else []) ++
  (List.range n).map (nominAx n)

/-- The total ordering principle: `GT n` plus totality `x_{ij} ∨ x_{ji}`. -/
def GTtot (n : Nat) : CNF (Nat × Nat) :=
  GT n ++ ((List.range n).flatMap fun i => (List.range n).flatMap fun j =>
      if i ≠ j then [totAx i j] else [])

theorem antiAx_mem {n i j : Nat} (hi : i < n) (hj : j < n) (hij : i ≠ j) : antiAx i j ∈ GT n := by
  simp only [GT, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inl (Or.inl ⟨i, hi, j, hj, by simp [hij]⟩)

theorem transAx_mem {n i j k : Nat} (hi : i < n) (hj : j < n) (hk : k < n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) : transAx i j k ∈ GT n := by
  simp only [GT, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inl (Or.inr ⟨i, hi, j, hj, k, hk, by simp [hij, hjk, hik]⟩)

theorem nominAx_mem {n j : Nat} (hj : j < n) : nominAx n j ∈ GT n := by
  simp only [GT, List.mem_append]
  exact Or.inr (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)

/-- A refutation of a sub-CNF is a refutation. -/
def Refutation.lift {V} {F G : CNF V} (hFG : ∀ C ∈ F, C ∈ G) (R : Refutation F) : Refutation G where
  steps := R.steps
  derived := fun k hk => (R.derived k hk).imp_left (hFG _)
  empty_mem := R.empty_mem

/-- `T m j l` : `l = x_{ij}` for some `i < m`, `i ≠ j`. -/
def T (m j : Nat) (l : Lit (Nat × Nat)) : Prop := ∃ i, i < m ∧ i ≠ j ∧ l = pos i j

def Lev (m : Nat) (L : List (Clause (Nat × Nat))) : Prop := ∀ j < m, CoversP L (T m j)

/-- From `T m j ∨ x_{mj}` derive `T m j ∨ ¬x_{im}` with two clauses. -/
theorem reach_D {n m i j : Nat} (hm : m < n) (hi : i < m) (hj : j < m) (L : List (Clause (Nat × Nat)))
    (hL : Valid (GT n) L) (hA : CoversP L (fun l => T m j l ∨ l = pos m j)) :
    Reach (GT n) L 2 (CoversP · (fun l => T m j l ∨ l = neg i m)) := by
  by_cases hij : i = j
  · subst hij
    refine reach_trans (reach_ax hL (antiAx_mem (by omega) hm (by omega)) (S := (· ∈ antiAx i m))
      (fun l hl => hl)) (fun M hv hB => reach_res (m, i) hv (hA.mono M) hB ?_ ?_)
    · intro l hl hne
      rcases hl with hl | rfl
      · exact Or.inl hl
      · exact absurd rfl hne
    · intro l hl hne
      simp only [antiAx, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact Or.inr rfl
      · exact absurd rfl hne
  · refine reach_trans (reach_ax hL (transAx_mem (j := m) (by omega) hm (by omega) (by omega) (by omega)
      hij) (S := (· ∈ transAx i m j)) (fun l hl => hl))
      (fun M hv hB => reach_res (m, j) hv (hA.mono M) hB ?_ ?_)
    · intro l hl hne
      rcases hl with hl | rfl
      · exact Or.inl hl
      · exact absurd rfl hne
    · intro l hl hne
      simp only [transAx, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl
      · exact Or.inr rfl
      · exact absurd rfl hne
      · exact Or.inl ⟨i, hi, hij, rfl⟩

/-- Cutting `x_{im}`, `i < t`, out of `T (m+1) m`, three clauses per literal. -/
theorem reach_chain {n m j : Nat} (hm : m < n) (hj : j < m) :
    ∀ t, t ≤ m → ∀ L, Valid (GT n) L → CoversP L (fun l => T m j l ∨ l = pos m j) →
      CoversP L (fun l => ∃ i, i < m ∧ l = pos i m) →
      Reach (GT n) L (3 * t) (CoversP · (fun l => T m j l ∨ ∃ i, t ≤ i ∧ i < m ∧ l = pos i m)) := by
  intro t
  induction t with
  | zero =>
    intro _ L hL _ hB
    exact reach_zero _ hL (hB.weaken fun l ⟨i, hi, he⟩ => Or.inr ⟨i, Nat.zero_le _, hi, he⟩)
  | succ t ih =>
    intro ht L hL hA hB
    have h1 := reach_trans (ih (by omega) L hL hA hB) (fun M hv hcur =>
      reach_keep (reach_D (i := t) hm (by omega) hj (L ++ M) hv (hA.mono M)) hcur)
    refine reach_le (reach_trans h1 (fun M hv ⟨hD, hcur⟩ => reach_res (t, m) hv hcur hD ?_ ?_))
      (by omega)
    · intro l hl hne
      rcases hl with hl | ⟨i, hi1, hi2, rfl⟩
      · exact Or.inl hl
      · refine Or.inr ⟨i, ?_, hi2, rfl⟩
        rcases Nat.lt_or_ge t i with h' | h'
        · exact h'
        · exact absurd (by have : i = t := by omega
                           subst this; rfl) hne
    · intro l hl hne
      rcases hl with hl | rfl
      · exact Or.inl hl
      · exact absurd rfl hne

theorem reach_level {n m : Nat} (hm : m < n) (L : List (Clause (Nat × Nat)))
    (hL : Valid (GT n) L) (hlev : Lev (m + 1) L) :
    Reach (GT n) L (m * (3 * m)) (Lev m) := by
  have h := reach_forall (F := GT n) (Lev (m + 1)) (fun j L => j < m → CoversP L (T m j)) (3 * m)
    (fun L M h j hj => (h j hj).mono M) (fun j L M h hj => (h hj).mono M) ?_
    (List.range m) L hL hlev
  · rw [List.length_range] at h
    exact reach_imp h (fun M ⟨_, hall⟩ j hj => hall j (List.mem_range.mpr hj) hj)
  · intro j L hL hlev
    by_cases hj : j < m
    · have hA : CoversP L (fun l => T m j l ∨ l = pos m j) :=
        (hlev j (by omega)).weaken fun l ⟨i, hi, hij, he⟩ => by
          by_cases e : i = m
          · subst e; exact Or.inr he
          · exact Or.inl ⟨i, by omega, hij, he⟩
      have hB : CoversP L (fun l => ∃ i, i < m ∧ l = pos i m) :=
        (hlev m (by omega)).weaken fun l ⟨i, hi, hij, he⟩ => ⟨i, by omega, he⟩
      refine reach_imp (reach_chain hm hj m (Nat.le_refl _) L hL hA hB) (fun M hc _ => hc.weaken ?_)
      intro l hl
      rcases hl with hl | ⟨i, hi1, hi2, _⟩
      · exact hl
      · omega
    · exact reach_zero _ hL (fun h => absurd h hj)

theorem reach_top (n : Nat) : Reach (GT n) [] n (Lev n) := by
  have h := reach_forall (F := GT n) (fun _ => True) (fun j L => j < n → CoversP L (T n j)) 1
    (fun _ _ _ => trivial) (fun j L M h hj => (h hj).mono M) ?_ (List.range n) [] (valid_nil _) trivial
  · rw [List.length_range, Nat.mul_one] at h
    exact reach_imp h (fun M ⟨_, hall⟩ j hj => hall j (List.mem_range.mpr hj) hj)
  · intro j L hL _
    by_cases hj : j < n
    · refine reach_imp (reach_ax hL (nominAx_mem hj) (S := T n j) ?_) (fun M h _ => h)
      intro l hl
      simp only [nominAx, List.mem_map, List.mem_filter, List.mem_range] at hl
      obtain ⟨i, ⟨hi, hij⟩, rfl⟩ := hl
      exact ⟨i, hi, by simpa using hij, rfl⟩
    · exact reach_zero _ hL (fun h => absurd h hj)

theorem reach_levels (n : Nat) :
    ∀ d, d < n → Reach (GT n) [] (n + d * (3 * n * n)) (Lev (n - d)) := by
  intro d
  induction d with
  | zero => intro _; simpa using reach_top n
  | succ d ih =>
    intro hd
    have hm : n - (d + 1) < n := by omega
    have e : n - (d + 1) + 1 = n - d := by omega
    have hc : (n - (d + 1)) * (3 * (n - (d + 1))) ≤ 3 * n * n := by
      have h1 : (n - (d + 1)) * (3 * (n - (d + 1))) ≤ n * (3 * n) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h2 : n * (3 * n) = 3 * n * n := by rw [Nat.mul_comm n (3 * n)]
      omega
    refine reach_le (reach_trans (ih (by omega)) (fun M hv hlev =>
      reach_level hm _ hv (by rw [e]; exact hlev))) ?_
    have e2 : (d + 1) * (3 * n * n) = d * (3 * n * n) + 3 * n * n := Nat.succ_mul _ _
    omega

/-- For every `n ≥ 1`, the ordering principle `GT n` has a resolution refutation with at most
`n + 3 n³` clauses. -/
theorem gt_upper (n : Nat) (hn : 1 ≤ n) :
    ∃ R : Refutation (GT n), R.steps.length ≤ n + 3 * n ^ 3 := by
  obtain ⟨M, hv, hlen, hlev⟩ := reach_levels n (n - 1) (by omega)
  have e : n - (n - 1) = 1 := by omega
  rw [e] at hlev
  obtain ⟨D, hD, hDe⟩ := hlev 0 (by omega)
  have : D = [] := by
    cases D with
    | nil => rfl
    | cons l D =>
      obtain ⟨i, hi, hi0, _⟩ := hDe l List.mem_cons_self
      omega
  subst this
  refine ⟨Refutation.ofValid _ hv hD, ?_⟩
  show ([] ++ M).length ≤ _
  have h1 : (n - 1) * (3 * n * n) ≤ n * (3 * n * n) := Nat.mul_le_mul (by omega) (Nat.le_refl _)
  have h2 : n * (3 * n * n) = 3 * n ^ 3 := by
    rw [Nat.pow_succ, Nat.pow_two, Nat.mul_comm n (3 * n * n), Nat.mul_assoc 3 n n, Nat.mul_assoc]
  simp only [List.nil_append]; omega

/-- The same bound for the total ordering principle (with `x_{ij} ∨ x_{ji}`). -/
theorem gttot_upper (n : Nat) (hn : 1 ≤ n) :
    ∃ R : Refutation (GTtot n), R.steps.length ≤ n + 3 * n ^ 3 := by
  obtain ⟨R, hR⟩ := gt_upper n hn
  exact ⟨Refutation.lift (fun C hC => List.mem_append_left _ hC) R, hR⟩

end Programme.«20261024-1110-proof-complexity».GT

#print axioms Programme.«20261024-1110-proof-complexity».GT.gt_upper
#print axioms Programme.«20261024-1110-proof-complexity».GT.gttot_upper
