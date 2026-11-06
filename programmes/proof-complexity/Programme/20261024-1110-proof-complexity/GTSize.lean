import Programme.«20261024-1110-proof-complexity».GT
/-!
# Polynomial-size refutations of the ordering principle, for all `n` (core Lean 4)

The upper-bound half of the width-vs-size control. `Work.GT3.gt_width` shows that every
resolution refutation of the 3-CNF ordering principle `Work.GT3.GT3 n` has width `≥ (n-1)/2`;
here we build, for every `n ≥ 1`, a refutation of the *same* CNF in the *same* `Refutation`
type with at most `3n³ + 2n² + 3n` clauses (Stålmarck 1996; Bonet–Galesi 2001). In particular
`GT3 n` is unsatisfiable for every `n ≥ 1`, so the width bound is not vacuous.

The construction is written once, generically (`levels`), for any CNF that contains
antisymmetry and transitivity clauses over some variables `x a b`. It is instantiated for
* `Work.GT3.GT3 n` (3-CNF, chain variables `y j t`): `gt3_upper`;
* `GTw n`, the wide ordering principle with the clause `⋁_{i≠j} x_{ij}` per `j` (the encoding
  of pr's `Work.GT.GT` in `GTUpper.lean`, restated over `Nat × Nat` in `Work.BSW`'s types):
  `gtw_upper`. This is an independent reproof of pr's `gt_upper` up to the type copy;
  it shares no code with `GTUpper.lean` / `HakenUpper.lean`.

Machinery: `Valid F L` says every line of `L` is an axiom or a resolvent of earlier lines;
`Cov L S` says some line of `L` has all its literals in `S` (subsumption); `Gr F L k P` says
`L` extends by at most `k` lines to a valid list satisfying `P`.

Levels: `T m j = {x_{ij} : i < m, i ≠ j}` ("`j` is not minimal among `0..m-1`").
From `T (m+1) j = T m j ∪ {x_{mj}}` and transitivity `¬x_{im} ∨ ¬x_{mj} ∨ x_{ij}` (antisymmetry
if `i = j`) we get `T m j ∪ {¬x_{im}}`; cutting these against `T (m+1) m = {x_{im} : i < m}`
for `i = 0, …, m-1` gives `T m j`. `T 1 0 = ∅`.
-/

set_option linter.unusedSectionVars false

namespace Programme.«20261024-1110-proof-complexity».GTSize
open Programme.«20261024-1110-proof-complexity».BSW

section Generic
variable {V : Type} [DecidableEq V]

/-- Every line is an axiom of `F` or a resolvent of two earlier lines. -/
def Valid (F : CNF V) (L : List (Clause V)) : Prop :=
  ∀ k (hk : k < L.length), L[k] ∈ F ∨
    ∃ a b, ∃ (ha : a < k) (hb : b < k),
      IsResolvent (L[a]'(Nat.lt_trans ha hk)) (L[b]'(Nat.lt_trans hb hk)) L[k]

theorem valid_nil (F : CNF V) : Valid F [] := fun k hk => absurd hk (Nat.not_lt_zero _)

theorem valid_snoc {F : CNF V} {L : List (Clause V)} (hL : Valid F L) {C : Clause V}
    (hC : C ∈ F ∨ ∃ A ∈ L, ∃ B ∈ L, IsResolvent A B C) : Valid F (L ++ [C]) := by
  intro k hk
  rw [List.length_append, List.length_singleton] at hk
  rcases Nat.lt_or_ge k L.length with h | h
  · rcases hL k h with h1 | ⟨a, b, ha, hb, hr⟩
    · left; rw [List.getElem_append_left h]; exact h1
    · right
      refine ⟨a, b, ha, hb, ?_⟩
      rw [List.getElem_append_left h, List.getElem_append_left (Nat.lt_trans ha h),
        List.getElem_append_left (Nat.lt_trans hb h)]
      exact hr
  · have hk' : k = L.length := by omega
    subst hk'
    rcases hC with hC | ⟨A, hA, B, hB, hr⟩
    · left; simp [hC]
    · right
      obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.mp hA
      obtain ⟨b, hb, rfl⟩ := List.mem_iff_getElem.mp hB
      refine ⟨a, b, ha, hb, ?_⟩
      rw [List.getElem_append_left ha, List.getElem_append_left hb]
      simpa using hr

/-- Some line of `L` has all its literals in `S`. -/
def Cov (L : List (Clause V)) (S : Lit V → Prop) : Prop := ∃ D ∈ L, ∀ l ∈ D, S l

theorem Cov.ext {L : List (Clause V)} {S : Lit V → Prop} (h : Cov L S) (M : List (Clause V)) :
    Cov (L ++ M) S := by
  obtain ⟨D, hD, hS⟩ := h; exact ⟨D, List.mem_append_left _ hD, hS⟩

theorem Cov.weak {L : List (Clause V)} {S S' : Lit V → Prop} (h : Cov L S)
    (hSS : ∀ l, S l → S' l) : Cov L S' := by
  obtain ⟨D, hD, hS⟩ := h; exact ⟨D, hD, fun l hl => hSS l (hS l hl)⟩

/-- `L` extends by at most `k` lines to a valid list satisfying `P`. -/
def Gr (F : CNF V) (L : List (Clause V)) (k : Nat) (P : List (Clause V) → Prop) : Prop :=
  ∃ M : List (Clause V), M.length ≤ k ∧ Valid F (L ++ M) ∧ P (L ++ M)

theorem gr_zero {F : CNF V} {L : List (Clause V)} {P : List (Clause V) → Prop} {k : Nat}
    (hL : Valid F L) (hP : P L) : Gr F L k P :=
  ⟨[], Nat.zero_le _, by simpa using hL, by simpa using hP⟩

theorem gr_bind {F : CNF V} {L : List (Clause V)} {k k' : Nat} {P Q : List (Clause V) → Prop}
    (h : Gr F L k P) (h' : ∀ M, Valid F (L ++ M) → P (L ++ M) → Gr F (L ++ M) k' Q) :
    Gr F L (k + k') Q := by
  obtain ⟨M, hM, hv, hP⟩ := h
  obtain ⟨M', hM', hv', hQ⟩ := h' M hv hP
  refine ⟨M ++ M', by rw [List.length_append]; omega, ?_, ?_⟩ <;> rw [← List.append_assoc] <;>
    assumption

theorem gr_seq {F : CNF V} {L : List (Clause V)} {k k' K : Nat} {P Q : List (Clause V) → Prop}
    (h : Gr F L k P) (h' : ∀ M, Valid F (L ++ M) → P (L ++ M) → Gr F (L ++ M) k' Q)
    (hk : k + k' ≤ K) : Gr F L K Q := by
  obtain ⟨M, hM, hv, hP⟩ := gr_bind h h'
  exact ⟨M, by omega, hv, hP⟩

theorem gr_mono {F : CNF V} {L : List (Clause V)} {k k' : Nat} {P Q : List (Clause V) → Prop}
    (h : Gr F L k P) (hk : k ≤ k') (hPQ : ∀ M, P (L ++ M) → Q (L ++ M)) : Gr F L k' Q := by
  obtain ⟨M, hM, hv, hP⟩ := h; exact ⟨M, by omega, hv, hPQ M hP⟩

/-- An axiom inside `S` costs one line. -/
theorem gr_ax {F : CNF V} {L : List (Clause V)} (hL : Valid F L) {C : Clause V} (hC : C ∈ F)
    {S : Lit V → Prop} (hS : ∀ l ∈ C, S l) : Gr F L 1 (Cov · S) :=
  ⟨[C], Nat.le_refl _, valid_snoc hL (Or.inl hC), ⟨C, by simp, hS⟩⟩

/-- Resolution on `x` of covered clauses, at most one line. -/
theorem gr_res {F : CNF V} {L : List (Clause V)} (hL : Valid F L) (x : V)
    {S S' R : Lit V → Prop} (hA : Cov L (fun l => S l ∨ l = ⟨x, true⟩))
    (hB : Cov L (fun l => S' l ∨ l = ⟨x, false⟩))
    (hR1 : ∀ l, S l → R l) (hR2 : ∀ l, S' l → R l) : Gr F L 1 (Cov · R) := by
  obtain ⟨A, hAL, hAS⟩ := hA
  obtain ⟨B, hBL, hBS⟩ := hB
  by_cases hxA : (⟨x, true⟩ : Lit V) ∈ A
  · by_cases hxB : (⟨x, false⟩ : Lit V) ∈ B
    · let C := A.filter (fun l => l ≠ ⟨x, true⟩) ++ B.filter (fun l => l ≠ ⟨x, false⟩)
      have hr : IsResolvent A B C := ⟨x, hxA, hxB,
        fun l hl hne => List.mem_append_left _ (List.mem_filter.mpr ⟨hl, by simpa using hne⟩),
        fun l hl hne => List.mem_append_right _ (List.mem_filter.mpr ⟨hl, by simpa using hne⟩)⟩
      refine ⟨[C], Nat.le_refl _, valid_snoc hL (Or.inr ⟨A, hAL, B, hBL, hr⟩), C, by simp, ?_⟩
      intro l hl
      simp only [C, List.mem_append, List.mem_filter, decide_eq_true_eq] at hl
      rcases hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
      · rcases hAS l hl with h | h
        · exact hR1 l h
        · exact absurd h hne
      · rcases hBS l hl with h | h
        · exact hR2 l h
        · exact absurd h hne
    · refine gr_zero hL ⟨B, hBL, fun l hl => ?_⟩
      rcases hBS l hl with h | rfl
      · exact hR2 l h
      · exact absurd hl hxB
  · refine gr_zero hL ⟨A, hAL, fun l hl => ?_⟩
    rcases hAS l hl with h | rfl
    · exact hR1 l h
    · exact absurd hl hxA

/-- Iterating a step over `i = 0..t-1`, for `t ≤ B`. -/
theorem gr_iter {F : CNF V} (Q : Nat → List (Clause V) → Prop) (c B : Nat)
    (step : ∀ i < B, ∀ L, Valid F L → Q i L → Gr F L c (Q (i + 1))) :
    ∀ t, t ≤ B → ∀ L, Valid F L → Q 0 L → Gr F L (t * c) (Q t) := by
  intro t
  induction t with
  | zero => intro _ L hL h; exact gr_zero hL h
  | succ t ih =>
    intro ht L hL h
    exact gr_seq (ih (by omega) L hL h) (fun M hv hq => step t (by omega) _ hv hq)
      (by rw [Nat.succ_mul]; omega)

/-- Conjunction over `j < m`, each conjunct costing `c` lines. -/
theorem gr_all {F : CNF V} (Pre : List (Clause V) → Prop) (Q : Nat → List (Clause V) → Prop)
    (c B : Nat) (hPre : ∀ L M, Pre L → Pre (L ++ M)) (hQ : ∀ j L M, Q j L → Q j (L ++ M))
    (step : ∀ j < B, ∀ L, Valid F L → Pre L → Gr F L c (Q j)) :
    ∀ m, m ≤ B → ∀ L, Valid F L → Pre L →
      Gr F L (m * c) (fun L => Pre L ∧ ∀ j < m, Q j L) := by
  intro m
  induction m with
  | zero =>
    intro _ L hL h
    exact gr_zero (P := fun L => Pre L ∧ ∀ j < 0, Q j L) hL
      ⟨h, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro hm L hL h
    refine gr_seq (ih (by omega) L hL h) (fun M hv ⟨hp, hall⟩ =>
      gr_mono (step m (by omega) _ hv hp) (Nat.le_refl _)
        (fun M' hq => ⟨hPre _ M' hp, fun j hj => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · exact hQ j _ M' (hall j hj)
          · exact hq⟩)) (by rw [Nat.succ_mul]; omega)

/-! ### The levels, generically -/

variable (F : CNF V) (x : Nat → Nat → V) (n : Nat)

def pX (a b : Nat) : Lit V := ⟨x a b, true⟩
def nX (a b : Nat) : Lit V := ⟨x a b, false⟩

/-- `T m j = {x_{ij} : i < m, i ≠ j}`. -/
def T (m j : Nat) (l : Lit V) : Prop := ∃ i, i < m ∧ i ≠ j ∧ l = pX x i j

def Lev (m : Nat) (L : List (Clause V)) : Prop := ∀ j < m, Cov L (T x m j)

/-- `F` contains (clauses inside) antisymmetry and transitivity on `0..n-1`. -/
structure HasOrd : Prop where
  anti : ∀ a < n, ∀ b < n, a ≠ b → ∃ C ∈ F, ∀ l ∈ C, l = nX x a b ∨ l = nX x b a
  trans : ∀ a < n, ∀ b < n, ∀ c < n, a ≠ b → b ≠ c → a ≠ c →
    ∃ C ∈ F, ∀ l ∈ C, l = nX x a b ∨ l = nX x b c ∨ l = pX x a c

variable {F x n}

theorem lev_ext {m : Nat} {L : List (Clause V)} (h : Lev x m L) (M : List (Clause V)) :
    Lev x m (L ++ M) := fun j hj => (h j hj).ext M

/-- From `T (m+1) j` (in `L`) derive a clause inside `T m j ∪ {¬x_{im}}`, two lines. -/
theorem step_D (hF : HasOrd F x n) {m i j : Nat} (hm : m < n) (hi : i < m) (hj : j < m)
    (L : List (Clause V)) (hL : Valid F L) (hA : Cov L (T x (m + 1) j)) :
    Gr F L 2 (Cov · (fun l => T x m j l ∨ l = nX x i m)) := by
  have hA' : Cov L (fun l => T x m j l ∨ l = ⟨x m j, true⟩) := hA.weak (by
    rintro l ⟨i', hi', hne, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h | rfl
    · exact Or.inl ⟨i', h, hne, rfl⟩
    · exact Or.inr rfl)
  by_cases hij : i = j
  · subst hij
    obtain ⟨C, hC, hCs⟩ := hF.anti i (by omega) m hm (by omega)
    exact gr_seq (gr_ax hL hC (S := fun l => l = nX x i m ∨ l = ⟨x m i, false⟩)
      (fun l hl => hCs l hl)) (fun M hv hB =>
        gr_res hv (x m i) (hA'.ext M) hB (fun l h => Or.inl h) (fun l h => Or.inr h)) (by omega)
  · obtain ⟨C, hC, hCs⟩ := hF.trans i (by omega) m hm j (by omega) (by omega) (by omega) hij
    refine gr_seq (gr_ax hL hC
      (S := fun l => (l = nX x i m ∨ l = pX x i j) ∨ l = ⟨x m j, false⟩)
      (fun l hl => by
        rcases hCs l hl with h | h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
        · exact Or.inl (Or.inr h))) (fun M hv hB =>
        gr_res hv (x m j) (hA'.ext M) hB (fun l h => Or.inl h) ?_) (by omega)
    rintro l (rfl | rfl)
    · exact Or.inr rfl
    · exact Or.inl ⟨i, hi, hij, rfl⟩

/-- One level down: `Lev (m+1) → Lev m`, at most `3m` lines per `j`. -/
theorem step_level (hF : HasOrd F x n) {m : Nat} (hm : m < n) (L : List (Clause V))
    (hL : Valid F L) (hlev : Lev x (m + 1) L) : Gr F L (3 * m * m) (Lev x m) := by
  have h := gr_all (F := F) (Lev x (m + 1)) (fun j L => Cov L (T x m j)) (3 * m) m
    (fun L M h => lev_ext h M) (fun j L M h => h.ext M) ?_ m (Nat.le_refl _) L hL hlev
  · exact gr_mono h (by rw [Nat.mul_comm]; exact Nat.le_refl _) (fun M h' => h'.2)
  intro j hj L hL hlev
  -- `Q i`: a clause inside `T m j ∪ {x_{i'm} : i ≤ i' < m}`
  let Q : Nat → List (Clause V) → Prop := fun i L =>
    Lev x (m + 1) L ∧ Cov L (fun l => T x m j l ∨ ∃ i', i ≤ i' ∧ i' < m ∧ l = pX x i' m)
  have h0 : Q 0 L := ⟨hlev, (hlev m (Nat.lt_succ_self m)).weak (by
    rintro l ⟨i', hi', hne, rfl⟩
    exact Or.inr ⟨i', Nat.zero_le _, by omega, rfl⟩)⟩
  have hit := gr_iter Q 3 m ?_ m (Nat.le_refl _) L hL h0
  · refine gr_mono hit (by rw [Nat.mul_comm]; exact Nat.le_refl _) (fun M ⟨_, hc⟩ => hc.weak ?_)
    rintro l (h | ⟨i', h1, h2, _⟩)
    · exact h
    · omega
  intro i hi L hL ⟨hlev', hc⟩
  refine gr_seq (k' := 1) (step_D hF hm hi hj L hL (hlev' j (by omega))) (fun M hv hD => ?_)
    (by omega)
  refine gr_mono (gr_res hv (x i m) (S := fun l => T x m j l ∨
      ∃ i', i + 1 ≤ i' ∧ i' < m ∧ l = pX x i' m) (S' := T x m j)
    ((hc.ext M).weak ?_) hD (fun l h => h) (fun l h => Or.inl h)) (Nat.le_refl _)
    (fun M' h => ⟨lev_ext (lev_ext hlev' M) M', h⟩)
  rintro l (h | ⟨i', h1, h2, rfl⟩)
  · exact Or.inl (Or.inl h)
  · rcases Nat.lt_or_ge i i' with h' | h'
    · exact Or.inl (Or.inr ⟨i', h', h2, rfl⟩)
    · have : i' = i := by omega
      subst this; exact Or.inr rfl

theorem sq_le {m n : Nat} (h : m ≤ n) : 3 * m * m ≤ 3 * n * n :=
  Nat.mul_le_mul (Nat.mul_le_mul_left 3 h) h

/-- All levels: from `Lev n`, at most `k·3n²` further lines reach `Lev (m+1)`, `m + 1 + k = n`. -/
theorem levels (hF : HasOrd F x n) : ∀ k m, m + 1 + k = n → ∀ L, Valid F L → Lev x n L →
    Gr F L (k * (3 * n * n)) (Lev x (m + 1)) := by
  intro k
  induction k with
  | zero =>
    intro m hm L hL hlev
    have : m + 1 = n := by omega
    subst this; exact gr_zero hL hlev
  | succ k ih =>
    intro m hm L hL hlev
    exact gr_seq (ih (m + 1) (by omega) L hL hlev)
      (fun M hv hl => step_level hF (m := m + 1) (by omega) _ hv hl)
      (by rw [Nat.add_mul, Nat.one_mul]; have := sq_le (m := m + 1) (n := n) (by omega); omega)

/-- From `Lev n`, the empty clause: a refutation with at most `|L| + (n-1)·3n²` lines. -/
theorem refute_of_lev (hF : HasOrd F x n) (hn : 1 ≤ n) (L : List (Clause V)) (hL : Valid F L)
    (hlev : Lev x n L) : ∃ R : Refutation F, R.steps.length ≤ L.length + (n - 1) * (3 * n * n) := by
  obtain ⟨M, hM, hv, h1⟩ := levels hF (n - 1) 0 (by omega) L hL hlev
  obtain ⟨D, hD, hDs⟩ := h1 0 (Nat.zero_lt_one)
  have hDe : D = [] := by
    cases D with
    | nil => rfl
    | cons l D =>
      obtain ⟨i, hi, hne, _⟩ := hDs l List.mem_cons_self
      exact absurd (show i = 0 by omega) hne
  subst hDe
  exact ⟨⟨L ++ M, hv, hD⟩, by rw [List.length_append]; omega⟩

theorem cube (n : Nat) (hn : 1 ≤ n) : (n - 1) * (3 * n * n) + 3 * n * n = 3 * n ^ 3 := by
  have e : n - 1 + 1 = n := by omega
  calc (n - 1) * (3 * n * n) + 3 * n * n = (n - 1 + 1) * (3 * n * n) := by rw [Nat.add_mul, Nat.one_mul]
    _ = 3 * n ^ 3 := by rw [e, Nat.pow_succ, Nat.pow_two, Nat.mul_comm n (3 * n * n),
                            Nat.mul_assoc 3 n n, Nat.mul_assoc]

end Generic

/-! ## The 3-CNF ordering principle `Work.GT3.GT3 n` -/

open Programme.«20261024-1110-proof-complexity».GT3 in
theorem hasOrd_gt (n : Nat) : HasOrd (GT3 n) (fun a b => GV.x a b) n where
  anti a ha b hb hab := ⟨[ng (.x a b), ng (.x b a)], by
      simp only [GT3, List.mem_append, List.mem_flatMap, List.mem_range]
      exact Or.inl (Or.inl ⟨a, ha, b, hb, by simp [hab]⟩),
    by intro l hl; simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
       rcases hl with rfl | rfl
       · exact Or.inl rfl
       · exact Or.inr rfl⟩
  trans a ha b hb c hc hab hbc hac := ⟨[ng (.x a b), ng (.x b c), pl (.x a c)], by
      simp only [GT3, List.mem_append, List.mem_flatMap, List.mem_range]
      exact Or.inl (Or.inr ⟨a, ha, b, hb, c, hc, by simp [hab, hbc, hac]⟩),
    by intro l hl; simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
       rcases hl with rfl | rfl | rfl
       · exact Or.inl rfl
       · exact Or.inr (Or.inl rfl)
       · exact Or.inr (Or.inr rfl)⟩

open Programme.«20261024-1110-proof-complexity».GT3 in
/-- Unrolling the chain of `j`: `y_{j,0}`, then `¬y_{j,t} ∨ x_{tj} ∨ y_{j,t+1}` for `t < n`,
then `¬y_{j,n}`: at most `2n + 3` lines give a clause inside `T n j`. -/
theorem chain (n j : Nat) (hj : j < n) (L : List (Clause GV)) (hL : Valid (GT3 n) L) :
    Gr (GT3 n) L (2 * n + 3) (Cov · (T (fun a b => GV.x a b) n j)) := by
  have memj : ∀ C, C ∈ ([pl (.y j 0)] :: [ng (.y j n)] :: (List.range n).map fun i =>
      if i = j then [ng (.y j i), pl (.y j (i + 1))]
      else [ng (.y j i), pl (.x i j), pl (.y j (i + 1))]) → C ∈ GT3 n := by
    intro C hC
    simp only [GT3, List.mem_append, List.mem_flatMap, List.mem_range]
    exact Or.inr ⟨j, hj, hC⟩
  have memi : ∀ t < n, (if t = j then [ng (.y j t), pl (.y j (t + 1))]
      else [ng (.y j t), pl (.x t j), pl (.y j (t + 1))]) ∈ GT3 n := fun t ht =>
    memj _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)))
  -- `Q t`: a clause inside `T t j ∪ {y_{j,t}}`
  let Q : Nat → List (Clause GV) → Prop := fun t L =>
    Cov L (fun l => T (fun a b => GV.x a b) t j l ∨ l = pl (.y j t))
  have h0 : Gr (GT3 n) L 1 (Q 0) := gr_ax hL (memj _ List.mem_cons_self)
    (fun l hl => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hl; exact Or.inr hl)
  have hstep : ∀ t < n, ∀ L, Valid (GT3 n) L → Q t L → Gr (GT3 n) L 2 (Q (t + 1)) := by
    intro t ht L hL hq
    by_cases htj : t = j
    · have hm := memi t ht
      rw [if_pos htj] at hm
      subst htj
      refine gr_seq (gr_ax hL hm
        (S := fun l => l = pl (.y t (t + 1)) ∨ l = ⟨GV.y t t, false⟩)
        (fun l hl => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl
          · exact Or.inr rfl
          · exact Or.inl rfl)) (fun M hv hB =>
          gr_res hv (GV.y t t) (hq.ext M) hB ?_ (fun l h => Or.inr h)) (by omega)
      rintro l ⟨i, hi, hne, rfl⟩; exact Or.inl ⟨i, by omega, hne, rfl⟩
    · have hm := memi t ht
      rw [if_neg htj] at hm
      refine gr_seq (gr_ax hL hm
        (S := fun l => (l = pX (fun a b => GV.x a b) t j ∨ l = pl (.y j (t + 1))) ∨
          l = ⟨GV.y j t, false⟩)
        (fun l hl => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl | rfl
          · exact Or.inr rfl
          · exact Or.inl (Or.inl rfl)
          · exact Or.inl (Or.inr rfl)))
        (fun M hv hB => gr_res hv (GV.y j t) (hq.ext M) hB ?_ ?_) (by omega)
      · rintro l ⟨i, hi, hne, rfl⟩; exact Or.inl ⟨i, by omega, hne, rfl⟩
      · rintro l (rfl | rfl)
        · exact Or.inl ⟨t, by omega, htj, rfl⟩
        · exact Or.inr rfl
  have hit := fun L hL hq => gr_iter (F := GT3 n) Q 2 n hstep n (Nat.le_refl _) L hL hq
  refine gr_seq h0 (fun M hv hq => gr_seq (hit _ hv hq) (fun M' hv' hq' =>
    gr_seq (gr_ax hv' (memj [ng (.y j n)] (List.mem_cons_of_mem _ List.mem_cons_self))
      (S := fun l => l = ⟨GV.y j n, false⟩)
      (fun l hl => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hl; exact hl))
      (fun M'' hv'' hB => gr_res hv'' (GV.y j n) (S' := fun _ => False)
        (hq'.ext M'') (hB.weak (fun l h => Or.inr h)) (fun l h => h) (fun l h => h.elim))
      (Nat.le_refl _)) (Nat.le_refl _)) (by omega)

open Programme.«20261024-1110-proof-complexity».GT3 in
/-- **Polynomial size, all `n ≥ 1`:** the 3-CNF ordering principle `GT3 n` (the formula of
`Work.GT3.gt_width`) has a resolution refutation with at most `3n³ + 2n² + 3n` clauses. -/
theorem gt3_upper (n : Nat) (hn : 1 ≤ n) :
    ∃ R : Refutation (GT3 n), R.steps.length ≤ 3 * n ^ 3 + 2 * n ^ 2 + 3 * n := by
  obtain ⟨M, hM, hv, _, hlev⟩ := gr_all (F := GT3 n) (fun _ => True)
    (fun j L => Cov L (T (fun a b => GV.x a b) n j)) (2 * n + 3) n (fun _ _ _ => trivial)
    (fun j L M h => h.ext M) (fun j hj L hL _ => chain n j hj L hL) n (Nat.le_refl _) []
    (valid_nil _) trivial
  obtain ⟨R, hR⟩ := refute_of_lev (hasOrd_gt n) hn ([] ++ M) hv hlev
  refine ⟨R, Nat.le_trans hR ?_⟩
  rw [List.nil_append]
  have e1 := cube n hn
  have e2 : n * (2 * n + 3) = 2 * n ^ 2 + 3 * n := by
    rw [Nat.pow_two, Nat.mul_add, Nat.mul_comm n (2 * n), Nat.mul_assoc, Nat.mul_comm n 3]
  have := Nat.zero_le (3 * n * n)
  omega

open Programme.«20261024-1110-proof-complexity».GT3 in
/-- `GT3 n` is unsatisfiable for every `n ≥ 1` (so `Work.GT3.gt_width` is not vacuous). -/
theorem gt3_unsat (n : Nat) (hn : 1 ≤ n) (a : GV → Bool) : ∃ C ∈ GT3 n, C.eval a = false := by
  obtain ⟨R, _⟩ := gt3_upper n hn
  apply Classical.byContradiction
  intro h
  have hall : ∀ C ∈ GT3 n, C.eval a = true := fun C hC => by
    cases e : C.eval a
    · exact absurd ⟨C, hC, e⟩ h
    · rfl
  have key : ∀ k (hk : k < R.steps.length), R.steps[k].eval a = true := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro hk
      rcases R.derived k hk with hax | ⟨i, j, hi, hj, hr⟩
      · exact hall _ hax
      · obtain ⟨v, hA, hB, hAC, hBC⟩ := hr
        have hA' := ih i hi (Nat.lt_trans hi hk)
        have hB' := ih j hj (Nat.lt_trans hj hk)
        unfold Clause.eval at *
        rw [List.any_eq_true] at hA' hB' ⊢
        obtain ⟨l, hl, hlv⟩ := hA'
        obtain ⟨m, hm, hmv⟩ := hB'
        by_cases e1 : l = ⟨v, true⟩
        · by_cases e2 : m = ⟨v, false⟩
          · subst e1; subst e2
            simp only [Lit.eval, if_true] at hlv
            simp only [Lit.eval, Bool.false_eq_true, if_false] at hmv
            rw [hlv] at hmv; exact absurd hmv (by decide)
          · exact ⟨m, hBC m hm e2, hmv⟩
        · exact ⟨l, hAC l hl e1, hlv⟩
  obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp R.empty_mem
  have := key k hk
  rw [hke] at this
  simp [Clause.eval] at this

/-! ## The wide ordering principle (pr's `Work.GT.GT`, restated in `Work.BSW` types) -/

def pw (i j : Nat) : Lit (Nat × Nat) := ⟨(i, j), true⟩
def nw (i j : Nat) : Lit (Nat × Nat) := ⟨(i, j), false⟩

/-- Antisymmetry, transitivity, and one wide no-minimum clause per element (no totality);
clause for clause the formula `Work.GT.GT n` of `agents/pr/lean/Work/GTUpper.lean`. -/
def GTw (n : Nat) : CNF (Nat × Nat) :=
  ((List.range n).flatMap fun i => (List.range n).flatMap fun j =>
      if i ≠ j then [[nw i j, nw j i]] else []) ++
  ((List.range n).flatMap fun i => (List.range n).flatMap fun j => (List.range n).flatMap fun k =>
      if i ≠ j ∧ j ≠ k ∧ i ≠ k then [[nw i j, nw j k, pw i k]] else []) ++
  (List.range n).map (fun j => ((List.range n).filter (· ≠ j)).map fun i => pw i j)

theorem hasOrd_gtw (n : Nat) : HasOrd (GTw n) (fun a b => (a, b)) n where
  anti a ha b hb hab := ⟨[nw a b, nw b a], by
      simp only [GTw, List.mem_append, List.mem_flatMap, List.mem_range]
      exact Or.inl (Or.inl ⟨a, ha, b, hb, by simp [hab]⟩),
    by intro l hl; simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
       rcases hl with rfl | rfl
       · exact Or.inl rfl
       · exact Or.inr rfl⟩
  trans a ha b hb c hc hab hbc hac := ⟨[nw a b, nw b c, pw a c], by
      simp only [GTw, List.mem_append, List.mem_flatMap, List.mem_range]
      exact Or.inl (Or.inr ⟨a, ha, b, hb, c, hc, by simp [hab, hbc, hac]⟩),
    by intro l hl; simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
       rcases hl with rfl | rfl | rfl
       · exact Or.inl rfl
       · exact Or.inr (Or.inl rfl)
       · exact Or.inr (Or.inr rfl)⟩

/-- **Independent reproof of pr's `gt_upper` (K12), in `Work.BSW` types:** for `n ≥ 1` the wide
ordering principle has a refutation with at most `n + 3n³` clauses. -/
theorem gtw_upper (n : Nat) (hn : 1 ≤ n) :
    ∃ R : Refutation (GTw n), R.steps.length ≤ n + 3 * n ^ 3 := by
  obtain ⟨M, hM, hv, _, hlev⟩ := gr_all (F := GTw n) (fun _ => True)
    (fun j L => Cov L (T (fun a b => (a, b)) n j)) 1 n (fun _ _ _ => trivial)
    (fun j L M h => h.ext M) (fun j hj L hL _ => by
      refine gr_ax hL (C := ((List.range n).filter (· ≠ j)).map fun i => pw i j) ?_ ?_
      · simp only [GTw, List.mem_append]
        exact Or.inr (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
      · intro l hl
        simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hl
        obtain ⟨i, ⟨hi, hne⟩, rfl⟩ := hl
        exact ⟨i, hi, hne, rfl⟩) n (Nat.le_refl _) [] (valid_nil _) trivial
  obtain ⟨R, hR⟩ := refute_of_lev (hasOrd_gtw n) hn ([] ++ M) hv hlev
  refine ⟨R, Nat.le_trans hR ?_⟩
  rw [List.nil_append]
  have e1 := cube n hn
  have := Nat.zero_le (3 * n * n)
  omega

end Programme.«20261024-1110-proof-complexity».GTSize

#print axioms Programme.«20261024-1110-proof-complexity».GTSize.gt3_upper
#print axioms Programme.«20261024-1110-proof-complexity».GTSize.gt3_unsat
#print axioms Programme.«20261024-1110-proof-complexity».GTSize.gtw_upper
