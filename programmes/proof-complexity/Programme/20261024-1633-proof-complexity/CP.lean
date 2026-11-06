import Programme.«20261024-1110-proof-complexity».Haken
import Programme.«20261024-1110-proof-complexity».HakenSharp

/-!
# Cutting planes, soundness, and a cubic-size refutation of PHP

A line is a linear inequality `∑_{v ∈ X} a v · x_v ≥ b` over the integers, where `X` is a
duplicate-free list of variables. A clause `C` is translated as `∑_{l ∈ C} [l] ≥ 1`, where
`[x] = x` and `[¬x] = 1 - x`.

`D F X L s` says `L` has a tree-like cutting-planes derivation from `F` with `s` nodes. The rules are
clause axioms, the bounds `x_v ≥ 0` and `-x_v ≥ -1`, addition, multiplication by a natural number,
and division with rounding: from `∑ c·a' v · x_v ≥ b` with `c > 0` derive `∑ a' v · x_v ≥ b'` for
any `b'` with `c (b' - 1) < b`, i.e. `b' ≤ ⌈b / c⌉`. A refutation derives `0 ≥ 1`.

Tree-like size bounds DAG size (the number of distinct lines) from above.
-/

namespace Programme.«20261024-1633-proof-complexity».CP

open Programme.«20261024-1110-proof-complexity».Haken

/-- A linear inequality `∑ a v · x_v ≥ b`. -/
structure Line (V : Type) where
  a : V → Int
  b : Int

/-- 0/1 value of a variable. -/
def val {V} (α : V → Bool) (v : V) : Int := if α v then 1 else 0

def Line.lhs {V} (X : List V) (α : V → Bool) (L : Line V) : Int := (X.map fun v => L.a v * val α v).sum

def Line.holds {V} (X : List V) (α : V → Bool) (L : Line V) : Prop := L.b ≤ L.lhs X α

def Line.add {V} (L M : Line V) : Line V := ⟨fun v => L.a v + M.a v, L.b + M.b⟩

def Line.smul {V} (c : Nat) (L : Line V) : Line V := ⟨fun v => (c : Int) * L.a v, (c : Int) * L.b⟩

/-- Signed coefficient of `v` contributed by literal `l`. -/
def litCoef {V} [DecidableEq V] (l : Lit V) (v : V) : Int :=
  if l.var = v then (if l.pos then 1 else -1) else 0

/-- `∑_{l ∈ C} [l] ≥ 1`, with `[¬x] = 1 - x` moved to the right-hand side. -/
def clauseLine {V} [DecidableEq V] (C : Clause V) : Line V :=
  ⟨fun v => (C.map fun l => litCoef l v).sum, 1 - (C.map fun l => if l.pos then (0 : Int) else 1).sum⟩

/-- Tree-like cutting-planes derivations with their number of nodes. -/
inductive D {V} [DecidableEq V] (F : CNF V) : Line V → Nat → Prop
  | ax (C : Clause V) : C ∈ F → D F (clauseLine C) 1
  | lo (u : V) : D F ⟨fun v => if u = v then 1 else 0, 0⟩ 1
  | hi (u : V) : D F ⟨fun v => if u = v then -1 else 0, -1⟩ 1
  | add {L M : Line V} {s t : Nat} : D F L s → D F M t → D F (L.add M) (s + t + 1)
  | smul {L : Line V} {s : Nat} (c : Nat) : D F L s → D F (L.smul c) (s + 1)
  | div {L : Line V} {s : Nat} (c : Nat) (a' : V → Int) (b' : Int) : D F L s → 0 < c →
      (∀ v, L.a v = (c : Int) * a' v) → (c : Int) * (b' - 1) < L.b → D F ⟨a', b'⟩ (s + 1)

/-- A cutting-planes refutation of `F` with `size` nodes, over a duplicate-free list `X` of
variables covering every variable of `F`. -/
structure Refutation {V} [DecidableEq V] (F : CNF V) where
  X : List V
  nodup : X.Nodup
  cover : ∀ C ∈ F, ∀ l ∈ C, l.var ∈ X
  size : Nat
  deriv : D F ⟨fun _ => 0, 1⟩ size

/-! ## Soundness -/

theorem sum_add {α} (X : List α) (f g : α → Int) :
    (X.map fun v => f v + g v).sum = (X.map f).sum + (X.map g).sum := by
  induction X with
  | nil => simp
  | cons x X ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_mul {α} (X : List α) (c : Int) (f : α → Int) :
    (X.map fun v => c * f v).sum = c * (X.map f).sum := by
  induction X with
  | nil => simp
  | cons x X ih => simp only [List.map_cons, List.sum_cons, ih, Int.mul_add]

theorem sum_zero {α} (X : List α) : (X.map fun _ => (0 : Int)).sum = 0 := by
  induction X with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, List.sum_cons, ih]; rfl

theorem sum_single {V} [DecidableEq V] (X : List V) (h : X.Nodup) (u : V) (r : Int) :
    (X.map fun v => if u = v then r else 0).sum = if u ∈ X then r else 0 := by
  induction X with
  | nil => simp
  | cons x X ih =>
    have hx : x ∉ X := (List.nodup_cons.mp h).1
    simp only [List.map_cons, List.sum_cons, ih (List.nodup_cons.mp h).2, List.mem_cons]
    by_cases e : u = x
    · subst e; simp [hx]
    · simp [e]

theorem lhs_add {V} (X : List V) (α : V → Bool) (L M : Line V) :
    (L.add M).lhs X α = L.lhs X α + M.lhs X α := by
  unfold Line.lhs Line.add
  simp only [Int.add_mul]
  exact sum_add X _ _

theorem lhs_smul {V} (X : List V) (α : V → Bool) (c : Nat) (L : Line V) :
    (L.smul c).lhs X α = c * L.lhs X α := by
  unfold Line.lhs Line.smul
  simp only [Int.mul_assoc]
  exact sum_mul X _ _

/-- Value of literal `l` as an integer. -/
def litVal {V} (α : V → Bool) (l : Lit V) : Int := if l.eval α then 1 else 0

theorem clause_lhs {V} [DecidableEq V] (X : List V) (hX : X.Nodup) (α : V → Bool) (C : Clause V)
    (hC : ∀ l ∈ C, l.var ∈ X) :
    (clauseLine C).lhs X α + (C.map fun l => if l.pos then (0 : Int) else 1).sum =
      (C.map fun l => litVal α l).sum := by
  induction C with
  | nil =>
    simp only [Line.lhs, clauseLine, List.map_nil, List.sum_nil, Int.zero_mul]
    rw [sum_zero]; rfl
  | cons l C ih =>
    have ih := ih (fun l' hl' => hC l' (List.mem_cons_of_mem _ hl'))
    have hl : l.var ∈ X := hC l (List.mem_cons_self ..)
    have split : (clauseLine (l :: C)).lhs X α =
        (X.map fun v => litCoef l v * val α v).sum + (clauseLine C).lhs X α := by
      unfold Line.lhs clauseLine
      simp only [List.map_cons, List.sum_cons, Int.add_mul]
      exact sum_add X _ _
    have single : (X.map fun v => litCoef l v * val α v).sum =
        (if l.pos then 1 else -1) * val α l.var := by
      have : (X.map fun v => litCoef l v * val α v).sum =
          (X.map fun v => if l.var = v then (if l.pos then 1 else -1) * val α l.var else 0).sum := by
        congr 1; apply List.map_congr_left; intro v _
        unfold litCoef; by_cases e : l.var = v
        · subst e; simp
        · simp [e]
      rw [this, sum_single X hX]; simp [hl]
    rw [split, single]
    simp only [List.map_cons, List.sum_cons]
    have hv : litVal α l = (if l.pos then 1 else -1) * val α l.var + (if l.pos then 0 else 1) := by
      unfold litVal val Lit.eval
      cases l.pos <;> cases α l.var <;> simp
    rw [hv]; omega

theorem litVals_pos {V} (α : V → Bool) (C : Clause V) (h : C.eval α = true) :
    1 ≤ (C.map fun l => litVal α l).sum := by
  induction C with
  | nil => simp [Clause.eval] at h
  | cons l C ih =>
    simp only [List.map_cons, List.sum_cons]
    have nn : ∀ (C : Clause V), 0 ≤ (C.map fun l => litVal α l).sum := by
      intro C; induction C with
      | nil => simp
      | cons l C ih =>
        simp only [List.map_cons, List.sum_cons]
        have : 0 ≤ litVal α l := by unfold litVal; split <;> omega
        omega
    unfold Clause.eval at h
    rw [List.any_cons] at h
    cases e : l.eval α
    · rw [e, Bool.false_or] at h
      have := ih h
      have : litVal α l = 0 := by simp [litVal, e]
      omega
    · have := nn C
      have : litVal α l = 1 := by simp [litVal, e]
      omega

theorem D_sound {V} [DecidableEq V] {F : CNF V} (X : List V) (hX : X.Nodup)
    (cover : ∀ C ∈ F, ∀ l ∈ C, l.var ∈ X) (α : V → Bool) (hα : ∀ C ∈ F, C.eval α = true)
    {L : Line V} {s : Nat} (d : D F L s) : L.holds X α := by
  induction d with
  | ax C hC =>
    have h1 := clause_lhs X hX α C (cover C hC)
    have h2 := litVals_pos α C (hα C hC)
    unfold Line.holds; simp only [clauseLine] at h1 ⊢; omega
  | lo u =>
    unfold Line.holds Line.lhs
    have : (X.map fun v => (if u = v then (1 : Int) else 0) * val α v).sum =
        (X.map fun v => if u = v then val α u else 0).sum := by
      congr 1; apply List.map_congr_left; intro v _
      by_cases e : u = v
      · subst e; simp
      · simp [e]
    simp only; rw [this, sum_single X hX]
    unfold val; split <;> (try split) <;> omega
  | hi u =>
    unfold Line.holds Line.lhs
    have : (X.map fun v => (if u = v then (-1 : Int) else 0) * val α v).sum =
        (X.map fun v => if u = v then -val α u else 0).sum := by
      congr 1; apply List.map_congr_left; intro v _
      by_cases e : u = v
      · subst e; simp
      · simp [e]
    simp only; rw [this, sum_single X hX]
    unfold val; split <;> (try split) <;> omega
  | add _ _ ih1 ih2 =>
    unfold Line.holds at *; rw [lhs_add]; simp only [Line.add]; omega
  | smul c _ ih =>
    unfold Line.holds at *; rw [lhs_smul]; simp only [Line.smul]
    exact Int.mul_le_mul_of_nonneg_left ih (Int.natCast_nonneg c)
  | @div L s c a' b' _ hc ha hb ih =>
    unfold Line.holds at *
    have e : L.lhs X α = (c : Int) * (Line.lhs X α ⟨a', b'⟩) := by
      unfold Line.lhs; rw [← sum_mul]; congr 1; apply List.map_congr_left; intro v _
      rw [ha v, Int.mul_assoc]
    rw [e] at ih
    have : (c : Int) * (b' - 1) < (c : Int) * (Line.lhs X α ⟨a', b'⟩) := Int.lt_of_lt_of_le hb ih
    have := Int.lt_of_mul_lt_mul_left this (Int.natCast_nonneg c)
    simp only; omega

/-- Cutting planes is sound: a CNF with a refutation has no satisfying assignment. -/
theorem cp_sound {V} [DecidableEq V] {F : CNF V} (R : Refutation F) :
    ¬ ∃ α : V → Bool, ∀ C ∈ F, C.eval α = true := by
  rintro ⟨α, hα⟩
  have := D_sound R.X R.nodup R.cover α hα R.deriv
  simp only [Line.holds, Line.lhs, Int.zero_mul] at this
  rw [sum_zero] at this
  omega

/-! ## A cubic-size refutation of `PHP n` -/

theorem D.cast {V} [DecidableEq V] {F : CNF V} {L M : Line V} {s t : Nat} (d : D F L s)
    (ha : ∀ v, L.a v = M.a v) (hb : L.b = M.b) (hs : s = t) : D F M t := by
  have : L = M := by cases L; cases M; simp only at ha hb; rw [funext ha, hb]
  subst this; subst hs; exact d

/-- `-∑_{p<k} x_{p,h} ≥ -1`. -/
def S (h k : Nat) : Line (Nat × Nat) := ⟨fun v => if v.2 = h ∧ v.1 < k then -1 else 0, -1⟩

theorem hole_line (p q h : Nat) : clauseLine (holeAx p q h) =
    ⟨fun v => (if (p, h) = v then -1 else 0) + (if (q, h) = v then -1 else 0), -1⟩ := by
  simp [clauseLine, holeAx, litCoef]

theorem pigeon_line (n p : Nat) : clauseLine (pigeonAx n p) =
    ⟨fun v => if v.1 = p ∧ v.2 < n then 1 else 0, 1⟩ := by
  unfold clauseLine pigeonAx
  congr 1
  · funext v
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.map_append, List.sum_append, ih]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, litCoef]
      obtain ⟨a, b⟩ := v
      simp only [Prod.mk.injEq]
      by_cases e1 : p = a <;> by_cases e2 : n = b <;> simp [e1, e2] <;> omega
  · simp only [List.map_map]
    have : ∀ l : List Nat, (l.map ((fun l : Lit (Nat × Nat) => if l.pos then (0 : Int) else 1) ∘
        fun h => (⟨(p, h), true⟩ : Lit (Nat × Nat)))).sum = 0 := by
      intro l; induction l with
      | nil => simp
      | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; simp
    rw [this]; rfl

theorem hole_mem {n p q h : Nat} (hpq : p < q) (hq : q ≤ n) (hh : h < n) : holeAx p q h ∈ PHP n := by
  unfold PHP
  apply List.mem_append_right
  simp only [List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter, decide_eq_true_eq]
  exact ⟨h, hh, p, by omega, q, ⟨by omega, hpq⟩, rfl⟩

theorem pigeon_mem {n p : Nat} (hp : p ≤ n) : pigeonAx n p ∈ PHP n := by
  unfold PHP
  apply List.mem_append_left
  simp only [List.mem_map, List.mem_range]
  exact ⟨p, by omega, rfl⟩

/-- Partial sums inside one division step: `m·S h (m+1)` plus hole axioms `(i, m+1, h)`, `i < j`. -/
theorem step_partial {n h m s : Nat} (hm : m + 1 ≤ n) (hh : h < n) (d : D (PHP n) (S h (m + 1)) s) :
    ∀ j, j ≤ m + 1 → D (PHP n)
      ⟨fun v => (m : Int) * (if v.2 = h ∧ v.1 < m + 1 then -1 else 0) +
        (if v.2 = h ∧ v.1 < j then -1 else 0) + (if v = (m + 1, h) then -(j : Int) else 0),
        -(m : Int) - j⟩ (s + 1 + 2 * j) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine (D.smul m d).cast ?_ ?_ rfl
    · intro v; simp only [Line.smul, S]; split <;> simp <;> omega
    · simp [Line.smul, S]
  | succ j ih =>
    intro hj
    have d2 := D.add (ih (by omega)) (D.ax _ (hole_mem (p := j) (q := m + 1) (h := h) (by omega) hm hh))
    rw [hole_line] at d2
    refine d2.cast ?_ ?_ (by omega)
    · intro ⟨a, b⟩
      simp only [Line.add, Prod.mk.injEq]
      by_cases e1 : b = h <;> by_cases e2 : a = j <;> by_cases e3 : a = m + 1 <;>
        simp [e1, e2, e3] <;> (repeat' split) <;> omega
    · simp [Line.add]; omega

theorem step {n h m s : Nat} (hm : m + 1 ≤ n) (hh : h < n) (d : D (PHP n) (S h (m + 1)) s) :
    D (PHP n) (S h (m + 2)) (s + 2 * m + 4) := by
  have d1 := step_partial hm hh d (m + 1) (Nat.le_refl _)
  refine (D.div (m + 1) (S h (m + 2)).a (S h (m + 2)).b d1 (by omega) ?_ ?_).cast
    (fun _ => rfl) rfl (by omega)
  · intro ⟨a, b⟩
    simp only [S, Prod.mk.injEq]
    by_cases e1 : b = h <;> by_cases e3 : a = m + 1 <;> simp [e1, e3] <;> (repeat' split) <;> omega
  · simp [S]; omega

theorem hole_chain {n h : Nat} (hh : h < n) :
    ∀ m, m ≤ n → D (PHP n) (S h (m + 1)) (m * m + 3 * m + 1) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine (D.hi (F := PHP n) (0, h)).cast ?_ rfl rfl
    intro ⟨a, b⟩; simp only [S, Prod.mk.injEq]
    by_cases e1 : b = h <;> by_cases e2 : a = 0 <;> simp [e1, e2] <;> omega
  | succ m ih =>
    intro hm
    exact (step (by omega) hh (ih (by omega))).cast (fun _ => rfl) rfl (by grind)

/-- Sum of the pigeon axioms for pigeons `p < k`. -/
theorem pigeon_sum (n : Nat) : ∀ k, 1 ≤ k → k ≤ n + 1 →
    D (PHP n) ⟨fun v => if v.1 < k ∧ v.2 < n then 1 else 0, k⟩ (2 * k - 1) := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro _ hk
    by_cases k0 : k = 0
    · subst k0
      have d := D.ax _ (pigeon_mem (n := n) (p := 0) (by omega))
      rw [pigeon_line] at d
      refine d.cast ?_ rfl rfl
      intro ⟨a, b⟩; by_cases e : a = 0 <;> simp [e] <;> omega
    · have d := D.add (ih (by omega) (by omega)) (D.ax _ (pigeon_mem (n := n) (p := k) (by omega)))
      rw [pigeon_line] at d
      refine d.cast ?_ (by simp [Line.add]) (by omega)
      intro ⟨a, b⟩; simp only [Line.add]
      by_cases e : a = k <;> (repeat' split) <;> simp_all <;> omega

theorem final_sum (n : Nat) : ∀ k, k ≤ n →
    D (PHP n) ⟨fun v => (if v.1 < n + 1 ∧ v.2 < n then 1 else 0) +
      (if v.1 < n + 1 ∧ v.2 < k then -1 else 0), (n + 1 : Int) - k⟩
      (2 * n + 1 + k * (n * n + 3 * n + 2)) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine (pigeon_sum n (n + 1) (by omega) (Nat.le_refl _)).cast ?_ (by simp) (by omega)
    intro v; simp
  | succ k ih =>
    intro hk
    have d := D.add (ih (by omega)) (hole_chain (n := n) (h := k) (by omega) n (Nat.le_refl _))
    refine d.cast ?_ (by simp [Line.add, S]; omega) (by grind)
    intro ⟨a, b⟩; simp only [Line.add, S]
    by_cases e : b = k <;> (repeat' split) <;> simp_all <;> omega

theorem grid_nodup (n : Nat) : (grid n).Nodup := by
  unfold grid List.Nodup
  rw [List.pairwise_flatMap]
  constructor
  · intro p _
    rw [List.pairwise_map]
    exact List.nodup_range.imp (fun h e => h (by simpa using e))
  · refine List.nodup_range.imp ?_
    intro p q hpq x hx y hy e
    simp only [List.mem_map] at hx hy
    obtain ⟨_, _, rfl⟩ := hx; obtain ⟨_, _, rfl⟩ := hy
    exact hpq (by simpa using congrArg Prod.fst e)

theorem grid_cover (n : Nat) : ∀ C ∈ PHP n, ∀ l ∈ C, l.var ∈ grid n := by
  intro C hC l hl
  unfold grid
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]
  rcases mem_PHP hC with ⟨p, hp, rfl⟩ | ⟨p, q, h, hpq, hq, hh, rfl⟩
  · simp only [pigeonAx, List.mem_map, List.mem_range] at hl
    obtain ⟨h, hh, rfl⟩ := hl
    exact ⟨p, by omega, h, hh, rfl⟩
  · simp only [holeAx, List.mem_cons, List.mem_nil_iff, or_false] at hl
    rcases hl with rfl | rfl
    · exact ⟨p, by omega, h, hh, rfl⟩
    · exact ⟨q, by omega, h, hh, rfl⟩

/-- `PHP^{n+1}_n` has a tree-like cutting-planes refutation with `n³ + 3n² + 4n + 1` nodes
(Cook–Coullard–Turán 1987). -/
def php_cp (n : Nat) : Refutation (PHP n) where
  X := grid n
  nodup := grid_nodup n
  cover := grid_cover n
  size := n * n * n + 3 * n * n + 4 * n + 1
  deriv := (final_sum n n (Nat.le_refl _)).cast
    (by intro v; simp only; split <;> simp_all) (by simp; omega) (by grind)

theorem php_cp_size (n : Nat) : (php_cp n).size = n * n * n + 3 * n * n + 4 * n + 1 := rfl

/-- Separation of resolution and cutting planes on `PHP^{n+1}_n`: cutting planes (this file) is
sound, for every `n` a cutting-planes refutation of `PHP n` with `n³+3n²+4n+1` nodes exists, and
every resolution refutation (library type) with `S` clauses has `18^{2⌊n/6⌋} ≤ 17^{2⌊n/6⌋} S`. -/
theorem res_cp_sep (n : Nat) :
    (∀ {V : Type} [DecidableEq V] (F : CNF V), Refutation F → ¬ ∃ α : V → Bool, ∀ C ∈ F, C.eval α = true) ∧
    (∃ R : Refutation (PHP n), R.size = n * n * n + 3 * n * n + 4 * n + 1) ∧
    ∀ R : Programme.«20261024-1110-proof-complexity».Haken.Refutation (PHP n),
      18 ^ (2 * (n / 6)) ≤ 17 ^ (2 * (n / 6)) * R.steps.length :=
  ⟨fun _ R => cp_sound R, ⟨php_cp n, rfl⟩,
    fun R => Programme.«20261024-1110-proof-complexity».HakenSharp.haken_sharp n R⟩

end Programme.«20261024-1633-proof-complexity».CP
