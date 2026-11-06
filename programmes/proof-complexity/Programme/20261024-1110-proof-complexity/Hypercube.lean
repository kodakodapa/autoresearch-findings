import Programme.«20261024-1110-proof-complexity».Tseitin

/-!
# Tseitin formulas on hypercubes: an exponential resolution lower bound (core Lean 4)

`Q k` is the edge list of the `k`-dimensional hypercube on vertices `0..2^k-1` (built recursively:
two copies of `Q k` and the matching `u ~ u + 2^k`). We prove for it, for all `k`:
* every vertex has degree `≤ k`, `2|E| = k 2^k`, and every edge joins two distinct vertices;
* edge expansion `min(|S|, 2^k - |S|) ≤ |∂S|` for every vertex set `S` (induction on `k`);
* so `Work.Tseitin.tseitin_width` / `tseitin_size` apply with `e = 2^k/3`, `w0 = k`.
With charge 1 at vertex 0 (`HQ k`) the formula is unsatisfiable, every refutation has a clause
with `≥ 2^k/3` edge literals (`k ≥ 2`), and for `k ≥ 7` every refutation with `L` clauses has
`(8k)^(2^(k-3)) ≤ L (8k-1)^(2^(k-3))`, i.e. `L ≥ exp(Ω(2^k/k))`.

## Main results (`#print axioms` at the end of the file)
* `hq_main` (claim K23): `hq_unsat` ∧ `hq_size`. Axioms: propext, Classical.choice, Quot.sound.
* `hq_width` (`k ≥ 2`): some line has `≥ 2^k/3` distinct edge literals. Same axioms.
* `cut_ge`: edge isoperimetry `min(|S|, 2^k-|S|) ≤ |∂S|`. Axioms: propext, Quot.sound.
* `deg_le`, `Q_ends`, `Q_len`: degree `≤ k`, endpoints `u < v < 2^k`, `2|E| = k 2^k`.
Formula size: `|HQ k| = 2^k · 2^(k-1)` clauses of width `k`, so `2^k/k = Θ(√|F| / log |F|)` up to
constants in the exponent.

## Prior art and what this file adds (request R4, `brief/requests/R4.md`)
The general Tseitin expansion bound used here (`Work.Tseitin`, K20/K21) probably also exists in
Lean 4 in cslib-community/complexitylib (`TseitinExpander`; R4 saw search snippets only). R4 found
no Lean instantiation on the hypercube. What this file adds: a machine-checked edge isoperimetric
inequality for `Q k` (`cut_ge`, by induction on `k`, no Mathlib) and its composition into an
explicit, unconditional size bound with stated constants for a concrete family (K23).
-/

namespace Programme.«20261024-1110-proof-complexity».Hypercube

open Programme.«20261024-1110-proof-complexity».Haken Programme.«20261024-1110-proof-complexity».Tseitin

/-- Edges of the hypercube on `0..2^k-1`. -/
def Q : Nat → List (Nat × Nat)
  | 0 => []
  | k + 1 => Q k ++ (Q k).map (fun p => (2 ^ k + p.1, 2 ^ k + p.2)) ++
      (List.range (2 ^ k)).map (fun u => (u, 2 ^ k + u))

/-- Charge `1` at vertex `0`, `0` elsewhere. -/
def chg (v : Nat) : Nat := if v = 0 then 1 else 0

/-- The Tseitin formula of the `k`-dimensional hypercube with one odd vertex. -/
def HQ (k : Nat) : CNF Nat := Tseitin (2 ^ k) (Q k) chg

/-- Number of edges of `E` with exactly one endpoint in `S`. -/
def cut (E : List (Nat × Nat)) (S : Nat → Bool) : Nat := E.countP fun p => S p.1 != S p.2

theorem range_edge (E : List (Nat × Nat)) : (List.range E.length).map (edge E) = E := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [edge, List.getElem?_eq_getElem h2]

theorem filter_len (E : List (Nat × Nat)) (f : Nat × Nat → Bool) :
    ((List.range E.length).filter fun i => f (edge E i)).length = E.countP f := by
  rw [← List.countP_eq_length_filter]
  conv => rhs; rw [← range_edge E]
  rw [List.countP_map]; rfl

theorem bd_len (E : List (Nat × Nat)) (S : Nat → Bool) : (bd E S).length = cut E S :=
  filter_len E (fun p => S p.1 != S p.2)

theorem inc_len (E : List (Nat × Nat)) (v : Nat) :
    (inc E v).length = E.countP (fun p => p.1 == v || p.2 == v) :=
  filter_len E (fun p => p.1 == v || p.2 == v)

theorem countP_or {α} (l : List α) (p q r : α → Bool) (h : ∀ x ∈ l, p x = true → q x = true ∨ r x = true) :
    l.countP p ≤ l.countP q + l.countP r := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ha := h a List.mem_cons_self
    simp only [List.countP_cons]
    cases hp : p a <;> cases hq : q a <;> cases hr : r a <;> simp_all <;> omega

theorem cnt_inj (f : Nat → Nat) (hf : ∀ a b, f a = f b → a = b) (v N : Nat) :
    (List.range N).countP (fun u => f u == v) ≤ 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.countP_append]
    by_cases h : f N = v
    · have : (List.range N).countP (fun u => f u == v) = 0 := by
        rw [List.countP_eq_zero]; intro a ha hfa
        have := hf a N (by simp at hfa; omega)
        have := List.mem_range.mp ha; omega
      rw [this]; simp [h]
    · simp [h]; exact ih

theorem size_le (n : Nat) (S : Nat → Bool) : size n S ≤ n := by
  have := List.countP_le_length (p := S) (l := List.range n)
  simpa [size] using this

theorem size_succ (k : Nat) (S : Nat → Bool) :
    size (2 ^ (k + 1)) S = size (2 ^ k) S + size (2 ^ k) (fun v => S (2 ^ k + v)) := by
  unfold size
  rw [Nat.pow_succ, Nat.mul_two, List.range_add, List.countP_append, List.countP_map]; rfl

theorem cut_succ (k : Nat) (S : Nat → Bool) :
    cut (Q (k + 1)) S = cut (Q k) S + cut (Q k) (fun v => S (2 ^ k + v)) +
      (List.range (2 ^ k)).countP (fun u => S u != S (2 ^ k + u)) := by
  simp only [cut, Q, List.countP_append, List.countP_map]; rfl

/-- **Edge expansion of the hypercube.** -/
theorem cut_ge (k : Nat) : ∀ S : Nat → Bool, min (size (2 ^ k) S) (2 ^ k - size (2 ^ k) S) ≤ cut (Q k) S := by
  induction k with
  | zero => intro S; have := size_le 1 S; simp at this ⊢; omega
  | succ k ih =>
    intro S
    rw [size_succ, cut_succ]
    have h1 := ih S
    have h2 := ih (fun v => S (2 ^ k + v))
    have h3 := size_le (2 ^ k) S
    have h4 := size_le (2 ^ k) (fun v => S (2 ^ k + v))
    have h5 := countP_or (List.range (2 ^ k)) S (fun u => S u != S (2 ^ k + u)) (fun u => S (2 ^ k + u))
      (by intro u _ h; cases h' : S (2 ^ k + u) <;> simp_all)
    have h6 := countP_or (List.range (2 ^ k)) (fun u => S (2 ^ k + u)) (fun u => S u != S (2 ^ k + u)) S
      (by intro u _ h; cases h' : S u <;> simp_all)
    have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ, Nat.mul_two]
    unfold size at h3 h4 h1 h2 ⊢
    rw [hp]; omega

theorem Q_ends (k : Nat) : ∀ p ∈ Q k, p.1 < p.2 ∧ p.2 < 2 ^ k := by
  have hp : ∀ k, 2 ^ (k + 1) = 2 ^ k + 2 ^ k := fun k => by rw [Nat.pow_succ, Nat.mul_two]
  induction k with
  | zero => simp [Q]
  | succ k ih =>
    intro p hp'
    simp only [Q, List.mem_append, List.mem_map, List.mem_range] at hp'
    rw [hp]
    rcases hp' with (h | ⟨q, hq, rfl⟩) | ⟨u, hu, rfl⟩
    · have := ih p h; omega
    · have := ih q hq; simp; omega
    · simp; have : 0 < 2 ^ k := Nat.two_pow_pos k; omega

theorem Q_len (k : Nat) : 2 * (Q k).length = k * 2 ^ k := by
  induction k with
  | zero => simp [Q]
  | succ k ih =>
    simp only [Q, List.length_append, List.length_map, List.length_range]
    rw [Nat.pow_succ, Nat.add_mul, ← Nat.mul_assoc, Nat.one_mul, ← ih]; omega

theorem deg_zero (k v : Nat) (hv : 2 ^ k ≤ v) : (Q k).countP (fun p => p.1 == v || p.2 == v) = 0 := by
  rw [List.countP_eq_zero]; intro p hp h
  have := Q_ends k p hp; simp at h; omega

/-- Every vertex of the hypercube has degree `≤ k`. -/
theorem deg_le (k : Nat) : ∀ v, (Q k).countP (fun p => p.1 == v || p.2 == v) ≤ k := by
  induction k with
  | zero => intro v; simp [Q]
  | succ k ih =>
    intro v
    simp only [Q, List.countP_append, List.countP_map]
    have hm := countP_or (List.range (2 ^ k)) ((fun p : Nat × Nat => p.1 == v || p.2 == v) ∘
        fun u => (u, 2 ^ k + u)) (fun u => u == v) (fun u => 2 ^ k + u == v)
      (by intro u _ h; simpa using h)
    have c1 := cnt_inj (fun u => u) (fun a b h => h) v (2 ^ k)
    have c2 := cnt_inj (fun u => 2 ^ k + u) (fun a b h => by omega) v (2 ^ k)
    by_cases hv : v < 2 ^ k
    · have hs : (Q k).countP ((fun p : Nat × Nat => p.1 == v || p.2 == v) ∘
          fun p => (2 ^ k + p.1, 2 ^ k + p.2)) = 0 := by
        rw [List.countP_eq_zero]; intro p _ h; simp at h; omega
      have hz : (List.range (2 ^ k)).countP (fun u => 2 ^ k + u == v) = 0 := by
        rw [List.countP_eq_zero]; intro p _ h; simp at h; omega
      have := ih v; omega
    · have hz : (List.range (2 ^ k)).countP (fun u => u == v) = 0 := by
        rw [List.countP_eq_zero]; intro p hp h; simp at h; have := List.mem_range.mp hp; omega
      have hs : (Q k).countP ((fun p : Nat × Nat => p.1 == v || p.2 == v) ∘
          fun p => (2 ^ k + p.1, 2 ^ k + p.2)) =
          (Q k).countP (fun p => p.1 == v - 2 ^ k || p.2 == v - 2 ^ k) := by
        apply List.countP_congr; intro p _
        simp only [Function.comp, Bool.or_eq_true, beq_iff_eq]; omega
      have := ih (v - 2 ^ k)
      have := deg_zero k v (by omega)
      omega

theorem chg_sum (n : Nat) (hn : 1 ≤ n) : ((List.range n).map chg).sum = 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rfl
    · rw [List.range_succ, List.map_append, List.sum_append, ih h]
      simp [chg]; omega

/-- **Unsatisfiability** of `HQ k`. -/
theorem hq_unsat (k : Nat) (α : Nat → Bool) : ∃ C ∈ HQ k, C.eval α = false :=
  tseitin_unsat (fun p hp => by have := Q_ends k p hp; omega)
    (by rw [chg_sum _ (Nat.two_pow_pos k)]) α

theorem hexp (k : Nat) : ∀ S : Nat → Bool, 2 ^ k / 3 < size (2 ^ k) S →
    size (2 ^ k) S ≤ 2 * (2 ^ k / 3) → 2 ^ k / 3 ≤ (bd (Q k) S).length := by
  intro S h1 h2
  rw [bd_len]; have := cut_ge k S; omega

theorem hconn (k : Nat) : ∀ S : Nat → Bool, 0 < size (2 ^ k) S → size (2 ^ k) S < 2 ^ k →
    bd (Q k) S ≠ [] := by
  intro S h1 h2 h
  have := cut_ge k S
  rw [← bd_len, h] at this; simp at this; omega

theorem hE (k : Nat) : ∀ p ∈ Q k, p.1 < 2 ^ k ∧ p.2 < 2 ^ k :=
  fun p hp => by have := Q_ends k p hp; omega

theorem three_le (k : Nat) (hk : 2 ≤ k) : 3 ≤ 2 ^ k := by
  have := Nat.pow_le_pow_right (by omega : 0 < 2) hk; simp at this; omega

/-- **Width**: for `k ≥ 2` every refutation of `HQ k` has a clause with `≥ 2^k/3` edge literals. -/
theorem hq_width (k : Nat) (hk : 2 ≤ k) (π : Refutation (HQ k)) :
    ∃ C ∈ π.steps, 2 ^ k / 3 ≤ Programme.«20261024-1110-proof-complexity».BSWR.wd (List.range (Q k).length) C :=
  tseitin_width (hE k) (hconn k) (hexp k) (three_le k hk) π

/-- **Size**: for `k ≥ 7` every refutation of `HQ k` with `L` clauses has
`(8k)^(2^(k-3)) ≤ L (8k-1)^(2^(k-3))`. -/
theorem hq_size (k : Nat) (hk : 7 ≤ k) (π : Refutation (HQ k)) :
    (8 * k) ^ 2 ^ (k - 3) ≤ π.steps.length * (8 * k - 1) ^ 2 ^ (k - 3) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 7 := ⟨k - 7, by omega⟩
  have hB : 2 ^ (j + 7 - 3) = 16 * 2 ^ j := by
    rw [show j + 7 - 3 = j + 4 by omega, Nat.pow_add]; omega
  have hN : 2 ^ (j + 7) = 128 * 2 ^ j := by rw [Nat.pow_add]; omega
  have hj : j < 2 ^ j := Nat.lt_two_pow_self
  have hwd : j + 7 + 2 ^ (j + 7 - 3) + 2 ^ (j + 7 - 3) < 2 ^ (j + 7) / 3 := by
    rw [hB, hN]; omega
  have hdeg : ∀ v, v < 2 ^ (j + 7) → (inc (Q (j + 7)) v).length ≤ j + 7 := by
    intro v _; rw [inc_len]; exact deg_le _ v
  have h := tseitin_size (hE _) (hconn _) (hexp _) (three_le _ (by omega)) hdeg hwd π
  generalize hBdef : 2 ^ (j + 7 - 3) = B at h ⊢
  have hL : 2 * (Q (j + 7)).length = 8 * (j + 7) * B := by
    rw [Q_len, hN, ← hBdef, hB, show 128 * 2 ^ j = 8 * (16 * 2 ^ j) by omega, Nat.mul_left_comm,
      Nat.mul_assoc]
  have hL' : 2 * (Q (j + 7)).length - B = (8 * (j + 7) - 1) * B := by
    rw [hL, Nat.sub_mul, Nat.one_mul]
  have hBpos : 0 < B := by rw [← hBdef, hB]; have := Nat.two_pow_pos j; omega
  rw [hL', hL] at h
  generalize π.steps.length = L at h ⊢
  generalize 8 * (j + 7) = a at h ⊢
  rw [Nat.mul_pow, Nat.mul_pow, ← Nat.mul_assoc] at h
  exact Nat.le_of_mul_le_mul_right h (Nat.pow_pos hBpos)

/-- **Main**: `HQ k` is unsatisfiable, and for `k ≥ 7` every resolution refutation of it with `L`
clauses has `(8k)^(2^(k-3)) ≤ L (8k-1)^(2^(k-3))`. -/
theorem hq_main (k : Nat) :
    (∀ α : Nat → Bool, ∃ C ∈ HQ k, C.eval α = false) ∧
    (7 ≤ k → ∀ π : Refutation (HQ k),
      (8 * k) ^ 2 ^ (k - 3) ≤ π.steps.length * (8 * k - 1) ^ 2 ^ (k - 3)) :=
  ⟨hq_unsat k, hq_size k⟩

end Programme.«20261024-1110-proof-complexity».Hypercube

#print axioms Programme.«20261024-1110-proof-complexity».Hypercube.hq_main
#print axioms Programme.«20261024-1110-proof-complexity».Hypercube.hq_width
#print axioms Programme.«20261024-1110-proof-complexity».Hypercube.cut_ge
#print axioms Programme.«20261024-1110-proof-complexity».Hypercube.hq_unsat
#print axioms Programme.«20261024-1110-proof-complexity».Hypercube.hq_size
#print axioms Programme.«20261024-1110-proof-complexity».Hypercube.deg_le
#print axioms Programme.«20261024-1110-proof-complexity».Hypercube.Q_len
#print axioms Programme.«20261024-1110-proof-complexity».Hypercube.Q_ends
