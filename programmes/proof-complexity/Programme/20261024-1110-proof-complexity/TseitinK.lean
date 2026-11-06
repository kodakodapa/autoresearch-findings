import Programme.«20261024-1110-proof-complexity».GT
/-!
# Tseitin formulas on the complete graph `K_n`: width `≈ n²/4` and size `2^{Ω(n²)}` (core Lean 4)

Variables are the edges `(a, b)`, `a < b < n`. Vertex `0` has charge `1`, every other vertex
charge `0`. For each vertex `u` the formula `TK n` holds the `2^{n-2}` clauses over the `n-1`
edges at `u` that forbid the assignments of the wrong parity (`pc`). The total charge is odd, so
`TK n` is unsatisfiable (`tk_unsat`).

1. `tk_no_der`: with `1 ≤ t`, `2t + 1 < n` and `2(W+1) < n t`, there is no width-`W` resolution
   refutation (`Der`). The proof uses `Work.GT3.no_der_of_family`. Duplicator keeps a total
   assignment `α` whose only parity violation is at one vertex `v`, and `v` is *light*: fewer
   than `t` of its edges have been queried. When a query makes `v` heavy, Duplicator moves the
   violation to a light vertex `v'` along a path `v - x - v'` of unqueried edges, by flipping
   those two edges. A light `v'` exists because the heavy vertices number at most `2|S|/t`.
   The middle vertex `x` exists because `v` and `v'` each have at most `t` queried edges.
   A vertex whose clause has all its variables queried is heavy, so its parity is right.
2. `tk_width`: every `Refutation (TK n)` has a line with more than `W` literals.
3. `tk_size`: composed with the Ben-Sasson–Wigderson relation `Work.BSW.bsw_size`
   (`N = n(n-1)/2`, initial width `n-1`).
4. `tk_size_explicit`: for `n ≥ 41`, every refutation has at least `(10/9)^{⌊n²/10⌋}` lines.

Known mathematics: Tseitin lower bounds (Urquhart 1987; Ben-Sasson–Wigderson 2001). Since `TK n`
has `n·2^{n-2}` clauses, the bound is quasi-polynomial in the formula size, `L^{Ω(log L)}`.

## Prior art and what this file adds

Prior-art request R4 reports a Lean 4 Tseitin-on-expanders module with a size-width result in
cslib-community/complexitylib (PR #667), seen from search snippets only, not read at source level.
So the general Tseitin bound is not new as a formalisation. No Lean instantiation on `K_n` was
found. What this file adds: (i) the `K_n` instance with its own Delayer argument (a light/heavy
vertex game, without a separate expansion lemma); (ii) an explicit unconditional size bound
`(10/9)^{⌊n²/10⌋}` for `n ≥ 41`; (iii) the statements use the single `Refutation` type shared with
the Haken bound (K1, K28), the upper bounds (K9, K12, K16) and solver certificates (K17);
(iv) core Lean 4 only, no Mathlib or CSLib.
-/

set_option linter.unusedSectionVars false

namespace Programme.«20261024-1110-proof-complexity».TseitinK
open Programme.«20261024-1110-proof-complexity».BSW

abbrev E := Nat × Nat

/-- The edge `{a, b}` as an ordered pair. -/
def edge (a b : Nat) : E := if a < b then (a, b) else (b, a)

/-- The edges at `u` in `K_n`. -/
def inc (n u : Nat) : List E := ((List.range n).filter (fun x => x ≠ u)).map (edge u)

/-- Clauses over the list `L` forbidding exactly the assignments of parity `p`. -/
def pc : List E → Bool → CNF E
  | [], p => if p then [] else [[]]
  | e :: L, p => (pc L p).map (⟨e, true⟩ :: ·) ++ (pc L (!p)).map (⟨e, false⟩ :: ·)

/-- Charge: `1` at vertex `0`. -/
def chg (u : Nat) : Bool := u == 0

/-- **Tseitin formula of `K_n`**, charge `1` at vertex `0`. -/
def TK (n : Nat) : CNF E := (List.range n).flatMap fun u => pc (inc n u) (!chg u)

/-- The edges `(a, b)`, `a < b < n`. -/
def edges : Nat → List E
  | 0 => []
  | m + 1 => edges m ++ (List.range m).map (fun a => (a, m))

/-- Parity of `α` on `L`. -/
def par (α : E → Bool) : List E → Bool
  | [] => false
  | e :: L => xor (α e) (par α L)

/-- Flip `α` at `f`. -/
def fl (α : E → Bool) (f : E) : E → Bool := fun g => if g = f then !α g else α g

/-- Number of edges at `u` in the query list `S`. -/
def deg (n : Nat) (S : List E) (u : Nat) : Nat := (inc n u).countP fun g => decide (g ∈ S)

/-! ## Edges -/

theorem edge_comm (a b : Nat) (h : a ≠ b) : edge a b = edge b a := by
  unfold edge
  by_cases h1 : a < b
  · have : ¬ b < a := by omega
    simp [h1, this]
  · have : b < a := by omega
    simp [h1, this]

theorem edge_eq {u x a b : Nat} (hux : u ≠ x) (hab : a ≠ b) :
    edge u x = edge a b ↔ (u = a ∧ x = b) ∨ (u = b ∧ x = a) := by
  unfold edge
  by_cases h1 : u < x <;> by_cases h2 : a < b <;> simp [h1, h2] <;> omega

theorem mem_inc {n u : Nat} {g : E} : g ∈ inc n u ↔ ∃ x, x < n ∧ x ≠ u ∧ edge u x = g := by
  simp [inc, and_assoc]

theorem nodup_map_on {α β : Type} (f : α → β) (l : List α) (hl : l.Nodup)
    (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) : (l.map f).Nodup :=
  List.Pairwise.map f (fun a b ⟨ha, hb, hab⟩ e => hab (hinj a ha b hb e)) (List.Pairwise.and_mem.mp hl)

theorem edge_mem_inc {n u a b : Nat} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    edge a b ∈ inc n u ↔ u = a ∨ u = b := by
  rw [mem_inc]
  constructor
  · rintro ⟨x, _, hxu, h⟩
    rcases (edge_eq (Ne.symm hxu) hab).mp h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl h1
    · exact Or.inr h1
  · rintro (rfl | rfl)
    · exact ⟨b, hb, Ne.symm hab, rfl⟩
    · exact ⟨a, ha, hab, edge_comm _ _ (Ne.symm hab)⟩

theorem inc_nodup (n u : Nat) : (inc n u).Nodup := by
  unfold inc
  apply nodup_map_on
  · exact List.Pairwise.filter _ List.nodup_range
  · intro x hx y hy h
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hx hy
    rcases (edge_eq (Ne.symm hx.2) (Ne.symm hy.2)).mp h with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h.symm hy.2

theorem inc_vertex {n u : Nat} {g : E} (h : g ∈ inc n u) : u = g.1 ∨ u = g.2 := by
  obtain ⟨x, _, _, rfl⟩ := mem_inc.mp h
  unfold edge; by_cases h1 : u < x <;> simp [h1]

theorem length_filter_ne (n u : Nat) (h : u < n) :
    ((List.range n).filter (fun x => x ≠ u)).length = n - 1 := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases e : m = u
    · subst e
      have : ((List.range m).filter (fun x => x ≠ m)) = List.range m := by
        apply List.filter_eq_self.mpr; intro x hx; simp at hx; simp; omega
      rw [this]; simp
    · rw [ih (by omega)]; simp [e]; omega

theorem length_inc {n u : Nat} (h : u < n) : (inc n u).length = n - 1 := by
  rw [inc, List.length_map, length_filter_ne n u h]

theorem mem_edges {n : Nat} {g : E} : g ∈ edges n ↔ g.1 < g.2 ∧ g.2 < n := by
  induction n with
  | zero => simp [edges]
  | succ m ih =>
    simp only [edges, List.mem_append, ih, List.mem_map, List.mem_range]
    constructor
    · rintro (h | ⟨a, ha, rfl⟩)
      · omega
      · simp; omega
    · intro h
      by_cases e : g.2 = m
      · right; exact ⟨g.1, by omega, by rw [← e]⟩
      · left; omega

theorem edges_nodup : ∀ n, (edges n).Nodup
  | 0 => List.nodup_nil
  | m + 1 => by
    unfold edges
    rw [List.nodup_append]
    refine ⟨edges_nodup m, ?_, ?_⟩
    · apply nodup_map_on
      · exact List.nodup_range
      · intro x _ y _ h; simpa using h
    · intro a ha b hb e
      subst e
      have := (mem_edges.mp ha).2
      simp at hb; obtain ⟨_, _, rfl⟩ := hb; simp at this

theorem length_edges : ∀ n, 2 * (edges n).length + n = n * n
  | 0 => rfl
  | m + 1 => by
    simp only [edges, List.length_append, List.length_map, List.length_range]
    have := length_edges m
    have h2 : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by
      rw [Nat.succ_mul, Nat.mul_succ]; omega
    rw [h2]; omega

theorem edge_mem_edges {n a x : Nat} (ha : a < n) (hx : x < n) (h : x ≠ a) : edge a x ∈ edges n := by
  rw [mem_edges]; unfold edge; by_cases h1 : a < x <;> simp [h1] <;> omega

theorem inc_sub_edges {n u : Nat} (hu : u < n) {g : E} (h : g ∈ inc n u) : g ∈ edges n := by
  obtain ⟨x, hx, hxu, rfl⟩ := mem_inc.mp h
  exact edge_mem_edges hu hx hxu

/-! ## Parity clauses -/

theorem pc_false (α : E → Bool) : ∀ (L : List E) (p : Bool) (C : Clause E), C ∈ pc L p →
    C.eval α = false → par α L = p
  | [], p, C, h, _ => by cases p <;> simp_all [pc, par]
  | e :: L, p, C, h, hf => by
    simp only [pc, List.mem_append, List.mem_map] at h
    rcases h with ⟨D, hD, rfl⟩ | ⟨D, hD, rfl⟩
    · simp [Clause.eval, Lit.eval] at hf
      have := pc_false α L p D hD (by simpa [Clause.eval, Lit.eval] using hf.2)
      simp [par, hf.1, this]
    · simp [Clause.eval, Lit.eval] at hf
      have := pc_false α L (!p) D hD (by simpa [Clause.eval, Lit.eval] using hf.2)
      simp [par, hf.1, this]

theorem pc_vars : ∀ (L : List E) (p : Bool) (C : Clause E), C ∈ pc L p →
    (∀ l ∈ C, l.var ∈ L) ∧ (∀ e ∈ L, ∃ l ∈ C, l.var = e) ∧ C.length = L.length
  | [], p, C, h => by cases p <;> simp_all [pc]
  | e :: L, p, C, h => by
    simp only [pc, List.mem_append, List.mem_map] at h
    rcases h with ⟨D, hD, rfl⟩ | ⟨D, hD, rfl⟩ <;>
    · obtain ⟨h1, h2, h3⟩ := pc_vars L _ D hD
      refine ⟨?_, ?_, by simp [h3]⟩
      · intro l hl; simp at hl
        rcases hl with rfl | hl
        · simp
        · exact List.mem_cons_of_mem _ (h1 l hl)
      · intro g hg; simp at hg
        rcases hg with rfl | hg
        · exact ⟨_, List.mem_cons_self, rfl⟩
        · obtain ⟨l, hl, e⟩ := h2 g hg; exact ⟨l, List.mem_cons_of_mem _ hl, e⟩

theorem mem_TK {n : Nat} {C : Clause E} : C ∈ TK n ↔ ∃ u, u < n ∧ C ∈ pc (inc n u) (!chg u) := by
  simp [TK]

/-! ## Parity and flips -/

theorem par_flip (α : E → Bool) (f : E) : ∀ L : List E, L.Nodup →
    par (fl α f) L = xor (par α L) (decide (f ∈ L))
  | [], _ => by simp [par]
  | e :: L, h => by
    have hL := (List.nodup_cons.mp h)
    rw [par, par, par_flip α f L hL.2]
    by_cases hf : e = f
    · subst hf; simp [fl, hL.1]
    · have : f ≠ e := Ne.symm hf
      simp [fl, hf, this]

theorem par_const : ∀ L : List E, par (fun _ => false) L = false
  | [] => rfl
  | _ :: L => by simp [par, par_const L]

theorem par_flip_edge (α : E → Bool) {n a b u : Nat} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    par (fl α (edge a b)) (inc n u) = xor (par α (inc n u)) (decide (u = a ∨ u = b)) := by
  rw [par_flip α _ _ (inc_nodup n u)]
  congr 1
  exact decide_eq_decide.mpr (edge_mem_inc ha hb hab)

/-! ## Counting -/

theorem countP_le_add {α : Type} (l : List α) (p q r : α → Bool)
    (h : ∀ x ∈ l, r x = true → p x = true ∨ q x = true) :
    l.countP r ≤ l.countP p + l.countP q := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ha := h a List.mem_cons_self
    cases ep : p a <;> cases eq : q a <;> cases er : r a <;> simp_all <;> omega

theorem countP_mem_le_countP {α : Type} [DecidableEq α] (L M : List α) (hL : L.Nodup) :
    L.countP (fun g => decide (g ∈ M)) ≤ M.countP (fun g => decide (g ∈ L)) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have hL' := List.nodup_cons.mp hL
    rw [List.countP_cons]
    have h1 := ih hL'.2
    have h2 : M.countP (fun g => decide (g = a)) + M.countP (fun g => decide (g ∈ L))
        ≤ M.countP (fun g => decide (g ∈ a :: L)) := by
      apply countP_add_le
      · intro x _ hx; simp at hx; simp [hx]
      · intro x _ hx; simp at hx; simp [hx]
      · intro x _ hx hx'; simp at hx hx'; subst hx; exact hL'.1 hx'
    have h3 : (if decide (a ∈ M) = true then 1 else 0) ≤ M.countP (fun g => decide (g = a)) := by
      by_cases ha : a ∈ M
      · have : 0 < M.countP (fun g => decide (g = a)) := List.countP_pos_iff.mpr ⟨a, ha, by simp⟩
        simp only [ha, decide_true, if_true]; omega
      · simp only [ha, decide_false]; simp
    exact Nat.le_trans (Nat.add_le_add h1 h3) (by rw [Nat.add_comm]; exact h2)

theorem sum_map_le {α : Type} (l : List α) (f g : α → Nat) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have := h a List.mem_cons_self
    omega

theorem sum_map_const {α : Type} (l : List α) (c : Nat) : (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.succ_mul]; omega

/-- At most `2|S|/t` vertices have `t` or more queried edges; so if `2|S| < n t`, some vertex
is light. -/
theorem exists_light (n t : Nat) (S : List E) (h : 2 * S.length < n * t) :
    ∃ v, v < n ∧ deg n S v < t := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ v ∈ List.range n, t ≤ deg n S v := by
    intro v hv
    have := List.mem_range.mp hv
    apply Classical.byContradiction; intro h'; exact hno ⟨v, this, by omega⟩
  have h1 : (List.range n).countP (fun _ => true) * t ≤ ((List.range n).map (deg n S)).sum :=
    countP_mul_le_sum _ _ _ _ (fun v hv _ => hall v hv)
  rw [List.countP_true, List.length_range] at h1
  have h2 : ((List.range n).map (deg n S)).sum
      ≤ ((List.range n).map fun u => S.countP fun s => decide (s ∈ inc n u)).sum :=
    sum_map_le _ _ _ (fun u _ => countP_mem_le_countP _ _ (inc_nodup n u))
  have h3 := double_count (List.range n) S (fun u s => decide (s ∈ inc n u))
  have h4 : (S.map fun s => (List.range n).countP fun u => decide (s ∈ inc n u)).sum
      ≤ (S.map fun _ => 2).sum := by
    apply sum_map_le
    intro s _
    have := countP_le_add (List.range n) (fun u => decide (u = s.1)) (fun u => decide (u = s.2))
      (fun u => decide (s ∈ inc n u)) (by
        intro u _ hu; simp only [decide_eq_true_eq] at hu ⊢
        rcases inc_vertex hu with e | e <;> simp [e])
    have := countP_eq_le_one (List.range n) s.1 List.nodup_range
    have := countP_eq_le_one (List.range n) s.2 List.nodup_range
    omega
  rw [sum_map_const] at h4
  omega

theorem deg_cons_le (n : Nat) (e : E) (S : List E) (u : Nat) : deg n (e :: S) u ≤ deg n S u + 1 := by
  have := countP_le_add (inc n u) (fun g => decide (g = e)) (fun g => decide (g ∈ S))
    (fun g => decide (g ∈ e :: S)) (by intro g _ h; simp at h; simp [h])
  have := countP_eq_le_one (inc n u) e (inc_nodup n u)
  unfold deg; omega

theorem deg_mono (n : Nat) {S S' : List E} (h : ∀ g ∈ S', g ∈ S) (u : Nat) : deg n S' u ≤ deg n S u :=
  List.countP_mono_left (by intro g _ hg; simp at hg ⊢; exact h g hg)

theorem length_nbr (n v : Nat) (S : List E) :
    ((List.range n).filter (fun x => decide (x ≠ v ∧ edge v x ∈ S))).length = deg n S v := by
  rw [← List.countP_eq_length_filter, deg, inc, List.countP_map, List.countP_filter]
  apply List.countP_congr
  intro x _; simp [Function.comp, and_comm]

/-- A middle vertex for the path `v - x - v'` avoiding the queried edges. -/
theorem exists_mid (n t : Nat) (S : List E) (v v' : Nat) (hv : deg n S v ≤ t) (hv' : deg n S v' < t)
    (h : 2 * t + 1 < n) :
    ∃ x, x < n ∧ x ≠ v ∧ x ≠ v' ∧ edge v x ∉ S ∧ edge v' x ∉ S := by
  let B := [v, v'] ++ (List.range n).filter (fun x => decide (x ≠ v ∧ edge v x ∈ S))
    ++ (List.range n).filter (fun x => decide (x ≠ v' ∧ edge v' x ∈ S))
  have hB : B.length < n := by
    simp only [B, List.length_append, length_nbr]; simp; omega
  obtain ⟨x, hxn, hxB⟩ := Programme.«20261024-1110-proof-complexity».GT3.exists_fresh n B hB
  have hx : ∀ y, y ∈ B → x ≠ y := fun y hy e => hxB (e ▸ hy)
  refine ⟨x, hxn, hx v (by simp [B]), hx v' (by simp [B]), ?_, ?_⟩
  · intro hm
    apply hxB
    have hxv : x ≠ v := hx v (by simp [B])
    simp [B, hxn, hxv, hm]
  · intro hm
    apply hxB
    have hxv : x ≠ v' := hx v' (by simp [B])
    simp [B, hxn, hxv, hm]

/-! ## Duplicator's family -/

/-- `α` violates parity exactly at a light vertex `v`. -/
def Adm (n t : Nat) (S : List E) (α : E → Bool) : Prop :=
  ∃ v, v < n ∧ deg n S v < t ∧ ∀ u, u < n → (par α (inc n u) = chg u ↔ u ≠ v)

theorem flip_two (α : E → Bool) {n v x v' : Nat} (hv : v < n) (hx : x < n) (hv' : v' < n)
    (h1 : x ≠ v) (h2 : x ≠ v') (h3 : v' ≠ v)
    (hviol : ∀ u, u < n → (par α (inc n u) = chg u ↔ u ≠ v)) :
    ∀ u, u < n → (par (fl (fl α (edge v x)) (edge v' x)) (inc n u) = chg u ↔ u ≠ v') := by
  intro u hu
  rw [par_flip_edge _ hv' hx (Ne.symm h2), par_flip_edge _ hv hx (Ne.symm h1)]
  have := hviol u hu
  by_cases a1 : u = v
  · subst a1
    have : par α (inc n u) ≠ chg u := fun h => (this.mp h) rfl
    simp [h3.symm, Ne.symm h1]
    revert this; cases par α (inc n u) <;> cases chg u <;> simp
  by_cases a2 : u = v'
  · subst a2
    have : par α (inc n u) = chg u := this.mpr a1
    simp [a1, this, Ne.symm h2]
  by_cases a3 : u = x
  · subst a3
    have : par α (inc n u) = chg u := this.mpr a1
    simp [a1, a2, this]
  · have : par α (inc n u) = chg u := this.mpr a1
    simp [a1, a2, a3, this]

/-- **Width lower bound for Tseitin on `K_n`.** If `1 ≤ t`, `2t+1 < n` and `2(W+1) < n t`,
then `TK n` has no width-`W` resolution refutation (any variable list `X`). -/
theorem tk_no_der (n t W : Nat) (ht : 1 ≤ t) (htn : 2 * t + 1 < n) (hW : 2 * (W + 1) < n * t)
    (X : List E) : ¬ Der (· ∈ TK n) X W [] := by
  apply Programme.«20261024-1110-proof-complexity».GT3.no_der_of_family (Adm n t)
  · intro S S' α ⟨v, hvn, hvl, hviol⟩ hs
    exact ⟨v, hvn, Nat.lt_of_le_of_lt (deg_mono n hs v) hvl, hviol⟩
  · intro S α ⟨v, hvn, hvl, hviol⟩ hlen e
    by_cases hl : deg n (e :: S) v < t
    · exact ⟨α, ⟨v, hvn, hl, hviol⟩, fun _ _ => rfl⟩
    · have hvt : deg n (e :: S) v ≤ t := by have := deg_cons_le n e S v; omega
      obtain ⟨v', hv'n, hv'l⟩ := exists_light n t (e :: S) (by simp; omega)
      have hne : v' ≠ v := by rintro rfl; omega
      obtain ⟨x, hxn, hxv, hxv', h1, h2⟩ := exists_mid n t (e :: S) v v' hvt hv'l htn
      refine ⟨fl (fl α (edge v x)) (edge v' x),
        ⟨v', hv'n, hv'l, flip_two α hvn hxn hv'n hxv hxv' hne hviol⟩, ?_⟩
      intro g hg
      have e1 : g ≠ edge v x := fun h => h1 (h ▸ List.mem_cons_of_mem _ hg)
      have e2 : g ≠ edge v' x := fun h => h2 (h ▸ List.mem_cons_of_mem _ hg)
      simp [fl, e1, e2]
  · intro S α C ⟨v, hvn, hvl, hviol⟩ hC hS
    obtain ⟨u, hu, hCu⟩ := mem_TK.mp hC
    obtain ⟨_, h2, _⟩ := pc_vars _ _ C hCu
    have hdeg : deg n S u = n - 1 := by
      unfold deg
      rw [List.countP_eq_length.mpr ?_, length_inc hu]
      intro g hg
      obtain ⟨l, hl, rfl⟩ := h2 g hg
      simpa using hS l hl
    have huv : u ≠ v := by rintro rfl; omega
    have hp := (hviol u hu).mpr huv
    cases hev : C.eval α
    · have := pc_false α _ _ C hCu hev
      rw [hp] at this; cases chg u <;> simp at this
    · rfl
  · refine ⟨fun _ => false, 0, by omega, by simp [deg]; omega, ?_⟩
    intro u _
    rw [par_const]; cases u <;> simp [chg]

/-! ## Width and size for `Refutation`s -/

theorem wd_le_len {X : List E} (hX : X.Nodup) : ∀ C : Clause E, wd X C ≤ C.length
  | [] => by simp [wd]
  | l :: D => by have := wd_cons hX l D; have := wd_le_len hX D; simp; omega

/-- Every clause of `TK n` lies over `edges n` and has `n - 1` literals. -/
theorem tk_ok (n : Nat) : ∀ C ∈ TK n, OK (edges n) (n - 1) C := by
  intro C hC
  obtain ⟨u, hu, hCu⟩ := mem_TK.mp hC
  obtain ⟨h1, _, h3⟩ := pc_vars _ _ C hCu
  refine ⟨fun l hl => inc_sub_edges hu (h1 l hl), ?_⟩
  have := wd_le_len (edges_nodup n) C
  rw [h3, length_inc hu] at this; exact this

/-- **Width of Tseitin on `K_n`:** under `1 ≤ t`, `2t+1 < n`, `2(W+1) < n t`, every resolution
refutation (weakening allowed) of `TK n` has a line with more than `W` distinct literals. -/
theorem tk_width (n t W : Nat) (ht : 1 ≤ t) (htn : 2 * t + 1 < n) (hW : 2 * (W + 1) < n * t)
    (π : Refutation (TK n)) : ∃ C ∈ π.steps, W < wd (edges n) C := by
  apply Classical.byContradiction
  intro h
  have hle : ∀ C ∈ π.steps, wd (edges n) C ≤ W := by
    intro C hC
    apply Classical.byContradiction; intro h'; exact h ⟨C, hC, by omega⟩
  exact tk_no_der n t W ht htn hW _
    (der_of_refutation (fun C hC => (tk_ok n C hC).1) π hle)

/-- **Size of Tseitin on `K_n` via Ben-Sasson–Wigderson.** With `N = |edges n| = n(n-1)/2`:
if `2(n + 2k) < n ⌊(n-3)/2⌋`, every resolution refutation `π` of `TK n` has
`(2N)^k ≤ |π| (2N-k)^k`. -/
theorem tk_size (n k : Nat) (h : 2 * (n + 2 * k) < n * ((n - 3) / 2)) (π : Refutation (TK n)) :
    (2 * (edges n).length) ^ k ≤ π.steps.length * (2 * (edges n).length - k) ^ k := by
  have ht : 1 ≤ (n - 3) / 2 := by
    apply Classical.byContradiction; intro h'
    have : (n - 3) / 2 = 0 := by omega
    rw [this] at h; omega
  apply bsw_size_sq (edges_nodup n) (tk_ok n) k _ π
  exact tk_no_der n ((n - 3) / 2) (n - 1 + 2 * k) ht (by omega) (by omega) _

/-- **Explicit form:** for `n ≥ 41`, every resolution refutation of the Tseitin formula on `K_n`
has at least `(10/9)^{⌊n²/10⌋}` lines. -/
theorem tk_size_explicit (n : Nat) (hn : 41 ≤ n) (π : Refutation (TK n)) :
    10 ^ (n * n / 10) ≤ 9 ^ (n * n / 10) * π.steps.length := by
  have hq : 10 * (n * n / 10) ≤ n * n := Nat.mul_div_le (n * n) 10
  have hq' : n * n < 10 * (n * n / 10) + 10 := by
    have := Nat.lt_mul_div_succ (n * n) (show 0 < 10 by decide); rw [Nat.mul_succ] at this; omega
  have h41 : 41 * n ≤ n * n := Nat.mul_le_mul_right n hn
  have hnt : n * n ≤ 2 * (n * ((n - 3) / 2)) + 4 * n := by
    have : n ≤ 2 * ((n - 3) / 2) + 4 := by omega
    have := Nat.mul_le_mul_left n this
    rw [Nat.mul_add, Nat.mul_left_comm] at this; omega
  have hsz := tk_size n (n * n / 10) (by omega) π
  have hE := length_edges n
  generalize n * n / 10 = k at *
  generalize (edges n).length = N at *
  have hA : 10 * (2 * N - k) ≤ 9 * (2 * N) := by omega
  have hpos : 0 < (2 * N - k) ^ k := Nat.pow_pos (by omega)
  apply Nat.le_of_mul_le_mul_right _ hpos
  calc 10 ^ k * (2 * N - k) ^ k = (10 * (2 * N - k)) ^ k := (Nat.mul_pow _ _ _).symm
    _ ≤ (9 * (2 * N)) ^ k := Nat.pow_le_pow_left hA k
    _ = 9 ^ k * (2 * N) ^ k := Nat.mul_pow _ _ _
    _ ≤ 9 ^ k * (π.steps.length * (2 * N - k) ^ k) := Nat.mul_le_mul_left _ hsz
    _ = 9 ^ k * π.steps.length * (2 * N - k) ^ k := (Nat.mul_assoc _ _ _).symm

/-! ## Unsatisfiability (handshake parity) -/

theorem pc_complete (α : E → Bool) : ∀ (L : List E) (p : Bool), par α L = p →
    ∃ C ∈ pc L p, C.eval α = false
  | [], p, h => by subst h; exact ⟨[], by simp [pc, par], rfl⟩
  | e :: L, p, h => by
    cases he : α e
    · have hL : par α L = p := by simpa [par, he] using h
      obtain ⟨D, hD, hDf⟩ := pc_complete α L p hL
      refine ⟨(⟨e, true⟩ : Lit E) :: D, by rw [pc]; exact List.mem_append_left _ (List.mem_map.mpr ⟨D, hD, rfl⟩), ?_⟩
      simp only [Clause.eval, List.any_cons, Lit.eval, he]; simpa [Clause.eval] using hDf
    · have hL : par α L = !p := by cases p <;> simp_all [par]
      obtain ⟨D, hD, hDf⟩ := pc_complete α L (!p) hL
      refine ⟨(⟨e, false⟩ : Lit E) :: D, by rw [pc]; exact List.mem_append_right _ (List.mem_map.mpr ⟨D, hD, rfl⟩), ?_⟩
      simp only [Clause.eval, List.any_cons, Lit.eval, he]; simpa [Clause.eval] using hDf

/-- `xs f m = f 0 xor … xor f (m-1)`. -/
def xs (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | m + 1 => xor (xs f m) (f m)

theorem xs_congr {f g : Nat → Bool} : ∀ m, (∀ u < m, f u = g u) → xs f m = xs g m
  | 0, _ => rfl
  | m + 1, h => by
    simp only [xs]; rw [xs_congr m (fun u hu => h u (by omega)), h m (by omega)]

theorem xs_xor (f g : Nat → Bool) : ∀ m, xs (fun u => xor (f u) (g u)) m = xor (xs f m) (xs g m)
  | 0 => rfl
  | m + 1 => by
    simp only [xs, xs_xor f g m]
    cases xs f m <;> cases xs g m <;> cases f m <;> cases g m <;> rfl

theorem par_append (α : E → Bool) : ∀ L M : List E, par α (L ++ M) = xor (par α L) (par α M)
  | [], M => by simp [par]
  | e :: L, M => by
    simp only [List.cons_append, par, par_append α L M]
    cases α e <;> cases par α L <;> cases par α M <;> rfl

theorem par_map_range (α : E → Bool) (h : Nat → E) : ∀ m, par α ((List.range m).map h) = xs (fun u => α (h u)) m
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.map_append, par_append, par_map_range α h m]
    simp [par, xs]

theorem inc_succ {m u : Nat} (hu : u < m) : inc (m + 1) u = inc m u ++ [edge u m] := by
  unfold inc
  rw [List.range_succ, List.filter_append, List.map_append]
  have : m ≠ u := by omega
  simp [this]

theorem inc_top (m : Nat) : inc (m + 1) m = (List.range m).map (edge m) := by
  have : (List.range m).filter (fun x => x ≠ m) = List.range m := by
    apply List.filter_eq_self.mpr; intro x hx; simp at hx; simp; omega
  unfold inc
  rw [List.range_succ, List.filter_append, this]
  simp

/-- **Handshake parity:** the parities at all vertices of `K_n` xor to `false`. -/
theorem handshake (α : E → Bool) : ∀ n, xs (fun u => par α (inc n u)) n = false
  | 0 => rfl
  | m + 1 => by
    simp only [xs]
    rw [xs_congr m (g := fun u => xor (par α (inc m u)) (α (edge u m)))
      (fun u hu => by simp only [inc_succ hu, par_append, par, Bool.xor_false]),
      xs_xor, handshake α m, inc_top, par_map_range,
      xs_congr m (f := fun u => α (edge m u)) (g := fun u => α (edge u m))
        (fun u hu => by rw [edge_comm m u (by omega)])]
    cases xs (fun u => α (edge u m)) m <;> rfl

theorem xs_chg : ∀ m, xs chg (m + 1) = true
  | 0 => rfl
  | m + 1 => by
    have := xs_chg m
    simp only [xs] at this ⊢; rw [this]; simp [chg]

/-- **`TK n` is unsatisfiable** for every `n ≥ 1`: every assignment falsifies a clause. -/
theorem tk_unsat (n : Nat) (hn : 1 ≤ n) (α : E → Bool) : ∃ C ∈ TK n, C.eval α = false := by
  have : ∃ u, u < n ∧ par α (inc n u) ≠ chg u := by
    apply Classical.byContradiction; intro h
    have hc := xs_congr n (f := fun u => par α (inc n u)) (g := chg) (fun u hu => by
      apply Classical.byContradiction; intro h'; exact h ⟨u, hu, h'⟩)
    rw [handshake] at hc
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [xs_chg] at hc; exact Bool.false_ne_true hc
  obtain ⟨u, hu, hne⟩ := this
  have hp : par α (inc n u) = !chg u := by revert hne; cases par α (inc n u) <;> cases chg u <;> simp
  obtain ⟨C, hC, hCf⟩ := pc_complete α _ _ hp
  exact ⟨C, mem_TK.mpr ⟨u, hu, hC⟩, hCf⟩

/-- **Headline.** The Tseitin formula on `K_n` (charge at vertex `0`) is unsatisfiable for every
`n ≥ 1`, and for `n ≥ 41` every resolution refutation of it has at least `(10/9)^{⌊n²/10⌋}` lines. -/
theorem tk_main :
    (∀ n, 1 ≤ n → ∀ α : E → Bool, ∃ C ∈ TK n, C.eval α = false) ∧
    (∀ n, 41 ≤ n → ∀ π : Refutation (TK n), 10 ^ (n * n / 10) ≤ 9 ^ (n * n / 10) * π.steps.length) :=
  ⟨tk_unsat, tk_size_explicit⟩

end Programme.«20261024-1110-proof-complexity».TseitinK

#print axioms Programme.«20261024-1110-proof-complexity».TseitinK.tk_no_der
#print axioms Programme.«20261024-1110-proof-complexity».TseitinK.tk_width
#print axioms Programme.«20261024-1110-proof-complexity».TseitinK.tk_size
#print axioms Programme.«20261024-1110-proof-complexity».TseitinK.tk_size_explicit
#print axioms Programme.«20261024-1110-proof-complexity».TseitinK.tk_unsat
#print axioms Programme.«20261024-1110-proof-complexity».TseitinK.tk_main
