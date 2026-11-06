/-!
# Approximators for monotone real formulas (deterministic layer)

The approximation method for monotone real formulas against clique-vs-colouring test graphs
(C1 step 2, plan in P77). An approximator is a base value `v₀` together with a list of entries
`(S, v)`, `S` a list of vertices. On a graph `G` it evaluates to the maximum of `v₀` and of the
values `v` of the entries whose set `S` is a clique of `G`.

This file proves the gate-by-gate facts that do not involve counting:
* `amap_eval`: a monotone unary gate applied to values is exact;
* `comb_le`: the binary combination `{S ∪ T : φ(v,w)}` never overshoots, on every graph;
* `comb_ge`: it is exact on graphs whose clique tests are union-closed on the entries,
  e.g. the positive test graphs (`posG`, a clique on `K`) when every entry set is empty or has
  no singleton part (`ns`; `comb_ns`, `pos_union`);
* `trim_le` / `trim_ge`: deleting long sets only lowers values, and is exact when no long set
  is a clique;
* `drop_eval`: deleting entries with value `≤ v₀` is exact;
* `eval_le_of_cover`: the domination principle used for plucking.
The negative test graphs are colouring graphs `negG c` (edges between differently coloured
vertices); a set is a clique of `negG c` iff it is rainbow (`clq_negG`).
-/

namespace Programme.«20261024-1633-proof-complexity».RealApprox

/-- `S` is a clique of `G`: distinct elements of `S` are adjacent. -/
def clq (G : Nat → Nat → Bool) (S : List Nat) : Prop := ∀ i ∈ S, ∀ j ∈ S, i ≠ j → G i j = true

instance (G : Nat → Nat → Bool) (S : List Nat) : Decidable (clq G S) := by
  unfold clq; infer_instance

theorem clq_nil (G : Nat → Nat → Bool) : clq G [] := by intro i h; simp at h

theorem clq_sub {G : Nat → Nat → Bool} {S T : List Nat} (h : ∀ i ∈ S, i ∈ T) (hT : clq G T) :
    clq G S := fun i hi j hj hij => hT i (h i hi) j (h j hj) hij

theorem clq_left {G : Nat → Nat → Bool} {S T : List Nat} (h : clq G (S ++ T)) : clq G S :=
  clq_sub (fun i hi => List.mem_append.2 (Or.inl hi)) h

theorem clq_right {G : Nat → Nat → Bool} {S T : List Nat} (h : clq G (S ++ T)) : clq G T :=
  clq_sub (fun i hi => List.mem_append.2 (Or.inr hi)) h

/-- An approximator: base value and entries `(set, value)`. -/
structure Approx where
  base : Int
  ents : List (List Nat × Int)

/-- Maximum of `v₀` and the values of the clique entries. -/
def evalL (G : Nat → Nat → Bool) (v₀ : Int) : List (List Nat × Int) → Int
  | [] => v₀
  | e :: A => if clq G e.1 then max e.2 (evalL G v₀ A) else evalL G v₀ A

def eval (a : Approx) (G : Nat → Nat → Bool) : Int := evalL G a.base a.ents

theorem evalL_base (G : Nat → Nat → Bool) (v₀ : Int) :
    ∀ A, v₀ ≤ evalL G v₀ A
  | [] => Int.le_refl _
  | e :: A => by
    have := evalL_base G v₀ A
    unfold evalL; split <;> omega

theorem evalL_ent (G : Nat → Nat → Bool) (v₀ : Int) :
    ∀ A, ∀ e ∈ A, clq G e.1 → e.2 ≤ evalL G v₀ A
  | [], e, h, _ => by simp at h
  | e' :: A, e, h, hc => by
    have ih := evalL_ent G v₀ A
    unfold evalL
    rcases List.mem_cons.1 h with h | h
    · subst h; simp only [hc, if_true]; omega
    · have := ih e h hc; split <;> omega

theorem evalL_le (G : Nat → Nat → Bool) (v₀ c : Int) (h0 : v₀ ≤ c) :
    ∀ A, (∀ e ∈ A, clq G e.1 → e.2 ≤ c) → evalL G v₀ A ≤ c
  | [], _ => h0
  | e :: A, h => by
    have ih := evalL_le G v₀ c h0 A (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    unfold evalL; split
    · have := h e (List.mem_cons_self ..) (by assumption); omega
    · exact ih

theorem evalL_attain (G : Nat → Nat → Bool) (v₀ : Int) :
    ∀ A, evalL G v₀ A = v₀ ∨ ∃ e ∈ A, clq G e.1 ∧ evalL G v₀ A = e.2
  | [] => Or.inl rfl
  | e :: A => by
    unfold evalL
    rcases evalL_attain G v₀ A with h | ⟨e', he', hc, h⟩
    · split
      · by_cases hle : e.2 ≤ v₀
        · left; rw [h]; omega
        · right; refine ⟨e, List.mem_cons_self .., by assumption, ?_⟩; rw [h]; omega
      · left; exact h
    · right; split
      · by_cases hle : e.2 ≤ evalL G v₀ A
        · exact ⟨e', List.mem_cons_of_mem _ he', hc, by omega⟩
        · exact ⟨e, List.mem_cons_self .., by assumption, by omega⟩
      · exact ⟨e', List.mem_cons_of_mem _ he', hc, h⟩

/-- All entries including the base, as the entry `([], v₀)`. -/
def ent (a : Approx) : List (List Nat × Int) := ([], a.base) :: a.ents

theorem eval_ent {a : Approx} {G : Nat → Nat → Bool} {e : List Nat × Int} (h : e ∈ ent a)
    (hc : clq G e.1) : e.2 ≤ eval a G := by
  rcases List.mem_cons.1 h with h | h
  · subst h; exact evalL_base G _ _
  · exact evalL_ent G _ _ e h hc

theorem eval_attain (a : Approx) (G : Nat → Nat → Bool) :
    ∃ e ∈ ent a, clq G e.1 ∧ eval a G = e.2 := by
  rcases evalL_attain G a.base a.ents with h | ⟨e, he, hc, h⟩
  · exact ⟨([], a.base), List.mem_cons_self .., clq_nil G, h⟩
  · exact ⟨e, List.mem_cons_of_mem _ he, hc, h⟩

/-- Domination: if every clique entry of `a` (and its base) is below `c`, so is `eval a`. -/
theorem eval_le_of_cover {a : Approx} {G : Nat → Nat → Bool} {c : Int}
    (h : ∀ e ∈ ent a, clq G e.1 → e.2 ≤ c) : eval a G ≤ c :=
  evalL_le G _ _ (h _ (List.mem_cons_self ..) (clq_nil G)) _
    (fun e he => h e (List.mem_cons_of_mem _ he))

/-! ## Gates -/

/-- Constant `k`. -/
def constA (k : Int) : Approx := ⟨k, []⟩

theorem const_eval (k : Int) (G : Nat → Nat → Bool) : eval (constA k) G = k := rfl

/-- Input `x_{uv}`. -/
def inpA (u v : Nat) : Approx := ⟨0, [([u, v], 1)]⟩

theorem inp_eval (u v : Nat) (G : Nat → Nat → Bool) (huv : u ≠ v) (hs : G u v = G v u) :
    eval (inpA u v) G = if G u v then 1 else 0 := by
  have hc : clq G [u, v] ↔ G u v = true := by
    constructor
    · intro h; exact h u (by simp) v (by simp) huv
    · intro h i hi j hj hij
      simp at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact absurd rfl hij
      · exact h
      · rw [← hs]; exact h
      · exact absurd rfl hij
  show (if clq G [u, v] then max 1 (0 : Int) else 0) = _
  by_cases h : G u v = true
  · rw [if_pos (hc.2 h), if_pos h]; rfl
  · have : ¬ clq G [u, v] := fun c => h (hc.1 c)
    rw [if_neg this, if_neg h]

/-- Unary gate `g` applied to every value. -/
def amap (g : Int → Int) (a : Approx) : Approx := ⟨g a.base, a.ents.map fun e => (e.1, g e.2)⟩

theorem amap_eval (g : Int → Int) (hg : ∀ x y, x ≤ y → g x ≤ g y) (a : Approx)
    (G : Nat → Nat → Bool) : eval (amap g a) G = g (eval a G) := by
  apply Int.le_antisymm
  · apply eval_le_of_cover
    intro e he hc
    rcases List.mem_cons.1 he with h | h
    · subst h; exact hg _ _ (evalL_base G _ _)
    · obtain ⟨e', he', rfl⟩ := List.mem_map.1 h
      exact hg _ _ (eval_ent (List.mem_cons_of_mem _ he') hc)
  · obtain ⟨e, he, hc, h⟩ := eval_attain a G
    rw [h]
    rcases List.mem_cons.1 he with h' | h'
    · subst h'; exact evalL_base G _ _
    · exact evalL_ent G _ _ (e.1, g e.2) (List.mem_map.2 ⟨e, h', rfl⟩) hc

/-- Binary gate `φ`: entries `(S ++ T, φ v w)` over all pairs of entries (bases included). -/
def comb (φ : Int → Int → Int) (a b : Approx) : Approx :=
  ⟨φ a.base b.base, (ent a).flatMap fun e => (ent b).map fun e' => (e.1 ++ e'.1, φ e.2 e'.2)⟩

theorem mem_comb {φ : Int → Int → Int} {a b : Approx} {x : List Nat × Int}
    (h : x ∈ (comb φ a b).ents) :
    ∃ e ∈ ent a, ∃ e' ∈ ent b, x = (e.1 ++ e'.1, φ e.2 e'.2) := by
  obtain ⟨e, he, h⟩ := List.mem_flatMap.1 h
  obtain ⟨e', he', rfl⟩ := List.mem_map.1 h
  exact ⟨e, he, e', he', rfl⟩

/-- The combination never overshoots. -/
theorem comb_le (φ : Int → Int → Int) (hφ : ∀ x x' y y', x ≤ x' → y ≤ y' → φ x y ≤ φ x' y')
    (a b : Approx) (G : Nat → Nat → Bool) :
    eval (comb φ a b) G ≤ φ (eval a G) (eval b G) := by
  apply eval_le_of_cover
  intro x hx hc
  rcases List.mem_cons.1 hx with h | h
  · subst h; exact hφ _ _ _ _ (evalL_base G _ _) (evalL_base G _ _)
  · obtain ⟨e, he, e', he', rfl⟩ := mem_comb h
    exact hφ _ _ _ _ (eval_ent he (clq_left hc)) (eval_ent he' (clq_right hc))

/-- The combination is exact when the clique tests are union-closed on the entries. -/
theorem comb_ge (φ : Int → Int → Int) (a b : Approx) (G : Nat → Nat → Bool)
    (hU : ∀ e ∈ ent a, ∀ e' ∈ ent b, clq G e.1 → clq G e'.1 → clq G (e.1 ++ e'.1)) :
    φ (eval a G) (eval b G) ≤ eval (comb φ a b) G := by
  obtain ⟨e, he, hc, h⟩ := eval_attain a G
  obtain ⟨e', he', hc', h'⟩ := eval_attain b G
  rw [h, h']
  have hm : (e.1 ++ e'.1, φ e.2 e'.2) ∈ (comb φ a b).ents :=
    List.mem_flatMap.2 ⟨e, he, List.mem_map.2 ⟨e', he', rfl⟩⟩
  exact evalL_ent G _ _ _ hm (hU e he e' he' hc hc')

/-- Delete the entries with sets longer than `ℓ`. -/
def trim (ℓ : Nat) (a : Approx) : Approx := ⟨a.base, a.ents.filter fun e => e.1.length ≤ ℓ⟩

theorem trim_le (ℓ : Nat) (a : Approx) (G : Nat → Nat → Bool) : eval (trim ℓ a) G ≤ eval a G := by
  apply eval_le_of_cover
  intro e he hc
  rcases List.mem_cons.1 he with h | h
  · subst h; exact evalL_base G _ _
  · exact eval_ent (List.mem_cons_of_mem _ (List.mem_filter.1 h).1) hc

theorem trim_ge (ℓ : Nat) (a : Approx) (G : Nat → Nat → Bool)
    (h : ∀ e ∈ a.ents, clq G e.1 → e.1.length ≤ ℓ) : eval a G ≤ eval (trim ℓ a) G := by
  apply eval_le_of_cover
  intro e he hc
  rcases List.mem_cons.1 he with h' | h'
  · subst h'; exact evalL_base G _ _
  · exact evalL_ent G _ _ e (List.mem_filter.2 ⟨h', by simpa using h e h' hc⟩) hc

/-- Delete the entries whose value does not exceed the base. -/
def drop (a : Approx) : Approx := ⟨a.base, a.ents.filter fun e => a.base < e.2⟩

theorem drop_eval (a : Approx) (G : Nat → Nat → Bool) : eval (drop a) G = eval a G := by
  apply Int.le_antisymm
  · apply eval_le_of_cover
    intro e he hc
    rcases List.mem_cons.1 he with h | h
    · subst h; exact evalL_base G _ _
    · exact eval_ent (List.mem_cons_of_mem _ (List.mem_filter.1 h).1) hc
  · apply eval_le_of_cover
    intro e he hc
    rcases List.mem_cons.1 he with h | h
    · subst h; exact evalL_base G _ _
    · by_cases hv : a.base < e.2
      · exact evalL_ent G _ _ e (List.mem_filter.2 ⟨h, by simpa using hv⟩) hc
      · have := evalL_base G a.base (drop a).ents
        show e.2 ≤ evalL G a.base _
        omega

/-! ## Test graphs -/

/-- Positive test graph: a clique on the vertex list `K`. -/
def posG (K : List Nat) (i j : Nat) : Bool := decide (i ∈ K) && decide (j ∈ K)

/-- Negative test graph of a colouring `c`: edges between differently coloured vertices. -/
def negG (c : Nat → Nat) (i j : Nat) : Bool := decide (c i ≠ c j)

/-- `S` has no singleton part: every element has a different element beside it. -/
def ns (S : List Nat) : Prop := ∀ i ∈ S, ∃ j ∈ S, j ≠ i

theorem ns_nil : ns [] := by intro i h; simp at h

theorem ns_pair {u v : Nat} (h : u ≠ v) : ns [u, v] := by
  intro i hi; simp at hi
  rcases hi with rfl | rfl
  · exact ⟨v, by simp, Ne.symm h⟩
  · exact ⟨u, by simp, h⟩

theorem ns_append {S T : List Nat} (hS : ns S) (hT : ns T) : ns (S ++ T) := by
  intro i hi
  rcases List.mem_append.1 hi with h | h
  · obtain ⟨j, hj, hji⟩ := hS i h; exact ⟨j, List.mem_append.2 (Or.inl hj), hji⟩
  · obtain ⟨j, hj, hji⟩ := hT i h; exact ⟨j, List.mem_append.2 (Or.inr hj), hji⟩

/-- On a set without singleton part, a clique of `posG K` is exactly a subset of `K`. -/
theorem clq_posG {K S : List Nat} (h : ns S) : clq (posG K) S ↔ ∀ i ∈ S, i ∈ K := by
  constructor
  · intro hc i hi
    obtain ⟨j, hj, hji⟩ := h i hi
    have := hc i hi j hj (fun e => hji e.symm)
    simp [posG] at this; exact this.1
  · intro hs i hi j hj _
    simp [posG, hs i hi, hs j hj]

/-- A clique of the colouring graph is a rainbow set. -/
theorem clq_negG {c : Nat → Nat} {S : List Nat} :
    clq (negG c) S ↔ ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c i ≠ c j := by
  unfold clq negG; simp

/-- Union-closure on positive test graphs for entries without singleton parts. -/
theorem pos_union (K : List Nat) (a b : Approx) (ha : ∀ e ∈ ent a, ns e.1)
    (hb : ∀ e ∈ ent b, ns e.1) :
    ∀ e ∈ ent a, ∀ e' ∈ ent b, clq (posG K) e.1 → clq (posG K) e'.1 →
      clq (posG K) (e.1 ++ e'.1) := by
  intro e he e' he' hc hc'
  rw [clq_posG (ha e he)] at hc
  rw [clq_posG (hb e' he')] at hc'
  rw [clq_posG (ns_append (ha e he) (hb e' he'))]
  intro i hi
  rcases List.mem_append.1 hi with h | h
  · exact hc i h
  · exact hc' i h

/-- So binary gates are exact on positive test graphs. -/
theorem comb_pos (φ : Int → Int → Int) (hφ : ∀ x x' y y', x ≤ x' → y ≤ y' → φ x y ≤ φ x' y')
    (K : List Nat) (a b : Approx) (ha : ∀ e ∈ ent a, ns e.1) (hb : ∀ e ∈ ent b, ns e.1) :
    eval (comb φ a b) (posG K) = φ (eval a (posG K)) (eval b (posG K)) :=
  Int.le_antisymm (comb_le φ hφ a b _) (comb_ge φ a b _ (pos_union K a b ha hb))

/-- The combination keeps entries free of singleton parts. -/
theorem comb_ns (φ : Int → Int → Int) (a b : Approx) (ha : ∀ e ∈ ent a, ns e.1)
    (hb : ∀ e ∈ ent b, ns e.1) : ∀ e ∈ ent (comb φ a b), ns e.1 := by
  intro x hx
  rcases List.mem_cons.1 hx with h | h
  · subst h; exact ns_nil
  · obtain ⟨e, he, e', he', rfl⟩ := mem_comb h
    exact ns_append (ha e he) (hb e' he')

/-- Summary: for monotone `g`, `φ`, unary gates are exact; binary gates never overshoot and are
exact on positive test graphs (entries without singleton parts); trimming only lowers values. -/
theorem gate_facts (g : Int → Int) (hg : ∀ x y, x ≤ y → g x ≤ g y)
    (φ : Int → Int → Int) (hφ : ∀ x x' y y', x ≤ x' → y ≤ y' → φ x y ≤ φ x' y')
    (a b : Approx) (ha : ∀ e ∈ ent a, ns e.1) (hb : ∀ e ∈ ent b, ns e.1) (ℓ : Nat) :
    (∀ G, eval (amap g a) G = g (eval a G)) ∧
    (∀ G, eval (comb φ a b) G ≤ φ (eval a G) (eval b G)) ∧
    (∀ K, eval (comb φ a b) (posG K) = φ (eval a (posG K)) (eval b (posG K))) ∧
    (∀ G, eval (trim ℓ a) G ≤ eval a G) :=
  ⟨amap_eval g hg a, comb_le φ hφ a b, fun K => comb_pos φ hφ K a b ha hb, trim_le ℓ a⟩

end Programme.«20261024-1633-proof-complexity».RealApprox
