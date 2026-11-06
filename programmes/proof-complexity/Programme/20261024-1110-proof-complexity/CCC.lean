import Programme.«20261024-1110-proof-complexity».Hypercube

/-!
# Tseitin formulas on cube-connected cycles: a bounded-degree family (core Lean 4)

`CC k` is the cube-connected-cycles graph of dimension `k`: vertex `x * k + i` (`x < 2^k`,
`i < k`) is position `i` on the cycle of cube vertex `x`; cycle edges join `v` to `nxt k v` (the
next position on the same cycle), and each hypercube edge `x ~ y` of dimension `i` (from `QL k`,
the labelled version of `Work.Hypercube.Q k`) joins `x * k + i` to `y * k + i`. Every vertex has
degree `≤ 3`, so the Tseitin formula `HC k` is a 3-CNF with at most `4 k 2^k` clauses.

Expansion (`cut_main`): for every vertex set `S` with `F` the fully occupied cycles and `p` the
number of partly occupied cycles, the cycles contribute `≥ p` boundary edges and the cube edges
`≥ cut_Q(F) - k p`; with the hypercube bound `cut_ge` this gives `(k+1) |∂S| ≥ 2^k/3` for
`|S|` in the middle third. With K20/K21 (`Work.Tseitin.tseitin_size`) and `w0 = 3`:
for `k ≥ 11` every refutation with `L` clauses has `(3k2^k)^B ≤ L (3k2^k - B)^B`,
`B = ⌊2^k/(8(k+1))⌋`, i.e. `L ≥ exp(Ω(2^k/k^3))`, `2^{Ω(|F|/log^4 |F|)}` in formula size.

## Main results (`#print axioms` at the end of the file)
* `hc_main` (claim K25): `CC_deg` ∧ `hc_unsat` ∧ `hc_size`. Axioms: propext, Classical.choice,
  Quot.sound. The size bound is nontrivial (beats `|F|`) only from about `k = 21`.
* `hc_width` (`k ≥ 2`): some line has `≥ ⌊⌊2^k/3⌋/(k+1)⌋` distinct edge literals.
* `cut_main`: the expansion bound above. `CC_len`: `2|E| = 3k2^k` (axioms propext, Quot.sound).
* `CC_ends` (`k ≥ 2`): endpoints in range and distinct. `QL_Q`: forgetting labels gives `Q k`.

## Prior art and what this file adds (request R4, `brief/requests/R4.md`)
The general Tseitin expansion bound used here (`Work.Tseitin`, K20/K21) probably also exists in
Lean 4 in cslib-community/complexitylib (`TseitinExpander`; R4 saw search snippets only). R4 found
no Lean instantiation on cube-connected cycles and no Lean statement of the `2^{Ω(|F|/log^4|F|)}`
bound. What this file adds: a bounded-degree (3-CNF) explicit family with a machine-checked
expansion bound (`cut_main`, reduced to the hypercube's `cut_ge`) and an explicit size bound (K25).
-/

namespace Programme.«20261024-1110-proof-complexity».CCC

open Programme.«20261024-1110-proof-complexity».Haken Programme.«20261024-1110-proof-complexity».Tseitin Programme.«20261024-1110-proof-complexity».Hypercube

/-- Hypercube edges labelled with their dimension (same recursion as `Q`). -/
def QL : Nat → List (Nat × Nat × Nat)
  | 0 => []
  | k + 1 => QL k ++ (QL k).map (fun t => (2 ^ k + t.1, 2 ^ k + t.2.1, t.2.2)) ++
      (List.range (2 ^ k)).map (fun u => (u, 2 ^ k + u, k))

/-- Next position on the same cycle of length `k`. -/
def nxt (k v : Nat) : Nat := v / k * k + (v % k + 1) % k

/-- Cycle edges of `m` cycles of length `k`. -/
def cyc (k m : Nat) : List (Nat × Nat) := (List.range (m * k)).map fun v => (v, nxt k v)

/-- Cube edges: dimension-`i` edge `x ~ y` joins `x * k + i` and `y * k + i`. -/
def cube (k : Nat) : List (Nat × Nat) :=
  (QL k).map fun t => (t.1 * k + t.2.2, t.2.1 * k + t.2.2)

/-- Edges of the cube-connected cycles of dimension `k` on `0..2^k * k - 1`. -/
def CC (k : Nat) : List (Nat × Nat) := cyc k (2 ^ k) ++ cube k

/-- The Tseitin formula of the cube-connected cycles, charge `1` at vertex `0`. -/
def HC (k : Nat) : CNF Nat := Tseitin (2 ^ k * k) (CC k) chg

theorem QL_Q (k : Nat) : (QL k).map (fun t => (t.1, t.2.1)) = Q k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [QL, Q, List.map_append, List.map_map, ← ih]
    rfl

theorem QL_lab (k : Nat) : ∀ t ∈ QL k, t.2.2 < k := by
  induction k with
  | zero => simp [QL]
  | succ k ih =>
    intro t ht
    simp only [QL, List.mem_append, List.mem_map, List.mem_range] at ht
    rcases ht with (h | ⟨q, hq, rfl⟩) | ⟨u, hu, rfl⟩
    · have := ih t h; omega
    · have := ih q hq; simp; omega
    · simp

theorem QL_ends (k : Nat) : ∀ t ∈ QL k, t.1 < t.2.1 ∧ t.2.1 < 2 ^ k := by
  intro t ht
  have : (t.1, t.2.1) ∈ Q k := by rw [← QL_Q]; exact List.mem_map_of_mem ht
  exact Q_ends k _ this

theorem blk {k x l : Nat} (hl : l < k) : (x * k + l) / k = x ∧ (x * k + l) % k = l := by
  have hk : 0 < k := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hl, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]

theorem succ_mod {k r : Nat} (hr : r < k) : (r + 1) % k = if r + 1 = k then 0 else r + 1 := by
  split
  · next h => rw [h, Nat.mod_self]
  · next h => exact Nat.mod_eq_of_lt (by omega)

theorem nxt_blk {k x i : Nat} (hi : i < k) : nxt k (x * k + i) = x * k + (i + 1) % k := by
  unfold nxt; rw [(blk hi).1, (blk hi).2]

theorem nxt_inj {k : Nat} (hk : 0 < k) (a b : Nat) (h : nxt k a = nxt k b) : a = b := by
  have ha := Nat.mod_lt a hk
  have hb := Nat.mod_lt b hk
  have ha' := Nat.mod_lt (a % k + 1) hk
  have hb' := Nat.mod_lt (b % k + 1) hk
  unfold nxt at h
  have h1 := blk (x := a / k) ha'
  have h2 := blk (x := b / k) hb'
  rw [h] at h1
  have hq : a / k = b / k := h1.1.symm.trans h2.1
  have hr : (a % k + 1) % k = (b % k + 1) % k := h1.2.symm.trans h2.2
  rw [succ_mod ha, succ_mod hb] at hr
  have hr' : a % k = b % k := by split at hr <;> split at hr <;> omega
  rw [← Nat.div_add_mod' a k, ← Nat.div_add_mod' b k, hq, hr']

theorem nxt_lt {k M v : Nat} (hk : 0 < k) (hv : v < M * k) : nxt k v < M * k := by
  have hq : v / k < M := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hv)
  have := Nat.mod_lt (v % k + 1) hk
  have : (v / k + 1) * k ≤ M * k := Nat.mul_le_mul_right _ hq
  rw [Nat.succ_mul] at this
  unfold nxt; omega

theorem nxt_ne {k : Nat} (hk : 2 ≤ k) (v : Nat) : nxt k v ≠ v := by
  intro h
  have ha := Nat.mod_lt v (by omega : 0 < k)
  have h' := h
  unfold nxt at h'
  conv at h' => rhs; rw [← Nat.div_add_mod' v k]
  rw [succ_mod ha] at h'
  split at h' <;> omega

/-- Number of vertices of `S` on cycle `x`. -/
def cnt (k : Nat) (S : Nat → Bool) (x : Nat) : Nat := (List.range k).countP fun i => S (x * k + i)

/-- Cycle `x` lies inside `S`. -/
def full (k : Nat) (S : Nat → Bool) (x : Nat) : Bool := cnt k S x == k

/-- Cycle `x` meets both `S` and its complement. -/
def part (k : Nat) (S : Nat → Bool) (x : Nat) : Bool := cnt k S x != k && cnt k S x != 0

theorem cnt_le (k : Nat) (S : Nat → Bool) (x : Nat) : cnt k S x ≤ k := by
  have := List.countP_le_length (p := fun i => S (x * k + i)) (l := List.range k)
  simpa [cnt] using this

theorem full_mem {k : Nat} {S : Nat → Bool} {x i : Nat} (h : full k S x = true) (hi : i < k) :
    S (x * k + i) = true := by
  simp only [full, beq_iff_eq, cnt] at h
  have h' : (List.range k).countP (fun i => S (x * k + i)) = (List.range k).length := by simpa using h
  exact List.countP_eq_length.mp h' i (List.mem_range.mpr hi)

theorem empty_mem {k : Nat} {S : Nat → Bool} {x i : Nat} (h : cnt k S x = 0) (hi : i < k) :
    S (x * k + i) = false := by
  unfold cnt at h
  have := List.countP_eq_zero.mp h i (List.mem_range.mpr hi)
  simpa using this

theorem size_blk (k : Nat) (S : Nat → Bool) (m : Nat) :
    size ((m + 1) * k) S = size (m * k) S + cnt k S m := by
  unfold size cnt
  rw [Nat.succ_mul, List.range_add, List.countP_append, List.countP_map]; rfl

theorem size_one (m : Nat) (P : Nat → Bool) : size (m + 1) P = size m P + if P m then 1 else 0 := by
  unfold size; rw [List.range_succ, List.countP_append]; simp [List.countP_cons]

/-- Block counting: `k f ≤ |S| ≤ k (f + p)`. -/
theorem size_bounds (k : Nat) (S : Nat → Bool) (m : Nat) :
    k * size m (full k S) ≤ size (m * k) S ∧
      size (m * k) S ≤ k * (size m (full k S) + size m (part k S)) := by
  induction m with
  | zero => simp [size]
  | succ m ih =>
    rw [size_blk, size_one, size_one]
    have hc := cnt_le k S m
    have hfp : (full k S m = true → cnt k S m = k) ∧ (full k S m = false → part k S m = false →
        cnt k S m = 0) := by
      simp only [full, part]; constructor
      · intro h; simpa using h
      · intro h1 h2; simp at h1; simp [h1] at h2; exact h2
    rw [Nat.mul_add] at ih; rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
    obtain ⟨hf1, hf2⟩ := hfp
    cases h1 : full k S m <;> cases h2 : part k S m
    · have := hf2 h1 h2; simp; omega
    · simp; omega
    · have := hf1 h1; simp; omega
    · have := hf1 h1; simp; omega

/-- Cycle-edge boundary of `S`. -/
theorem cyc_cut (k : Nat) (_hk : 0 < k) (S : Nat → Bool) (m : Nat) :
    size m (part k S) ≤ cut (cyc k m) S := by
  induction m with
  | zero => simp [size]
  | succ m ih =>
    rw [size_one]
    have hsplit : cut (cyc k (m + 1)) S = cut (cyc k m) S +
        (List.range k).countP (fun i => S (m * k + i) != S (m * k + (i + 1) % k)) := by
      unfold cut cyc
      rw [Nat.succ_mul, List.range_add, List.map_append, List.countP_append, List.map_map,
        List.countP_map, List.countP_map]
      congr 1
      apply List.countP_congr
      intro i hi
      simp only [Function.comp, nxt_blk (List.mem_range.mp hi)]
    rw [hsplit]
    split
    · next hp =>
      suffices 0 < (List.range k).countP (fun i => S (m * k + i) != S (m * k + (i + 1) % k)) by omega
      apply Nat.pos_of_ne_zero
      intro h0
      have hc : ∀ i, i < k → S (m * k + i) = S (m * k) := by
        intro i
        induction i with
        | zero => intro _; rfl
        | succ i ihi =>
          intro hi
          have := List.countP_eq_zero.mp h0 i (List.mem_range.mpr (by omega))
          rw [Nat.mod_eq_of_lt hi] at this
          rw [← ihi (by omega)]
          cases h1 : S (m * k + i) <;> cases h2 : S (m * k + (i + 1)) <;> simp_all
      simp only [part, cnt, bne_iff_ne, ne_eq, Bool.and_eq_true] at hp
      cases h : S (m * k)
      · apply hp.2; rw [List.countP_eq_zero]; intro i hi; rw [hc i (List.mem_range.mp hi), h]; simp
      · apply hp.1
        have : (List.range k).countP (fun i => S (m * k + i)) = (List.range k).length := by
          rw [List.countP_eq_length]; intro i hi; rw [hc i (List.mem_range.mp hi), h]
        simpa using this
    · omega

/-- Edges with an endpoint in `P` are at most `D |P|` when degrees are `≤ D`. -/
theorem deg_sum (E : List (Nat × Nat)) (P : Nat → Bool) (D : Nat)
    (hdeg : ∀ v, E.countP (fun p => p.1 == v || p.2 == v) ≤ D) :
    ∀ n, E.countP (fun p => (decide (p.1 < n) && P p.1) || (decide (p.2 < n) && P p.2)) ≤
      D * size n P := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [size_one, Nat.mul_add]
    have h := countP_or E (fun p => (decide (p.1 < n + 1) && P p.1) || (decide (p.2 < n + 1) && P p.2))
      (fun p => (decide (p.1 < n) && P p.1) || (decide (p.2 < n) && P p.2))
      (fun p => (p.1 == n || p.2 == n) && P n)
      (by
        intro p _ hp
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp ⊢
        rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · by_cases h3 : p.1 = n
          · subst h3; exact Or.inr ⟨Or.inl rfl, h2⟩
          · exact Or.inl (Or.inl ⟨by omega, h2⟩)
        · by_cases h3 : p.2 = n
          · subst h3; exact Or.inr ⟨Or.inr rfl, h2⟩
          · exact Or.inl (Or.inr ⟨by omega, h2⟩))
    cases hP : P n
    · have : E.countP (fun p => (p.1 == n || p.2 == n) && P n) = 0 := by
        rw [List.countP_eq_zero]; intro p _; simp [hP]
      simp; omega
    · have : E.countP (fun p => (p.1 == n || p.2 == n) && P n) ≤ D := by
        have := hdeg n; simp only [hP, Bool.and_true]; exact this
      simp; omega

/-- Cube-edge boundary: `cut_Q(F) ≤ cut_cube(S) + k p`. -/
theorem cube_cut (k : Nat) (S : Nat → Bool) :
    cut (Q k) (full k S) ≤ cut (cube k) S + k * size (2 ^ k) (part k S) := by
  have hQ : cut (Q k) (full k S) = (QL k).countP (fun t => full k S t.1 != full k S t.2.1) := by
    unfold cut; rw [← QL_Q, List.countP_map]; rfl
  have hC : cut (cube k) S = (QL k).countP
      (fun t => S (t.1 * k + t.2.2) != S (t.2.1 * k + t.2.2)) := by
    unfold cut cube; rw [List.countP_map]; rfl
  have hP : (QL k).countP (fun t => part k S t.1 || part k S t.2.1) ≤ k * size (2 ^ k) (part k S) := by
    have h := deg_sum (Q k) (part k S) k (deg_le k) (2 ^ k)
    rw [← QL_Q, List.countP_map] at h
    refine Nat.le_trans (Nat.le_of_eq ?_) h
    apply List.countP_congr
    intro t ht
    have := QL_ends k t ht
    simp only [Function.comp, decide_eq_true (by omega : t.1 < 2 ^ k),
      decide_eq_true (by omega : t.2.1 < 2 ^ k), Bool.true_and]
  rw [hQ, hC]
  refine Nat.le_trans (countP_or _ _ (fun t => S (t.1 * k + t.2.2) != S (t.2.1 * k + t.2.2))
    (fun t => part k S t.1 || part k S t.2.1) ?_) (by omega)
  intro t ht h
  have hl := QL_lab k t ht
  apply Classical.byContradiction
  intro hno
  simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hno
  obtain ⟨hs, hp1, hp2⟩ := hno
  have em : ∀ x, part k S x = false → full k S x = false → S (x * k + t.2.2) = false := by
    intro x h1 h2
    simp only [part, full] at h1 h2
    have : cnt k S x = 0 := by simp at h2; simp [h2] at h1; exact h1
    exact empty_mem this hl
  cases hf1 : full k S t.1 <;> cases hf2 : full k S t.2.1 <;> rw [hf1, hf2] at h
  · simp at h
  · rw [em _ hp1 hf1, full_mem hf2 hl] at hs; simp at hs
  · rw [full_mem hf1 hl, em _ hp2 hf2] at hs; simp at hs
  · simp at h

/-- At each cube vertex there is at most one edge of each dimension. -/
theorem QL_deg (k : Nat) : ∀ x j, (QL k).countP (fun t => (t.1 == x || t.2.1 == x) && t.2.2 == j) ≤ 1 := by
  induction k with
  | zero => intro x j; simp [QL]
  | succ k ih =>
    intro x j
    simp only [QL, List.countP_append, List.countP_map]
    have hz : ∀ {β : Type} (l : List β) (f : β → Bool),
        (∀ t ∈ l, f t = false) → l.countP f = 0 := by
      intro β l f h; rw [List.countP_eq_zero]; intro t ht; simp [h t ht]
    by_cases hj : j = k
    · subst hj
      rw [hz (QL j) _ (fun t ht => by have := QL_lab j t ht; simp; omega),
        hz (QL j) _ (fun t ht => by have := QL_lab j t ht; simp [Function.comp]; omega)]
      by_cases hx : x < 2 ^ j
      · have : (List.range (2 ^ j)).countP ((fun t : Nat × Nat × Nat => (t.1 == x || t.2.1 == x) &&
            t.2.2 == j) ∘ fun u => (u, 2 ^ j + u, j)) = (List.range (2 ^ j)).countP (fun u => u == x) := by
          apply List.countP_congr; intro u _; simp [Function.comp]; omega
        rw [this]; have := cnt_inj (fun u => u) (fun a b h => h) x (2 ^ j); simp at this ⊢; omega
      · have : (List.range (2 ^ j)).countP ((fun t : Nat × Nat × Nat => (t.1 == x || t.2.1 == x) &&
            t.2.2 == j) ∘ fun u => (u, 2 ^ j + u, j)) =
            (List.range (2 ^ j)).countP (fun u => 2 ^ j + u == x) := by
          apply List.countP_congr; intro u hu; have := List.mem_range.mp hu
          simp [Function.comp]; omega
        rw [this]; have := cnt_inj (fun u => 2 ^ j + u) (fun a b h => by omega) x (2 ^ j); omega
    · rw [hz (List.range (2 ^ k)) _ (fun u _ => by simp [Function.comp]; omega)]
      by_cases hx : x < 2 ^ k
      · rw [hz (QL k) ((fun t : Nat × Nat × Nat => (t.1 == x || t.2.1 == x) && t.2.2 == j) ∘
            fun t => (2 ^ k + t.1, 2 ^ k + t.2.1, t.2.2)) (fun t _ => by simp; omega)]
        have := ih x j; omega
      · rw [hz (QL k) _ (fun t ht => by have := QL_ends k t ht; simp; omega)]
        have : (QL k).countP ((fun t : Nat × Nat × Nat => (t.1 == x || t.2.1 == x) && t.2.2 == j) ∘
            fun t => (2 ^ k + t.1, 2 ^ k + t.2.1, t.2.2)) =
            (QL k).countP (fun t => (t.1 == x - 2 ^ k || t.2.1 == x - 2 ^ k) && t.2.2 == j) := by
          apply List.countP_congr; intro t _; simp [Function.comp]; omega
        rw [this]; have := ih (x - 2 ^ k) j; omega

/-- Every vertex of `CC k` has degree `≤ 3`. -/
theorem CC_deg (k : Nat) (hk : 0 < k) (w : Nat) : (CC k).countP (fun p => p.1 == w || p.2 == w) ≤ 3 := by
  simp only [CC, cyc, cube, List.countP_append, List.countP_map]
  have h1 := countP_or (List.range (2 ^ k * k))
    ((fun p : Nat × Nat => p.1 == w || p.2 == w) ∘ fun v => (v, nxt k v)) (fun v => v == w)
    (fun v => nxt k v == w) (by intro v _ h; simpa using h)
  have c1 := cnt_inj (fun u => u) (fun a b h => h) w (2 ^ k * k)
  have c2 := cnt_inj (nxt k) (nxt_inj hk) w (2 ^ k * k)
  have h2 : (QL k).countP ((fun p : Nat × Nat => p.1 == w || p.2 == w) ∘
      fun t => (t.1 * k + t.2.2, t.2.1 * k + t.2.2)) ≤
      (QL k).countP (fun t => (t.1 == w / k || t.2.1 == w / k) && t.2.2 == w % k) := by
    apply List.countP_mono_left
    intro t ht h
    have hl := QL_lab k t ht
    have b1 := blk (x := t.1) hl
    have b2 := blk (x := t.2.1) hl
    simp only [Function.comp, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h ⊢
    rcases h with h | h
    · rw [← h, b1.1, b1.2]; simp
    · rw [← h, b2.1, b2.2]; simp
  have := QL_deg k (w / k) (w % k)
  omega

theorem cut_CC (k : Nat) (S : Nat → Bool) : cut (CC k) S = cut (cyc k (2 ^ k)) S + cut (cube k) S := by
  simp only [cut, CC, List.countP_append]

/-- The facts behind the expansion of `CC k`, with `f` full and `p` partial cycles. -/
theorem facts (k : Nat) (hk : 0 < k) (S : Nat → Bool) :
    k * size (2 ^ k) (full k S) ≤ size (2 ^ k * k) S ∧
    size (2 ^ k * k) S ≤ k * size (2 ^ k) (full k S) + k * size (2 ^ k) (part k S) ∧
    size (2 ^ k) (part k S) ≤ cut (CC k) S ∧
    min (size (2 ^ k) (full k S)) (2 ^ k - size (2 ^ k) (full k S)) + size (2 ^ k) (part k S) ≤
      cut (CC k) S + k * size (2 ^ k) (part k S) ∧
    size (2 ^ k) (full k S) ≤ 2 ^ k := by
  have h1 := size_bounds k S (2 ^ k)
  have h2 := cyc_cut k hk S (2 ^ k)
  have h3 := cube_cut k S
  have h4 := cut_ge k (full k S)
  have h5 := size_le (2 ^ k) (full k S)
  rw [Nat.mul_add] at h1
  rw [cut_CC]
  omega

/-- **Expansion of the cube-connected cycles**: a set with between a third and two thirds of the
vertices has `(k+1) |∂S| ≥ ⌊2^k/3⌋`. -/
theorem cut_main (k : Nat) (hk : 0 < k) (S : Nat → Bool) (h1 : 2 ^ k * k / 3 < size (2 ^ k * k) S)
    (h2 : size (2 ^ k * k) S ≤ 2 * (2 ^ k * k / 3)) : 2 ^ k / 3 ≤ (k + 1) * cut (CC k) S := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := facts k hk S
  generalize size (2 ^ k) (full k S) = f at *
  generalize size (2 ^ k) (part k S) = p at *
  generalize size (2 ^ k * k) S = s at *
  generalize cut (CC k) S = c at *
  generalize hM : 2 ^ k = M at *
  generalize hT : M / 3 = T
  have hT3 : T * 3 ≤ M := by rw [← hT]; exact Nat.div_mul_le_self M 3
  have hX : M * k / 3 * 3 ≤ M * k := Nat.div_mul_le_self _ 3
  have hkT : k * T ≤ M * k / 3 := by
    rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_assoc, Nat.mul_comm M k]
    exact Nat.mul_le_mul_left k hT3
  have hfp : T < f + p := by
    apply Nat.lt_of_mul_lt_mul_left (a := k); rw [Nat.mul_add]; omega
  have hf : f ≤ M - T := by
    apply Nat.le_of_mul_le_mul_left _ hk
    rw [Nat.mul_sub, Nat.mul_comm k M]; omega
  have hkc : k * p ≤ k * c := Nat.mul_le_mul_left k a3
  rw [Nat.succ_mul]
  omega

theorem hexp' (k : Nat) (hk : 0 < k) : ∀ S : Nat → Bool, 2 ^ k * k / 3 < size (2 ^ k * k) S →
    size (2 ^ k * k) S ≤ 2 * (2 ^ k * k / 3) → 2 ^ k / 3 / (k + 1) ≤ (bd (CC k) S).length := by
  intro S h1 h2
  rw [bd_len]
  apply Nat.div_le_of_le_mul
  exact cut_main k hk S h1 h2

theorem hconn' (k : Nat) (hk : 0 < k) : ∀ S : Nat → Bool, 0 < size (2 ^ k * k) S →
    size (2 ^ k * k) S < 2 ^ k * k → bd (CC k) S ≠ [] := by
  intro S h1 h2 h
  have h0 : cut (CC k) S = 0 := by rw [← bd_len, h]; rfl
  obtain ⟨a1, a2, a3, a4, a5⟩ := facts k hk S
  rw [h0] at a3 a4
  have hp : size (2 ^ k) (part k S) = 0 := by omega
  rw [hp, Nat.mul_zero] at a2 a4
  have hmin : min (size (2 ^ k) (full k S)) (2 ^ k - size (2 ^ k) (full k S)) = 0 := by omega
  rcases Nat.min_eq_zero_iff.mp hmin with h3 | h3
  · rw [h3] at a2; omega
  · have : size (2 ^ k) (full k S) = 2 ^ k := by omega
    rw [this, Nat.mul_comm] at a1; omega

theorem CC_ends (k : Nat) (hk : 2 ≤ k) : ∀ p ∈ CC k, p.1 < 2 ^ k * k ∧ p.2 < 2 ^ k * k ∧ p.1 ≠ p.2 := by
  intro p hp
  simp only [CC, cyc, cube, List.mem_append, List.mem_map, List.mem_range] at hp
  rcases hp with ⟨v, hv, rfl⟩ | ⟨t, ht, rfl⟩
  · exact ⟨hv, nxt_lt (by omega) hv, (nxt_ne hk v).symm⟩
  · have hl := QL_lab k t ht
    have he := QL_ends k t ht
    have m1 : (t.1 + 1) * k ≤ 2 ^ k * k := Nat.mul_le_mul_right k (by omega)
    have m2 : (t.2.1 + 1) * k ≤ 2 ^ k * k := Nat.mul_le_mul_right k (by omega)
    have m3 : (t.1 + 1) * k ≤ t.2.1 * k := Nat.mul_le_mul_right k (by omega)
    rw [Nat.succ_mul] at m1 m2 m3
    refine ⟨by omega, by omega, by simp; omega⟩

/-- **Unsatisfiability** of `HC k` (`k ≥ 2`). -/
theorem hc_unsat (k : Nat) (hk : 2 ≤ k) (α : Nat → Bool) : ∃ C ∈ HC k, C.eval α = false :=
  tseitin_unsat (CC_ends k hk)
    (by rw [chg_sum _ (Nat.mul_pos (Nat.two_pow_pos k) (by omega))]) α

theorem CC_len (k : Nat) : 2 * (CC k).length = 3 * k * 2 ^ k := by
  have h1 : (QL k).length = (Q k).length := by rw [← QL_Q, List.length_map]
  have h2 := Q_len k
  simp only [CC, cyc, cube, List.length_append, List.length_map, List.length_range]
  rw [h1, Nat.mul_comm (2 ^ k) k]
  rw [Nat.mul_add, h2, Nat.mul_assoc 3, Nat.succ_mul 2]

theorem pow_big (k : Nat) (hk : 11 ≤ k) : 96 * (k + 1) ≤ 2 ^ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 11 := ⟨k - 11, by omega⟩
  induction j with
  | zero => decide
  | succ j ih => rw [show j + 1 + 11 = j + 11 + 1 by omega, Nat.pow_succ]; have := ih (by omega); omega

/-- **Width**: for `k ≥ 2` every refutation of `HC k` has a clause with at least
`⌊⌊2^k/3⌋/(k+1)⌋` edge literals. -/
theorem hc_width (k : Nat) (hk : 2 ≤ k) (π : Refutation (HC k)) :
    ∃ C ∈ π.steps, 2 ^ k / 3 / (k + 1) ≤ Programme.«20261024-1110-proof-complexity».BSWR.wd (List.range (CC k).length) C :=
  tseitin_width (fun p hp => ⟨(CC_ends k hk p hp).1, (CC_ends k hk p hp).2.1⟩) (hconn' k (by omega))
    (hexp' k (by omega)) (by have := Nat.mul_le_mul (three_le k hk) hk; omega) π

/-- **Size**: for `k ≥ 11`, with `B = ⌊2^k/(8(k+1))⌋`, every refutation of `HC k` with `L`
clauses has `(3k2^k)^B ≤ L (3k2^k - B)^B`. -/
theorem hc_size (k : Nat) (hk : 11 ≤ k) (π : Refutation (HC k)) :
    (3 * k * 2 ^ k) ^ (2 ^ k / (8 * (k + 1))) ≤
      π.steps.length * (3 * k * 2 ^ k - 2 ^ k / (8 * (k + 1))) ^ (2 ^ k / (8 * (k + 1))) := by
  have hdeg : ∀ v, v < 2 ^ k * k → (inc (CC k) v).length ≤ 3 := by
    intro v _; rw [inc_len]; exact CC_deg k (by omega) v
  have hwd : 3 + 2 ^ k / (8 * (k + 1)) + 2 ^ k / (8 * (k + 1)) < 2 ^ k / 3 / (k + 1) := by
    have hM := pow_big k hk
    generalize 2 ^ k = M at *
    generalize hc : k + 1 = c at *
    have hB : M / (8 * c) * (8 * c) ≤ M := Nat.div_mul_le_self M (8 * c)
    generalize M / (8 * c) = B at *
    rw [Nat.mul_left_comm] at hB
    have h3 := Nat.div_add_mod M 3
    have h3' := Nat.mod_lt M (by omega : 0 < 3)
    apply Nat.lt_of_succ_le
    rw [Nat.le_div_iff_mul_le (by omega), Nat.succ_mul, Nat.add_mul, Nat.add_mul]
    omega
  have h := tseitin_size (fun p hp => ⟨(CC_ends k (by omega) p hp).1, (CC_ends k (by omega) p hp).2.1⟩)
    (hconn' k (by omega)) (hexp' k (by omega))
    (by have := Nat.mul_le_mul (three_le k (by omega)) (by omega : 1 ≤ k); omega) hdeg hwd π
  rw [CC_len] at h
  exact h

/-- **Main**: for `k ≥ 2` the Tseitin formula `HC k` of the cube-connected cycles (degree `≤ 3`)
is unsatisfiable, and for `k ≥ 11` every resolution refutation with `L` clauses has
`(3k2^k)^B ≤ L (3k2^k - B)^B` with `B = ⌊2^k/(8(k+1))⌋`. -/
theorem hc_main (k : Nat) (hk : 2 ≤ k) :
    (∀ v, (CC k).countP (fun p => p.1 == v || p.2 == v) ≤ 3) ∧
    (∀ α : Nat → Bool, ∃ C ∈ HC k, C.eval α = false) ∧
    (11 ≤ k → ∀ π : Refutation (HC k),
      (3 * k * 2 ^ k) ^ (2 ^ k / (8 * (k + 1))) ≤
        π.steps.length * (3 * k * 2 ^ k - 2 ^ k / (8 * (k + 1))) ^ (2 ^ k / (8 * (k + 1)))) :=
  ⟨CC_deg k (by omega), hc_unsat k hk, hc_size k⟩

end Programme.«20261024-1110-proof-complexity».CCC

#print axioms Programme.«20261024-1110-proof-complexity».CCC.hc_main
#print axioms Programme.«20261024-1110-proof-complexity».CCC.hc_width
#print axioms Programme.«20261024-1110-proof-complexity».CCC.cut_main

#print axioms Programme.«20261024-1110-proof-complexity».CCC.hc_unsat
#print axioms Programme.«20261024-1110-proof-complexity».CCC.hc_size
#print axioms Programme.«20261024-1110-proof-complexity».CCC.CC_deg
#print axioms Programme.«20261024-1110-proof-complexity».CCC.CC_len
#print axioms Programme.«20261024-1110-proof-complexity».CCC.CC_ends
#print axioms Programme.«20261024-1110-proof-complexity».CCC.QL_Q
#print axioms Programme.«20261024-1110-proof-complexity».CCC.cyc_cut
#print axioms Programme.«20261024-1110-proof-complexity».CCC.cube_cut
