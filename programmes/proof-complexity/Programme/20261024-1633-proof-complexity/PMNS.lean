import Programme.«20261024-1633-proof-complexity».NSLocal

/-!
# Perfect matchings in hypergraphs: degree-`Δ` Nullstellensatz refutations modulo `p`

The hypergraph perfect-matching CNF `PM n H`: vertices `0..n-1`, hyperedges `H` (lists of
vertices), one variable per hyperedge (its index), and for every vertex `v` the clause "some edge
at `v` is chosen" (`ALO`) and, for every pair of edges at `v`, "not both" (`AMO`).

`pm_ns`: if `p` divides the size of every hyperedge and `n` is invertible modulo `p`, `PM n H`
has a Nullstellensatz refutation over `Z/p` of degree `Δ` (maximum vertex degree, `Δ ≥ 2`).
Reason: `∑_v (S_v - 1) = ∑_e |e| x_e - n ≡ -n`, where `S_v` is the number of chosen edges at `v`,
and on the cube `S_v - 1 = -∏_{e∋v}(1-x_e) + ∑_{i<j} ∏_{k<i}(1-x_{e_k}) x_{e_i} x_{e_j}`
(edges at `v` in order) is a combination of `v`'s own clauses (`local_ns_blocks`).
For `3`-uniform `H` and `3 ∤ n` this is the easy side of the mod-3 counting principle over `F_3`.
-/

namespace Programme.«20261024-1633-proof-complexity».PMNS

open Classical Programme.«20261024-1110-proof-complexity».Haken
open Programme.«20261024-1633-proof-complexity».NS Programme.«20261024-1633-proof-complexity».NSLocal

/-! ## The formula -/

/-- Indices of the hyperedges containing `v`. -/
def incH (H : List (List Nat)) (v : Nat) : List Nat :=
  (List.range H.length).filter fun i => decide (v ∈ H.getD i [])

/-- The pair clauses `¬x ∨ ¬y` of a list, each with the list of variables before `x`. -/
def pairsW : List Nat → List (Clause Nat × List Nat)
  | [] => []
  | x :: L => L.map (fun y => ([⟨x, false⟩, ⟨y, false⟩], [])) ++
      (pairsW L).map fun q => (q.1, x :: q.2)

def ind (a : Nat → Bool) (x : Nat) : Int := if a x then 1 else 0

def prodNot (a : Nat → Bool) (W : List Nat) : Int := (W.map fun w => 1 - ind a w).prod

/-- Clauses of vertex `v` with their local multipliers (scaled by `c`). -/
def blk (H : List (List Nat)) (c : Int) (v : Nat) :
    List (Clause Nat × List (List Nat × ((Nat → Bool) → Int))) :=
  ((incH H v).map (fun i => (⟨i, true⟩ : Lit Nat)), [([], fun _ => -c)]) ::
    (pairsW (incH H v)).map fun q => (q.1, [(q.2, fun a => c * prodNot a q.2)])

def PMblock (H : List (List Nat)) (v : Nat) : CNF Nat := (blk H 0 v).map Prod.fst

/-- The perfect-matching CNF of the hypergraph `H` on vertices `0..n-1`. -/
def PM (n : Nat) (H : List (List Nat)) : CNF Nat := (List.range n).flatMap (PMblock H)

/-! ## The local identity -/

theorem pairsW_lens (L : List Nat) : ∀ q ∈ pairsW L, q.1.length = 2 ∧
    q.2.length + 2 ≤ L.length ∧ (∀ x ∈ q.2, x ∈ L) ∧ (∀ l ∈ q.1, l.var ∈ L) := by
  induction L with
  | nil => simp [pairsW]
  | cons x L ih =>
    intro q hq
    simp only [pairsW, List.mem_append, List.mem_map] at hq
    rcases hq with ⟨y, hy, rfl⟩ | ⟨q', hq', rfl⟩
    · refine ⟨rfl, ?_, by simp, ?_⟩
      · have := List.length_pos_of_mem hy; simp; omega
      · intro l hl; simp at hl; rcases hl with rfl | rfl <;> simp [hy]
    · obtain ⟨h1, h2, h3, h4⟩ := ih q' hq'
      refine ⟨h1, by simp; omega, ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons] at hz ⊢
        rcases hz with h | h
        · exact Or.inl h
        · exact Or.inr (h3 _ h)
      · intro l hl; simp [h4 l hl]

theorem clausePoly_pair (a : Nat → Bool) (x y : Nat) :
    (clausePoly ([⟨x, false⟩, ⟨y, false⟩] : Clause Nat)).eval a = ind a x * ind a y := by
  rw [clausePoly_eval]
  unfold ind; cases hx : a x <;> cases hy : a y <;> simp [Clause.eval, Lit.eval, hx, hy]

theorem clausePoly_alo (a : Nat → Bool) (L : List Nat) :
    (clausePoly (L.map fun i => (⟨i, true⟩ : Lit Nat))).eval a = prodNot a L := by
  rw [clausePoly_eval]
  induction L with
  | nil => simp [Clause.eval, prodNot]
  | cons x L ih =>
    simp only [List.map_cons, Clause.eval, List.any_cons, prodNot, List.prod_cons] at ih ⊢
    have hl : Lit.eval a ⟨x, true⟩ = a x := by simp [Lit.eval]
    rw [hl, ← ih]
    unfold ind
    cases a x <;> simp

theorem sum_map_mul {α} (L : List α) (k : Int) (f : α → Int) :
    (L.map fun x => k * f x).sum = k * (L.map f).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ih, Int.mul_add]

/-- `∑_{(C,W)} ∏_W (1 - x) · f_C = S_L - 1 + ∏_L (1 - x)` on the cube. -/
theorem pairs_identity (a : Nat → Bool) (L : List Nat) :
    ((pairsW L).map fun q => prodNot a q.2 * (clausePoly q.1).eval a).sum =
      (L.map (ind a)).sum - 1 + prodNot a L := by
  induction L with
  | nil => simp [pairsW, prodNot]
  | cons x L ih =>
    simp only [pairsW, List.map_append, List.sum_append, List.map_map, Function.comp_def,
      List.map_cons, List.sum_cons, prodNot, List.prod_cons, List.map_nil, List.prod_nil,
      Int.one_mul, clausePoly_pair, Int.mul_assoc, sum_map_mul]
    simp only [prodNot] at ih
    rw [ih]
    have : ind a x = 0 ∨ ind a x = 1 := by unfold ind; cases a x <;> simp
    rcases this with h | h <;> simp [h] <;> omega

/-- The block sum for vertex `v`: `c (S_v - 1)`. -/
theorem blk_sum (H : List (List Nat)) (c : Int) (v : Nat) (a : Nat → Bool) :
    ((blk H c v).map fun r => ((r.2.map fun t => t.2 a).sum) * (clausePoly r.1).eval a).sum =
      c * (((incH H v).map (ind a)).sum - 1) := by
  simp only [blk, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, Int.add_zero,
    List.map_map, Function.comp_def, clausePoly_alo]
  simp only [Int.mul_assoc, sum_map_mul]
  rw [pairs_identity, Int.mul_add, Int.mul_sub, Int.neg_mul]
  omega

/-! ## Double counting -/

theorem sum_zero (Vs : List Nat) : (Vs.map fun _ => (0 : Int)).sum = 0 := by
  induction Vs <;> simp [*]

theorem swap_step (Vs : List Nat) (i : Nat) (R : List Nat) (P : Nat → Nat → Bool) (g : Nat → Int) :
    (Vs.map fun v => (((i :: R).filter (P v)).map g).sum).sum =
      g i * ((Vs.countP fun v => P v i : Nat) : Int) + (Vs.map fun v => ((R.filter (P v)).map g).sum).sum := by
  induction Vs with
  | nil => simp
  | cons v Vs ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons, List.filter_cons, List.map_cons, List.sum_cons]
    cases h : P v i
    · simp only [Bool.false_eq_true, ite_false, Nat.add_zero]; omega
    · simp only [ite_true, List.map_cons, List.sum_cons]
      rw [show (((List.countP (fun v => P v i) Vs + 1 : Nat)) : Int) =
        ((List.countP (fun v => P v i) Vs : Nat) : Int) + 1 by omega, Int.mul_add, Int.mul_one]
      omega

theorem sum_filter_swap (n : Nat) (R : List Nat) (P : Nat → Nat → Bool) (g : Nat → Int) :
    ((List.range n).map fun v => ((R.filter (P v)).map g).sum).sum =
      (R.map fun i => g i * ((List.range n).countP fun v => P v i : Nat)).sum := by
  induction R with
  | nil => simp [sum_zero]
  | cons i R ih => rw [swap_step, ih, List.map_cons, List.sum_cons]

theorem dvd_sum_map (L : List Nat) (f : Nat → Int) (k : Int) (h : ∀ i ∈ L, k ∣ f i) :
    k ∣ (L.map f).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    rw [List.map_cons, List.sum_cons]
    exact Int.dvd_add (h i (List.mem_cons_self ..)) (ih fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem sum_c_sub (n : Nat) (c : Int) (f : Nat → Int) :
    ((List.range n).map fun v => c * (f v - 1)).sum = c * (((List.range n).map f).sum - n) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.add_zero]
    rw [show ((m + 1 : Nat) : Int) = (m : Int) + 1 by omega]
    rw [Int.mul_sub, Int.mul_sub, Int.mul_sub, Int.mul_add, Int.mul_add, Int.mul_one]
    omega

theorem countP_mem (n : Nat) (e : List Nat) (he : e.Nodup) (hlt : ∀ v ∈ e, v < n) :
    (List.range n).countP (fun v => decide (v ∈ e)) = e.length := by
  rw [List.countP_eq_length_filter]
  apply List.Perm.length_eq
  apply (List.perm_ext_iff_of_nodup ((List.nodup_range).filter _) he).mpr
  intro v
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hlt v h, h⟩⟩

/-! ## The refutation -/

theorem pm_ns (p n Δ : Nat) (c : Int) (H : List (List Nat))
    (hH : ∀ e ∈ H, e.Nodup ∧ (∀ v ∈ e, v < n) ∧ (p : Int) ∣ (e.length : Int))
    (hc : (-(c * n)) % (p : Int) = 1 % (p : Int))
    (hΔ : ∀ v, v < n → (incH H v).length ≤ Δ) (h2 : 2 ≤ Δ) :
    Nonempty (NSRefutation p (PM n H) Δ) := by
  have hB : ∀ v, (PMblock H v).length = (blk H c v).length := by
    intro v; simp [PMblock, blk]
  have hBj : ∀ v j, j < (blk H c v).length → (PMblock H v).getD j [] = ((blk H c v).getD j ([], [])).1 := by
    intro v j hj
    have hj' : j < (PMblock H v).length := (hB v) ▸ hj
    simp only [List.getD, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj', Option.getD_some]
    cases j with
    | zero => simp [PMblock, blk]
    | succ j => simp [PMblock, blk]
  -- facts about the rows of `blk`
  have rows : ∀ v, ∀ r ∈ blk H c v, ∀ t ∈ r.2, (∀ x ∈ t.1, x ∈ incH H v) ∧
      (∀ a b : Nat → Bool, (∀ x ∈ t.1, a x = b x) → t.2 a = t.2 b) ∧
      t.1.length + r.1.length ≤ (incH H v).length := by
    intro v r hr t ht
    simp only [blk, List.mem_cons, List.mem_map] at hr
    rcases hr with rfl | ⟨q, hq, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      subst ht
      refine ⟨by simp, fun _ _ _ => rfl, by simp⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      subst ht
      obtain ⟨h1, h2, h3, _⟩ := pairsW_lens _ q hq
      refine ⟨h3, ?_, by show q.2.length + q.1.length ≤ _; omega⟩
      intro a b hab
      simp only [prodNot]
      congr 1; congr 1
      apply List.map_congr_left
      intro w hw; simp [ind, hab w hw]
  have getD_mem : ∀ v j, j < (blk H c v).length → (blk H c v).getD j ([], []) ∈ blk H c v := by
    intro v j hj
    simp only [List.getD, List.getElem?_eq_getElem hj, Option.getD_some]
    exact List.getElem_mem hj
  apply local_ns_blocks p n Δ (PMblock H) (fun v j => ((blk H c v).getD j ([], [])).2)
  · intro v _ j hj t ht a b h1 _
    rw [hB] at hj
    exact (rows v _ (getD_mem v j hj) t ht).2.1 a b h1
  · intro v hv j hj t ht
    rw [hB] at hj
    rw [hBj v j hj]
    have := (rows v _ (getD_mem v j hj) t ht).2.2
    have := hΔ v hv
    omega
  · intro v hv j hj
    rw [hB] at hj
    rw [hBj v j hj]
    simp only [blk] at hj ⊢
    cases j with
    | zero => simpa using hΔ v hv
    | succ j =>
      simp only [List.length_cons, List.length_map] at hj
      have hj' : j < (pairsW (incH H v)).length := by omega
      simp only [List.getD, List.getElem?_cons_succ, List.getElem?_map,
        List.getElem?_eq_getElem hj', Option.map_some, Option.getD_some]
      rw [(pairsW_lens _ _ (List.getElem_mem hj')).1]
      exact h2
  · intro a
    have e1 : ∀ v, ((List.range (PMblock H v).length).map fun j =>
        ((((blk H c v).getD j ([], [])).2.map fun t => t.2 a).sum) *
          (clausePoly ((PMblock H v).getD j [])).eval a).sum = c * (((incH H v).map (ind a)).sum - 1) := by
      intro v
      rw [← blk_sum H c v a, hB, ← range_map_getD (blk H c v) ([], [])]
      congr 1
      apply List.map_congr_left
      intro j hj
      rw [hBj v j (List.mem_range.mp hj)]
    simp only [e1]
    -- `∑_v c (S_v - 1) = c (∑_e |e| x_e - n)`
    rw [sum_c_sub]
    have e3 : ((List.range n).map fun v => ((incH H v).map (ind a)).sum).sum =
        ((List.range H.length).map fun i => ind a i * ((H.getD i []).length : Int)).sum := by
      unfold incH
      rw [sum_filter_swap]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hi := List.mem_range.mp hi
      have hmem : H.getD i [] ∈ H := by
        simp only [List.getD, List.getElem?_eq_getElem hi, Option.getD_some]
        exact List.getElem_mem hi
      obtain ⟨hnd, hlt, _⟩ := hH _ hmem
      rw [countP_mem n _ hnd hlt]
    have e4 : (p : Int) ∣ ((List.range H.length).map fun i => ind a i * ((H.getD i []).length : Int)).sum := by
      apply dvd_sum_map
      intro i hi
      have hi := List.mem_range.mp hi
      have hmem : H.getD i [] ∈ H := by
        simp only [List.getD, List.getElem?_eq_getElem hi, Option.getD_some]
        exact List.getElem_mem hi
      exact Int.dvd_trans (hH _ hmem).2.2 (Int.dvd_mul_left _ _)
    rw [e3]
    obtain ⟨d, hd⟩ := e4
    rw [hd, ← hc, Int.mul_sub]
    rw [show c * (↑p * d) - c * ↑n = -(c * ↑n) + ↑p * (c * d) by
      rw [← Int.mul_assoc, Int.mul_comm c, Int.mul_assoc]; omega]
    exact Int.add_mul_emod_self_left _ _ _

/-- A Nullstellensatz refutation modulo `p ≥ 2` certifies unsatisfiability. -/
theorem ns_sound {p : Nat} (hp : 2 ≤ p) {F : CNF Nat} {D : Nat} (R : NSRefutation p F D)
    (a : Nat → Bool) : ∃ C ∈ F, Clause.eval a C = false := by
  apply Classical.byContradiction
  intro hno
  have h := R.identity a
  have e : ((List.range F.length).map fun i => (R.g i).eval a * (clausePoly (F.getD i [])).eval a)
      = (List.range F.length).map fun _ => (0 : Int) := by
    apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    have hmem : F.getD i [] ∈ F := by
      simp only [List.getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact List.getElem_mem hi
    have : Clause.eval a (F.getD i []) = true := by
      cases hc : Clause.eval a (F.getD i [])
      · exact absurd ⟨_, hmem, hc⟩ hno
      · rfl
    rw [clausePoly_eval, this]; simp
  rw [e, sum_zero] at h
  have h1 : (1 : Int) % (p : Int) = 1 := Int.emod_eq_of_lt (by omega) (by omega)
  rw [h1] at h
  simp at h

/-- `3`-uniform hypergraphs on `n` vertices with `3 ∤ n` and maximum degree `≤ Δ` (`Δ ≥ 2`): the
perfect-matching CNF has a degree-`Δ` Nullstellensatz refutation over `F_3`, so it is
unsatisfiable. -/
theorem pm3_ns (n Δ : Nat) (H : List (List Nat))
    (hH : ∀ e ∈ H, e.Nodup ∧ (∀ v ∈ e, v < n) ∧ e.length = 3) (hn : n % 3 ≠ 0)
    (hΔ : ∀ v, v < n → (incH H v).length ≤ Δ) (h2 : 2 ≤ Δ) :
    Nonempty (NSRefutation 3 (PM n H) Δ) ∧ ∀ a : Nat → Bool, ∃ C ∈ PM n H, Clause.eval a C = false := by
  have hR : Nonempty (NSRefutation 3 (PM n H) Δ) := by
    apply pm_ns 3 n Δ (if n % 3 = 1 then -1 else 1) H
    · intro e he
      obtain ⟨h1, h2, h3⟩ := hH e he
      exact ⟨h1, h2, by rw [h3]; exact Int.dvd_refl _⟩
    · split <;> omega
    · exact hΔ
    · exact h2
  obtain ⟨R⟩ := hR
  exact ⟨⟨R⟩, fun a => ns_sound (by omega) R a⟩

end Programme.«20261024-1633-proof-complexity».PMNS

#print axioms Programme.«20261024-1633-proof-complexity».PMNS.pm_ns
#print axioms Programme.«20261024-1633-proof-complexity».PMNS.pm3_ns
