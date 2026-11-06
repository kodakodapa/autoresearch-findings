/-!
# A valued switching lemma for clique indicators (no weight bound)

The approximation step for monotone real formulas on graphs, without sunflowers and without any
bound on the range of gate values. An approximator is a list of entries `(S, v)`: a vertex set
`S` (the clique indicator of `S`) with an integer value `v`. On a positive test (a clique `K`) the
entry is *on* when `S ⊆ K`; on a negative test (a colouring `c`) when `S` is rainbow.

`vswitch`: any such list `Pr` with sets of size `≤ d` can be replaced by a list `D` of
`≤ (4s²+1)^b` entries with sets of size `≤ 2b` so that, for **every** threshold `θ` at once:
* on a clique `K`: an entry of `Pr` of value `≥ θ` on `K` gives one of `D`, unless `K` contains
  one of `≤ (4s²)^b` sets of `≥ b` vertices (`Ed`);
* on a colouring `c`: an entry of `D` of value `≥ θ` on `c` gives one of `Pr`, unless `c` is
  constant on the classes of one of `≤ (d²)^s` merge lists with `s` merges each (`Er`).

Proof: a DNF→CNF hitting tree (`t1`, clauses are merge lists `σ`, branching on a monochromatic pair
of a maximum-value entry not yet hit) and a CNF→DNF tree (`t2`, branching on a pair of one class of
a minimum-weight clause not yet hit). Choosing the maximum (resp. minimum) makes one tree serve all
thresholds; this is what removes the dependence on the number of distinct values.
-/

namespace Programme.«20261025-0459b-proof-complexity».VSwitch

/-- Representative of `v` under the merge list `σ` (pairs `(z, r)`: `z` was merged into `r`). -/
def rho : List (Nat × Nat) → Nat → Nat
  | [], v => v
  | e :: σ, v => if v = e.1 then e.2 else rho σ v

/-- Two distinct members of `A` have the same representative. -/
def hit (σ : List (Nat × Nat)) (A : List Nat) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ rho σ a = rho σ b

/-- The colouring `c` is constant on every merged pair. -/
def cons (c : Nat → Nat) (σ : List (Nat × Nat)) : Prop := ∀ e ∈ σ, c e.1 = c e.2

/-- `A` is rainbow under `c`. -/
def rb (c : Nat → Nat) (A : List Nat) : Prop := ∀ a ∈ A, ∀ b ∈ A, a ≠ b → c a ≠ c b

/-- Merge representative `y` into representative `x`. -/
def step (σ : List (Nat × Nat)) (x y : Nat) : List (Nat × Nat) :=
  (y, x) :: σ.map fun e => (e.1, if e.2 = y then x else e.2)

/-- Merged vertices are distinct and never a representative. -/
def Valid (σ : List (Nat × Nat)) : Prop :=
  (σ.map Prod.fst).Nodup ∧ ∀ e ∈ σ, ∀ e' ∈ σ, e.1 ≠ e'.2

/-- All vertices mentioned by `σ`. -/
def supp (σ : List (Nat × Nat)) : List Nat := σ.flatMap fun e => [e.1, e.2]

theorem supp_length (σ : List (Nat × Nat)) : (supp σ).length = 2 * σ.length := by
  induction σ with
  | nil => rfl
  | cons e σ ih =>
    have : supp (e :: σ) = [e.1, e.2] ++ supp σ := by simp [supp]
    rw [this, List.length_append, ih]; simp; omega

theorem mem_supp {σ : List (Nat × Nat)} {e : Nat × Nat} (he : e ∈ σ) :
    e.1 ∈ supp σ ∧ e.2 ∈ supp σ := by
  unfold supp; simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨⟨e, he, Or.inl rfl⟩, ⟨e, he, Or.inr rfl⟩⟩

theorem cons_rho {c : Nat → Nat} : ∀ {σ : List (Nat × Nat)}, cons c σ → ∀ v, c (rho σ v) = c v
  | [], _, v => rfl
  | e :: σ, h, v => by
    unfold rho
    split
    · rename_i hv; subst hv; exact (h e List.mem_cons_self).symm
    · exact cons_rho (fun e' he' => h e' (List.mem_cons_of_mem _ he')) v

theorem cons_step {c : Nat → Nat} {σ : List (Nat × Nat)} {x y : Nat} (h : cons c σ)
    (hxy : c x = c y) : cons c (step σ x y) := by
  intro e he
  simp only [step, List.mem_cons, List.mem_map] at he
  rcases he with rfl | ⟨e', he', rfl⟩
  · exact hxy.symm
  · simp only
    split
    · rename_i h2; rw [h e' he', h2, hxy]
    · exact h e' he'

theorem hit_not_rb {c : Nat → Nat} {σ : List (Nat × Nat)} {Q : List Nat} (hc : cons c σ)
    (hh : hit σ Q) : ¬ rb c Q := by
  obtain ⟨a, ha, b, hb, hab, he⟩ := hh
  intro hr
  apply hr a ha b hb hab
  rw [← cons_rho hc a, ← cons_rho hc b, he]

theorem hit_mono {σ : List (Nat × Nat)} {A B : List Nat} (hAB : ∀ x ∈ A, x ∈ B) (h : hit σ A) :
    hit σ B := by
  obtain ⟨a, ha, b, hb, hab, he⟩ := h
  exact ⟨a, hAB a ha, b, hAB b hb, hab, he⟩

theorem rho_cases : ∀ (σ : List (Nat × Nat)) (v : Nat),
    (v ∉ σ.map Prod.fst ∧ rho σ v = v) ∨ ∃ e ∈ σ, e.1 = v ∧ rho σ v = e.2
  | [], v => Or.inl ⟨by simp, rfl⟩
  | e :: σ, v => by
    unfold rho
    by_cases hv : v = e.1
    · simp only [hv, ite_true]; exact Or.inr ⟨e, List.mem_cons_self, rfl, rfl⟩
    · simp only [hv, ite_false]
      rcases rho_cases σ v with ⟨h1, h2⟩ | ⟨e', he', h1, h2⟩
      · left; refine ⟨?_, h2⟩
        simp only [List.map_cons, List.mem_cons, not_or]; exact ⟨hv, h1⟩
      · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', h1, h2⟩

theorem rho_notdom {σ : List (Nat × Nat)} (hv : Valid σ) (v : Nat) :
    rho σ v ∉ σ.map Prod.fst := by
  rcases rho_cases σ v with ⟨h1, h2⟩ | ⟨e, he, _, h2⟩
  · rw [h2]; exact h1
  · rw [h2]; intro hm
    obtain ⟨e', he', h⟩ := List.mem_map.1 hm
    exact hv.2 e' he' e he h

theorem rho_lt {σ : List (Nat × Nat)} {m : Nat} (hr : ∀ e ∈ σ, e.1 < m ∧ e.2 < m) {v : Nat}
    (hv : v < m) : rho σ v < m := by
  rcases rho_cases σ v with ⟨_, h2⟩ | ⟨e, he, _, h2⟩
  · rw [h2]; exact hv
  · rw [h2]; exact (hr e he).2

theorem rho_supp {σ : List (Nat × Nat)} {a b : Nat} (hab : a ≠ b) (he : rho σ a = rho σ b) :
    a ∈ supp σ ∧ b ∈ supp σ := by
  rcases rho_cases σ a with ⟨_, ha⟩ | ⟨e, hem, h1, h2⟩ <;>
    rcases rho_cases σ b with ⟨_, hb⟩ | ⟨e', hem', h1', h2'⟩
  · exact absurd (by rw [← ha, he, hb]) hab
  · refine ⟨?_, h1' ▸ (mem_supp hem').1⟩
    have : a = e'.2 := by rw [← ha, he, h2']
    rw [this]; exact (mem_supp hem').2
  · refine ⟨h1 ▸ (mem_supp hem).1, ?_⟩
    have : b = e.2 := by rw [← hb, ← he, h2]
    rw [this]; exact (mem_supp hem).2
  · exact ⟨h1 ▸ (mem_supp hem).1, h1' ▸ (mem_supp hem').1⟩

theorem step_fst (σ : List (Nat × Nat)) (x y : Nat) :
    (step σ x y).map Prod.fst = y :: σ.map Prod.fst := by
  simp only [step, List.map_cons, List.map_map]; rfl

theorem valid_step {σ : List (Nat × Nat)} (hv : Valid σ) {x y : Nat}
    (hx : x ∉ σ.map Prod.fst) (hy : y ∉ σ.map Prod.fst) (hxy : x ≠ y) : Valid (step σ x y) := by
  refine ⟨?_, ?_⟩
  · rw [step_fst]; exact List.nodup_cons.2 ⟨hy, hv.1⟩
  · intro e he e' he'
    have hfst : e.1 ∈ (step σ x y).map Prod.fst := List.mem_map_of_mem he
    rw [step_fst, List.mem_cons] at hfst
    simp only [step, List.mem_cons, List.mem_map] at he'
    rcases he' with rfl | ⟨f, hf, rfl⟩
    · simp only
      rcases hfst with h | h
      · rw [h]; exact Ne.symm hxy
      · intro e2; rw [e2] at h; exact hx h
    · simp only
      split
      · rcases hfst with h | h
        · rw [h]; exact Ne.symm hxy
        · intro e2; rw [e2] at h; exact hx h
      · rename_i hfy
        rcases hfst with h | h
        · rw [h]; exact Ne.symm hfy
        · obtain ⟨g, hg, hge⟩ := List.mem_map.1 h
          rw [← hge]; exact hv.2 g hg f hf

theorem step_range {σ : List (Nat × Nat)} {m x y : Nat} (hr : ∀ e ∈ σ, e.1 < m ∧ e.2 < m)
    (hx : x < m) (hy : y < m) : ∀ e ∈ step σ x y, e.1 < m ∧ e.2 < m := by
  intro e he
  simp only [step, List.mem_cons, List.mem_map] at he
  rcases he with rfl | ⟨f, hf, rfl⟩
  · exact ⟨hy, hx⟩
  · simp only; refine ⟨(hr f hf).1, ?_⟩; split
    · exact hx
    · exact (hr f hf).2

theorem step_length (σ : List (Nat × Nat)) (x y : Nat) :
    (step σ x y).length = σ.length + 1 := by simp [step]

/-! ## Finite choices -/

theorem exists_max {α : Type} (L : List α) (P : α → Prop) (f : α → Int) :
    (∃ x ∈ L, P x) → ∃ x ∈ L, P x ∧ ∀ y ∈ L, P y → f y ≤ f x := by
  induction L with
  | nil => intro h; simp at h
  | cons a L ih =>
    intro h
    by_cases hL : ∃ x ∈ L, P x
    · obtain ⟨x, hx, hPx, hmax⟩ := ih hL
      by_cases hPa : P a ∧ f x ≤ f a
      · refine ⟨a, List.mem_cons_self, hPa.1, fun y hy hPy => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact Int.le_refl _
        · exact Int.le_trans (hmax y hy hPy) hPa.2
      · refine ⟨x, List.mem_cons_of_mem _ hx, hPx, fun y hy hPy => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · apply Classical.byContradiction; intro hn; exact hPa ⟨hPy, by omega⟩
        · exact hmax y hy hPy
    · obtain ⟨x, hx, hPx⟩ := h
      rcases List.mem_cons.1 hx with rfl | hx
      · refine ⟨x, List.mem_cons_self, hPx, fun y hy hPy => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact Int.le_refl _
        · exact absurd ⟨y, hy, hPy⟩ hL
      · exact absurd ⟨x, hx, hPx⟩ hL

/-- Upward-closed predicates on `Int` form a chain, so a finite family has a smallest one. -/
theorem exists_min_chain {α : Type} (L : List α) (P : α → Prop) (g : α → Int → Prop)
    (hup : ∀ x θ θ', θ ≤ θ' → g x θ → g x θ') :
    (∃ x ∈ L, P x) → ∃ x ∈ L, P x ∧ ∀ y ∈ L, P y → ∀ θ, g y θ → g x θ := by
  induction L with
  | nil => intro h; simp at h
  | cons a L ih =>
    intro h
    by_cases hL : ∃ x ∈ L, P x
    · obtain ⟨x, hx, hPx, hmin⟩ := ih hL
      by_cases hPa : P a ∧ ¬ ∀ θ, g a θ → g x θ
      · obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀, g a θ₀ ∧ ¬ g x θ₀ :=
          Classical.byContradiction fun hn => hPa.2 fun θ hθ =>
            Classical.byContradiction fun hx' => hn ⟨θ, hθ, hx'⟩
        have hxa : ∀ θ, g x θ → g a θ := by
          intro θ hθ
          by_cases hle : θ ≤ θ₀
          · exact absurd (hup x θ θ₀ hle hθ) hθ₀.2
          · exact hup a θ₀ θ (by omega) hθ₀.1
        refine ⟨a, List.mem_cons_self, hPa.1, fun y hy hPy θ hθ => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hθ
        · exact hxa θ (hmin y hy hPy θ hθ)
      · refine ⟨x, List.mem_cons_of_mem _ hx, hPx, fun y hy hPy θ hθ => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · apply Classical.byContradiction; intro hn
          exact hPa ⟨hPy, fun h' => hn (h' θ hθ)⟩
        · exact hmin y hy hPy θ hθ
    · obtain ⟨x, hx, hPx⟩ := h
      rcases List.mem_cons.1 hx with rfl | hx
      · refine ⟨x, List.mem_cons_self, hPx, fun y hy hPy θ hθ => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hθ
        · exact absurd ⟨y, hy, hPy⟩ hL
      · exact absurd ⟨x, hx, hPx⟩ hL

theorem Nat.pos_pow_of_pos' {b : Nat} (n : Nat) (h : 0 < b) : 0 < b ^ n := Nat.pow_pos h

theorem sum_le {β : Type} (g : β → Nat) (L : List β) (k : Nat) (h : ∀ x ∈ L, g x ≤ k) :
    (L.map g).sum ≤ L.length * k := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have := h a List.mem_cons_self
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

/-- All ordered pairs of members of `A` satisfying `p`. -/
def pairs (A : List Nat) (p : Nat → Nat → Bool) : List (Nat × Nat) :=
  (A.flatMap fun a => A.map fun b => (a, b)).filter fun q => p q.1 q.2

theorem pairs_length (A : List Nat) (p : Nat → Nat → Bool) :
    (pairs A p).length ≤ A.length * A.length := by
  unfold pairs
  refine Nat.le_trans (List.length_filter_le _ _) ?_
  rw [List.length_flatMap]
  have := sum_le (fun a => (A.map fun b => (a, b)).length) A A.length (by intro x _; simp)
  exact this

theorem mem_pairs {A : List Nat} {p : Nat → Nat → Bool} {a b : Nat} (ha : a ∈ A) (hb : b ∈ A)
    (h : p a b = true) : (a, b) ∈ pairs A p := by
  unfold pairs
  rw [List.mem_filter]
  refine ⟨List.mem_flatMap.2 ⟨a, ha, List.mem_map.2 ⟨b, hb, rfl⟩⟩, h⟩

theorem pairs_prop {A : List Nat} {p : Nat → Nat → Bool} {q : Nat × Nat} (h : q ∈ pairs A p) :
    p q.1 q.2 = true := (List.mem_filter.1 h).2

/-- A choice of sublists for each pair, with a property guaranteed on members. -/
theorem choose_fam {γ : Type} (ps : List (Nat × Nat)) (Prp : Nat × Nat → γ → γ → Prop)
    (h : ∀ q ∈ ps, ∃ N E, Prp q N E) (dflt : γ) :
    ∃ Nf Ef : Nat × Nat → γ, ∀ q ∈ ps, Prp q (Nf q) (Ef q) := by
  have : ∀ q : Nat × Nat, ∃ N E, q ∈ ps → Prp q N E := by
    intro q
    by_cases hq : q ∈ ps
    · obtain ⟨N, E, hp⟩ := h q hq; exact ⟨N, E, fun _ => hp⟩
    · exact ⟨dflt, dflt, fun h => absurd h hq⟩
  exact ⟨fun q => Classical.choose (this q),
    fun q => Classical.choose (Classical.choose_spec (this q)),
    fun q hq => Classical.choose_spec (Classical.choose_spec (this q)) hq⟩

/-! ## The DNF→CNF tree -/

/-- **DNF→CNF tree.** From a node `σ` with budget `j`: nodes `N` (clauses) and dead ends `E` (rise
events, `≤ (d²)^j`, each with exactly `j` more merges). Walk: if `c` is constant on `σ` and every
node `c` is constant on leaves some entry of value `≥ θ` unhit, then some entry of value `≥ θ` is
rainbow under `c`, or `c` is constant on a dead end. -/
theorem t1 (m d : Nat) (Pr : List (List Nat × Int))
    (hPr : ∀ e ∈ Pr, e.1.length ≤ d ∧ ∀ x ∈ e.1, x < m) :
    ∀ (j : Nat) (σ : List (Nat × Nat)), Valid σ → (∀ e ∈ σ, e.1 < m ∧ e.2 < m) →
    ∃ N E : List (List (Nat × Nat)), σ ∈ N ∧ E.length ≤ (d * d) ^ j ∧
      (∀ τ ∈ N, τ.length ≤ σ.length + j ∧ ∀ e ∈ τ, e.1 < m ∧ e.2 < m) ∧
      (∀ τ ∈ E, Valid τ ∧ (∀ e ∈ τ, e.1 < m ∧ e.2 < m) ∧ τ.length = σ.length + j) ∧
      ∀ (c : Nat → Nat) (θ : Int), cons c σ →
        (∀ τ ∈ N, cons c τ → ∃ e ∈ Pr, θ ≤ e.2 ∧ ¬ hit τ e.1) →
        (∃ e ∈ Pr, θ ≤ e.2 ∧ rb c e.1) ∨ ∃ τ ∈ E, cons c τ := by
  intro j
  induction j with
  | zero =>
    intro σ hv hr
    refine ⟨[σ], [σ], List.mem_singleton_self _, by simp, ?_, ?_, ?_⟩
    · intro τ hτ; rw [List.mem_singleton] at hτ; subst hτ; exact ⟨by omega, hr⟩
    · intro τ hτ; rw [List.mem_singleton] at hτ; subst hτ; exact ⟨hv, hr, by omega⟩
    · intro c θ hc _; exact Or.inr ⟨σ, List.mem_singleton_self _, hc⟩
  | succ j ih =>
    intro σ hv hr
    by_cases hex : ∃ e ∈ Pr, ¬ hit σ e.1
    · obtain ⟨es, hes, hun, hmax⟩ := exists_max Pr (fun e => ¬ hit σ e.1) (fun e => e.2) hex
      let ps := pairs es.1 fun a b => decide (rho σ a ≠ rho σ b)
      have hps : ∀ q ∈ ps, ∃ N E : List (List (Nat × Nat)),
          (fun q N E => step σ (rho σ q.1) (rho σ q.2) ∈ N ∧ E.length ≤ (d * d) ^ j ∧
            (∀ τ ∈ N, τ.length ≤ (step σ (rho σ q.1) (rho σ q.2)).length + j ∧
              ∀ e ∈ τ, e.1 < m ∧ e.2 < m) ∧
            (∀ τ ∈ E, Valid τ ∧ (∀ e ∈ τ, e.1 < m ∧ e.2 < m) ∧
              τ.length = (step σ (rho σ q.1) (rho σ q.2)).length + j) ∧
            ∀ (c : Nat → Nat) (θ : Int), cons c (step σ (rho σ q.1) (rho σ q.2)) →
              (∀ τ ∈ N, cons c τ → ∃ e ∈ Pr, θ ≤ e.2 ∧ ¬ hit τ e.1) →
              (∃ e ∈ Pr, θ ≤ e.2 ∧ rb c e.1) ∨ ∃ τ ∈ E, cons c τ) q N E := by
        intro q hq
        have hne := of_decide_eq_true (pairs_prop hq)
        have hq1 : q.1 ∈ es.1 := (List.mem_flatMap.1 (List.mem_filter.1 hq).1).elim
          fun a ⟨ha, hb⟩ => by obtain ⟨b, _, hb⟩ := List.mem_map.1 hb; rw [← hb]; exact ha
        have hq2 : q.2 ∈ es.1 := (List.mem_flatMap.1 (List.mem_filter.1 hq).1).elim
          fun a ⟨_, hb⟩ => by obtain ⟨b, hb', hb⟩ := List.mem_map.1 hb; rw [← hb]; exact hb'
        exact ih _ (valid_step hv (rho_notdom hv _) (rho_notdom hv _) hne)
          (step_range hr (rho_lt hr ((hPr es hes).2 _ hq1)) (rho_lt hr ((hPr es hes).2 _ hq2)))
      obtain ⟨Nf, Ef, hf⟩ := choose_fam ps _ hps []
      refine ⟨σ :: ps.flatMap Nf, ps.flatMap Ef, List.mem_cons_self, ?_, ?_, ?_, ?_⟩
      · rw [List.length_flatMap]
        calc (ps.map fun q => (Ef q).length).sum ≤ ps.length * (d * d) ^ j :=
              sum_le _ ps _ (fun q hq => (hf q hq).2.1)
          _ ≤ (d * d) * (d * d) ^ j := by
              apply Nat.mul_le_mul_right
              refine Nat.le_trans (pairs_length _ _) ?_
              exact Nat.mul_le_mul (hPr es hes).1 (hPr es hes).1
          _ = (d * d) ^ (j + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      · intro τ hτ
        rcases List.mem_cons.1 hτ with rfl | hτ
        · exact ⟨by omega, hr⟩
        · obtain ⟨q, hq, hτ⟩ := List.mem_flatMap.1 hτ
          have := (hf q hq).2.2.1 τ hτ
          rw [step_length] at this; exact ⟨by omega, this.2⟩
      · intro τ hτ
        obtain ⟨q, hq, hτ⟩ := List.mem_flatMap.1 hτ
        have := (hf q hq).2.2.2.1 τ hτ
        rw [step_length] at this; exact ⟨this.1, this.2.1, by omega⟩
      · intro c θ hc hall
        obtain ⟨e, he, hθe, hue⟩ := hall σ List.mem_cons_self hc
        have hθ : θ ≤ es.2 := Int.le_trans hθe (hmax e he hue)
        by_cases hrb : rb c es.1
        · exact Or.inl ⟨es, hes, hθ, hrb⟩
        · obtain ⟨a, ha, b, hb, hab, hcab⟩ : ∃ a ∈ es.1, ∃ b ∈ es.1, a ≠ b ∧ c a = c b := by
            apply Classical.byContradiction; intro hn; apply hrb
            intro a ha b hb hab hcab; exact hn ⟨a, ha, b, hb, hab, hcab⟩
          have hrab : rho σ a ≠ rho σ b := fun h => hun ⟨a, ha, b, hb, hab, h⟩
          have hq : (a, b) ∈ ps := mem_pairs ha hb (decide_eq_true hrab)
          have hc' : cons c (step σ (rho σ a) (rho σ b)) :=
            cons_step hc (by rw [cons_rho hc, cons_rho hc, hcab])
          rcases (hf (a, b) hq).2.2.2.2 c θ hc' (fun τ hτ => hall τ
              (List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨(a, b), hq, hτ⟩))) with h | ⟨τ, hτ, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨τ, List.mem_flatMap.2 ⟨(a, b), hq, hτ⟩, h⟩
    · refine ⟨[σ], [], List.mem_singleton_self _, by simp, ?_, by simp, ?_⟩
      · intro τ hτ; rw [List.mem_singleton] at hτ; subst hτ; exact ⟨by omega, hr⟩
      · intro c θ hc hall
        obtain ⟨e, he, _, hue⟩ := hall σ (List.mem_singleton_self _) hc
        exact absurd ⟨e, he, hue⟩ hex

/-! ## The CNF→DNF tree -/

/-- Add `x` to `Q` unless present. -/
def add (x : Nat) (Q : List Nat) : List Nat := if x ∈ Q then Q else x :: Q

theorem mem_add {x y : Nat} {Q : List Nat} : y ∈ add x Q ↔ y = x ∨ y ∈ Q := by
  unfold add; split
  · rename_i h; constructor
    · exact Or.inr
    · rintro (rfl | h'); exact h; exact h'
  · simp

theorem add_nodup {x : Nat} {Q : List Nat} (h : Q.Nodup) : (add x Q).Nodup := by
  unfold add; split
  · exact h
  · rename_i hx; exact List.nodup_cons.2 ⟨hx, h⟩

theorem add_length (x : Nat) (Q : List Nat) :
    Q.length ≤ (add x Q).length ∧ (add x Q).length ≤ Q.length + 1 ∧
      (x ∉ Q → (add x Q).length = Q.length + 1) := by
  unfold add; split
  · rename_i h; exact ⟨by omega, by omega, fun h' => absurd h h'⟩
  · simp

/-- Add both endpoints of `q`. -/
def ext (Q : List Nat) (q : Nat × Nat) : List Nat := add q.2 (add q.1 Q)

theorem supp_lt {σ : List (Nat × Nat)} {m : Nat} (hr : ∀ e ∈ σ, e.1 < m ∧ e.2 < m) :
    ∀ x ∈ supp σ, x < m := by
  intro x hx
  unfold supp at hx
  simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨e, he, rfl | rfl⟩ := hx
  · exact (hr e he).1
  · exact (hr e he).2

/-- **CNF→DNF tree.** Clauses are the merge lists `N1` (each `≤ s` merges); `low σ θ` says clause
`σ` is present at threshold `θ` (upward closed in `θ`). From node `Q` with budget `j`: nodes `N`
(monomials, `≤ (4s²+1)^j`) and dead ends `E` (`≤ (4s²)^j`, each with `≥ j` new vertices). Walk:
if `K ⊇ Q` hits every clause present at `θ`, then some node `R ⊆ K` hits every clause present at
`θ`, or `K` contains a dead end. -/
theorem t2 (m s : Nat) (N1 : List (List (Nat × Nat)))
    (hN1 : ∀ σ ∈ N1, σ.length ≤ s ∧ ∀ e ∈ σ, e.1 < m ∧ e.2 < m)
    (low : List (Nat × Nat) → Int → Prop) (hup : ∀ σ θ θ', θ ≤ θ' → low σ θ → low σ θ') :
    ∀ (j : Nat) (Q : List Nat), Q.Nodup → (∀ x ∈ Q, x < m) →
    ∃ N E : List (List Nat), Q ∈ N ∧ N.length ≤ (4 * s * s + 1) ^ j ∧
      E.length ≤ (4 * s * s) ^ j ∧
      (∀ R ∈ N, R.Nodup ∧ R.length ≤ Q.length + 2 * j ∧ ∀ x ∈ R, x < m) ∧
      (∀ R ∈ E, R.Nodup ∧ Q.length + j ≤ R.length ∧ ∀ x ∈ R, x < m) ∧
      ∀ (K : List Nat) (θ : Int), (∀ x ∈ Q, x ∈ K) → (∀ σ ∈ N1, low σ θ → hit σ K) →
        (∃ R ∈ N, (∀ x ∈ R, x ∈ K) ∧ ∀ σ ∈ N1, low σ θ → hit σ R) ∨
        ∃ R ∈ E, ∀ x ∈ R, x ∈ K := by
  intro j
  induction j with
  | zero =>
    intro Q hQ hQm
    refine ⟨[Q], [Q], List.mem_singleton_self _, by simp, by simp, ?_, ?_, ?_⟩
    · intro R hR; rw [List.mem_singleton] at hR; subst hR; exact ⟨hQ, by omega, hQm⟩
    · intro R hR; rw [List.mem_singleton] at hR; subst hR; exact ⟨hQ, by omega, hQm⟩
    · intro K θ hQK _
      by_cases hc : ∀ σ ∈ N1, low σ θ → hit σ Q
      · exact Or.inl ⟨Q, List.mem_singleton_self _, hQK, hc⟩
      · exact Or.inr ⟨Q, List.mem_singleton_self _, hQK⟩
  | succ j ih =>
    intro Q hQ hQm
    by_cases hex : ∃ σ ∈ N1, ¬ hit σ Q
    · obtain ⟨σs, hσs, hun, hmin⟩ := exists_min_chain N1 (fun σ => ¬ hit σ Q) low hup hex
      let ps := pairs (supp σs) fun a b => decide (a ≠ b ∧ rho σs a = rho σs b)
      have hgrow : ∀ q ∈ ps, Q.length + 1 ≤ (ext Q q).length ∧ (ext Q q).Nodup ∧
          (ext Q q).length ≤ Q.length + 2 ∧ (∀ x ∈ ext Q q, x < m) ∧
          ∀ x, x ∈ ext Q q ↔ x = q.2 ∨ x = q.1 ∨ x ∈ Q := by
        intro q hq
        have hp := of_decide_eq_true (pairs_prop hq)
        have hq1 : q.1 ∈ supp σs := (List.mem_flatMap.1 (List.mem_filter.1 hq).1).elim
          fun a ⟨ha, hb⟩ => by obtain ⟨b, _, hb⟩ := List.mem_map.1 hb; rw [← hb]; exact ha
        have hq2 : q.2 ∈ supp σs := (List.mem_flatMap.1 (List.mem_filter.1 hq).1).elim
          fun a ⟨_, hb⟩ => by obtain ⟨b, hb', hb⟩ := List.mem_map.1 hb; rw [← hb]; exact hb'
        have hnb : ¬ (q.1 ∈ Q ∧ q.2 ∈ Q) := fun h => hun ⟨q.1, h.1, q.2, h.2, hp.1, hp.2⟩
        have l1 := add_length q.1 Q
        have l2 := add_length q.2 (add q.1 Q)
        have hmem : ∀ x, x ∈ ext Q q ↔ x = q.2 ∨ x = q.1 ∨ x ∈ Q := by
          intro x; unfold ext; rw [mem_add, mem_add]
        refine ⟨?_, add_nodup (add_nodup hQ), by unfold ext; omega, ?_, hmem⟩
        · unfold ext
          by_cases h1 : q.1 ∈ Q
          · have h2 : q.2 ∉ add q.1 Q := by
              rw [mem_add]; rintro (h | h)
              · exact hp.1 h.symm
              · exact hnb ⟨h1, h⟩
            have := l2.2.2 h2; have := l1.1; omega
          · have := l1.2.2 h1; have := l2.1; omega
        · have hsl := supp_lt (hN1 σs hσs).2
          intro x hx; rcases (hmem x).1 hx with rfl | rfl | hx
          · exact hsl _ hq2
          · exact hsl _ hq1
          · exact hQm x hx
      have hps : ∀ q ∈ ps, ∃ N E : List (List Nat),
          (fun q N E => ext Q q ∈ N ∧ N.length ≤ (4 * s * s + 1) ^ j ∧
            E.length ≤ (4 * s * s) ^ j ∧
            (∀ R ∈ N, R.Nodup ∧ R.length ≤ (ext Q q).length + 2 * j ∧ ∀ x ∈ R, x < m) ∧
            (∀ R ∈ E, R.Nodup ∧ (ext Q q).length + j ≤ R.length ∧ ∀ x ∈ R, x < m) ∧
            ∀ (K : List Nat) (θ : Int), (∀ x ∈ ext Q q, x ∈ K) →
              (∀ σ ∈ N1, low σ θ → hit σ K) →
              (∃ R ∈ N, (∀ x ∈ R, x ∈ K) ∧ ∀ σ ∈ N1, low σ θ → hit σ R) ∨
              ∃ R ∈ E, ∀ x ∈ R, x ∈ K) q N E := by
        intro q hq
        exact ih (ext Q q) (hgrow q hq).2.1 (hgrow q hq).2.2.2.1
      obtain ⟨Nf, Ef, hf⟩ := choose_fam ps _ hps []
      have hpsl : ps.length ≤ 4 * s * s := by
        refine Nat.le_trans (pairs_length _ _) ?_
        rw [supp_length]
        have := (hN1 σs hσs).1
        have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 this) (Nat.mul_le_mul_left 2 this)
        calc 2 * σs.length * (2 * σs.length) ≤ 2 * s * (2 * s) := this
          _ = 4 * s * s := by rw [Nat.mul_mul_mul_comm, Nat.mul_assoc 4]
      refine ⟨Q :: ps.flatMap Nf, ps.flatMap Ef, List.mem_cons_self, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.length_cons, List.length_flatMap]
        have := sum_le (fun q => (Nf q).length) ps _ (fun q hq => (hf q hq).2.1)
        calc (ps.map fun q => (Nf q).length).sum + 1
            ≤ ps.length * (4 * s * s + 1) ^ j + 1 := by omega
          _ ≤ (4 * s * s) * (4 * s * s + 1) ^ j + (4 * s * s + 1) ^ j := by
              have := Nat.mul_le_mul_right ((4 * s * s + 1) ^ j) hpsl
              have : 1 ≤ (4 * s * s + 1) ^ j := Nat.pos_pow_of_pos' _ (by omega)
              omega
          _ = (4 * s * s + 1) ^ (j + 1) := by rw [Nat.pow_succ, Nat.mul_succ, Nat.mul_comm]
      · rw [List.length_flatMap]
        calc (ps.map fun q => (Ef q).length).sum ≤ ps.length * (4 * s * s) ^ j :=
              sum_le _ ps _ (fun q hq => (hf q hq).2.2.1)
          _ ≤ (4 * s * s) * (4 * s * s) ^ j := Nat.mul_le_mul_right _ hpsl
          _ = (4 * s * s) ^ (j + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      · intro R hR
        rcases List.mem_cons.1 hR with rfl | hR
        · exact ⟨hQ, by omega, hQm⟩
        · obtain ⟨q, hq, hR⟩ := List.mem_flatMap.1 hR
          have := (hf q hq).2.2.2.1 R hR
          have := (hgrow q hq).2.2.1
          exact ⟨(hf q hq).2.2.2.1 R hR |>.1, by omega, (hf q hq).2.2.2.1 R hR |>.2.2⟩
      · intro R hR
        obtain ⟨q, hq, hR⟩ := List.mem_flatMap.1 hR
        have h1 := (hf q hq).2.2.2.2.1 R hR
        have := (hgrow q hq).1
        exact ⟨h1.1, by omega, h1.2.2⟩
      · intro K θ hQK hK
        by_cases hc : ∀ σ ∈ N1, low σ θ → hit σ Q
        · exact Or.inl ⟨Q, List.mem_cons_self, hQK, hc⟩
        · obtain ⟨σ, hσ, hlow, hnh⟩ : ∃ σ ∈ N1, low σ θ ∧ ¬ hit σ Q := by
            apply Classical.byContradiction; intro hn; apply hc
            intro σ hσ hl; apply Classical.byContradiction; intro hh; exact hn ⟨σ, hσ, hl, hh⟩
          have hls := hmin σ hσ hnh θ hlow
          obtain ⟨a, ha, b, hb, hab, he⟩ := hK σs hσs hls
          have hsp := rho_supp hab he
          have hq : (a, b) ∈ ps := mem_pairs hsp.1 hsp.2 (decide_eq_true ⟨hab, he⟩)
          have hext : ∀ x ∈ ext Q (a, b), x ∈ K := by
            intro x hx
            rcases ((hgrow (a, b) hq).2.2.2.2 x).1 hx with rfl | rfl | hx
            · exact hb
            · exact ha
            · exact hQK x hx
          rcases (hf (a, b) hq).2.2.2.2.2 K θ hext hK with ⟨R, hR, h⟩ | ⟨R, hR, h⟩
          · exact Or.inl ⟨R, List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨(a, b), hq, hR⟩), h⟩
          · exact Or.inr ⟨R, List.mem_flatMap.2 ⟨(a, b), hq, hR⟩, h⟩
    · refine ⟨[Q], [], List.mem_singleton_self _, ?_, by simp, ?_, by simp, ?_⟩
      · simp; exact Nat.pos_pow_of_pos' _ (by omega)
      · intro R hR; rw [List.mem_singleton] at hR; subst hR; exact ⟨hQ, by omega, hQm⟩
      · intro K θ hQK _
        refine Or.inl ⟨Q, List.mem_singleton_self _, hQK, fun σ hσ _ => ?_⟩
        apply Classical.byContradiction; intro hn; exact hex ⟨σ, hσ, hn⟩

/-! ## The valued switch -/

/-- Clause `σ` is present at threshold `θ`: it hits every entry of value `≥ θ`. -/
def low (Pr : List (List Nat × Int)) (σ : List (Nat × Nat)) (θ : Int) : Prop :=
  ∀ e ∈ Pr, θ ≤ e.2 → hit σ e.1

theorem low_up (Pr : List (List Nat × Int)) :
    ∀ σ θ θ', θ ≤ θ' → low Pr σ θ → low Pr σ θ' :=
  fun _ _ _ hle h e he hθ => h e he (Int.le_trans hle hθ)

theorem valid_nil : Valid [] := ⟨List.nodup_nil, by simp⟩

/-- **Valued switching lemma.** See the module docstring. -/
theorem vswitch (m s b d : Nat) (Pr : List (List Nat × Int))
    (hPr : ∀ e ∈ Pr, e.1.length ≤ d ∧ ∀ x ∈ e.1, x < m) :
    ∃ (D : List (List Nat × Int)) (Er : List (List (Nat × Nat))) (Ed : List (List Nat)),
      D.length ≤ (4 * s * s + 1) ^ b ∧
      (∀ e ∈ D, e.1.Nodup ∧ e.1.length ≤ 2 * b ∧ ∀ x ∈ e.1, x < m) ∧
      Er.length ≤ (d * d) ^ s ∧
      (∀ τ ∈ Er, Valid τ ∧ (∀ e ∈ τ, e.1 < m ∧ e.2 < m) ∧ τ.length = s) ∧
      Ed.length ≤ (4 * s * s) ^ b ∧
      (∀ R ∈ Ed, R.Nodup ∧ b ≤ R.length ∧ ∀ x ∈ R, x < m) ∧
      (∀ (K : List Nat) (θ : Int), (∃ e ∈ Pr, θ ≤ e.2 ∧ ∀ x ∈ e.1, x ∈ K) →
        (∃ e ∈ D, θ ≤ e.2 ∧ ∀ x ∈ e.1, x ∈ K) ∨ ∃ R ∈ Ed, ∀ x ∈ R, x ∈ K) ∧
      (∀ (c : Nat → Nat) (θ : Int), (∃ e ∈ D, θ ≤ e.2 ∧ rb c e.1) →
        (∃ e ∈ Pr, θ ≤ e.2 ∧ rb c e.1) ∨ ∃ τ ∈ Er, cons c τ) := by
  obtain ⟨N1, Er, _, hErl, hN1, hEr, walk1⟩ := t1 m d Pr hPr s [] valid_nil (by simp)
  obtain ⟨N2, Ed, _, hN2l, hEdl, hN2, hEd, walk2⟩ :=
    t2 m s N1 (fun σ hσ => ⟨by have := (hN1 σ hσ).1; simp at this; omega, (hN1 σ hσ).2⟩)
      (low Pr) (low_up Pr) b [] List.nodup_nil (by simp)
  let cond : List Nat → Int → Prop := fun Q θ => ∀ σ ∈ N1, low Pr σ θ → hit σ Q
  have hval : ∀ Q, ∃ o : Option Int, (∀ u, o = some u → cond Q u) ∧
      ∀ e ∈ Pr, cond Q e.2 → ∃ u, o = some u ∧ e.2 ≤ u := by
    intro Q
    by_cases hex : ∃ e ∈ Pr, cond Q e.2
    · obtain ⟨e, _, hc, hmax⟩ := exists_max Pr (fun e => cond Q e.2) (fun e => e.2) hex
      exact ⟨some e.2, ⟨fun u hu => by cases hu; exact hc,
        fun e' he' hc' => ⟨e.2, rfl, hmax e' he' hc'⟩⟩⟩
    · exact ⟨none, ⟨fun u hu => absurd hu (by simp), fun e he hc => absurd ⟨e, he, hc⟩ hex⟩⟩
  let val := fun Q => Classical.choose (hval Q)
  have hvs := fun Q => Classical.choose_spec (hval Q)
  let D := N2.filterMap fun Q => (val Q).map fun u => (Q, u)
  have hmemD : ∀ e ∈ D, e.1 ∈ N2 ∧ cond e.1 e.2 := by
    intro e he
    obtain ⟨Q, hQ, h⟩ := List.mem_filterMap.1 he
    cases hv : val Q with
    | none => rw [hv] at h; cases h
    | some u =>
      rw [hv] at h; cases h
      exact ⟨hQ, (hvs Q).1 u hv⟩
  have hinD : ∀ Q ∈ N2, ∀ u, val Q = some u → (Q, u) ∈ D := by
    intro Q hQ u hu
    exact List.mem_filterMap.2 ⟨Q, hQ, by rw [hu]; rfl⟩
  refine ⟨D, Er, Ed, Nat.le_trans (List.length_filterMap_le _ _) hN2l, ?_, hErl, ?_, hEdl, ?_,
    ?_, ?_⟩
  · intro e he
    have := hN2 e.1 (hmemD e he).1
    simp at this; exact ⟨this.1, by omega, this.2.2⟩
  · intro τ hτ; have := hEr τ hτ; exact ⟨this.1, this.2.1, by have := this.2.2; simp at this; exact this⟩
  · intro R hR; have := hEd R hR; simp at this; exact ⟨this.1, by omega, this.2.2⟩
  · intro K θ ⟨e, he, hθe, heK⟩
    obtain ⟨e', he', hθ', hmin⟩ :=
      exists_max Pr (fun e => θ ≤ e.2) (fun e => -e.2) ⟨e, he, hθe⟩
    have hback : ∀ σ, low Pr σ e'.2 → low Pr σ θ := by
      intro σ h y hy hθy
      exact h y hy (by have := hmin y hy hθy; omega)
    rcases walk2 K θ (by simp) (fun σ _ hl => hit_mono heK (hl e he hθe)) with
      ⟨R, hR, hRK, hc⟩ | h
    · left
      obtain ⟨u, hu, hle⟩ := (hvs R).2 e' he' (fun σ hσ hl => hc σ hσ (hback σ hl))
      exact ⟨(R, u), hinD R hR u hu, Int.le_trans hθ' hle, hRK⟩
    · exact Or.inr h
  · intro c θ ⟨e, he, hθ, hrb⟩
    have hc := (hmemD e he).2
    apply walk1 c θ (by simp [cons])
    intro τ hτ hcτ
    apply Classical.byContradiction; intro hn
    have hl : low Pr τ θ := by
      intro y hy hθy
      apply Classical.byContradiction; intro hh; exact hn ⟨y, hy, hθy, hh⟩
    exact hit_not_rb hcτ (hc τ hτ (low_up Pr τ θ e.2 hθ hl)) hrb

end Programme.«20261025-0459b-proof-complexity».VSwitch
