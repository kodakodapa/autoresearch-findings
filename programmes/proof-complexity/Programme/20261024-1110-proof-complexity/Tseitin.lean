import Programme.«20261024-1110-proof-complexity».Haken
import Programme.«20261024-1110-proof-complexity».BSWRe

/-!
# Tseitin formulas: width lower bound from edge expansion (core Lean 4)

For a graph on vertices `0..n-1` with edge list `E` (variables = edge indices `0..|E|-1`) and a
charge `χ`, `Tseitin n E χ` is the CNF which, at each vertex `v`, forbids every assignment to the
incident edges whose parity differs from `χ v` (one clause per forbidden assignment).

Theorem (Ben-Sasson–Wigderson 2001, the Tseitin width bound): if the graph is connected (every
nonempty proper vertex set has a boundary edge) and every vertex set `S` with
`n/3 < |S| ≤ 2(n/3)` has at least `e` boundary edges, then every resolution refutation (weakening
allowed) contains a clause with at least `e` distinct literals over the edge variables; and there is
no width-`(e-1)` derivation of the empty clause (`Work.BSWR.Der`). Composing with the size–width
relation (`Work.BSWR.bsw_size`) gives a size bound.

Proof. `Imp S C`: every assignment satisfying the parity constraints of all vertices in `S`
satisfies `C`. Axioms are implied by one vertex, a resolvent by the union of the sets of its
premises, and the empty clause by no set of size `≤ n/3` (a minimum such set has no boundary edge,
by the flipping argument below, contradicting connectivity). For a minimum set `S` implying `C`,
every boundary edge of `S` occurs in `C`: otherwise flip that edge in an assignment that satisfies
`S` minus the inner endpoint and falsifies `C`. The first line not implied by a set of size
`≤ n/3` is implied by a set of size `≤ 2(n/3)`; its minimum set is medium, so `C` is wide.

## Prior art and what this file adds (request R4, `brief/requests/R4.md`)
R4 found, from search snippets only (no source opened), a Lean 4 module
`Complexity/Logics/Propositional/Resolution/TseitinExpander` in cslib-community/complexitylib
(PR #667, 2026-10-24) and a resolution size–width result there. Its statements, expansion notion
and size bound are unverified, so the general theorem here (K20/K21) should be read as a probable
re-formalisation of a known Lean result, not a first one. What this file adds, as far as checked:
* the bound is stated over the same `Work.Haken.Refutation` type as Haken's PHP lower bound (K1),
  the PHP/GT upper bounds (K9, K12, K16) and the kernel-checked solver certificates (K17), so lower
  and upper bounds for several families live in one type;
* core Lean 4 only (no Mathlib, no CSLib), axioms propext, Classical.choice, Quot.sound;
* the hypotheses are exactly BSW 2001 Thm 4.4's middle-third expansion plus a cut form of
  connectivity, over an arbitrary charge, with an explicit size corollary via `Work.BSWR.bsw_size`;
* the proof measures each line by a minimum implying vertex set and needs no separate
  "medium-measure" lemma (K7).
The graph instantiations (`Work.Hypercube`, `Work.CCC`) were not found in R4's search.
-/

namespace Programme.«20261024-1110-proof-complexity».Tseitin

open Classical Programme.«20261024-1110-proof-complexity».Haken

/-! ## Generic lemmas -/

theorem exists_min (P : Nat → Prop) (h : ∃ k, P k) : ∃ k, P k ∧ ∀ j, j < k → ¬ P j := by
  obtain ⟨k, hk⟩ := h
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases h' : ∃ j, j < k ∧ P j
    · obtain ⟨j, hj, hPj⟩ := h'; exact ih j hj hPj
    · exact ⟨k, hk, fun j hj hP => h' ⟨j, hj, hP⟩⟩

theorem countP_lt {α} (l : List α) (p q : α → Bool) (hpq : ∀ x ∈ l, p x = true → q x = true)
    (x : α) (hx : x ∈ l) (hq : q x = true) (hp : p x = false) : l.countP p < l.countP q := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.countP_cons]
    have hpq' : ∀ y ∈ l, p y = true → q y = true := fun y hy => hpq y (List.mem_cons_of_mem _ hy)
    have hle := List.countP_mono_left hpq'
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [hq, hp]; omega
    · have := ih hpq' hx
      by_cases ha : p a = true
      · have := hpq a List.mem_cons_self ha; simp [ha, this]; omega
      · simp [ha]; split <;> omega

theorem countP_flatMap_ge {α β} (X : List α) (f : α → List β) (p : β → Bool) :
    X.countP (fun x => (f x).any p) ≤ (X.flatMap f).countP p := by
  induction X with
  | nil => simp
  | cons a X ih =>
    rw [List.flatMap_cons, List.countP_append, List.countP_cons]
    by_cases h : (f a).any p = true
    · have : 0 < (f a).countP p := by
        obtain ⟨y, hy, hpy⟩ := List.any_eq_true.mp h
        exact List.countP_pos_iff.mpr ⟨y, hy, hpy⟩
      simp [h]; omega
    · simp [h]; omega

/-- Flipping one variable `i` that occurs once in `L` changes the parity of `L.countP α`. -/
theorem countP_flip {L : List Nat} (hL : L.Nodup) (α : Nat → Bool) {i : Nat} (hi : i ∈ L) :
    (L.countP (fun x => if x = i then !α x else α x) + L.countP α) % 2 = 1 := by
  induction L with
  | nil => simp at hi
  | cons a L ih =>
    have ha : a ∉ L := (List.nodup_cons.mp hL).1
    have hL' : L.Nodup := (List.nodup_cons.mp hL).2
    simp only [List.countP_cons]
    by_cases hai : a = i
    · subst hai
      have e : L.countP (fun x => if x = a then !α x else α x) = L.countP α := by
        apply List.countP_congr; intro x hx
        have : x ≠ a := fun h => ha (h ▸ hx)
        simp [this]
      rw [e]; cases α a <;> simp <;> omega
    · have hi' : i ∈ L := by
        rcases List.mem_cons.mp hi with h | h
        · exact absurd h.symm hai
        · exact h
      have := ih hL' hi'
      simp only [hai, ite_false]
      split <;> omega

theorem countP_unflip {L : List Nat} (α : Nat → Bool) {i : Nat} (hi : i ∉ L) :
    L.countP (fun x => if x = i then !α x else α x) = L.countP α := by
  apply List.countP_congr; intro x hx
  have : x ≠ i := fun h => hi (h ▸ hx)
  simp [this]

/-! ## The Tseitin formula -/

/-- Edge number `i` (a default for out-of-range indices). -/
def edge (E : List (Nat × Nat)) (i : Nat) : Nat × Nat := (E[i]?).getD (0, 0)

/-- Indices of the edges incident to `v`. -/
def inc (E : List (Nat × Nat)) (v : Nat) : List Nat :=
  (List.range E.length).filter fun i => (edge E i).1 == v || (edge E i).2 == v

/-- All clauses with exactly the variables `L`, in order, with every choice of signs. -/
def signs : List Nat → List (Clause Nat)
  | [] => [[]]
  | x :: L => (signs L).flatMap fun c => [⟨x, true⟩ :: c, ⟨x, false⟩ :: c]

/-- Parity of the assignment falsifying `c`. -/
def cpar (c : Clause Nat) : Nat := (c.countP fun l => !l.pos) % 2

/-- The clauses of vertex `v`: one per assignment to its edges with the wrong parity. -/
def vclauses (E : List (Nat × Nat)) (χ : Nat → Nat) (v : Nat) : List (Clause Nat) :=
  (signs (inc E v)).filter fun c => cpar c != χ v % 2

/-- The Tseitin formula of the graph `(0..n-1, E)` with charge `χ`. -/
def Tseitin (n : Nat) (E : List (Nat × Nat)) (χ : Nat → Nat) : CNF Nat :=
  (List.range n).flatMap (vclauses E χ)

/-- `α` satisfies the parity constraint of `v`. -/
def SatV (E : List (Nat × Nat)) (χ : Nat → Nat) (α : Nat → Bool) (v : Nat) : Prop :=
  (inc E v).countP α % 2 = χ v % 2

/-- Number of vertices `< n` in `S`. -/
def size (n : Nat) (S : Nat → Bool) : Nat := (List.range n).countP S

/-- Indices of the boundary edges of `S` (exactly one endpoint in `S`). -/
def bd (E : List (Nat × Nat)) (S : Nat → Bool) : List Nat :=
  (List.range E.length).filter fun i => S (edge E i).1 != S (edge E i).2

theorem edge_mem {E : List (Nat × Nat)} {i : Nat} (h : i < E.length) : edge E i ∈ E := by
  simp [edge, List.getElem?_eq_getElem h]

theorem mem_signs {L : List Nat} {c : Clause Nat} : c ∈ signs L → c.map Lit.var = L := by
  induction L generalizing c with
  | nil => simp [signs]
  | cons x L ih =>
    simp only [signs, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    rintro ⟨c', hc', rfl | rfl⟩ <;> simp [ih hc']

theorem map_mem_signs (L : List Nat) (f : Nat → Bool) :
    L.map (fun x => (⟨x, f x⟩ : Lit Nat)) ∈ signs L := by
  induction L with
  | nil => simp [signs]
  | cons x L ih =>
    simp only [signs, List.map_cons, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨_, ih, ?_⟩
    cases f x <;> simp

theorem lit_false {α : Nat → Bool} {l : Lit Nat} : l.eval α = false ↔ l.pos = !α l.var := by
  cases l with | mk x p => cases p <;> cases h : α x <;> simp [Lit.eval, h]

theorem eval_false {α : Nat → Bool} {C : Clause Nat} :
    C.eval α = false ↔ ∀ l ∈ C, l.eval α = false := by
  unfold Clause.eval; rw [List.any_eq_false]; simp

theorem eval_true {α : Nat → Bool} {C : Clause Nat} :
    C.eval α = true ↔ ∃ l ∈ C, l.eval α = true := by
  unfold Clause.eval; rw [List.any_eq_true]

/-- A vertex constraint satisfied by `α` satisfies all clauses of that vertex. -/
theorem vsound {E : List (Nat × Nat)} {χ : Nat → Nat} {α : Nat → Bool} {v : Nat}
    (hv : SatV E χ α v) {C : Clause Nat} (hC : C ∈ vclauses E χ v) : C.eval α = true := by
  unfold vclauses at hC
  rw [List.mem_filter] at hC
  obtain ⟨hs, hp⟩ := hC
  cases he : C.eval α
  · exfalso
    have hl := eval_false.mp he
    have e1 : C.countP (fun l => !l.pos) = (C.map Lit.var).countP α := by
      rw [List.countP_map]
      apply List.countP_congr; intro l hlC
      have := lit_false.mp (hl l hlC)
      simp [this]
    rw [mem_signs hs] at e1
    unfold cpar at hp
    unfold SatV at hv
    rw [e1, hv] at hp
    simp at hp
  · rfl

theorem tseitin_mem {n : Nat} {E : List (Nat × Nat)} {χ : Nat → Nat} {C : Clause Nat}
    (hC : C ∈ Tseitin n E χ) : ∃ v, v < n ∧ C ∈ vclauses E χ v := by
  unfold Tseitin at hC
  obtain ⟨v, hv, hC⟩ := List.mem_flatMap.mp hC
  exact ⟨v, List.mem_range.mp hv, hC⟩

/-! ## Implication by vertex sets -/

section
variable (n : Nat) (E : List (Nat × Nat)) (χ : Nat → Nat)

/-- Every assignment satisfying the constraints of the vertices of `S` satisfies `C`. -/
def Imp (S : Nat → Bool) (C : Clause Nat) : Prop :=
  ∀ α : Nat → Bool, (∀ v, v < n → S v = true → SatV E χ α v) → C.eval α = true

/-- `C` is implied by a set of at most `t` vertices. -/
def Good (t : Nat) (C : Clause Nat) : Prop := ∃ S, size n S ≤ t ∧ Imp n E χ S C

end

variable {n : Nat} {E : List (Nat × Nat)} {χ : Nat → Nat}

theorem good_axiom {t : Nat} (ht : 1 ≤ t) {C : Clause Nat} (hC : C ∈ Tseitin n E χ) :
    Good n E χ t C := by
  obtain ⟨v, _, hCv⟩ := tseitin_mem hC
  refine ⟨fun w => w == v, ?_, ?_⟩
  · have := countP_le_one_of_nodup (List.range n) (fun w => w == v) v List.nodup_range
      (by intro y hy; simpa using hy)
    unfold size; omega
  · intro α hα
    exact vsound (hα v ‹_› (by simp)) hCv

theorem imp_weak {S : Nat → Bool} {A C : Clause Nat} (hA : Imp n E χ S A) (h : ∀ l ∈ A, l ∈ C) :
    Imp n E χ S C := by
  intro α hα
  obtain ⟨l, hl, hle⟩ := eval_true.mp (hA α hα)
  exact eval_true.mpr ⟨l, h l hl, hle⟩

theorem imp_union {S T : Nat → Bool} {A B C : Clause Nat} (hA : Imp n E χ S A) (hB : Imp n E χ T B)
    (h : ∀ α : Nat → Bool, C.eval α = false → A.eval α = false ∨ B.eval α = false) :
    Imp n E χ (fun w => S w || T w) C := by
  intro α hα
  cases hC : C.eval α
  · exfalso
    rcases h α hC with h1 | h1
    · have := hA α (fun v hv hs => hα v hv (by simp [hs])); rw [h1] at this; exact Bool.noConfusion this
    · have := hB α (fun v hv hs => hα v hv (by simp [hs])); rw [h1] at this; exact Bool.noConfusion this
  · rfl

theorem size_union (S T : Nat → Bool) : size n (fun w => S w || T w) ≤ size n S + size n T :=
  countP_or_le _ _ _

/-- For a minimum set `S` implying `C`, every boundary edge of `S` is a variable of `C`. -/
theorem bd_in (hE : ∀ p ∈ E, p.1 < n ∧ p.2 < n) {S : Nat → Bool} {C : Clause Nat}
    (hS : Imp n E χ S C) (hmin : ∀ S', size n S' < size n S → ¬ Imp n E χ S' C) :
    ∀ i ∈ bd E S, ∃ l ∈ C, l.var = i := by
  intro i hi
  unfold bd at hi
  rw [List.mem_filter, List.mem_range] at hi
  obtain ⟨hiE, hb⟩ := hi
  have hmemE := hE _ (edge_mem hiE)
  -- the endpoint `u` in `S` and the endpoint `w` outside
  obtain ⟨u, w, hu, hw, hun, huw⟩ : ∃ u w, S u = true ∧ S w = false ∧ u < n ∧
      ((edge E i).1 = u ∧ (edge E i).2 = w ∨ (edge E i).1 = w ∧ (edge E i).2 = u) := by
    cases h1 : S (edge E i).1 <;> cases h2 : S (edge E i).2 <;> simp [h1, h2] at hb
    · exact ⟨_, _, h2, h1, hmemE.2, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨_, _, h1, h2, hmemE.1, Or.inl ⟨rfl, rfl⟩⟩
  apply Classical.byContradiction
  intro hnot
  have hnot' : ∀ l ∈ C, l.var ≠ i := fun l hl he => hnot ⟨l, hl, he⟩
  let S' : Nat → Bool := fun x => S x && x != u
  have hlt : size n S' < size n S := by
    unfold size
    apply countP_lt (List.range n) S' S
    · intro x _ h; simp [S'] at h; exact h.1
    · exact List.mem_range.mpr hun
    · exact hu
    · simp [S']
  have hn' := hmin S' hlt
  unfold Imp at hn'
  rw [Classical.not_forall] at hn'
  obtain ⟨α, hα⟩ := hn'
  rw [Classical.not_imp] at hα
  obtain ⟨hαS, hαC⟩ := hα
  have hαC' : C.eval α = false := by cases h : C.eval α <;> simp_all
  let α' : Nat → Bool := fun x => if x = i then !α x else α x
  have hu_inc : i ∈ inc E u := by
    unfold inc; rw [List.mem_filter, List.mem_range]
    refine ⟨hiE, ?_⟩
    rcases huw with ⟨h1, _⟩ | ⟨_, h2⟩
    · simp [h1]
    · simp [h2]
  have hnodup : (inc E u).Nodup := nodup_filter _ List.nodup_range
  -- `α` violates `u`: otherwise it satisfies all of `S`
  have hviol : ¬ SatV E χ α u := by
    intro hsu
    have := hS α (fun v hv hs => by
      by_cases hvu : v = u
      · subst hvu; exact hsu
      · exact hαS v hv (by simp [S', hs, hvu]))
    rw [hαC'] at this; exact Bool.noConfusion this
  have hS' : ∀ v, v < n → S v = true → SatV E χ α' v := by
    intro v hv hs
    by_cases hvu : v = u
    · subst hvu
      have := countP_flip hnodup α hu_inc
      change ((inc E v).countP α' + _) % 2 = 1 at this
      unfold SatV at hviol ⊢
      omega
    · have hvw : v ≠ w := by intro h; subst h; rw [hs] at hw; exact Bool.noConfusion hw
      have hni : i ∉ inc E v := by
        unfold inc; rw [List.mem_filter]
        intro ⟨_, h⟩
        have h' : (edge E i).1 = v ∨ (edge E i).2 = v := by simpa using h
        rcases huw with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at h' <;> omega
      have := hαS v hv (by simp [S', hs, hvu])
      unfold SatV at this ⊢
      rw [countP_unflip α hni]; exact this
  have hC' := hS α' hS'
  have : C.eval α' = false := by
    rw [eval_false]; intro l hl
    have h1 := (eval_false.mp hαC') l hl
    have hv := hnot' l hl
    have e : α' l.var = α l.var := by simp [α', hv]
    cases l with | mk x p => simp only [Lit.eval] at h1 ⊢; simp only at e; rw [e]; exact h1
  rw [this] at hC'; exact Bool.noConfusion hC'

/-! ## Width from boundary -/

open Programme.«20261024-1110-proof-complexity».BSWR in
theorem bd_le_wd {S : Nat → Bool} {C : Clause Nat} (h : ∀ i ∈ bd E S, ∃ l ∈ C, l.var = i) :
    (bd E S).length ≤ wd (List.range E.length) C := by
  unfold bd wd lits
  rw [← List.countP_eq_length_filter]
  refine Nat.le_trans ?_ (countP_flatMap_ge _ _ _)
  apply List.countP_mono_left
  intro x hx hb
  have hxb : x ∈ bd E S := by unfold bd; rw [List.mem_filter]; exact ⟨hx, hb⟩
  obtain ⟨l, hl, hlv⟩ := h x hxb
  cases l with | mk y p =>
    simp only at hlv; subst hlv
    cases p <;> simp [hl]

section main
variable (hE : ∀ p ∈ E, p.1 < n ∧ p.2 < n)
  (hconn : ∀ S : Nat → Bool, 0 < size n S → size n S < n → bd E S ≠ [])
  {e : Nat}
  (hexp : ∀ S : Nat → Bool, n / 3 < size n S → size n S ≤ 2 * (n / 3) → e ≤ (bd E S).length)
include hE

/-- A clause implied by `≤ 2(n/3)` vertices and of width `< e` is implied by `≤ n/3` vertices. -/
theorem good_step (hexp : ∀ S : Nat → Bool, n / 3 < size n S → size n S ≤ 2 * (n / 3) →
      e ≤ (bd E S).length) {C : Clause Nat}
    (h2 : Good n E χ (2 * (n / 3)) C) (hw : Programme.«20261024-1110-proof-complexity».BSWR.wd (List.range E.length) C < e) :
    Good n E χ (n / 3) C := by
  obtain ⟨S, hs, hI⟩ := h2
  obtain ⟨k, ⟨S0, hk, hI0⟩, hmin⟩ :=
    exists_min (fun k => ∃ S, size n S = k ∧ Imp n E χ S C) ⟨_, S, rfl, hI⟩
  have hk2 : k ≤ size n S := by
    apply Nat.le_of_not_lt; intro hlt; exact hmin _ hlt ⟨S, rfl, hI⟩
  by_cases hkt : k ≤ n / 3
  · exact ⟨S0, hk ▸ hkt, hI0⟩
  · exfalso
    have h1 := hexp S0 (by omega) (by omega)
    have hb := bd_in hE hI0 (fun S' hS' hI' => hmin _ (hk ▸ hS') ⟨S', rfl, hI'⟩)
    have h2 := bd_le_wd hb
    omega

include hconn in
/-- No set of at most `n/3` vertices implies the empty clause. -/
theorem not_good_empty (hn : 1 ≤ n) : ¬ Good n E χ (n / 3) [] := by
  rintro ⟨S, hs, hI⟩
  obtain ⟨k, ⟨S0, hk, hI0⟩, hmin⟩ :=
    exists_min (fun k => ∃ S, size n S = k ∧ Imp n E χ S []) ⟨_, S, rfl, hI⟩
  have hk2 : k ≤ size n S := by
    apply Nat.le_of_not_lt; intro hlt; exact hmin _ hlt ⟨S, rfl, hI⟩
  have hb := bd_in hE hI0 (fun S' hS' hI' => hmin _ (hk ▸ hS') ⟨S', rfl, hI'⟩)
  have hnil : bd E S0 = [] := by
    cases h : bd E S0 with
    | nil => rfl
    | cons i _ =>
      obtain ⟨l, hl, _⟩ := hb i (by rw [h]; exact List.mem_cons_self)
      simp at hl
  by_cases hk0 : k = 0
  · have hz : ∀ v, v < n → S0 v = false := by
      intro v hv
      have := List.countP_eq_zero.mp (show size n S0 = 0 by omega) v (List.mem_range.mpr hv)
      simpa using this
    have := hI0 (fun _ => false) (fun v hv hs => by rw [hz v hv] at hs; exact Bool.noConfusion hs)
    simp [Clause.eval] at this
  · exact hconn S0 (by omega) (by omega) hnil

omit hE in
theorem neg_eval (α : Nat → Bool) (l : Lit Nat) : (Programme.«20261024-1110-proof-complexity».BSWR.neg l).eval α = !l.eval α := by
  cases l with | mk x p => cases p <;> simp [Programme.«20261024-1110-proof-complexity».BSWR.neg, Lit.eval]

include hconn hexp in
/-- **Tseitin width bound** (no width-`W` derivation of the empty clause for `W < e`). -/
theorem tseitin_no_der (hn : 3 ≤ n) {W : Nat} (hW : W < e) :
    ¬ Programme.«20261024-1110-proof-complexity».BSWR.Der (· ∈ Tseitin n E χ) (List.range E.length) W [] := by
  intro hD
  have key : ∀ C, Programme.«20261024-1110-proof-complexity».BSWR.Der (· ∈ Tseitin n E χ) (List.range E.length) W C →
      Good n E χ (n / 3) C := by
    intro C hC
    induction hC with
    | ax hax _ => exact good_axiom (by omega) hax
    | @res A B C l _ _ hlA hlB hA hB hok ihA ihB =>
      obtain ⟨SA, hsA, hIA⟩ := ihA
      obtain ⟨SB, hsB, hIB⟩ := ihB
      apply good_step hE hexp _ (Nat.lt_of_le_of_lt hok.2 hW)
      refine ⟨_, Nat.le_trans (size_union SA SB) (by omega), imp_union hIA hIB ?_⟩
      intro α hCf
      have hc := eval_false.mp hCf
      cases hl : l.eval α
      · left; rw [eval_false]; intro m hm
        by_cases hml : m = l
        · subst hml; exact hl
        · exact hc m (hA m hm hml)
      · right; rw [eval_false]; intro m hm
        by_cases hml : m = Programme.«20261024-1110-proof-complexity».BSWR.neg l
        · subst hml; rw [neg_eval, hl]; rfl
        · exact hc m (hB m hm hml)
    | weak _ hsub _ ih =>
      obtain ⟨S, hs, hI⟩ := ih
      exact ⟨S, hs, imp_weak hI hsub⟩
  exact not_good_empty hE hconn (by omega) (key _ hD)

include hconn hexp in
/-- **Tseitin width bound**: every resolution refutation (weakening allowed) has a clause with at
least `e` distinct literals over the edge variables. -/
theorem tseitin_width (hn : 3 ≤ n) (π : Refutation (Tseitin n E χ)) :
    ∃ C ∈ π.steps, e ≤ Programme.«20261024-1110-proof-complexity».BSWR.wd (List.range E.length) C := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ C ∈ π.steps, Programme.«20261024-1110-proof-complexity».BSWR.wd (List.range E.length) C < e := by
    intro C hC; apply Nat.lt_of_not_le; intro h; exact hno ⟨C, hC, h⟩
  have key : ∀ k (hk : k < π.steps.length), Good n E χ (n / 3) π.steps[k] := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro hk
      rcases π.derived k hk with hax | ⟨a, b, ha, hb, hres⟩
      · exact good_axiom (by omega) hax
      · obtain ⟨SA, hsA, hIA⟩ := ih a ha (Nat.lt_trans ha hk)
        obtain ⟨SB, hsB, hIB⟩ := ih b hb (Nat.lt_trans hb hk)
        apply good_step hE hexp _ (hall _ (List.getElem_mem hk))
        exact ⟨_, Nat.le_trans (size_union SA SB) (by omega),
          imp_union hIA hIB (fun α h => resolvent_sound hres α h)⟩
  obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp π.empty_mem
  have := key k hk
  rw [hke] at this
  exact not_good_empty hE hconn (by omega) this

omit hE in
open Programme.«20261024-1110-proof-complexity».BSWR in
theorem wd_le_length (C : Clause Nat) : wd (List.range E.length) C ≤ C.length := by
  induction C with
  | nil => simp [wd]
  | cons l C ih =>
    have := wd_cons (List.nodup_range (n := E.length)) l C
    simp only [List.length_cons]; omega

include hconn hexp in
/-- **Tseitin size bound** (width bound composed with Ben-Sasson–Wigderson): if every vertex has
degree `≤ w0` and `w0 + d + b < e`, every refutation with `S` clauses has
`(2|E|)^b ≤ S (2|E| - d)^b`. -/
theorem tseitin_size (hn : 3 ≤ n) {w0 d b : Nat} (hdeg : ∀ v, v < n → (inc E v).length ≤ w0)
    (hwd : w0 + d + b < e) (π : Refutation (Tseitin n E χ)) :
    (2 * E.length) ^ b ≤ π.steps.length * (2 * E.length - d) ^ b := by
  have hF : ∀ C ∈ Tseitin n E χ, Programme.«20261024-1110-proof-complexity».BSWR.OK (List.range E.length) w0 C := by
    intro C hC
    obtain ⟨v, hv, hCv⟩ := tseitin_mem hC
    unfold vclauses at hCv
    have hm := mem_signs (List.mem_filter.mp hCv).1
    refine ⟨?_, ?_⟩
    · intro l hl
      have : l.var ∈ inc E v := by rw [← hm]; exact List.mem_map_of_mem hl
      unfold inc at this
      exact (List.mem_filter.mp this).1
    · have h1 := wd_le_length (E := E) C
      have h2 : C.length = (inc E v).length := by rw [← hm, List.length_map]
      have := hdeg v hv
      omega
  have := Programme.«20261024-1110-proof-complexity».BSWR.bsw_size (List.nodup_range (n := E.length)) hF d b
    (tseitin_no_der hE hconn hexp hn hwd) π
  rw [List.length_range] at this
  exact this

end main

/-! ## Unsatisfiability for odd total charge (handshake lemma) -/

theorem count_two {a b : Nat} (hab : a ≠ b) (k : Nat) :
    (List.range k).countP (fun v => a == v || b == v) =
      (if a < k then 1 else 0) + (if b < k then 1 else 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.countP_append, ih]
    simp only [List.countP_cons, List.countP_nil]
    by_cases ha : a = k <;> by_cases hb : b = k
    · exact absurd (ha.trans hb.symm) hab
    · subst ha
      have : b < a + 1 ↔ b < a := by omega
      simp [this]; split <;> omega
    · subst hb
      have : a < b + 1 ↔ a < b := by omega
      simp [this]
    · have h1 : (a == k || b == k) = false := by simp [ha, hb]
      have h2 : a < k + 1 ↔ a < k := by omega
      have h3 : b < k + 1 ↔ b < k := by omega
      simp [h1, h2, h3]

theorem sum_mod_two {l : List Nat} {f g : Nat → Nat} (h : ∀ v ∈ l, f v % 2 = g v % 2) :
    (l.map f).sum % 2 = (l.map g).sum % 2 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
    omega

theorem sum_ite_two (l : List Nat) (α : Nat → Bool) :
    (l.map fun i => if α i = true then 2 else 0).sum = 2 * l.countP α := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.countP_cons]
    cases h : α a <;> simp <;> omega

/-- **Unsatisfiability**: if every edge joins two distinct vertices `< n` and the total charge
is odd, every assignment violates the parity constraint of some vertex; equivalently, every
assignment falsifies some clause of `Tseitin n E χ`. -/
theorem tseitin_unsat (hE : ∀ p ∈ E, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2)
    (hχ : ((List.range n).map χ).sum % 2 = 1) (α : Nat → Bool) :
    ∃ C ∈ Tseitin n E χ, C.eval α = false := by
  apply Classical.byContradiction
  intro hno
  have hsat : ∀ v, v < n → SatV E χ α v := by
    intro v hv
    apply Classical.byContradiction
    intro hns
    -- the clause forbidding `α` on the edges of `v`
    let c : Clause Nat := (inc E v).map fun x => (⟨x, !α x⟩ : Lit Nat)
    have hc : c ∈ vclauses E χ v := by
      unfold vclauses; rw [List.mem_filter]
      refine ⟨map_mem_signs _ _, ?_⟩
      have : c.countP (fun l => !l.pos) = (inc E v).countP α := by
        simp only [c, List.countP_map]
        apply List.countP_congr; intro x _; simp [Function.comp]
      unfold cpar; rw [this]; unfold SatV at hns; simpa using hns
    apply hno
    refine ⟨c, ?_, ?_⟩
    · unfold Tseitin; exact List.mem_flatMap.mpr ⟨v, List.mem_range.mpr hv, hc⟩
    · rw [eval_false]; intro l hl
      simp only [c, List.mem_map] at hl
      obtain ⟨x, _, rfl⟩ := hl
      cases h : α x <;> simp [Lit.eval, h]
  -- handshake: the sum over vertices of the true incident edges is even
  have hhand : ((List.range n).map fun v => (inc E v).countP α).sum = 2 * (List.range E.length).countP α := by
    have e1 : ∀ v, (inc E v).countP α = (List.range E.length).countP
        (fun i => α i && ((edge E i).1 == v || (edge E i).2 == v)) := by
      intro v; unfold inc; rw [List.countP_filter]
    simp only [e1]
    rw [double_count (List.range n) (List.range E.length)
      (fun v i => α i && ((edge E i).1 == v || (edge E i).2 == v))]
    rw [← sum_ite_two]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hiE := List.mem_range.mp hi
    obtain ⟨h1, h2, h3⟩ := hE _ (edge_mem hiE)
    cases hα : α i
    · simp
    · simp only [Bool.true_and, ite_true]
      rw [count_two h3 n]; simp [h1, h2]
  have := sum_mod_two (l := List.range n) (f := fun v => (inc E v).countP α) (g := χ)
    (fun v hv => hsat v (List.mem_range.mp hv))
  omega

end Programme.«20261024-1110-proof-complexity».Tseitin

#print axioms Programme.«20261024-1110-proof-complexity».Tseitin.tseitin_width
#print axioms Programme.«20261024-1110-proof-complexity».Tseitin.tseitin_no_der
#print axioms Programme.«20261024-1110-proof-complexity».Tseitin.tseitin_size
#print axioms Programme.«20261024-1110-proof-complexity».Tseitin.tseitin_unsat
