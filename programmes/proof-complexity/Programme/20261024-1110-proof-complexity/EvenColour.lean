import Programme.«20261024-1110-proof-complexity».Tseitin

/-!
# Even colouring formulas (Markström 2006) in the Tseitin vocabulary (core Lean 4)

For a graph on vertices `0..n-1` with edge list `E` (variables = edge indices), `EC n E` is the CNF
which, at each vertex `v`, forbids every assignment to the incident edges `inc E v` in which the
number of true edges differs from `deg v / 2` (one clause per forbidden assignment).

* `ec_unsat`: if every edge joins two distinct vertices `< n`, every degree is even and `|E|` is
  odd, every assignment falsifies a clause of `EC n E` (handshake: the true edges would number
  `|E| / 2`).
* `tseitin_sub`: every clause of the Tseitin formula with charge `deg v / 2` is a clause of
  `EC n E`, so every resolution refutation of that Tseitin formula is one of `EC n E`
  (`ec_of_tseitin`, same size). Lower bounds for Tseitin do not transfer to EC.
-/

namespace Programme.«20261024-1110-proof-complexity».EvenColour

open Classical Programme.«20261024-1110-proof-complexity».Haken Programme.«20261024-1110-proof-complexity».Tseitin

/-- The clauses of vertex `v`: one per assignment to its edges with the wrong number of true edges. -/
def ecclauses (E : List (Nat × Nat)) (v : Nat) : List (Clause Nat) :=
  (signs (inc E v)).filter fun c => c.countP (fun l => !l.pos) != (inc E v).length / 2

/-- The even colouring formula of the graph `(0..n-1, E)`. -/
def EC (n : Nat) (E : List (Nat × Nat)) : CNF Nat :=
  (List.range n).flatMap (ecclauses E)

/-- Tseitin with charge `deg v / 2` is a sub-CNF of `EC`. -/
theorem tseitin_sub {n : Nat} {E : List (Nat × Nat)} {C : Clause Nat}
    (hC : C ∈ Tseitin n E (fun v => (inc E v).length / 2)) : C ∈ EC n E := by
  obtain ⟨v, hv, hC⟩ := tseitin_mem hC
  unfold vclauses at hC; rw [List.mem_filter] at hC
  obtain ⟨hs, hp⟩ := hC
  unfold EC; refine List.mem_flatMap.mpr ⟨v, List.mem_range.mpr hv, ?_⟩
  unfold ecclauses; rw [List.mem_filter]
  refine ⟨hs, ?_⟩
  unfold cpar at hp
  simp only [bne_iff_ne, ne_eq] at hp ⊢
  intro h; rw [h] at hp; exact hp rfl

/-- Every refutation of the Tseitin formula with charge `deg v / 2` is a refutation of `EC`. -/
def ec_of_tseitin {n : Nat} {E : List (Nat × Nat)}
    (R : Refutation (Tseitin n E (fun v => (inc E v).length / 2))) : Refutation (EC n E) where
  steps := R.steps
  derived := fun k hk => (R.derived k hk).imp_left tseitin_sub
  empty_mem := R.empty_mem

theorem ec_of_tseitin_length {n : Nat} {E : List (Nat × Nat)}
    (R : Refutation (Tseitin n E (fun v => (inc E v).length / 2))) :
    (ec_of_tseitin R).steps.length = R.steps.length := rfl

/-- Handshake lemma: summing the true incident edges over all vertices counts each true edge twice. -/
theorem handshake {n : Nat} {E : List (Nat × Nat)} (hE : ∀ p ∈ E, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2)
    (α : Nat → Bool) :
    ((List.range n).map fun v => (inc E v).countP α).sum = 2 * (List.range E.length).countP α := by
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

theorem sum_half {l : List Nat} {f : Nat → Nat} (h : ∀ v ∈ l, f v % 2 = 0) :
    2 * (l.map fun v => f v / 2).sum = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
    omega

/-- **Unsatisfiability**: all degrees even and `|E|` odd (edges between distinct vertices `< n`). -/
theorem ec_unsat {n : Nat} {E : List (Nat × Nat)} (hE : ∀ p ∈ E, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2)
    (heven : ∀ v, v < n → (inc E v).length % 2 = 0) (hodd : E.length % 2 = 1) (α : Nat → Bool) :
    ∃ C ∈ EC n E, C.eval α = false := by
  apply Classical.byContradiction
  intro hno
  have hsat : ∀ v, v < n → (inc E v).countP α = (inc E v).length / 2 := by
    intro v hv
    apply Classical.byContradiction
    intro hns
    let c : Clause Nat := (inc E v).map fun x => (⟨x, !α x⟩ : Lit Nat)
    have hcnt : c.countP (fun l => !l.pos) = (inc E v).countP α := by
      simp only [c, List.countP_map]
      apply List.countP_congr; intro x _; simp [Function.comp]
    have hc : c ∈ ecclauses E v := by
      unfold ecclauses; rw [List.mem_filter]
      refine ⟨map_mem_signs _ _, ?_⟩
      rw [hcnt]; simpa using hns
    apply hno
    refine ⟨c, ?_, ?_⟩
    · unfold EC; exact List.mem_flatMap.mpr ⟨v, List.mem_range.mpr hv, hc⟩
    · rw [eval_false]; intro l hl
      simp only [c, List.mem_map] at hl
      obtain ⟨x, _, rfl⟩ := hl
      cases h : α x <;> simp [Lit.eval, h]
  have hT := handshake hE α
  have hD := handshake hE (fun _ => true)
  simp only [List.countP_true] at hD
  rw [List.map_congr_left (fun v hv => hsat v (List.mem_range.mp hv))] at hT
  have hH := sum_half (l := List.range n) (f := fun v => (inc E v).length)
    (fun v hv => heven v (List.mem_range.mp hv))
  rw [List.length_range] at hD
  omega

/-- Both parts together. -/
theorem ec_main {n : Nat} {E : List (Nat × Nat)} (hE : ∀ p ∈ E, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2)
    (heven : ∀ v, v < n → (inc E v).length % 2 = 0) (hodd : E.length % 2 = 1) :
    (∀ α : Nat → Bool, ∃ C ∈ EC n E, C.eval α = false) ∧
    ∀ R : Refutation (Tseitin n E (fun v => (inc E v).length / 2)),
      ∃ R' : Refutation (EC n E), R'.steps.length = R.steps.length :=
  ⟨ec_unsat hE heven hodd, fun R => ⟨ec_of_tseitin R, rfl⟩⟩

end Programme.«20261024-1110-proof-complexity».EvenColour

#print axioms Programme.«20261024-1110-proof-complexity».EvenColour.ec_unsat
#print axioms Programme.«20261024-1110-proof-complexity».EvenColour.tseitin_sub
#print axioms Programme.«20261024-1110-proof-complexity».EvenColour.ec_of_tseitin
#print axioms Programme.«20261024-1110-proof-complexity».EvenColour.ec_main
