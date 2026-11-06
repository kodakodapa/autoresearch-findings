import Programme.«20261104-1627-proof-complexity».NoDropPolynomial

namespace Programme.«20261104-1627-proof-complexity».MatchingReduction
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».MatchQuot
open Programme.«20261025-1627-proof-complexity».NoDrop

/-- A support contains no forbidden pair of the canonical matching quotient. -/
def Safe (A : List (Poly Nat)) (s : List Nat) : Prop :=
  ∀ u ∈ s, ∀ w ∈ s, prod2 u w ∉ A

/-- Square-free reduction with collision monomials deleted. -/
noncomputable def reduce (A : List (Poly Nat)) (P : Poly Nat) : Poly Nat := by
  classical
  exact ⟨(P.terms.filter fun t => decide (Safe A t.2)).map
    fun t => (t.1, t.2.eraseDups)⟩

theorem mono_dedup (s : List Nat) (a : Nat → Bool) :
    monoEval a s.eraseDups = monoEval a s := by
  simp only [monoEval_all, List.mem_eraseDups]

theorem unsafe_zero {A : List (Poly Nat)} {s : List Nat}
    (hs : ¬ Safe A s) {a : Nat → Bool} (ha : Good A a) : monoEval a s = 0 := by
  classical
  rw [monoEval_all, ite_eq_right]
  intro h
  apply hs
  intro u hu w hw hp
  exact ha u w hp ⟨h u hu, h w hw⟩

theorem eval_reduce (A : List (Poly Nat)) (P : Poly Nat)
    (a : Nat → Bool) (ha : Good A a) : (reduce A P).eval a = P.eval a := by
  classical
  unfold reduce Poly.eval
  simp only [List.map_map]
  rw [sum_filter]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  by_cases h : Safe A t.2
  · simp [h, mono_dedup]
  · simp [h, unsafe_zero h ha]

private theorem dedup_loop_length (xs acc : List Nat) :
    (List.eraseDupsBy.loop (fun x y : Nat => x == y) xs acc).length ≤
      xs.length + acc.length := by
  induction xs generalizing acc with
  | nil => simp [List.eraseDupsBy.loop]
  | cons x xs ih =>
    simp only [List.eraseDupsBy.loop]
    split
    · have h := ih acc; simp only [List.length_cons]; omega
    · have h := ih (x :: acc); simp only [List.length_cons] at *; omega

theorem deg_reduce (A : List (Poly Nat)) (P : Poly Nat) :
    (reduce A P).deg ≤ P.deg := by
  classical
  rw [deg_le_iff]
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  have hd := (deg_le_iff P P.deg).mp (Nat.le_refl _) s (List.mem_filter.mp hs).1
  have hl : s.2.eraseDups.length ≤ s.2.length := by
    simpa [List.eraseDups, List.eraseDupsBy] using dedup_loop_length s.2 []
  exact Nat.le_trans hl hd

private theorem nodup_dedup (s : List Nat) : s.eraseDups.Nodup := by
  cases s with
  | nil => simp
  | cons x xs =>
    rw [List.eraseDups_cons, List.nodup_cons]
    constructor
    · simp only [List.mem_eraseDups, List.mem_filter]
      intro h
      simpa using h.2
    · exact nodup_dedup (xs.filter fun b => !b == x)
termination_by s.length
decreasing_by have := List.length_filter_le (fun b => !b == x) xs; simp_all; omega

/-- Every surviving support is square-free and avoids forbidden pairs. -/
theorem support_reduce (A : List (Poly Nat)) (P : Poly Nat)
    (t : Int × List Nat) (ht : t ∈ (reduce A P).terms) :
    t.2.Nodup ∧ Safe A t.2 := by
  classical
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  have hsafe : Safe A s.2 := of_decide_eq_true (List.mem_filter.mp hs).2
  constructor
  · exact nodup_dedup _
  · intro u hu w hw
    exact hsafe u (List.mem_eraseDups.mp hu) w (List.mem_eraseDups.mp hw)

/-- Reduction preserves canonical NS membership in both directions. -/
theorem nsIn_reduce_iff (p D : Nat) (A : List (Poly Nat)) (P : Poly Nat) :
    NSIn p A D (reduce A P).eval ↔ NSIn p A D P.eval := by
  constructor
  · intro h
    apply Programme.«20261104-1627-proof-complexity».NoDropPolynomial.congr_good h
    intro a ha
    rw [eval_reduce A P a ha]
    simp
  · intro h
    apply Programme.«20261104-1627-proof-complexity».NoDropPolynomial.congr_good h
    intro a ha
    rw [eval_reduce A P a ha]
    simp

/-- Multiplication commutes with reduction as functions on Good points. -/
theorem multiply_compatible (A : List (Poly Nat)) (P : Poly Nat)
    (x : Nat) (a : Nat → Bool) (ha : Good A a) :
    (reduce A (P.mulVar x)).eval a =
      (reduce A ((reduce A P).mulVar x)).eval a := by
  rw [eval_reduce A (P.mulVar x) a ha,
    eval_reduce A ((reduce A P).mulVar x) a ha]
  simp only [eval_mulVar]
  rw [eval_reduce A P a ha]

/-- The proved normal-form interface; no label-span conversion is assumed. -/
theorem normal_form (A : List (Poly Nat)) (P : Poly Nat) :
    (reduce A P).deg ≤ P.deg ∧
    (∀ a, Good A a → (reduce A P).eval a = P.eval a) ∧
    (∀ t ∈ (reduce A P).terms, t.2.Nodup ∧ Safe A t.2) :=
  ⟨deg_reduce A P, eval_reduce A P, support_reduce A P⟩

end Programme.«20261104-1627-proof-complexity».MatchingReduction
#print axioms Programme.«20261104-1627-proof-complexity».MatchingReduction.normal_form
#print axioms Programme.«20261104-1627-proof-complexity».MatchingReduction.nsIn_reduce_iff
#print axioms Programme.«20261104-1627-proof-complexity».MatchingReduction.multiply_compatible
