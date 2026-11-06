import Programme.«20261104-1627-proof-complexity».TailThreePivots
import Programme.«20261104-1627-proof-complexity».OrdinarySoundness
set_option maxHeartbeats 2000000
namespace Programme.«20261104-1627-proof-complexity».LargerPivotConstraint
open Programme.«20261104-1627-proof-complexity».MatchingLabels Programme.«20261104-1627-proof-complexity».TailPivot Programme.«20261104-1627-proof-complexity».TailWeighted
/-- Alternating six-cycle on three old rows and holes zero and one. -/
def cycle (m : Nat) (v : Vector) : Int :=
  vectorCoeff v ⟨[(0,0),(1,1)],true,m⟩ -
  vectorCoeff v ⟨[(0,1),(1,0)],true,m⟩ +
  vectorCoeff v ⟨[(1,0),(2,1)],true,m⟩ -
  vectorCoeff v ⟨[(1,1),(2,0)],true,m⟩ +
  vectorCoeff v ⟨[(0,1),(2,0)],true,m⟩ -
  vectorCoeff v ⟨[(0,0),(2,1)],true,m⟩
theorem cycle_append (m : Nat) (v w : Vector) :
    cycle m (v ++ w) = cycle m v + cycle m w := by
  simp only [cycle, vectorCoeff_append]
  omega
theorem cycle_scale (m : Nat) (v : Vector) (c : Int) :
    cycle m (v.map fun t => (c*t.1,t.2)) = c * cycle m v := by
  simp only [cycle, Programme.«20261104-1627-proof-complexity».MixedAggregate.coeff_scale]
  simp only [Int.mul_add, Int.mul_sub]
/-- Fixed-board identities checked by kernel reduction. -/
theorem four_pivot_cycle :
    ∀ N ∈ matchings 4 5 1, ∀ j ∈ cols 5 N,
      cycle 3 (pivotRows 3 5 N j) = 0 := by
  intro N hN j hj
  simp [matchings, rows, cols, freeRow, freeCol, List.range_succ] at hN
  rcases hN with (h | h | h | h | h) | (h | h | h | h | h) | (h | h | h | h | h) | (h | h | h | h | h)
  all_goals subst N
  all_goals simp [cols, freeCol, List.range_succ] at hj
  all_goals rcases hj with h | h | h | h <;> subst j <;> simp [cycle, pivotRows, vectorCoeff, rows, freeRow, ordered, List.range_succ, List.mergeSort] <;> decide +kernel
theorem five_pivot_cycle :
    ∀ N ∈ matchings 5 5 1, ∀ j ∈ cols 5 N,
      cycle 4 (pivotRows 4 5 N j) = 0 := by
  intro N hN j hj
  simp [matchings, rows, cols, freeRow, freeCol, List.range_succ] at hN
  rcases hN with (h | h | h | h | h) | (h | h | h | h | h) | (h | h | h | h | h) | (h | h | h | h | h) | (h | h | h | h | h)
  all_goals subst N
  all_goals simp [cols, freeCol, List.range_succ] at hj
  all_goals rcases hj with h | h | h | h <;> subst j <;> simp [cycle, pivotRows, vectorCoeff, rows, freeRow, ordered, List.range_succ, List.mergeSort] <;> decide +kernel
theorem weighted_cycle {m n : Nat} {L : Data}
    (h : ∀ t ∈ L, cycle m (pivotRows m n t.2.1 t.2.2) = 0) :
    cycle m (combine (rowCorrections m n L)) = 0 := by
  induction L with
  | nil => rfl
  | cons t L ih =>
    change cycle m ((pivotRows m n t.2.1 t.2.2).map
      (fun s => (t.1*s.1,s.2)) ++ combine (rowCorrections m n L)) = 0
    rw [cycle_append, cycle_scale, h t (by simp), ih (fun s hs => h s (by simp [hs]))]
    simp
def single (m : Nat) : Vector := [(1,⟨[(0,0),(1,1)],true,m⟩)]
theorem single_cycle (m : Nat) : cycle m (single m) = 1 := by
  simp [cycle, single, vectorCoeff]
theorem four_no_unrestricted_weights (L : Data)
    (h : ∀ t ∈ L, t.2.1 ∈ matchings 4 5 1 ∧ t.2.2 ∈ cols 5 t.2.1) :
    combine (rowCorrections 3 5 L) ≠ single 3 := by
  intro he
  have hc := weighted_cycle (fun t ht => four_pivot_cycle _ (h t ht).1 _ (h t ht).2)
  rw [he, single_cycle] at hc
  contradiction
theorem five_no_unrestricted_weights (L : Data)
    (h : ∀ t ∈ L, t.2.1 ∈ matchings 5 5 1 ∧ t.2.2 ∈ cols 5 t.2.1) :
    combine (rowCorrections 4 5 L) ≠ single 4 := by
  intro he
  have hc := weighted_cycle (fun t ht => five_pivot_cycle _ (h t ht).1 _ (h t ht).2)
  rw [he, single_cycle] at hc
  contradiction
theorem cycle_congruent_three {m : Nat} {v w : Vector}
    (h : ∀ g, (3 : Int) ∣ vectorCoeff v g - vectorCoeff w g) :
    (3 : Int) ∣ cycle m v - cycle m w := by
  have h1 := h ⟨[(0,0),(1,1)],true,m⟩
  have h2 := h ⟨[(0,1),(1,0)],true,m⟩
  have h3 := h ⟨[(1,0),(2,1)],true,m⟩
  have h4 := h ⟨[(1,1),(2,0)],true,m⟩
  have h5 := h ⟨[(0,1),(2,0)],true,m⟩
  have h6 := h ⟨[(0,0),(2,1)],true,m⟩
  simp only [cycle]
  omega

theorem four_no_mod_three_weights (L : Data)
    (h : ∀ t ∈ L, t.2.1 ∈ matchings 4 5 1 ∧ t.2.2 ∈ cols 5 t.2.1) :
    ¬ (∀ g, (3 : Int) ∣ vectorCoeff (single 3) g -
      vectorCoeff (combine (rowCorrections 3 5 L)) g) := by
  intro he
  have hc := weighted_cycle (fun t ht => four_pivot_cycle _ (h t ht).1 _ (h t ht).2)
  have hh := cycle_congruent_three (m := 3) he
  rw [single_cycle, hc] at hh
  omega

theorem five_no_mod_three_weights (L : Data)
    (h : ∀ t ∈ L, t.2.1 ∈ matchings 5 5 1 ∧ t.2.2 ∈ cols 5 t.2.1) :
    ¬ (∀ g, (3 : Int) ∣ vectorCoeff (single 4) g -
      vectorCoeff (combine (rowCorrections 4 5 L)) g) := by
  intro he
  have hc := weighted_cycle (fun t ht => five_pivot_cycle _ (h t ht).1 _ (h t ht).2)
  have hh := cycle_congruent_three (m := 4) he
  rw [single_cycle, hc] at hh
  omega

theorem rr_tail_cycle_four :
    cycle 3 (splitPigeon 3 2 (rr 5 [(0,0)] 1 3)) = -1 := by
  simp [cycle, splitPigeon, pigeonBlock, usesPigeon, rr, cols, freeCol,
    ordered, vectorCoeff, List.range_succ]

theorem rr_tail_cycle_five :
    cycle 4 (splitPigeon 4 2 (rr 5 [(0,0)] 1 4)) = -1 := by
  simp [cycle, splitPigeon, pigeonBlock, usesPigeon, rr, cols, freeCol,
    ordered, vectorCoeff, List.range_succ]

theorem rr_kernel_four : Kernel 3 4 5 3 (rr 5 [(0,0)] 1 3) := by
  apply rr_kernel (e := 1)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide

theorem rr_kernel_five : Kernel 3 5 5 3 (rr 5 [(0,0)] 1 4) := by
  apply rr_kernel (e := 1)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide

theorem four_kernel_tail_no_rc_weights (L : Data)
    (h : ∀ t ∈ L, t.2.1 ∈ matchings 4 5 1 ∧ t.2.2 ∈ cols 5 t.2.1) :
    ¬ (∀ g, (3 : Int) ∣
      vectorCoeff (splitPigeon 3 2 (rr 5 [(0,0)] 1 3)) g -
      vectorCoeff (combine (rowCorrections 3 5 L)) g) := by
  intro he
  have hc := weighted_cycle (fun t ht => four_pivot_cycle _ (h t ht).1 _ (h t ht).2)
  have hh := cycle_congruent_three (m := 3) he
  rw [rr_tail_cycle_four, hc] at hh
  omega

theorem five_kernel_tail_no_rc_weights (L : Data)
    (h : ∀ t ∈ L, t.2.1 ∈ matchings 5 5 1 ∧ t.2.2 ∈ cols 5 t.2.1) :
    ¬ (∀ g, (3 : Int) ∣
      vectorCoeff (splitPigeon 4 2 (rr 5 [(0,0)] 1 4)) g -
      vectorCoeff (combine (rowCorrections 4 5 L)) g) := by
  intro he
  have hc := weighted_cycle (fun t ht => five_pivot_cycle _ (h t ht).1 _ (h t ht).2)
  have hh := cycle_congruent_three (m := 4) he
  rw [rr_tail_cycle_five, hc] at hh
  omega

theorem rr_tail_four :
    ∀ t ∈ rr 5 [(0,0)] 1 3, pigeonBlock 3 t.2 ≠ 1 := by
  simp [rr, cols, freeCol, ordered, List.range_succ, pigeonBlock, usesPigeon]

theorem rr_tail_five :
    ∀ t ∈ rr 5 [(0,0)] 1 4, pigeonBlock 4 t.2 ≠ 1 := by
  simp [rr, cols, freeCol, ordered, List.range_succ, pigeonBlock, usesPigeon]

end Programme.«20261104-1627-proof-complexity».LargerPivotConstraint
#print axioms Programme.«20261104-1627-proof-complexity».LargerPivotConstraint.four_no_unrestricted_weights
#print axioms Programme.«20261104-1627-proof-complexity».LargerPivotConstraint.five_no_unrestricted_weights

#print axioms Programme.«20261104-1627-proof-complexity».LargerPivotConstraint.four_no_mod_three_weights
#print axioms Programme.«20261104-1627-proof-complexity».LargerPivotConstraint.five_no_mod_three_weights

#print axioms Programme.«20261104-1627-proof-complexity».LargerPivotConstraint.rr_kernel_four
#print axioms Programme.«20261104-1627-proof-complexity».LargerPivotConstraint.rr_kernel_five

#print axioms Programme.«20261104-1627-proof-complexity».LargerPivotConstraint.four_kernel_tail_no_rc_weights
#print axioms Programme.«20261104-1627-proof-complexity».LargerPivotConstraint.five_kernel_tail_no_rc_weights
#print axioms Programme.«20261104-1627-proof-complexity».LargerPivotConstraint.rr_tail_four
#print axioms Programme.«20261104-1627-proof-complexity».LargerPivotConstraint.rr_tail_five
