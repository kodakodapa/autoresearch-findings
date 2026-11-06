import Programme.«20261104-1627-proof-complexity».AnchoredLift
import Programme.«20261104-1627-proof-complexity».PigeonKernel
import Programme.«20261104-1627-proof-complexity».RRCoordinates

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels

theorem vectorCoeff_scale (a : Int) (v : Vector) (g : Label) :
    vectorCoeff (v.map fun t => (a*t.1,t.2)) g = a * vectorCoeff v g := by
  induction v with
  | nil => simp [vectorCoeff]
  | cons t v ih =>
    simp only [List.map_cons, vectorCoeff, List.filter_cons] at *
    by_cases h : (t.2 == g) = true
    · simp [h, ih, Int.mul_add]
    · simp [h, ih]

theorem splitPigeon_scale (m b : Nat) (a : Int) (v : Vector) :
    splitPigeon m b (v.map fun t => (a*t.1,t.2)) =
      (splitPigeon m b v).map (fun t => (a*t.1,t.2)) := by
  induction v with
  | nil => rfl
  | cons t v ih =>
    simp only [List.map_cons, splitPigeon, List.filter_cons] at *
    split <;> simp_all

theorem vectorCoeff_split_combine_cons (m b : Nat) (a : Int) (u : Vector)
    (c : List (Int × Vector)) (g : Label) :
    vectorCoeff (splitPigeon m b (combine ((a,u)::c))) g =
      a * vectorCoeff (splitPigeon m b u) g +
        vectorCoeff (splitPigeon m b (combine c)) g := by
  simp only [combine, List.flatMap_cons, splitPigeon_append,
    vectorCoeff_append, splitPigeon_scale, vectorCoeff_scale]

/-- Lift arbitrary integer combinations, preserving their exact G1 coordinates. -/
theorem combination_first_block_lift {m n d : Nat} (c : List (Int × Vector))
    (hc : ∀ t ∈ c, t.2 ∈ syzygies m n d) :
    ∃ C : List (Int × Vector),
      (∀ t ∈ C, t.2 ∈ syzygies (m+1) n d) ∧
      ∀ g, vectorCoeff (splitPigeon m 1 (combine C)) g =
        vectorCoeff (splitPigeon m 1 (combine c)) g := by
  induction c with
  | nil => exact ⟨[], by simp, by intro g; rfl⟩
  | cons t c ih =>
    obtain ⟨u, hu, he⟩ := syzygy_first_block_lift (hc t (by simp))
    obtain ⟨C, hC, hCe⟩ := ih (by intro x hx; exact hc x (by simp [hx]))
    refine ⟨(t.1,u)::C, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hu
      · exact hC x hx
    · intro g
      rw [vectorCoeff_split_combine_cons, vectorCoeff_split_combine_cons, he, hCe]

theorem vectorCoeff_split (m b : Nat) (v : Vector) (g : Label) :
    vectorCoeff (splitPigeon m b v) g =
      if pigeonBlock m g == b then vectorCoeff v g else 0 := by
  induction v with
  | nil => simp [splitPigeon, vectorCoeff]
  | cons t v ih =>
    by_cases hg : t.2 = g
    · subst g
      by_cases hb : (pigeonBlock m t.2 == b) = true
      · simp [splitPigeon, vectorCoeff, hb] at *; exact ih
      · simp [splitPigeon, vectorCoeff, hb] at *; exact ih
    · have he : (t.2 == g) = false := by simp [beq_iff_eq, hg]
      by_cases hb : (pigeonBlock m t.2 == b) = true
      all_goals simp [splitPigeon, vectorCoeff, hb, he] at *; exact ih

/-- Smaller-board spanning cancels the larger kernel vector's first block. -/
theorem first_block_cancellation {p m n d : Nat} {v : Vector}
    (hv : Kernel p (m+1) n d v) (hs : Spanning p m n d) :
    ∃ C : List (Int × Vector),
      (∀ t ∈ C, t.2 ∈ syzygies (m+1) n d) ∧
      ∀ g, (p : Int) ∣ vectorCoeff (splitPigeon m 1 v) g -
        vectorCoeff (splitPigeon m 1 (combine C)) g := by
  obtain ⟨c, hc, he⟩ := hs _ (splitPigeon_one_kernel hv)
  obtain ⟨C, hC, hCe⟩ := combination_first_block_lift c hc
  refine ⟨C, hC, ?_⟩
  intro g
  rw [hCe]
  by_cases hg : (pigeonBlock m g == 1) = true
  · have hh := he g
    simpa only [vectorCoeff_split, hg, ↓reduceIte] using hh
  · have hf : (pigeonBlock m g == 1) = false := Bool.eq_false_iff.mpr hg
    simp only [vectorCoeff_split, hf, Bool.false_eq_true, ↓reduceIte, Int.sub_self]
    exact ⟨0, by simp⟩

/-- The actual raw residual has zero G1 coordinates modulo p. This statement
makes no unproved assertion that the subtracted generators are kernels. -/
theorem first_block_residual {p m n d : Nat} {v : Vector}
    (hv : Kernel p (m+1) n d v) (hs : Spanning p m n d) :
    ∃ C : List (Int × Vector),
      (∀ t ∈ C, t.2 ∈ syzygies (m+1) n d) ∧
      ∀ g, (p : Int) ∣ vectorCoeff (splitPigeon m 1
        (v ++ (combine C).map (fun t => (-t.1,t.2)))) g := by
  obtain ⟨C, hC, he⟩ := first_block_cancellation hv hs
  refine ⟨C, hC, ?_⟩
  intro g
  have hneg : ((combine C).map fun t => (-t.1,t.2)) =
      ((combine C).map fun t => ((-1 : Int)*t.1,t.2)) := by
    congr 1
    funext t
    simp
  rw [splitPigeon_append, vectorCoeff_append, hneg,
    splitPigeon_scale, vectorCoeff_scale]
  simpa only [Int.neg_one_mul, Int.sub_eq_add_neg] using he g

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.combination_first_block_lift
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.first_block_cancellation

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.first_block_residual
