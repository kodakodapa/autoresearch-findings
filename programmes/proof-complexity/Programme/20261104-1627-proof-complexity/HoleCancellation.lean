/- Hole-growth cancellation, adapted from canonical PigeonCancellation. -/
import Programme.«20261104-1627-proof-complexity».RRCoordinates
import Programme.«20261104-1627-proof-complexity».HoleAnchoredLift
import Programme.«20261104-1627-proof-complexity».HoleKernel
import Programme.«20261104-1627-proof-complexity».AnchoredValidity
namespace Programme.«20261104-1627-proof-complexity».HoleCancellation
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261104-1627-proof-complexity».HoleProjection Programme.«20261104-1627-proof-complexity».HoleGenerators
theorem vectorCoeff_scale (a : Int) (v : Vector) (g : Label) :
    vectorCoeff (v.map fun t => (a*t.1,t.2)) g = a * vectorCoeff v g := by
  induction v with
  | nil => simp [vectorCoeff]
  | cons t v ih =>
    simp only [List.map_cons, vectorCoeff, List.filter_cons] at *
    by_cases h : (t.2 == g) = true
    · simp [h, ih, Int.mul_add]
    · simp [h, ih]

theorem splitHole_scale (n b : Nat) (a : Int) (v : Vector) :
    splitHole n b (v.map fun t => (a*t.1,t.2)) =
      (splitHole n b v).map (fun t => (a*t.1,t.2)) := by
  induction v with
  | nil => rfl
  | cons t v ih =>
    simp only [List.map_cons, splitHole, List.filter_cons] at *
    split <;> simp_all

theorem vectorCoeff_split_combine_cons (n b : Nat) (a : Int) (u : Vector)
    (c : List (Int × Vector)) (g : Label) :
    vectorCoeff (splitHole n b (combine ((a,u)::c))) g =
      a * vectorCoeff (splitHole n b u) g +
        vectorCoeff (splitHole n b (combine c)) g := by
  simp only [combine, List.flatMap_cons, splitHole_append,
    vectorCoeff_append, splitHole_scale, vectorCoeff_scale]

/-- Lift arbitrary integer combinations, preserving their exact G1 coordinates. -/
theorem combination_first_block_lift {m n d : Nat} (c : List (Int × Vector))
    (hc : ∀ t ∈ c, t.2 ∈ syzygies m n d) :
    ∃ C : List (Int × Vector),
      (∀ t ∈ C, t.2 ∈ syzygies m (n+1) d) ∧
      ∀ g, vectorCoeff (splitHole n 1 (combine C)) g =
        vectorCoeff (splitHole n 1 (combine c)) g := by
  induction c with
  | nil => exact ⟨[], by simp, by intro g; rfl⟩
  | cons t c ih =>
    obtain ⟨u, hu, he⟩ := Programme.«20261104-1627-proof-complexity».HoleAnchoredLift.syzygy_first_block_lift (hc t (by simp))
    obtain ⟨C, hC, hCe⟩ := ih (by intro x hx; exact hc x (by simp [hx]))
    refine ⟨(t.1,u)::C, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hu
      · exact hC x hx
    · intro g
      rw [vectorCoeff_split_combine_cons, vectorCoeff_split_combine_cons, he, hCe]

theorem vectorCoeff_split (n b : Nat) (v : Vector) (g : Label) :
    vectorCoeff (splitHole n b v) g =
      if holeBlock n g == b then vectorCoeff v g else 0 := by
  induction v with
  | nil => simp [splitHole, vectorCoeff]
  | cons t v ih =>
    by_cases hg : t.2 = g
    · subst g
      by_cases hb : (holeBlock n t.2 == b) = true
      · simp [splitHole, vectorCoeff, hb] at *; exact ih
      · simp [splitHole, vectorCoeff, hb] at *; exact ih
    · have he : (t.2 == g) = false := by simp [beq_iff_eq, hg]
      by_cases hb : (holeBlock n t.2 == b) = true
      all_goals simp [splitHole, vectorCoeff, hb, he] at *; exact ih

/-- Smaller-board spanning cancels the larger kernel vector's first block. -/
theorem first_block_cancellation {p m n d : Nat} {v : Vector}
    (hn : 0 < n) (hv : Kernel p m (n+1) d v) (hs : Spanning p m n d) :
    ∃ C : List (Int × Vector),
      (∀ t ∈ C, t.2 ∈ syzygies m (n+1) d) ∧
      ∀ g, (p : Int) ∣ vectorCoeff (splitHole n 1 v) g -
        vectorCoeff (splitHole n 1 (combine C)) g := by
  obtain ⟨c, hc, he⟩ := hs _ (Programme.«20261104-1627-proof-complexity».HoleKernel.splitHole_one_kernel hn hv)
  obtain ⟨C, hC, hCe⟩ := combination_first_block_lift c hc
  refine ⟨C, hC, ?_⟩
  intro g
  rw [hCe]
  by_cases hg : (holeBlock n g == 1) = true
  · have hh := he g
    simpa only [vectorCoeff_split, hg, ↓reduceIte] using hh
  · have hf : (holeBlock n g == 1) = false := Bool.eq_false_iff.mpr hg
    simp only [vectorCoeff_split, hf, Bool.false_eq_true, ↓reduceIte, Int.sub_self]
    exact ⟨0, by simp⟩

/-- The actual raw residual has zero G1 coordinates modulo p. This statement
makes no unproved assertion that the subtracted generators are kernels. -/
theorem first_block_residual {p m n d : Nat} {v : Vector}
    (hn : 0 < n) (hv : Kernel p m (n+1) d v) (hs : Spanning p m n d) :
    ∃ C : List (Int × Vector),
      (∀ t ∈ C, t.2 ∈ syzygies m (n+1) d) ∧
      ∀ g, (p : Int) ∣ vectorCoeff (splitHole n 1
        (v ++ (combine C).map (fun t => (-t.1,t.2)))) g := by
  obtain ⟨C, hC, he⟩ := first_block_cancellation hn hv hs
  refine ⟨C, hC, ?_⟩
  intro g
  have hneg : ((combine C).map fun t => (-t.1,t.2)) =
      ((combine C).map fun t => ((-1 : Int)*t.1,t.2)) := by
    congr 1
    funext t
    simp
  rw [splitHole_append, vectorCoeff_append, hneg,
    splitHole_scale, vectorCoeff_scale]
  simpa only [Int.neg_one_mul, Int.sub_eq_add_neg] using he g



/-- Cancellation preserves Kernel, using canonical soundness of all generators. -/
theorem first_block_residual_sound {p m n d : Nat} {v : Vector}
    (hn : 0 < n) (hv : Kernel p m (n+1) d v) (hs : Spanning p m n d) :
    ∃ C : List (Int × Vector),
      (∀ t ∈ C, t.2 ∈ syzygies m (n+1) d) ∧
      Kernel p m (n+1) d (v ++ (combine C).map (fun t => (-t.1,t.2))) ∧
      ∀ g, (p : Int) ∣ vectorCoeff (splitHole n 1
        (v ++ (combine C).map (fun t => (-t.1,t.2)))) g := by
  obtain ⟨C, hC, he⟩ := first_block_residual hn hv hs
  refine ⟨C, hC, ?_, he⟩
  have hk := kernel_scale (kernel_combine C (fun t ht =>
    syzygies_sound p m (n+1) d t.2 (hC t ht))) (-1)
  have hneg : ((combine C).map fun t => ((-1 : Int)*t.1,t.2)) =
      ((combine C).map fun t => (-t.1,t.2)) := by simp
  rw [hneg] at hk
  exact kernel_append hv hk

end Programme.«20261104-1627-proof-complexity».HoleCancellation
#print axioms Programme.«20261104-1627-proof-complexity».HoleCancellation.combination_first_block_lift
#print axioms Programme.«20261104-1627-proof-complexity».HoleCancellation.first_block_cancellation
#print axioms Programme.«20261104-1627-proof-complexity».HoleCancellation.first_block_residual

#print axioms Programme.«20261104-1627-proof-complexity».HoleCancellation.first_block_residual_sound
