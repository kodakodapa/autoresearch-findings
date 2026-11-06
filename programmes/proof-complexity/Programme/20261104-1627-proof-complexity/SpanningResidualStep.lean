import Programme.«20261104-1627-proof-complexity».SpanningSquareThree
import Programme.«20261104-1627-proof-complexity».KernelLinear

namespace Programme.«20261104-1627-proof-complexity».SpanningResidualStep
open Programme.«20261104-1627-proof-complexity».MatchingLabels Programme.«20261104-1627-proof-complexity».SpanningSquareThree

/-- The substantive residual obligation after cancelling the first pigeon block.
This is a proposition to prove, not a new axiom. -/
def ResidualSpanning (p m n d : Nat) : Prop :=
  ∀ v, Kernel p (m+1) n d v →
    (∀ g, (p : Int) ∣ vectorCoeff (splitPigeon m 1 v) g) →
    ∃ c : List (Int × Vector),
      (∀ t ∈ c, t.2 ∈ syzygies (m+1) n d) ∧
      ∀ g, (p : Int) ∣ vectorCoeff v g - vectorCoeff (combine c) g

/-- Assemble cancellation of the first block with a proof for its residual.
The degree is unchanged throughout this step. -/
theorem spanning_successor {p m n d : Nat}
    (small : Spanning p m n d)
    (sound : ∀ u ∈ syzygies (m+1) n d, Kernel p (m+1) n d u)
    (remaining : ResidualSpanning p m n d) : Spanning p (m+1) n d := by
  intro v hv
  obtain ⟨C,hC,hk,hzero⟩ := first_block_kernel_residual hv small sound
  obtain ⟨B,hB,hcoeff⟩ := remaining _ hk hzero
  refine ⟨C ++ B, ?_, ?_⟩
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hC t ht
    · exact hB t ht
  · intro g
    have he := hcoeff g
    have hneg : ((combine C).map fun t => (-t.1,t.2)) =
        ((combine C).map fun t => ((-1 : Int)*t.1,t.2)) := by simp
    rw [vectorCoeff_append, hneg, vectorCoeff_scale] at he
    rw [combine_append_coeff]
    simpa only [Int.neg_one_mul, Int.sub_eq_add_neg, Int.neg_add,
      Int.add_assoc] using he

/-- The already established first nontrivial square, with its canonical name. -/
theorem square_two : Square 3 2 := spanning_square_three

/-- At degree three, these two applications still require a 3-by-5 degree-three
base case. Degree-two square spanning supplies none of these hypotheses. -/
theorem five_by_five_degree_three
    (base : Spanning 3 3 5 3)
    (sound4 : ∀ u ∈ syzygies 4 5 3, Kernel 3 4 5 3 u)
    (residual4 : ResidualSpanning 3 3 5 3)
    (sound5 : ∀ u ∈ syzygies 5 5 3, Kernel 3 5 5 3 u)
    (residual5 : ResidualSpanning 3 4 5 3) : Spanning 3 5 5 3 :=
  spanning_successor (spanning_successor base sound4 residual4) sound5 residual5

end Programme.«20261104-1627-proof-complexity».SpanningResidualStep
#print axioms Programme.«20261104-1627-proof-complexity».SpanningResidualStep.spanning_successor
#print axioms Programme.«20261104-1627-proof-complexity».SpanningResidualStep.five_by_five_degree_three
