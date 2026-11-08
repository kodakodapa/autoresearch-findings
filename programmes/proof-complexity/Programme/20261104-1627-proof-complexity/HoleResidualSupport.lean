/- Hole-tail residual support, adapted from canonical ResidualSupport. -/
import Programme.«20261104-1627-proof-complexity».HoleCancellation
import Programme.«20261104-1627-proof-complexity».ResidualSupport
namespace Programme.«20261104-1627-proof-complexity».HoleResidualSupport
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261104-1627-proof-complexity».ResidualSupport (kernel_of_congruent)
open Programme.«20261104-1627-proof-complexity».HoleProjection Programme.«20261104-1627-proof-complexity».HoleCancellation

theorem vectorCoeff_partition (n : Nat) (v : Vector) (g : Label) :
    vectorCoeff v g = vectorCoeff (splitHole n 1 v) g +
      vectorCoeff (splitHole n 2 v) g + vectorCoeff (splitHole n 3 v) g := by
  have h (g : Label) : holeBlock n g = 1 ∨ holeBlock n g = 2 ∨ holeBlock n g = 3 := by
    unfold holeBlock
    split <;> simp_all
    split <;> simp_all
  rw [Programme.«20261104-1627-proof-complexity».HoleCancellation.vectorCoeff_split, Programme.«20261104-1627-proof-complexity».HoleCancellation.vectorCoeff_split, Programme.«20261104-1627-proof-complexity».HoleCancellation.vectorCoeff_split]
  rcases h g with h | h | h <;> simp [h]

/-- Delete block one literally, rather than only making its coefficients zero. -/
def holeTailBlocks (n : Nat) (v : Vector) : Vector :=
  splitHole n 2 v ++ splitHole n 3 v

theorem tail_congruent {p n : Nat} {v : Vector}
    (hz : ∀ g, (p : Int) ∣ vectorCoeff (splitHole n 1 v) g) :
    ∀ g, (p : Int) ∣ vectorCoeff v g - vectorCoeff (holeTailBlocks n v) g := by
  intro g
  have he := vectorCoeff_partition n v g
  rw [holeTailBlocks, vectorCoeff_append]
  have hh : vectorCoeff v g -
      (vectorCoeff (splitHole n 2 v) g + vectorCoeff (splitHole n 3 v) g) =
      vectorCoeff (splitHole n 1 v) g := by omega
  rw [hh]
  exact hz g

theorem tail_kernel {p m n d : Nat} {v : Vector}
    (hv : Kernel p m (n+1) d v)
    (hz : ∀ g, (p : Int) ∣ vectorCoeff (splitHole n 1 v) g) :
    Kernel p m (n+1) d (holeTailBlocks n v) := by
  apply kernel_of_congruent hv _ (tail_congruent hz)
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact hv.1 t (List.mem_filter.mp h).1
  · exact hv.1 t (List.mem_filter.mp h).1

theorem tail_support (n : Nat) (v : Vector) :
    ∀ t ∈ holeTailBlocks n v, holeBlock n t.2 ≠ 1 := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · have hh := (List.mem_filter.mp h).2
    have : holeBlock n t.2 = 2 := by simpa using hh
    omega
  · have hh := (List.mem_filter.mp h).2
    have : holeBlock n t.2 = 3 := by simpa using hh
    omega

/-- The remaining mathematical obligation may be restricted to literal tail support. -/
def ResidualSpanning (p m n d : Nat) : Prop :=
  ∀ v, Kernel p m (n+1) d v →
    (∀ g, (p : Int) ∣ vectorCoeff (splitHole n 1 v) g) →
    ∃ c : List (Int × Vector),
      (∀ t ∈ c, t.2 ∈ syzygies m (n+1) d) ∧
      ∀ g, (p : Int) ∣ vectorCoeff v g - vectorCoeff (combine c) g

def TailSpanning (p m n d : Nat) : Prop :=
  ∀ v, Kernel p m (n+1) d v →
    (∀ t ∈ v, holeBlock n t.2 ≠ 1) →
    ∃ c : List (Int × Vector),
      (∀ t ∈ c, t.2 ∈ syzygies m (n+1) d) ∧
      ∀ g, (p : Int) ∣ vectorCoeff v g - vectorCoeff (combine c) g

theorem residual_of_tail {p m n d : Nat} (h : TailSpanning p m n d) :
    ResidualSpanning p m n d := by
  intro v hv hz
  obtain ⟨c,hc,he⟩ := h (holeTailBlocks n v) (tail_kernel hv hz) (tail_support n v)
  refine ⟨c,hc,fun g => ?_⟩
  have hh := Int.dvd_add (tail_congruent hz g) (he g)
  have heq : vectorCoeff v g - vectorCoeff (holeTailBlocks n v) g +
      (vectorCoeff (holeTailBlocks n v) g - vectorCoeff (combine c) g) =
      vectorCoeff v g - vectorCoeff (combine c) g := by omega
  rwa [heq] at hh

theorem tail_of_residual {p m n d : Nat} (h : ResidualSpanning p m n d) :
    TailSpanning p m n d := by
  intro v hv hs
  apply h v hv
  have hz : splitHole n 1 v = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro t ht
    have hh := List.mem_filter.mp ht
    exact hs t hh.1 (by simpa using hh.2)
  intro g
  simp [hz, vectorCoeff]

theorem residual_iff_tail (p m n d : Nat) :
    ResidualSpanning p m n d ↔ TailSpanning p m n d :=
  ⟨tail_of_residual, residual_of_tail⟩

theorem spanning_successor {p m n d : Nat}
    (hn : 0 < n) (small : Spanning p m n d)
    (remaining : ResidualSpanning p m n d) : Spanning p m (n+1) d := by
  intro v hv
  obtain ⟨C,hC,hk,hzero⟩ := first_block_residual_sound hn hv small
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
    rw [vectorCoeff_append, hneg, Programme.«20261104-1627-proof-complexity».HoleCancellation.vectorCoeff_scale] at he
    rw [Programme.«20261104-1627-proof-complexity».SpanningSquareThree.combine_append_coeff]
    simpa only [Int.neg_one_mul, Int.sub_eq_add_neg, Int.neg_add,
      Int.add_assoc] using he


end Programme.«20261104-1627-proof-complexity».HoleResidualSupport
#print axioms Programme.«20261104-1627-proof-complexity».HoleResidualSupport.tail_kernel
#print axioms Programme.«20261104-1627-proof-complexity».HoleResidualSupport.residual_iff_tail
#print axioms Programme.«20261104-1627-proof-complexity».HoleResidualSupport.spanning_successor
