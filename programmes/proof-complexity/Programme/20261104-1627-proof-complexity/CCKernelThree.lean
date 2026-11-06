import Programme.«20261104-1627-proof-complexity».CCNormalize
import Programme.«20261104-1627-proof-complexity».KernelLinear

namespace Programme.«20261104-1627-proof-complexity».CCNormalize
open Programme.«20261104-1627-proof-complexity».MatchingLabels Programme.«20261104-1627-proof-complexity».MixedEliminate
open Programme.«20261029-1156-proof-complexity».StdPC

private theorem pair_cf (a b : Nat) (u : List Nat) :
    ([a,b].Perm u) ↔ ([b,a].Perm u) := by
  exact ⟨fun h => (List.Perm.swap a b []).trans h,
    fun h => (List.Perm.swap b a []).trans h⟩

/-- Soundness of the particular correction on the square degree-two board. -/
theorem cc_three_kernel (p : Nat) : Kernel p 3 3 2 (cc 3 [] 0 1) := by
  constructor
  · intro t ht
    have he : cc 3 [] 0 1 =
      [(1,edgeColLabel 0 1 0),(1,edgeColLabel 1 1 0),(1,edgeColLabel 2 1 0),
       (-1,edgeColLabel 0 0 1),(-1,edgeColLabel 1 0 1),(-1,edgeColLabel 2 0 1)] := by
      simp [cc, rows, Programme.«20261104-1627-proof-complexity».MatchingLabels.freeRow, ordered, edgeColLabel, List.range_succ] <;> rfl
    rw [he] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals unfold labels matchings rows cols Programme.«20261104-1627-proof-complexity».MatchingLabels.freeRow freeCol edgeColLabel
    all_goals decide
  · intro u
    have h01 := pair_cf 0 4 u
    have h02 := pair_cf 0 7 u
    have h10 := pair_cf 3 1 u
    have h12 := pair_cf 3 7 u
    have h20 := pair_cf 6 1 u
    have h21 := pair_cf 6 4 u
    change (p : Int) ∣ coeff (top 3 3 (cc 3 [] 0 1)) u - coeff ⟨[]⟩ u
    have ht : (top 3 3 (cc 3 [] 0 1)).terms =
      [(1,[3,1]),(1,[6,1]),(1,[0,4]),(1,[6,4]),(1,[0,7]),(1,[3,7]),
       (-1,[4,0]),(-1,[7,0]),(-1,[1,3]),(-1,[7,3]),(-1,[1,6]),(-1,[4,6])] := by
        simp [top, cc, rows, Programme.«20261104-1627-proof-complexity».MatchingLabels.freeRow, ordered, topLabel, mono, List.range_succ] <;> rfl
    simp only [coeff, ht]
    by_cases h1 : [0,4].Perm u <;>
      by_cases h2 : [0,7].Perm u <;>
      by_cases h3 : [3,1].Perm u <;>
      by_cases h4 : [3,7].Perm u <;>
      by_cases h5 : [6,1].Perm u <;>
      by_cases h6 : [6,4].Perm u <;>
      simp_all [cf]

 theorem corrected_kernel {p : Nat} (v : Vector) (hv : Kernel p 3 3 2 v) :
    Kernel p 3 3 2 (corrected 3 v) := by
  exact kernel_append hv (kernel_scale (cc_three_kernel p) (-circulation v 0 0 1 2))
end Programme.«20261104-1627-proof-complexity».CCNormalize
#print axioms Programme.«20261104-1627-proof-complexity».CCNormalize.cc_three_kernel
#print axioms Programme.«20261104-1627-proof-complexity».CCNormalize.corrected_kernel
