import Programme.«20261104-1627-proof-complexity».TailTwoSupport
import Programme.«20261104-1627-proof-complexity».DegreeTwoLabels
namespace Programme.«20261104-1627-proof-complexity».IncidentSection
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261104-1627-proof-complexity».TailMatchingCoordinates
open Programme.«20261104-1627-proof-complexity».MixedAggregate

theorem block_two_zero_of_singletons {p m n : Nat} {v : Vector}
    (hv : valid (m+1) n 2 v)
    (hz : ∀ i, i < m → ∀ j, j < n →
      (p : Int) ∣ vectorCoeff v ⟨[(i,j)],true,m⟩) :
    ∀ g, pigeonBlock m g = 2 → (p : Int) ∣ vectorCoeff v g := by
  intro g hg
  by_cases hl : g ∈ labels (m+1) n 2
  · obtain ⟨M,hM,rfl⟩ := (block_two_iff (by decide : 0 < 2) g).mp ⟨hl,hg⟩
    obtain ⟨i,hi,j,hj,rfl⟩ := matching_one_cases hM
    exact hz i hi j hj
  · have he : vectorCoeff v g = 0 := by
      unfold vectorCoeff
      have hf : v.filter (fun t => t.2 == g) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro t ht
        have hmem := hv t ht
        simpa only [beq_iff_eq] using
          (show t.2 ≠ g by intro h; exact hl (h ▸ hmem))
      rw [hf]; rfl
    rw [he]; exact ⟨0, by simp⟩
theorem tail_two_block_three {p m n : Nat} (hn : 2 < n)
    {v : Vector} (hv : Kernel p (m+1) n 2 v)
    (ht : ∀ t ∈ v, pigeonBlock m t.2 ≠ 1) :
    ∃ C : List (Int × Vector), ∃ w : Vector,
      (∀ t ∈ C, t.2 ∈ syzygies (m+1) n 2) ∧
      Kernel p (m+1) n 2 w ∧
      (∀ t ∈ w, pigeonBlock m t.2 = 3) ∧
      ∀ g, (p : Int) ∣ vectorCoeff
        (v ++ (combine C).map (fun t => (-t.1,t.2))) g - vectorCoeff w g := by
  obtain ⟨a,b,hab⟩ := tail_two_row_col hn hv ht
  let C := twoCorrection m n a b
  let u := v ++ (combine C).map (fun t => (-t.1,t.2))
  have hC := twoCorrection_member m n a b
  have hu : Kernel p (m+1) n 2 u := by
    have hk := kernel_scale (kernel_combine C (fun t ht =>
      syzygies_sound p (m+1) n 2 t.2 (hC t ht))) (-1)
    have he : ((combine C).map fun t => ((-1 : Int)*t.1,t.2)) =
        ((combine C).map fun t => (-t.1,t.2)) := by simp
    rw [he] at hk
    exact kernel_append hv hk
  have hut : ∀ t ∈ u, pigeonBlock m t.2 ≠ 1 :=
    correction_residual_support ht a b
  have hz : ∀ g, pigeonBlock m g = 2 → (p : Int) ∣ vectorCoeff u g := by
    apply block_two_zero_of_singletons hu.1
    intro i hi j hj
    have he : ((combine C).map fun t => (-t.1,t.2)) =
        ((combine C).map fun t => ((-1 : Int)*t.1,t.2)) := by simp
    change (p : Int) ∣ vectorCoeff (v ++ _) _
    rw [vectorCoeff_append,he,coeff_scale]
    have hc := twoCorrection_coordinate hi hj a b
    change vectorCoeff (combine C) _ = _ at hc
    rw [hc]
    simpa only [Int.neg_mul,Int.one_mul,Int.sub_eq_add_neg] using hab i hi j hj
  refine ⟨C,splitPigeon m 3 u,hC,block_three_kernel hu hut hz,?_,
    block_three_congruent hut hz⟩
  intro t ht'
  exact of_decide_eq_true (List.mem_filter.mp ht').2
end Programme.«20261104-1627-proof-complexity».IncidentSection
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.block_two_zero_of_singletons

#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.tail_two_block_three
