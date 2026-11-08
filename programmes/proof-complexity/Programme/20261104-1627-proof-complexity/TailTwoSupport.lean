import Programme.«20261104-1627-proof-complexity».TailTwoCorrection
import Programme.«20261104-1627-proof-complexity».TailNormalization
namespace Programme.«20261104-1627-proof-complexity».IncidentSection
open Programme.«20261104-1627-proof-complexity».MatchingLabels
private theorem singleton_block (m j i : Nat) (r : Bool) :
    pigeonBlock m ⟨ordered [(m,j)],r,i⟩ = 3 := by
  simp [ordered, pigeonBlock, usesPigeon]
theorem twoCorrection_support (m n : Nat) (a b : Nat → Int) :
    ∀ t ∈ combine (twoCorrection m n a b), pigeonBlock m t.2 ≠ 1 := by
  intro t ht
  obtain ⟨s,hs,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨u,hu,he⟩ := List.mem_map.mp ht
  subst t
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hs
    rcases List.mem_append.mp hu with hu | hu
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hu
      simp only [List.nil_append]
      rw [singleton_block]
      decide
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hu
      have hi' := List.mem_range.mp hi
      simp [pigeonBlock,usesPigeon,ordered,show i ≠ m by omega]
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hs
    rcases List.mem_append.mp hu with hu | hu
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hu
      have him : i ≠ m := by simpa using (List.mem_filter.mp hi).2
      simp [pigeonBlock,usesPigeon,ordered,him]
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hu
      simp only [List.nil_append]
      rw [singleton_block]
      decide
theorem correction_residual_support {m n : Nat} {v : Vector}
    (ht : ∀ t ∈ v, pigeonBlock m t.2 ≠ 1) (a b : Nat → Int) :
    ∀ t ∈ v ++ (combine (twoCorrection m n a b)).map (fun t => (-t.1,t.2)),
      pigeonBlock m t.2 ≠ 1 := by
  intro t ht'
  rcases List.mem_append.mp ht' with h | h
  · exact ht t h
  · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp h
    exact twoCorrection_support m n a b u hu

theorem block_three_congruent {p m : Nat} {v : Vector}
    (ht : ∀ t ∈ v, pigeonBlock m t.2 ≠ 1)
    (hz : ∀ g, pigeonBlock m g = 2 → (p : Int) ∣ vectorCoeff v g) :
    ∀ g, (p : Int) ∣ vectorCoeff v g - vectorCoeff (splitPigeon m 3 v) g := by
  intro g
  have filter_coeff (b : Nat) : vectorCoeff (splitPigeon m b v) g =
      if pigeonBlock m g = b then vectorCoeff v g else 0 := by
    clear ht hz
    induction v with
    | nil => simp [splitPigeon,vectorCoeff]
    | cons t v ih =>
      by_cases he : t.2 = g
      · subst g
        by_cases hb : pigeonBlock m t.2 = b <;>
          simp [splitPigeon,vectorCoeff,hb] at ih ⊢ <;> exact ih
      · by_cases hb : pigeonBlock m t.2 = b <;>
          simp [splitPigeon,vectorCoeff,he,hb] at ih ⊢ <;> exact ih
  rw [filter_coeff]
  rcases pigeonBlock_cases m g with h | h | h
  · have he : vectorCoeff v g = 0 := by
      unfold vectorCoeff
      have hf : v.filter (fun t => t.2 == g) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro t ht'
        have hn := ht t ht'
        simpa only [beq_iff_eq] using (show t.2 ≠ g by intro he; exact hn (he ▸ h))
      rw [hf]; rfl
    simp [h,he]
  · simpa [h] using hz g h
  · simp [h]

theorem block_three_kernel {p m n d : Nat} {v : Vector}
    (hv : Kernel p (m+1) n d v)
    (ht : ∀ t ∈ v, pigeonBlock m t.2 ≠ 1)
    (hz : ∀ g, pigeonBlock m g = 2 → (p : Int) ∣ vectorCoeff v g) :
    Kernel p (m+1) n d (splitPigeon m 3 v) :=
  kernel_of_aggregate_congruent hv (splitPigeon_valid m 3 hv.1)
    (block_three_congruent ht hz)
end Programme.«20261104-1627-proof-complexity».IncidentSection
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.twoCorrection_support

#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.correction_residual_support
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.block_three_congruent
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.block_three_kernel
