import Programme.«20261104-1627-proof-complexity».PigeonProjection

namespace Programme.«20261104-1627-proof-complexity».TailMatchingCoordinates
open Programme.«20261104-1627-proof-complexity».MatchingLabels

/-- The actual matching-coordinate function carried by block two. -/
def tailCoordinates (m : Nat) (v : Vector) (M : Matching) : Int :=
  vectorCoeff v ⟨M,true,m⟩

theorem block_two_iff {m n d : Nat} (hd : 0 < d) (g : Label) :
    (g ∈ labels (m+1) n d ∧ pigeonBlock m g = 2) ↔
    ∃ M ∈ matchings m n (d-1), g = ⟨M,true,m⟩ := by
  constructor
  · rintro ⟨hg,hb⟩
    have hu : usesPigeon m g = false := by
      unfold pigeonBlock at hb
      split at hb <;> simp_all
    have hr : g.isRow = true ∧ g.mark = m := by
      simp only [pigeonBlock, hu, Bool.false_eq_true, ↓reduceIte] at hb
      split at hb
      · rename_i h
        simpa using h
      · contradiction
    have ha : ∀ e ∈ g.base, e.1 ≠ m := by
      intro e he eq
      have : usesPigeon m g = true := by
        simp only [usesPigeon, List.any_eq_true]
        exact ⟨e,he,by simp [eq]⟩
      simp_all
    have hm : g.base ∈ matchings (m+1) n (d-1) := by
      simp only [labels, show d ≠ 0 by omega, ↓reduceIte,
        List.mem_flatMap, List.mem_append, List.mem_map] at hg
      obtain ⟨M,hM,hg⟩ := hg
      rcases hg with ⟨i,hi,eq⟩ | ⟨j,hj,eq⟩
      all_goals subst g; exact hM
    refine ⟨g.base, matching_drop_last g.base hm ha, ?_⟩
    cases g
    simp_all
  · rintro ⟨M,hM,rfl⟩
    have ha := matching_rows_lt hM
    have hu : usesPigeon m (⟨M,true,m⟩ : Label) = false := by
      apply Bool.eq_false_iff.mpr
      intro hh
      obtain ⟨e,he,hh⟩ := List.any_eq_true.mp hh
      have := ha e he
      simp only [beq_iff_eq] at hh
      omega
    constructor
    · simp only [labels, show d ≠ 0 by omega, ↓reduceIte,
        List.mem_flatMap, List.mem_append, List.mem_map]
      refine ⟨M, matching_add_last M hM, Or.inl ⟨m, ?_,rfl⟩⟩
      simp only [rows,List.mem_filter,List.mem_range,freeRow,List.all_eq_true]
      refine ⟨by omega, ?_⟩
      intro e he
      have := ha e he
      simpa using (show e.1 ≠ m by omega)
    · simp [pigeonBlock,hu]

theorem block_two_coordinate {m n d : Nat} (hd : 0 < d)
    {M : Matching} (hM : M ∈ matchings m n (d-1)) (v : Vector) :
    vectorCoeff (splitPigeon m 2 v) ⟨M,true,m⟩ = tailCoordinates m v M := by
  have hb := (block_two_iff hd (⟨M,true,m⟩ : Label)).mpr ⟨M,hM,rfl⟩
  unfold tailCoordinates
  induction v with
  | nil => rfl
  | cons t v ih =>
    simp only [splitPigeon, List.filter_cons]
    by_cases ht : t.2 = (⟨M,true,m⟩ : Label)
    · have htb : pigeonBlock m t.2 = 2 := by simpa [ht] using hb.2
      simp [htb, hb.2, vectorCoeff,ht,splitPigeon] at ih ⊢
      exact ih
    · by_cases htb : pigeonBlock m t.2 = 2
      · simp [htb, hb.2, vectorCoeff,ht,splitPigeon] at ih ⊢
        exact ih
      · simp [htb, hb.2, vectorCoeff,ht,splitPigeon] at ih ⊢
        exact ih

end Programme.«20261104-1627-proof-complexity».TailMatchingCoordinates
#print axioms Programme.«20261104-1627-proof-complexity».TailMatchingCoordinates.block_two_iff

#print axioms Programme.«20261104-1627-proof-complexity».TailMatchingCoordinates.block_two_coordinate
