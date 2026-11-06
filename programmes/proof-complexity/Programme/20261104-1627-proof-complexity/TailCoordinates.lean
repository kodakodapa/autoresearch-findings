import Programme.«20261104-1627-proof-complexity».ResidualSupport

namespace Programme.«20261104-1627-proof-complexity».TailCoordinates
open Programme.«20261104-1627-proof-complexity».MatchingLabels Programme.«20261104-1627-proof-complexity».ResidualSupport

/-- The last-row pivot part has no last-row edge in its base. -/
theorem block_two_iff (m : Nat) (g : Label) :
    pigeonBlock m g = 2 ↔
    usesPigeon m g = false ∧ g.isRow = true ∧ g.mark = m := by
  unfold pigeonBlock
  cases hu : usesPigeon m g <;> cases hr : g.isRow <;>
    by_cases hm : g.mark = m <;> simp [hu, hr, hm]

/-- The remaining part is exactly the base-incident part. -/
theorem block_three_iff (m : Nat) (g : Label) :
    pigeonBlock m g = 3 ↔ usesPigeon m g = true := by
  unfold pigeonBlock
  cases hu : usesPigeon m g <;> simp [hu]
  cases hr : g.isRow <;> by_cases hm : g.mark = m <;> simp [hr, hm]

/-- Literal tail support is precisely the union of these two coordinate types. -/
theorem tail_label_iff (m : Nat) (g : Label) :
    pigeonBlock m g ≠ 1 ↔
    (usesPigeon m g = false ∧ g.isRow = true ∧ g.mark = m) ∨
    usesPigeon m g = true := by
  constructor
  · intro h
    rcases pigeonBlock_cases m g with h1 | h2 | h3
    · exact False.elim (h h1)
    · exact Or.inl ((block_two_iff m g).mp h2)
    · exact Or.inr ((block_three_iff m g).mp h3)
  · intro h
    rcases h with h | h
    · rw [(block_two_iff m g).mpr h]; decide
    · rw [(block_three_iff m g).mpr h]; decide

/-- A tail vector has no column label whose base avoids the last pigeon. -/
theorem tail_column_incident {m : Nat} {v : Vector}
    (hs : ∀ t ∈ v, pigeonBlock m t.2 ≠ 1)
    {t : Int × Label} (ht : t ∈ v) (hc : t.2.isRow = false) :
    ∃ e ∈ t.2.base, e.1 = m := by
  have h := (tail_label_iff m t.2).mp (hs t ht)
  have hu : usesPigeon m t.2 = true := by
    rcases h with h | h
    · simp [hc] at h
    · exact h
  obtain ⟨e, he, hr⟩ := List.any_eq_true.mp hu
  exact ⟨e, he, by simpa using hr⟩

/-- After pivot coordinates vanish, only base-incident coordinates survive modulo p. -/
theorem tail_coeff_incident {p m : Nat} {v : Vector}
    (hs : ∀ t ∈ v, pigeonBlock m t.2 ≠ 1)
    (hz : ∀ g, (p : Int) ∣ vectorCoeff (splitPigeon m 2 v) g)
    (g : Label) :
    (p : Int) ∣ vectorCoeff v g - vectorCoeff (splitPigeon m 3 v) g := by
  have hnil : splitPigeon m 1 v = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro t ht
    have h := List.mem_filter.mp ht
    exact hs t h.1 (by simpa using h.2)
  have he := vectorCoeff_splitPigeon m v g
  have hz' := hz g
  simp only [hnil, vectorCoeff, List.filter_nil, List.map_nil, List.sum_nil,
    Int.zero_add] at he
  change vectorCoeff v g = vectorCoeff (splitPigeon m 2 v) g +
    vectorCoeff (splitPigeon m 3 v) g at he
  rw [he]
  simpa using hz'

/-- Once the last-row pivot is eliminated, its base-incident remainder is itself
in the same polynomial kernel, ready for a hole-section argument. -/
theorem incident_kernel {p m n d : Nat} {v : Vector}
    (hv : Kernel p (m+1) n d v)
    (hs : ∀ t ∈ v, pigeonBlock m t.2 ≠ 1)
    (hz : ∀ g, (p : Int) ∣ vectorCoeff (splitPigeon m 2 v) g) :
    Kernel p (m+1) n d (splitPigeon m 3 v) := by
  exact kernel_of_congruent hv (splitPigeon_valid m 3 hv.1)
    (tail_coeff_incident hs hz)

end Programme.«20261104-1627-proof-complexity».TailCoordinates
#print axioms Programme.«20261104-1627-proof-complexity».TailCoordinates.tail_label_iff
#print axioms Programme.«20261104-1627-proof-complexity».TailCoordinates.tail_column_incident
#print axioms Programme.«20261104-1627-proof-complexity».TailCoordinates.tail_coeff_incident

#print axioms Programme.«20261104-1627-proof-complexity».TailCoordinates.incident_kernel
