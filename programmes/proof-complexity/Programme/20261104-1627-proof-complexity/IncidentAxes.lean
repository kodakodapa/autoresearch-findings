import Programme.«20261104-1627-proof-complexity».IncidentMonomials

namespace Programme.«20261104-1627-proof-complexity».IncidentSection
open Programme.«20261104-1627-proof-complexity».MatchingLabels

private theorem all_perm {α : Type} {L K : List α} (hp : L.Perm K) (f : α → Bool) :
    L.all f = K.all f := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  exact ⟨fun hh a ha => hh a (hp.mem_iff.mpr ha),
    fun hh a ha => hh a (hp.mem_iff.mp ha)⟩

theorem section_free_row {m n e h : Nat} {B : Matching}
    (hB : B ∈ matchings (m+1) n (e+1)) (hx : (m,h) ∈ B) (i : Nat) :
    freeRow B i = (decide (m ≠ i) && freeRow (sectionBase m h B) i) := by
  unfold freeRow
  rw [all_perm (List.perm_cons_erase hx)]
  rw [← section_push hB hx]
  simp only [pushMatching, List.all_map, Function.comp_def, List.all_cons]
  by_cases hi : m = i <;> simp [hi]

theorem section_free_col {m n e h : Nat} {B : Matching}
    (hB : B ∈ matchings (m+1) n (e+1)) (hx : (m,h) ∈ B) (j : Nat) :
    freeCol B (omitHole h j) = freeCol (sectionBase m h B) j := by
  unfold freeCol
  rw [all_perm (List.perm_cons_erase hx)]
  rw [← section_push hB hx]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, pushMatching,
    List.all_map, Function.comp_def, List.all_eq_true]
  have hn : h ≠ omitHole h j := (omitHole_ne h j).symm
  constructor
  · intro hh a ha he
    exact hh.2 a ha (congrArg (omitHole h) he)
  · intro hh
    refine ⟨hn, ?_⟩
    intro a ha he
    exact hh a ha (omitHole_injective h he)

theorem section_rows {m n e h : Nat} {B : Matching}
    (hB : B ∈ matchings (m+1) n (e+1)) (hx : (m,h) ∈ B) :
    rows (m+1) B = rows m (sectionBase m h B) := by
  unfold rows
  rw [List.range_succ, List.filter_append]
  have hz : freeRow B m = false := by rw [section_free_row hB hx]; simp
  simp only [List.filter_cons, hz, Bool.false_eq_true, ↓reduceIte,
    List.filter_nil, List.append_nil]
  apply List.filter_congr
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [section_free_row hB hx]
  simp [show m ≠ i by omega]

/-- The free holes correspond bijectively under the actual omission map. -/
theorem section_cols {m n e h : Nat} (hh : h < n+1) {B : Matching}
    (hB : B ∈ matchings (m+1) (n+1) (e+1)) (hx : (m,h) ∈ B) :
    (cols n (sectionBase m h B)).map (omitHole h) |>.Perm (cols (n+1) B) := by
  apply List.perm_ext_iff_of_nodup
    ((List.nodup_range (n := n)).filter _ |>.map (omitHole h) (by intro a b hab he; exact hab (omitHole_injective h he)))
    ((List.nodup_range (n := n+1)).filter _ ) |>.mpr
  intro j
  simp only [List.mem_map, cols, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨a,⟨ha,hf⟩,rfl⟩
    exact ⟨omitHole_lt ha, by rw [section_free_col hB hx]; exact hf⟩
  · rintro ⟨hj,hf⟩
    have hjh : j ≠ h := by
      intro he
      have ht := List.all_eq_true.mp hf (m,h) hx
      simp [he] at ht
    have hc : closeHole h j < n := by
      unfold closeHole
      split <;> omega
    refine ⟨closeHole h j, ⟨hc, ?_⟩, omit_close h j hjh⟩
    rw [← section_free_col hB hx, omit_close h j hjh]
    exact hf

end Programme.«20261104-1627-proof-complexity».IncidentSection
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.section_free_row
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.section_free_col
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.section_rows

#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.section_cols
