import Programme.«20261104-1627-proof-complexity».IncidentLabelCoefficient

namespace Programme.«20261104-1627-proof-complexity».IncidentSection
open Programme.«20261104-1627-proof-complexity».MatchingLabels

/-- A nonincident base can hit the incident monomial only by extending at that edge. -/
theorem nonincident_extension_iff {m n d h : Nat} (hh : h < n+1)
    {B E : Matching} (hB : B ∈ matchings (m+1) (n+1) d)
    (hx : (m,h) ∉ B) (hE : E ∈ matchings m n d)
    (i j : Nat) (hj : j < n+1) :
    ((i*(n+1)+j)::mono (n+1) B).Perm
      ((m*(n+1)+h)::mono (n+1) (pushMatching h E)) ↔
    i = m ∧ j = h ∧ B = pushMatching h E := by
  have hc := matching_cols_lt hB
  have hp := matching_push_mem h E hE
  have hpc := matching_cols_lt hp
  have hcols : ∀ a ∈ (i,j)::B, a.2 < n+1 := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hj
    · exact hc a ha
  have htcols : ∀ a ∈ (m,h)::pushMatching h E, a.2 < n+1 := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hh
    · exact hpc a ha
  change (mono (n+1) ((i,j)::B)).Perm
    (mono (n+1) ((m,h)::pushMatching h E)) ↔ _
  rw [mono_perm_iff (by omega) _ _ hcols htcols]
  constructor
  · intro ht
    have hm : (m,h) ∈ (i,j)::B := ht.symm.mem_iff.mp (by simp)
    have he : (m,h) = (i,j) := (List.mem_cons.mp hm).resolve_right hx
    have hi : i = m := (congrArg Prod.fst he).symm
    have hj' : j = h := (congrArg Prod.snd he).symm
    subst i; subst j
    have hb := List.Perm.cons_inv ht
    have hs := matching_rows_strict hB
    have ht := matching_rows_strict hp
    exact ⟨rfl,rfl,hb.eq_of_pairwise (by intro a b _ _ hab hba; omega) hs ht⟩
  · rintro ⟨rfl,rfl,rfl⟩
    exact List.Perm.refl _

/-- Every surviving extension of a nonincident tail label is the block-two label. -/
theorem nonincident_tail_label {m n d h : Nat} (hh : h < n+1)
    {g : Label} (hg : g ∈ labels (m+1) (n+1) (d+1))
    (hx : (m,h) ∉ g.base) (ht : pigeonBlock m g ≠ 1)
    {E : Matching} (hE : E ∈ matchings m n d)
    {i j : Nat} (hj : j < n+1)
    (he : if g.isRow then i = g.mark else j = g.mark)
    (hp : ((i*(n+1)+j)::mono (n+1) g.base).Perm
      ((m*(n+1)+h)::mono (n+1) (pushMatching h E))) :
    g = ⟨pushMatching h E,true,m⟩ := by
  have hb : g.base ∈ matchings (m+1) (n+1) d := by
    simp only [labels, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
      List.mem_flatMap, List.mem_append, List.mem_map] at hg
    obtain ⟨B,hB,hg⟩ := hg
    rcases hg with ⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩ <;> exact hB
  obtain ⟨hi,hj',hb'⟩ := (nonincident_extension_iff hh hb hx hE i j hj).mp hp
  have hu : usesPigeon m g = false := by
    apply Bool.eq_false_iff.mpr
    intro hu
    obtain ⟨a,ha,ha'⟩ := List.any_eq_true.mp hu
    rw [hb'] at ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    have hr := matching_rows_lt hE b hb
    simp only [beq_iff_eq] at ha'
    change b.1 = m at ha'
    omega
  have hr : g.isRow = true := by
    cases hr : g.isRow
    · simp [pigeonBlock,hu,hr] at ht
    · rfl
  have hm : g.mark = m := by
    have he' : i = g.mark := by simpa only [hr, ↓reduceIte] using he
    omega
  cases g
  simp_all

end Programme.«20261104-1627-proof-complexity».IncidentSection
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.nonincident_extension_iff

#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.nonincident_tail_label
