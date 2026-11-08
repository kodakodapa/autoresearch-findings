import Programme.«20261104-1627-proof-complexity».NonincidentExtensions
namespace Programme.«20261104-1627-proof-complexity».IncidentSection
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC
private theorem cf_single (L : List Nat) (hn : L.Nodup) (f : Nat → List Nat)
    (u : List Nat) (a : Nat) (ht : ∀ j ∈ L, (f j).Perm u ↔ j = a) :
    cf (L.map fun j => (1,f j)) u = if a ∈ L then 1 else 0 := by
  induction L with
  | nil => simp [cf]
  | cons b L ih =>
    have hb := ht b (by simp)
    have hi := ih hn.tail (by intro j hj; exact ht j (by simp [hj]))
    by_cases he : b = a
    · subst b
      have hp := hb.mpr rfl
      have ha : a ∉ L := (List.nodup_cons.mp hn).1
      simp [cf, hp, ha] at hi ⊢
      omega
    · have hp : ¬ (f b).Perm u := fun h => he (hb.mp h)
      simpa [cf, hp, he, Ne.symm he] using hi
private theorem cf_none (L : List Nat) (f : Nat → List Nat) (u : List Nat)
    (ht : ∀ j ∈ L, ¬ (f j).Perm u) : cf (L.map fun j => (1,f j)) u = 0 := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have ha := ht a (by simp)
    have hi := ih (by intro j hj; exact ht j (by simp [hj]))
    simpa [cf, ha] using hi

theorem nonincident_label_coeff {m n d h : Nat} (hh : h < n+1)
    {g : Label} (hg : g ∈ labels (m+1) (n+1) (d+1))
    (hx : (m,h) ∉ g.base) (ht : pigeonBlock m g ≠ 1)
    {E : Matching} (hE : E ∈ matchings m n d) :
    coeff (topLabel (m+1) (n+1) g)
      ((m*(n+1)+h)::mono (n+1) (pushMatching h E)) =
      if g = ⟨pushMatching h E,true,m⟩ then 1 else 0 := by
  by_cases he : g = ⟨pushMatching h E,true,m⟩
  · subst g
    change cf ((cols (n+1) (pushMatching h E)).map fun j =>
      (1,(m*(n+1)+j)::mono (n+1) (pushMatching h E))) _ = _
    have hc : h ∈ cols (n+1) (pushMatching h E) := by
      simp only [cols, List.mem_filter, List.mem_range, freeCol, List.all_eq_true]
      refine ⟨hh, ?_⟩
      intro a ha
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      simpa only [bne_iff_ne] using omitHole_ne h b.2
    rw [cf_single (cols (n+1) (pushMatching h E)) (by exact (List.nodup_range).filter _) _ _ h]
    · simp [hc]
    · intro j hj
      have jb := List.mem_range.mp (List.mem_filter.mp hj).1
      have hp := matching_add_last _ (matching_push_mem h E hE)
      have hn := nonincident_extension_iff hh hp hx hE m j jb
      simpa using hn
  · have hz : ∀ i j, j < n+1 →
        (if g.isRow then i = g.mark else j = g.mark) →
        ¬ ((i*(n+1)+j)::mono (n+1) g.base).Perm
          ((m*(n+1)+h)::mono (n+1) (pushMatching h E)) := by
      intro i j hj hm hp
      exact he (nonincident_tail_label hh hg hx ht hE hj hm hp)
    cases hr : g.isRow
    · simp only [topLabel, hr, Bool.false_eq_true, ↓reduceIte]
      change cf ((rows (m+1) g.base).map fun i =>
        (1,(i*(n+1)+g.mark)::mono (n+1) g.base)) _ = _
      have hm : g.mark < n+1 := by
        simp only [labels, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
          List.mem_flatMap, List.mem_append, List.mem_map] at hg
        obtain ⟨B,hB,hg⟩ := hg
        rcases hg with ⟨a,ha,hg⟩ | ⟨a,ha,hg⟩
        · cases hg; simp at hr
        · cases hg; exact List.mem_range.mp (List.mem_filter.mp ha).1
      rw [cf_none]
      · simp [he]
      · intro i hi; exact hz i g.mark hm (by simp [hr])
    · simp only [topLabel, hr, ↓reduceIte]
      change cf ((cols (n+1) g.base).map fun j =>
        (1,(g.mark*(n+1)+j)::mono (n+1) g.base)) _ = _
      rw [cf_none]
      · simp [he]
      · intro j hj
        exact hz g.mark j (List.mem_range.mp (List.mem_filter.mp hj).1) (by simp [hr])
end Programme.«20261104-1627-proof-complexity».IncidentSection
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.nonincident_label_coeff
