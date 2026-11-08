import Programme.«20261104-1627-proof-complexity».IncidentAxes

namespace Programme.«20261104-1627-proof-complexity».IncidentSection
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC

private theorem cf_of_perm {L K : List (Int × List Nat)} (h : L.Perm K) (u : List Nat) :
    cf L u = cf K u := by
  have hp := ((h.filter (fun t => decide (t.2.Perm u))).map Prod.fst)
  have hs {a b : List Int} (hp : a.Perm b) : a.sum = b.sum := by
    induction hp with
    | nil => rfl
    | cons x hp ih => simp only [List.sum_cons,ih]
    | swap x y l => simp only [List.sum_cons]; omega
    | trans hp hq ih ij => exact ih.trans ij
  exact hs hp

private theorem cf_tests (L : List Nat) (f g : Nat → List Nat) (u v : List Nat)
    (ht : ∀ a ∈ L, (f a).Perm u ↔ (g a).Perm v) :
    cf (L.map fun a => (1,f a)) u = cf (L.map fun a => (1,g a)) v := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have ha := ht a (by simp)
    have hi := ih (by intro b hb; exact ht b (by simp [hb]))
    by_cases hp : (f a).Perm u
    · have hq := ha.mp hp
      simpa [cf,hp,hq] using congrArg (fun z : Int => 1+z) hi
    · have hq : ¬ (g a).Perm v := fun h => hp (ha.mpr h)
      simpa [cf,hp,hq] using hi

/-- Exact coefficient transport for each label whose base contains the incident edge. -/
theorem incident_label_coeff {m n d h : Nat} (hn : 0 < n) (hh : h < n+1)
    (hd : 1 < d) {g : Label} (hg : g ∈ labels (m+1) (n+1) d)
    (hx : (m,h) ∈ g.base) {E : Matching}
    (hE : E ∈ matchings m n (d-1)) :
    coeff (topLabel (m+1) (n+1) g)
      ((m*(n+1)+h) :: mono (n+1) (pushMatching h E)) =
    coeff (topLabel m n (sectionLabel m h g)) (mono n E) := by
  have he : d-1 = (d-2)+1 := by omega
  have hEc := matching_cols_lt hE
  simp only [labels, show d ≠ 0 by omega, ↓reduceIte,
    List.mem_flatMap, List.mem_append, List.mem_map] at hg
  obtain ⟨B,hB,hg⟩ := hg
  have hB' : B ∈ matchings (m+1) (n+1) ((d-2)+1) := by simpa only [he] using hB
  rcases hg with ⟨i,hi,rfl⟩ | ⟨j,hj,rfl⟩
  · change cf ((cols (n+1) B).map fun j => (1,(i*(n+1)+j)::mono (n+1) B)) _ =
      cf ((cols n (sectionBase m h B)).map fun j => (1,(i*n+j)::mono n (sectionBase m h B))) _
    rw [← cf_of_perm ((section_cols hh hB' hx).map
      (fun j => (1,(i*(n+1)+j)::mono (n+1) B))) _]
    simp only [List.map_map, Function.comp_def]
    apply cf_tests
    intro j hj
    exact incident_extension_perm hn hh hB' hx hEc i j (List.mem_range.mp (List.mem_filter.mp hj).1)
  · have jh : j ≠ h := by
      have ht := List.all_eq_true.mp (List.mem_filter.mp hj).2 (m,h) hx
      exact (show h ≠ j by simpa only [freeCol,bne_iff_ne] using ht).symm
    have jc : closeHole h j < n := by
      have jb := List.mem_range.mp (List.mem_filter.mp hj).1
      unfold closeHole
      split <;> omega
    change cf ((rows (m+1) B).map fun i => (1,(i*(n+1)+j)::mono (n+1) B)) _ =
      cf ((rows m (sectionBase m h B)).map fun i => (1,(i*n+closeHole h j)::mono n (sectionBase m h B))) _
    rw [section_rows hB' hx]
    apply cf_tests
    intro i hi
    have ht := incident_extension_perm hn hh hB' hx hEc i (closeHole h j) jc
    simpa only [omit_close h j jh] using ht

end Programme.«20261104-1627-proof-complexity».IncidentSection
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.incident_label_coeff
