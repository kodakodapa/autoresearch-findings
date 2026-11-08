import Programme.«20261104-1627-proof-complexity».MatchingDeletion
import Programme.«20261104-1627-proof-complexity».OmissionCoverage
import Programme.«20261104-1627-proof-complexity».PigeonProjection

namespace Programme.«20261104-1627-proof-complexity».IncidentSection
open Programme.«20261104-1627-proof-complexity».MatchingLabels

/-- Delete the incident last-pigeon edge and close its hole. -/
def sectionBase (m h : Nat) (M : Matching) : Matching :=
  pullMatching h (M.erase (m,h))

 theorem incident_base {m n e h : Nat} (hh : h < n)
    {M : Matching} (hM : M ∈ matchings (m+1) n (e+1))
    (hx : (m,h) ∈ M) :
    sectionBase m h M ∈ matchings m (n-1) e := by
  have hf := matching_erase_fresh hM hx
  have he := matching_erase_mem hM hx
  have hr : ∀ a ∈ M.erase (m,h), a.1 ≠ m := by
    simpa only [rows, List.mem_filter, freeRow, List.all_eq_true, bne_iff_ne]
      using (List.mem_filter.mp hf.1).2
  have hc : ∀ a ∈ M.erase (m,h), a.2 ≠ h := by
    simpa only [cols, List.mem_filter, freeCol, List.all_eq_true, bne_iff_ne]
      using (List.mem_filter.mp hf.2).2
  have hs := matching_drop_last _ he hr
  have hn : n-1+1 = n := by omega
  unfold sectionBase
  apply matching_pull_mem (by omega)
  · simpa only [hn] using hs
  · exact hc

def sectionLabel (m h : Nat) (g : Label) : Label :=
  ⟨sectionBase m h g.base, g.isRow,
    if g.isRow then g.mark else closeHole h g.mark⟩

theorem incident_label {m n d h : Nat} (hh : h < n) (hd : 1 < d)
    {g : Label} (hg : g ∈ labels (m+1) n d) (hx : (m,h) ∈ g.base) :
    sectionLabel m h g ∈ labels m (n-1) (d-1) := by
  simp only [labels, show d ≠ 0 by omega, ↓reduceIte,
    List.mem_flatMap, List.mem_append, List.mem_map] at hg
  obtain ⟨M,hM,hg⟩ := hg
  have hlen : d-1 = (d-2)+1 := by omega
  rcases hg with ⟨i,hi,rfl⟩ | ⟨j,hj,rfl⟩
  · have hb := incident_base hh (by simpa only [hlen] using hM) hx
    have hif := List.mem_filter.mp hi
    have him : i ≠ m := by
      have := List.all_eq_true.mp hif.2 (m,h) hx
      exact (show m ≠ i by simpa only [freeRow, bne_iff_ne] using this).symm
    have hir : i ∈ rows m (sectionBase m h M) := by
      simp only [rows, List.mem_filter, List.mem_range] at hi ⊢
      refine ⟨by omega, ?_⟩
      simp only [freeRow, sectionBase, pullMatching, List.all_map,
        List.all_eq_true, Function.comp_apply]
      intro a ha
      exact List.all_eq_true.mp hi.2 a (List.mem_of_mem_erase ha)
    simp only [labels, show d-1 ≠ 0 by omega, ↓reduceIte,
      List.mem_flatMap, List.mem_append, List.mem_map]
    exact ⟨sectionBase m h M, hb, Or.inl ⟨i,hir,rfl⟩⟩
  · have hb := incident_base hh (by simpa only [hlen] using hM) hx
    have hjf := List.mem_filter.mp hj
    have hjh : j ≠ h := by
      have := List.all_eq_true.mp hjf.2 (m,h) hx
      have : h ≠ j := by simpa only [freeCol, bne_iff_ne] using this
      exact this.symm
    have hjr : closeHole h j ∈ cols (n-1) (sectionBase m h M) := by
      simp only [cols, List.mem_filter, List.mem_range] at hj ⊢
      refine ⟨?_, ?_⟩
      · unfold closeHole
        split <;> omega
      · simp only [freeCol, sectionBase, pullMatching, List.all_map,
          List.all_eq_true, Function.comp_apply, bne_iff_ne]
        intro a ha heq
        have hf := matching_erase_fresh (by simpa only [hlen] using hM) hx
        have hah : a.2 ≠ h := by
          have ht := List.all_eq_true.mp (List.mem_filter.mp hf.2).2 a ha
          simpa only [freeCol,bne_iff_ne] using ht
        have he := congrArg (omitHole h) heq
        rw [omit_close h a.2 hah, omit_close h j hjh] at he
        have ht := List.all_eq_true.mp hj.2 a (List.mem_of_mem_erase ha)
        exact (show a.2 ≠ j by simpa only [freeCol,bne_iff_ne] using ht) he
    simp only [labels, show d-1 ≠ 0 by omega, ↓reduceIte,
      List.mem_flatMap, List.mem_append, List.mem_map]
    exact ⟨sectionBase m h M, hb, Or.inr ⟨closeHole h j,hjr,rfl⟩⟩

/-- Actual incident-edge section, retaining the original integer weights. -/
def sectionVector (m h : Nat) (v : Vector) : Vector :=
  (v.filter fun t => (m,h) ∈ t.2.base).map fun t => (t.1, sectionLabel m h t.2)

theorem section_valid {m n d h : Nat} (hh : h < n) (hd : 1 < d)
    {v : Vector} (hv : valid (m+1) n d v) :
    valid m (n-1) (d-1) (sectionVector m h v) := by
  intro t ht
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
  have hs := List.mem_filter.mp ha
  exact incident_label hh hd (hv a hs.1) (of_decide_eq_true hs.2)

end Programme.«20261104-1627-proof-complexity».IncidentSection
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.incident_base

#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.incident_label
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.section_valid
