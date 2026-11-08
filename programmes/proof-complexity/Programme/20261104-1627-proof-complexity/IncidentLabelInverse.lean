import Programme.«20261104-1627-proof-complexity».IncidentReconstruction
namespace Programme.«20261104-1627-proof-complexity».IncidentSection
open Programme.«20261104-1627-proof-complexity».MatchingLabels

def restoreLabel (m h : Nat) (g : Label) : Label :=
  ⟨ordered (pushMatching h g.base ++ [(m,h)]), g.isRow,
    if g.isRow then g.mark else omitHole h g.mark⟩

theorem section_label_reconstruct {m n d h : Nat} (hd : 1 < d)
    {g : Label} (hg : g ∈ labels (m+1) n d) (hx : (m,h) ∈ g.base) :
    restoreLabel m h (sectionLabel m h g) = g := by
  have hb : g.base ∈ matchings (m+1) n (d-1) := by
    simp only [labels, show d ≠ 0 by omega, ↓reduceIte,
      List.mem_flatMap, List.mem_append, List.mem_map] at hg
    obtain ⟨M,hM,hg⟩ := hg
    rcases hg with ⟨i,hi,rfl⟩ | ⟨j,hj,rfl⟩ <;> exact hM
  have he : d-1 = (d-2)+1 := by omega
  have hbase := section_reconstruct (by simpa only [he] using hb) hx
  have hmark : g.isRow = false → g.mark ≠ h := by
    intro hr
    simp only [labels, show d ≠ 0 by omega, ↓reduceIte,
      List.mem_flatMap, List.mem_append, List.mem_map] at hg
    obtain ⟨M,hM,hg⟩ := hg
    rcases hg with ⟨i,hi,rfl⟩ | ⟨j,hj,rfl⟩
    · contradiction
    · have ht := List.all_eq_true.mp (List.mem_filter.mp hj).2 (m,h) hx
      exact (show h ≠ j by simpa only [freeCol,bne_iff_ne] using ht).symm
  cases g with
  | mk M r a =>
    cases r with
    | false =>
      have hm : a ≠ h := hmark rfl
      change Label.mk (ordered (pushMatching h (sectionBase m h M) ++ [(m,h)])) false (omitHole h (closeHole h a)) = Label.mk M false a
      rw [hbase, omit_close h a hm]
    | true =>
      change Label.mk (ordered (pushMatching h (sectionBase m h M) ++ [(m,h)])) true a = Label.mk M true a
      rw [hbase]

theorem section_label_injective {m n d h : Nat} (hd : 1 < d)
    {g k : Label} (hg : g ∈ labels (m+1) n d)
    (hk : k ∈ labels (m+1) n d) (hx : (m,h) ∈ g.base)
    (hy : (m,h) ∈ k.base) (he : sectionLabel m h g = sectionLabel m h k) :
    g = k := by
  rw [← section_label_reconstruct hd hg hx,
    ← section_label_reconstruct hd hk hy, he]
end Programme.«20261104-1627-proof-complexity».IncidentSection
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.section_label_reconstruct
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.section_label_injective
