import Programme.«20261104-1627-proof-complexity».IncidentLabelInverse

namespace Programme.«20261104-1627-proof-complexity».IncidentSection
open Programme.«20261104-1627-proof-complexity».MatchingLabels

/-- Taking the incident section preserves each incident label's total integer weight. -/
theorem section_coordinate {m n d h : Nat} (hd : 1 < d)
    {v : Vector} (hv : valid (m+1) n d v)
    {g : Label} (hg : g ∈ labels (m+1) n d) (hx : (m,h) ∈ g.base) :
    vectorCoeff (sectionVector m h v) (sectionLabel m h g) = vectorCoeff v g := by
  induction v with
  | nil => simp [sectionVector, vectorCoeff]
  | cons t v ih =>
    have ht : t.2 ∈ labels (m+1) n d := hv t (by simp)
    have hv' : valid (m+1) n d v := by
      intro a ha
      exact hv a (by simp [ha])
    have hi := ih hv'
    by_cases hs : (m,h) ∈ t.2.base
    · have he : sectionLabel m h t.2 = sectionLabel m h g ↔ t.2 = g := by
        constructor
        · exact section_label_injective hd ht hg hs hx
        · intro e; rw [e]
      by_cases ht' : t.2 = g
      · have he' := he.mpr ht'
        simpa [sectionVector, vectorCoeff, hs, hx, ht', he'] using congrArg (fun z : Int => t.1 + z) hi
      · have he' : sectionLabel m h t.2 ≠ sectionLabel m h g :=
          fun e => ht' (he.mp e)
        simpa [sectionVector, vectorCoeff, hs, ht', he'] using hi
    · have he : t.2 ≠ g := by intro e; apply hs; simpa [e] using hx
      simpa [sectionVector, vectorCoeff, hs, he] using hi


end Programme.«20261104-1627-proof-complexity».IncidentSection
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.section_coordinate
