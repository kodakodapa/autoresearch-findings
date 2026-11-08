import Programme.«20261104-1627-proof-complexity».IncidentSection

namespace Programme.«20261104-1627-proof-complexity».IncidentSection
open Programme.«20261104-1627-proof-complexity».MatchingLabels

theorem section_push {m n e h : Nat} {M : Matching}
    (hM : M ∈ matchings (m+1) n (e+1)) (hx : (m,h) ∈ M) :
    pushMatching h (sectionBase m h M) = M.erase (m,h) := by
  apply push_pull
  have hf := matching_erase_fresh hM hx
  intro a ha
  have ht := List.all_eq_true.mp (List.mem_filter.mp hf.2).2 a ha
  simpa only [freeCol, bne_iff_ne] using ht

theorem section_reconstruct {m n e h : Nat} {M : Matching}
    (hM : M ∈ matchings (m+1) n (e+1)) (hx : (m,h) ∈ M) :
    ordered (pushMatching h (sectionBase m h M) ++ [(m,h)]) = M := by
  rw [section_push hM hx]
  exact matching_erase_reconstruct hM hx

theorem section_injective {m n e h : Nat} {M N : Matching}
    (hM : M ∈ matchings (m+1) n (e+1)) (hx : (m,h) ∈ M)
    (hN : N ∈ matchings (m+1) n (e+1)) (hy : (m,h) ∈ N)
    (he : sectionBase m h M = sectionBase m h N) : M = N := by
  rw [← section_reconstruct hM hx, ← section_reconstruct hN hy, he]

theorem section_mono_perm {m n e h : Nat} {M : Matching}
    (hM : M ∈ matchings (m+1) n (e+1)) (hx : (m,h) ∈ M) :
    (mono n M).Perm ((m*n+h) :: mono n (pushMatching h (sectionBase m h M))) := by
  rw [section_push hM hx]
  exact (List.perm_cons_erase hx).map (fun a => a.1*n+a.2)

end Programme.«20261104-1627-proof-complexity».IncidentSection
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.section_reconstruct
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.section_injective
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.section_mono_perm
