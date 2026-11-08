import Programme.«20261104-1627-proof-complexity».IncidentCoordinates

namespace Programme.«20261104-1627-proof-complexity».IncidentSection
open Programme.«20261104-1627-proof-complexity».MatchingLabels

/-- Board-code monomials reflect permutations when the hole coordinates are bounded. -/
theorem mono_perm_iff {n : Nat} (hn : 0 < n) (A B : Matching)
    (hA : ∀ a ∈ A, a.2 < n) (hB : ∀ b ∈ B, b.2 < n) :
    (mono n A).Perm (mono n B) ↔ A.Perm B := by
  have decode (L : Matching) (hL : ∀ a ∈ L, a.2 < n) :
      (mono n L).map (fun x => (x / n, x % n)) = L := by
    unfold mono
    rw [List.map_map]
    apply Eq.trans (b := L.map id)
    · apply List.map_congr_left
      intro a ha
      have hh := hL a ha
      apply Prod.ext
      · simp [Function.comp_def, Nat.add_div, Nat.div_eq_of_lt hh, Nat.mod_eq_of_lt hh, hn, hh]
      · simp [Function.comp_def, Nat.add_mod, Nat.mod_eq_of_lt hh]
    · exact List.map_id L
  constructor
  · intro hp
    have hh := hp.map (fun x => (x / n, x % n))
    simpa only [decode A hA, decode B hB] using hh
  · exact fun hp => hp.map _

/-- Cancel the selected incident edge from an arbitrary extension monomial.
The remaining word is still in the large-board stride. -/
theorem incident_term_perm {m n e h : Nat} {B : Matching}
    (hB : B ∈ matchings (m+1) n (e+1)) (hx : (m,h) ∈ B)
    (x : Nat) (E : Matching) :
    (x :: mono n B).Perm ((m*n+h) :: mono n (pushMatching h E)) ↔
    (x :: mono n (pushMatching h (sectionBase m h B))).Perm
      (mono n (pushMatching h E)) := by
  have hb := section_mono_perm hB hx
  constructor
  · intro hp
    have hp' := (List.Perm.cons x hb).symm.trans hp
    have hs : ((m*n+h) :: x :: mono n (pushMatching h (sectionBase m h B))).Perm
        ((m*n+h) :: mono n (pushMatching h E)) :=
      (List.Perm.swap _ _ _).trans hp'
    exact List.Perm.cons_inv hs
  · intro hp
    exact (List.Perm.cons x hb).trans
      ((List.Perm.swap _ _ _).trans (List.Perm.cons (m*n+h) hp))

/-- The actual incident extension test equals the smaller-board extension test. -/
theorem incident_extension_perm {m n e h : Nat} (hn : 0 < n) (hh : h < n+1)
    {B E : Matching} (hB : B ∈ matchings (m+1) (n+1) (e+1))
    (hx : (m,h) ∈ B) (hE : ∀ a ∈ E, a.2 < n)
    (i j : Nat) (hj : j < n) :
    ((i*(n+1)+omitHole h j) :: mono (n+1) B).Perm
        ((m*(n+1)+h) :: mono (n+1) (pushMatching h E)) ↔
    ((i*n+j) :: mono n (sectionBase m h B)).Perm (mono n E) := by
  have hs := incident_base hh hB hx
  have hs' : ∀ a ∈ sectionBase m h B, a.2 < n := by
    have hh' := matching_cols_lt hs
    simpa only [Nat.add_sub_cancel] using hh'
  have hpcols (L : Matching) (hL : ∀ a ∈ L, a.2 < n) :
      ∀ a ∈ pushMatching h L, a.2 < n+1 := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact omitHole_lt (hL b hb)
  rw [incident_term_perm hB hx]
  change (mono (n+1) (pushMatching h ((i,j)::sectionBase m h B))).Perm
      (mono (n+1) (pushMatching h E)) ↔ _
  have hc : ∀ a ∈ (i,j)::sectionBase m h B, a.2 < n := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hj
    · exact hs' a ha
  rw [mono_perm_iff (by omega) _ _ (hpcols _ hc) (hpcols _ hE)]
  have hpp : (pushMatching h ((i,j)::sectionBase m h B)).Perm (pushMatching h E) ↔
      ((i,j)::sectionBase m h B).Perm E := by
    constructor
    · intro hp
      have ht := hp.map (fun a => (a.1,closeHole h a.2))
      change (pullMatching h (pushMatching h ((i,j)::sectionBase m h B))).Perm
        (pullMatching h (pushMatching h E)) at ht
      simpa only [pull_push] using ht
    · exact fun hp => hp.map _
  rw [hpp]
  exact (mono_perm_iff hn _ _ hc hE).symm

end Programme.«20261104-1627-proof-complexity».IncidentSection
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.mono_perm_iff
#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.incident_term_perm

#print axioms Programme.«20261104-1627-proof-complexity».IncidentSection.incident_extension_perm
