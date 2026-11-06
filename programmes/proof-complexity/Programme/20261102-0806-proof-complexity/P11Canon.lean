import Programme.«20261102-0806-proof-complexity».P11Candidate
import Init.Data.List.Perm

namespace Programme.«20261102-0806-proof-complexity».P11Canon
open Programme.«20261102-0806-proof-complexity».P11Candidate
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261025-1627-proof-complexity».MomGen

theorem state_perm {g h : List Nat} (hp : g.Perm h) : state g = state h := by
  have hc : ∀ a b, count g a b = count h a b := by
    intro a b
    exact (hp.filter _).length_eq
  have hr : ∀ f, rows g f = rows h f := by
    intro f
    simp only [rows, hc]
  simp only [state, hr]

theorem state_canon {N : Nat} {g : List Nat} (hn : g.Nodup)
    (hb : ∀ v ∈ g, v < N) : state (canon N g) = state g := by
  apply state_perm
  apply (List.perm_ext_iff_of_nodup (canon_nodup N g) hn).mpr
  intro v
  exact mem_canon' hb v

theorem state_canon_extend {g : List Nat} (hg : CM 21 121 g)
    {i j : Nat} (hi : i < 142) (hj : j < 21) (hf : pfree 21 g i) :
    state (canon (142 * 21) ((i * 21 + j) :: g)) =
      state ((i * 21 + j) :: g) := by
  apply state_canon
  · apply List.nodup_cons.mpr
    constructor
    · intro hm
      have he := hf _ hm
      have hd : (i * 21 + j) / 21 = i := by omega
      exact he hd
    · exact CM_nodup hg
  · intro v hv
    rcases List.mem_cons.mp hv with h | h
    · subst v; omega
    · exact CM_lt hg h

#print axioms state_canon_extend
end Programme.«20261102-0806-proof-complexity».P11Canon
