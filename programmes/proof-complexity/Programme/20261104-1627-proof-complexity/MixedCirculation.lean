import Programme.«20261104-1627-proof-complexity».MixedNormalForm

namespace Programme.«20261104-1627-proof-complexity».MixedEliminate
open Programme.«20261104-1627-proof-complexity».MatchingLabels

/-- The oriented three-hole circulation in the column coordinates. -/
def circulation (v : Vector) (a b c j : Nat) : Int :=
  vectorCoeff v (edgeColLabel a b c) +
  vectorCoeff v (edgeColLabel a c j) +
  vectorCoeff v (edgeColLabel a j b) -
  vectorCoeff v (edgeColLabel a b j) -
  vectorCoeff v (edgeColLabel a j c) -
  vectorCoeff v (edgeColLabel a c b)

/-- Six matching equations eliminate every row coordinate. -/
theorem kernel_circulation {p m n : Nat} (hn : 0 < n)
    (v : Vector) (hv : Kernel p m n 2 v)
    (a i b c j : Nat) (ha : a < m) (hi : i < m) (hai : a ≠ i)
    (hb : b < n) (hc : c < n) (hj : j < n)
    (hbc : b ≠ c) (hbj : b ≠ j) (hcj : c ≠ j) :
    (p : Int) ∣ circulation v a b c j - circulation v i b c j := by
  have h1 := kernel_two_equations hn v hv a b i c ha hb hi hc hai hbc
  have h2 := kernel_two_equations hn v hv a b i j ha hb hi hj hai hbj
  have h3 := kernel_two_equations hn v hv a c i b ha hc hi hb hai (Ne.symm hbc)
  have h4 := kernel_two_equations hn v hv a c i j ha hc hi hj hai hcj
  have h5 := kernel_two_equations hn v hv a j i b ha hj hi hb hai (Ne.symm hbj)
  have h6 := kernel_two_equations hn v hv a j i c ha hj hi hc hai (Ne.symm hcj)
  have h := Int.dvd_sub (Int.dvd_add (Int.dvd_sub (Int.dvd_sub h1 h2) h3) h4)
    (Int.dvd_sub h6 h5)
  obtain ⟨q, hq⟩ := h
  exact ⟨q, by unfold circulation; omega⟩

end Programme.«20261104-1627-proof-complexity».MixedEliminate
#print axioms Programme.«20261104-1627-proof-complexity».MixedEliminate.kernel_circulation
