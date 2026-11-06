import Programme.«20261104-1627-proof-complexity».TwoEdgeCoefficients

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels

/-- Three holes suffice to compare two base holes through a common disjoint hole. -/
theorem third_hole {n b c : Nat} (hn : 3 ≤ n) :
    ∃ j, j < n ∧ b ≠ j ∧ c ≠ j := by
  by_cases hb : b = 0
  · by_cases hc : c = 1
    · exact ⟨2, by omega, by omega, by omega⟩
    · exact ⟨1, by omega, by omega, hc⟩
  · by_cases hc : c = 0
    · by_cases hb1 : b = 1
      · exact ⟨2, by omega, by omega, by omega⟩
      · exact ⟨1, by omega, hb1, by omega⟩
    · exact ⟨0, by omega, hb, hc⟩

/-- Rigidity of row-only degree-two top relations, over any modulus. -/
theorem row_two_rigidity {p m n : Nat} (hn : 3 ≤ n)
    (R : Nat → Nat → Nat → Int)
    (hR : ∀ a < m, ∀ i < m, a ≠ i → ∀ b < n, ∀ j < n, b ≠ j →
      (p : Int) ∣ R a b i + R i j a) :
    (∀ a < m, ∀ i < m, a ≠ i → ∀ b < n, ∀ c < n,
      (p : Int) ∣ R a b i - R a c i) ∧
    (∀ a < m, ∀ i < m, a ≠ i →
      (p : Int) ∣ R a 0 i + R i 0 a) := by
  have hind : ∀ a < m, ∀ i < m, a ≠ i → ∀ b < n, ∀ c < n,
      (p : Int) ∣ R a b i - R a c i := by
    intro a ha i hi hai b hb c hc
    obtain ⟨j,hj,hbj,hcj⟩ := third_hole (b := b) (c := c) hn
    have h := Int.dvd_sub (hR a ha i hi hai b hb j hj hbj)
      (hR a ha i hi hai c hc j hj hcj)
    rwa [show R a b i + R i j a - (R a c i + R i j a) =
      R a b i - R a c i by omega] at h
  refine ⟨hind, ?_⟩
  intro a ha i hi hai
  have h := Int.dvd_add (hR a ha i hi hai 0 (by omega) 1 (by omega) (by omega))
    (hind i hi a ha (Ne.symm hai) 0 (by omega) 1 (by omega))
  rwa [show R a 0 i + R i 1 a + (R i 0 a - R i 1 a) =
    R a 0 i + R i 0 a by omega] at h

/-- A kernel vector with vanishing column coordinates has row-only rigidity.
Column coordinates need only vanish modulo p, not as integers. -/
theorem kernel_two_row_rigidity {p m n : Nat} (hn : 3 ≤ n)
    (v : Vector) (hv : Kernel p m n 2 v)
    (hc : ∀ a < m, ∀ b < n, ∀ j < n, b ≠ j →
      (p : Int) ∣ vectorCoeff v (edgeColLabel a b j)) :
    (∀ a < m, ∀ i < m, a ≠ i → ∀ b < n, ∀ c < n,
      (p : Int) ∣ vectorCoeff v (edgeRowLabel a b i) -
        vectorCoeff v (edgeRowLabel a c i)) ∧
    (∀ a < m, ∀ i < m, a ≠ i →
      (p : Int) ∣ vectorCoeff v (edgeRowLabel a 0 i) +
        vectorCoeff v (edgeRowLabel i 0 a)) := by
  apply row_two_rigidity hn
  intro a ha i hi hai b hb j hj hbj
  have h := kernel_two_equations (by omega) v hv a b i j ha hb hi hj hai hbj
  have h' := Int.dvd_sub h (Int.dvd_add (hc a ha b hb j hj hbj)
    (hc i hi j hj b hb (Ne.symm hbj)))
  have he : vectorCoeff v (edgeRowLabel a b i) +
      vectorCoeff v (edgeRowLabel i j a) + vectorCoeff v (edgeColLabel a b j) +
      vectorCoeff v (edgeColLabel i j b) -
      (vectorCoeff v (edgeColLabel a b j) + vectorCoeff v (edgeColLabel i j b)) =
      vectorCoeff v (edgeRowLabel a b i) + vectorCoeff v (edgeRowLabel i j a) := by omega
  rwa [he] at h'

/-- These are the coefficients of the ordered rr generators: the reversed
pigeon order changes the sign. This supplies the scalar reconstruction. -/
theorem kernel_two_row_ordered {p m n : Nat} (hn : 3 ≤ n)
    (v : Vector) (hv : Kernel p m n 2 v)
    (hc : ∀ a < m, ∀ b < n, ∀ j < n, b ≠ j →
      (p : Int) ∣ vectorCoeff v (edgeColLabel a b j))
    (a i b : Nat) (ha : a < m) (hi : i < m) (hai : a ≠ i) (hb : b < n) :
    (p : Int) ∣ vectorCoeff v (edgeRowLabel a b i) -
      (if i < a then vectorCoeff v (edgeRowLabel a 0 i)
       else -vectorCoeff v (edgeRowLabel i 0 a)) := by
  obtain ⟨hind,hanti⟩ := kernel_two_row_rigidity hn v hv hc
  by_cases hia : i < a
  · simpa [hia] using hind a ha i hi hai b hb 0 (by omega)
  · have h := Int.dvd_add (hind a ha i hi hai b hb 0 (by omega))
      (hanti a ha i hi hai)
    have he : vectorCoeff v (edgeRowLabel a b i) - vectorCoeff v (edgeRowLabel a 0 i) +
        (vectorCoeff v (edgeRowLabel a 0 i) + vectorCoeff v (edgeRowLabel i 0 a)) =
        vectorCoeff v (edgeRowLabel a b i) - (-vectorCoeff v (edgeRowLabel i 0 a)) := by omega
    rw [he] at h
    simpa [hia] using h

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.row_two_rigidity
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.kernel_two_row_rigidity

#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.kernel_two_row_ordered
