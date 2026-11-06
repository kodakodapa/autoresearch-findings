import Programme.«20261025-1627-proof-complexity».NoDrop

namespace Programme.«20261104-1627-proof-complexity».NoDropPolynomial
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».MatchQuot
open Programme.«20261025-1627-proof-complexity».NoDrop

/-- NS membership only depends on values at good points. -/
theorem congr_good {p D : Nat} {A : List (Poly Nat)}
    {f g : (Nat → Bool) → Int} (hg : NSIn p A D g)
    (hfg : ∀ a, Good A a → (p : Int) ∣ f a - g a) : NSIn p A D f := by
  obtain ⟨L, hL, h⟩ := hg
  refine ⟨L, hL, fun a ha => ?_⟩
  have hh := Int.dvd_sub (h a ha) (hfg a ha)
  have ee : (L.map fun e => e.1.eval a * e.2.eval a).sum - g a - (f a - g a) =
      (L.map fun e => e.1.eval a * e.2.eval a).sum - f a := by omega
  rwa [ee] at hh

/-- The whole-cube degree witness reduces canonical NoDrop to polynomial lines. -/
theorem nodrop_iff_polynomial (p D : Nat) (A : List (Poly Nat)) :
    NoDrop p A D ↔
      ∀ Q : Poly Nat, Q.deg ≤ D - 1 →
        NSIn p A D Q.eval → NSIn p A (D - 1) Q.eval := by
  constructor
  · intro h Q hd hQ
    exact h Q.eval hQ ⟨Q, hd, fun a => by simp⟩
  · intro h f hf hdeg
    obtain ⟨Q, hd, heq⟩ := hdeg
    have hQ : NSIn p A D Q.eval := nsIn_congr hf heq
    apply congr_good (h Q hd hQ)
    intro a _
    have hh := Int.dvd_neg.mpr (heq a)
    have ee : -(Q.eval a - f a) = f a - Q.eval a := by omega
    rwa [ee] at hh

end Programme.«20261104-1627-proof-complexity».NoDropPolynomial
#print axioms Programme.«20261104-1627-proof-complexity».NoDropPolynomial.congr_good
#print axioms Programme.«20261104-1627-proof-complexity».NoDropPolynomial.nodrop_iff_polynomial
