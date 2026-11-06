import Programme.«20261104-1627-proof-complexity».AnchoredLucasLowering
import Programme.«20261104-1627-proof-complexity».AnchoredTwo

namespace Programme.«20261104-1627-proof-complexity».AnchoredTwoLowering
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261025-0459-proof-complexity».OntoFPHP

/-- The t=2 anchored case now has no residual-identity hypothesis. -/
theorem lowering_two {n k s : Nat} {N : Matching}
    (hk : 9 ∣ k) (hs : s ≤ n) (hN : N ∈ matchings (n+k) n s) :
    NSIn 3 (ontoFPHP n k) (s+1) (rho n (z (n+k) n 2 N)).eval := by
  have hi := Programme.«20261104-1627-proof-complexity».AnchoredTwo.anchored_identity_two (p := 3) hN
  have he : s+2-1 = s+1 := by omega
  have h := Programme.«20261104-1627-proof-complexity».AnchoredLucasLowering.anchored_lowering (N := N) hk hs
    (by decide : 2 < 9) (by simpa only [he] using hi)
  simpa only [he] using h

#print axioms lowering_two
end Programme.«20261104-1627-proof-complexity».AnchoredTwoLowering

