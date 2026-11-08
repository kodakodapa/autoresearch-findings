import Programme.«20261104-1627-proof-complexity».AnchoredThreeAssembly
import Programme.«20261104-1627-proof-complexity».WeightedTopTransport

namespace Programme.«20261104-1627-proof-complexity».AnchoredThree
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261025-0459-proof-complexity».OntoLucas (bin)
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261025-0459-proof-complexity».OntoFPHP

/-- Unconditional three-step anchored residual identity. -/
theorem identity_three {p m n s : Nat} {N : Matching}
    (hN : N ∈ matchings m n s) :
    W p m n (s+2) ((rho n (z m n 3 N)).sub
      ⟨[((bin (m-s) 3 : Int) - bin (n-s) 3, mono n N)]⟩) := by
  exact Programme.«20261104-1627-proof-complexity».AnchoredThreeAssembly.identity_three hN
    (Programme.«20261104-1627-proof-complexity».WeightedTopTransport.layer_top m n 0 1 N)
    (Programme.«20261104-1627-proof-complexity».WeightedTopTransport.layer_top m n 1 0 N)

/-- Concrete canonical lowering; no top-transport premise remains. -/
theorem lowering_three {n k s : Nat} {N : Matching}
    (hk : 9 ∣ k) (hs : s ≤ n) (hN : N ∈ matchings (n+k) n s) :
    NSIn 3 (ontoFPHP n k) (s+2) (rho n (z (n+k) n 3 N)).eval := by
  exact Programme.«20261104-1627-proof-complexity».AnchoredThreeAssembly.lowering_three hk hs hN
    (Programme.«20261104-1627-proof-complexity».WeightedTopTransport.layer_top (n+k) n 0 1 N)
    (Programme.«20261104-1627-proof-complexity».WeightedTopTransport.layer_top (n+k) n 1 0 N)

#print axioms identity_three
#print axioms lowering_three
end Programme.«20261104-1627-proof-complexity».AnchoredThree
