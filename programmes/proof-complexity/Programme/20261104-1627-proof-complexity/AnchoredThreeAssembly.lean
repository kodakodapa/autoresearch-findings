import Programme.«20261104-1627-proof-complexity».WeightedTailSums
import Programme.«20261104-1627-proof-complexity».AnchoredLucasLowering
namespace Programme.«20261104-1627-proof-complexity».AnchoredThreeAssembly
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC
open Programme.«20261025-0459-proof-complexity».OntoLucas (bin)
open Programme.«20261104-1627-proof-complexity».WeightedTailSums
/-- Only the two actual top transports remain hypotheses. -/
theorem identity_three {p m n s : Nat} {N : Matching}
    (hN : N ∈ matchings m n s)
    (h0 : ∀ u, coeff (top m n (layer m n 0 2 N)) u = coeff (incomingPoly m n 1 1 N) u)
    (h1 : ∀ u, coeff (top m n (layer m n 1 1 N)) u = coeff (incomingPoly m n 2 0 N) u) :
    W p m n (s+2) ((rho n (z m n 3 N)).sub
      ⟨[((bin (m-s) 3 : Int) - bin (n-s) 3, mono n N)]⟩) := by
  refine ⟨layer m n 0 2 N ++ layer m n 1 1 N, ?_, ?_⟩
  · have hw := Programme.«20261104-1627-proof-complexity».TailWitnessBudget.witness_bounded (t := 3) hN
    have he : Programme.«20261104-1627-proof-complexity».BinomialTails.witness m n 3 N = layer m n 0 2 N ++ layer m n 1 1 N := by
      simp [Programme.«20261104-1627-proof-complexity».BinomialTails.witness, layer, piece, List.range_succ]
      rfl
    rw [he] at hw
    simpa using hw
  · intro u
    have hz := Programme.«20261104-1627-proof-complexity».AnchoredWeights.rho_weighted_coeff m n 3 N u
    have hb := bottom_rho hN 2 u
    have hr := layer_rho m n 1 1 N u
    have he := relations_coeff m n (layer m n 0 2 N ++ layer m n 1 1 N) u
    have ht : coeff (top m n (layer m n 0 2 N ++ layer m n 1 1 N)) u =
        coeff (top m n (layer m n 0 2 N)) u + coeff (top m n (layer m n 1 1 N)) u := by
      simp [top, coeff, List.flatMap_append, cf_append]
    have hh : coeff (rho n (layer m n 0 2 N ++ layer m n 1 1 N)) u =
        coeff (rho n (layer m n 0 2 N)) u + coeff (rho n (layer m n 1 1 N)) u := by
      simp [rho, coeff, List.map_append, cf_append]
    rw [ht,hh,h0 u,h1 u,hr,hb,incoming_zero] at he
    change (p : Int) ∣ coeff ((rho n (z m n 3 N)).sub
      ⟨[((bin (m-s) 3 : Int) - bin (n-s) 3, mono n N)]⟩) u -
      coeff (relations m n (layer m n 0 2 N ++ layer m n 1 1 N)) u
    rw [he]
    simp only [Poly.sub, coeff, cf_append, List.map_cons, List.map_nil]
    change (p : Int) ∣ cf (rho n (z m n 3 N)).terms u +
      cf [(-((bin (m-s) 3 : Int) - bin (n-s) 3),mono n N)] u - _
    change cf (rho n (z m n 3 N)).terms u = cf (Programme.«20261104-1627-proof-complexity».AnchoredWeights.weighted m n 3 N).terms u at hz
    rw [hz]
    by_cases h : (mono n N).Perm u <;> simp [cf,h] <;>
      exact ⟨0, by omega⟩
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261025-0459-proof-complexity».OntoFPHP
/-- Lucas cancellation now follows from exactly the two top equalities. -/
theorem lowering_three {n k s : Nat} {N : Matching}
    (hk : 9 ∣ k) (hs : s ≤ n) (hN : N ∈ matchings (n+k) n s)
    (h0 : ∀ u, coeff (top (n+k) n (layer (n+k) n 0 2 N)) u =
      coeff (incomingPoly (n+k) n 1 1 N) u)
    (h1 : ∀ u, coeff (top (n+k) n (layer (n+k) n 1 1 N)) u =
      coeff (incomingPoly (n+k) n 2 0 N) u) :
    NSIn 3 (ontoFPHP n k) (s+2) (rho n (z (n+k) n 3 N)).eval := by
  have hi := identity_three (p := 3) hN h0 h1
  have he : s+3-1 = s+2 := by omega
  have h := Programme.«20261104-1627-proof-complexity».AnchoredLucasLowering.anchored_lowering N hk hs
    (by decide : 3 < 9) (by simpa only [he] using hi)
  simpa only [he] using h

#print axioms identity_three
#print axioms lowering_three
end Programme.«20261104-1627-proof-complexity».AnchoredThreeAssembly
