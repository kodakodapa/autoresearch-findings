import Programme.«20261104-1627-proof-complexity».WeightedTopTransport
import Programme.«20261104-1627-proof-complexity».AnchoredLucasLowering
namespace Programme.«20261104-1627-proof-complexity».AnchoredFour
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC
open Programme.«20261025-0459-proof-complexity».OntoLucas (bin)
open Programme.«20261104-1627-proof-complexity».WeightedTailSums Programme.«20261104-1627-proof-complexity».WeightedTopTransport

theorem identity_four {p m n s : Nat} {N : Matching}
    (hN : N ∈ matchings m n s) :
    W p m n (s+3) ((rho n (z m n 4 N)).sub
      ⟨[((bin (m-s) 4 : Int) - bin (n-s) 4, mono n N)]⟩) := by
  let V := layer m n 0 3 N ++ layer m n 1 2 N ++ layer m n 2 1 N
  refine ⟨V, ?_, ?_⟩
  · have hw := Programme.«20261104-1627-proof-complexity».TailWitnessBudget.witness_bounded (t := 4) hN
    have he : Programme.«20261104-1627-proof-complexity».BinomialTails.witness m n 4 N = V := by
      simp [Programme.«20261104-1627-proof-complexity».BinomialTails.witness, V, layer, List.range_succ]
      rfl
    rw [he] at hw
    simpa using hw
  · intro u
    have ht (v w : Vector) : coeff (top m n (v++w)) u =
        coeff (top m n v) u + coeff (top m n w) u := by
      simp [top, coeff, List.flatMap_append, cf_append]
    have hr (v w : Vector) : coeff (rho n (v++w)) u =
        coeff (rho n v) u + coeff (rho n w) u := by
      simp [rho, coeff, List.map_append, cf_append]
    have he := relations_coeff m n V u
    simp only [V, ht, hr] at he
    rw [layer_top m n 0 2, layer_top m n 1 1, layer_top m n 2 0,
      layer_rho m n 1 2, layer_rho m n 2 1, bottom_rho hN 3,
      incoming_zero] at he
    have hz := Programme.«20261104-1627-proof-complexity».AnchoredWeights.rho_weighted_coeff m n 4 N u
    change (p : Int) ∣ coeff ((rho n (z m n 4 N)).sub
      ⟨[((bin (m-s) 4 : Int) - bin (n-s) 4, mono n N)]⟩) u -
      coeff (relations m n V) u
    rw [he]
    simp only [Poly.sub, coeff, cf_append, List.map_cons, List.map_nil]
    change cf (rho n (z m n 4 N)).terms u =
      cf (Programme.«20261104-1627-proof-complexity».AnchoredWeights.weighted m n 4 N).terms u at hz
    rw [hz]
    by_cases h : (mono n N).Perm u <;> simp [cf,h] <;>
      exact ⟨0, by omega⟩
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261025-0459-proof-complexity».OntoFPHP

theorem lowering_four {n k s : Nat} {N : Matching}
    (hk : 9 ∣ k) (hs : s ≤ n) (hN : N ∈ matchings (n+k) n s) :
    NSIn 3 (ontoFPHP n k) (s+3) (rho n (z (n+k) n 4 N)).eval := by
  have he : s+4-1 = s+3 := by omega
  have hi := identity_four (p := 3) hN
  have h := Programme.«20261104-1627-proof-complexity».AnchoredLucasLowering.anchored_lowering
    N hk hs (by decide : 4 < 9) (by simpa only [he] using hi)
  simpa only [he] using h
end Programme.«20261104-1627-proof-complexity».AnchoredFour
#print axioms Programme.«20261104-1627-proof-complexity».AnchoredFour.identity_four

#print axioms Programme.«20261104-1627-proof-complexity».AnchoredFour.lowering_four
