import Programme.«20261104-1627-proof-complexity».WeightedTopTransport
import Programme.«20261104-1627-proof-complexity».AnchoredLucasLowering
namespace Programme.«20261104-1627-proof-complexity».AnchoredGeneral
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC
open Programme.«20261025-0459-proof-complexity».OntoLucas (bin)
open Programme.«20261104-1627-proof-complexity».WeightedTailSums Programme.«20261104-1627-proof-complexity».WeightedTopTransport

def chain (m n r : Nat) (N : Matching) : Nat → Vector
  | 0 => []
  | q+1 => layer m n r (q+1) N ++ chain m n (r+1) N q

theorem chain_mem {m n r q : Nat} {N : Matching} {a : Int × Label}
    (ha : a ∈ chain m n r N q) :
    ∃ i, i < q ∧ a ∈ layer m n (r+i) (q-i) N := by
  induction q generalizing r with
  | zero => simp [chain] at ha
  | succ q ih =>
    rcases List.mem_append.mp ha with h | h
    · exact ⟨0, by omega, by simpa using h⟩
    · obtain ⟨i,hi,ha⟩ := ih h
      refine ⟨i+1, by omega, ?_⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ha

theorem chain_telescope (m n r q : Nat) (N : Matching) (u : List Nat) :
    coeff (relations m n (chain m n r N (q+1))) u =
    coeff (incomingPoly m n (r+q+1) 0 N) u -
      coeff (incomingPoly m n r (q+1) N) u := by
  induction q generalizing r with
  | zero =>
    have he := relations_coeff m n (layer m n r 1 N) u
    simpa [chain, layer_top m n r 0, layer_rho] using he
  | succ q ih =>
    have ht (v w : Vector) : coeff (top m n (v++w)) u =
        coeff (top m n v) u + coeff (top m n w) u := by
      simp [top, coeff, List.flatMap_append, cf_append]
    have hr (v w : Vector) : coeff (rho n (v++w)) u =
        coeff (rho n v) u + coeff (rho n w) u := by
      simp [rho, coeff, List.map_append, cf_append]
    have he := relations_coeff m n (chain m n r N (q+2)) u
    have hi := ih (r+1)
    have hj := relations_coeff m n (chain m n (r+1) N (q+1)) u
    rw [chain, ht, hr, layer_top m n r (q+1), layer_rho] at he
    have idx : r+1+q+1 = r+(q+1)+1 := by omega
    rw [idx] at hi
    rw [chain]
    omega
theorem identity_general {p m n s q : Nat} {N : Matching}
    (hN : N ∈ matchings m n s) :
    W p m n (s+q+1) ((rho n (z m n (q+2) N)).sub
      ⟨[((bin (m-s) (q+2) : Int) - bin (n-s) (q+2), mono n N)]⟩) := by
  let V := chain m n 0 N (q+1)
  refine ⟨V, ?_, ?_⟩
  · intro a ha
    obtain ⟨i,hi,hai⟩ := chain_mem ha
    have hw := Programme.«20261104-1627-proof-complexity».TailWitnessBudget.witness_bounded (t := q+2) hN
    have hm : a ∈ Programme.«20261104-1627-proof-complexity».BinomialTails.witness m n (q+2) N := by
      apply List.mem_flatMap.mpr
      refine ⟨i, List.mem_range.mpr (by omega), ?_⟩
      have he : q+2-1-i = q+1-i := by omega
      simpa [layer, piece, he] using hai
    obtain ⟨d,hd,ha⟩ := hw a hm
    exact ⟨d, by omega, ha⟩
  · intro u
    have he := chain_telescope m n 0 q N u
    rw [incoming_zero] at he
    have hb := bottom_rho hN (q+1) u
    rw [layer_rho] at hb
    rw [hb] at he
    have hz := Programme.«20261104-1627-proof-complexity».AnchoredWeights.rho_weighted_coeff m n (q+2) N u
    change (p : Int) ∣ coeff ((rho n (z m n (q+2) N)).sub
      ⟨[((bin (m-s) (q+2) : Int) - bin (n-s) (q+2), mono n N)]⟩) u -
      coeff (relations m n V) u
    have idx : 0+q+1+1 = q+2 := by omega
    simp only [Nat.zero_add] at he
    change cf (rho n (z m n (q+2) N)).terms u =
      cf (Programme.«20261104-1627-proof-complexity».AnchoredWeights.weighted m n (q+2) N).terms u at hz
    change coeff (relations m n V) u = _ at he
    rw [he]
    simp only [Poly.sub, coeff, cf_append, List.map_cons, List.map_nil]
    rw [hz]
    simp only [show q+2 = q+1+1 by omega] at *
    by_cases h : (mono n N).Perm u <;> simp [cf,h] <;>
      exact ⟨0, by omega⟩

open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261025-0459-proof-complexity».OntoFPHP

theorem lowering_general {n k s q : Nat} {N : Matching}
    (hk : 9 ∣ k) (hs : s ≤ n) (ht : q+2 < 9)
    (hN : N ∈ matchings (n+k) n s) :
    NSIn 3 (ontoFPHP n k) (s+q+1) (rho n (z (n+k) n (q+2) N)).eval := by
  have he : s+(q+2)-1 = s+q+1 := by omega
  have hi := identity_general (p := 3) (q := q) hN
  have h := Programme.«20261104-1627-proof-complexity».AnchoredLucasLowering.anchored_lowering
    N hk hs ht (by simpa only [he] using hi)
  simpa only [he] using h
end Programme.«20261104-1627-proof-complexity».AnchoredGeneral
#print axioms Programme.«20261104-1627-proof-complexity».AnchoredGeneral.chain_telescope
#print axioms Programme.«20261104-1627-proof-complexity».AnchoredGeneral.identity_general
#print axioms Programme.«20261104-1627-proof-complexity».AnchoredGeneral.lowering_general
