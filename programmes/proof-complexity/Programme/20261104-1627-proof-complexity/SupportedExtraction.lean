import Programme.«20261104-1627-proof-complexity».AxiomExtraction
import Programme.«20261104-1627-proof-complexity».SupportedCertificates
import Programme.«20261104-1627-proof-complexity».SafeDifferences
namespace Programme.«20261104-1627-proof-complexity».SupportedExtraction
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».MatchQuot
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261104-1627-proof-complexity».SupportedCertificates Programme.«20261104-1627-proof-complexity».MatchingReduction

theorem reduce_supported {B : Nat → Bool} {A : List (Poly Nat)} {P : Poly Nat}
    (h : Supported B P) : Supported B (reduce A P) := by
  classical
  intro t ht x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact h s (List.mem_filter.mp hs).1 x (List.mem_eraseDups.mp hx)

/-- Unconditional extraction for supported canonical NS membership. -/
theorem supported_extraction {p n k D : Nat} (hn : 0 < n) (Q : Poly Nat)
    (hQ : Supported (fun x => decide (x < (n+k)*n)) Q)
    (h : NSIn p (ontoFPHP n k) D Q.eval) :
    ∃ v : Vector, (∀ z ∈ v, ∃ d, d ≤ D ∧ z.2 ∈ labels (n+k) n d) ∧
      ∀ a, Good (ontoFPHP n k) a →
        (p : Int) ∣ (relations (n+k) n v).eval a - Q.eval a := by
  classical
  obtain ⟨L,hL,he⟩ := (supported_certificate_iff p D _ _ (onto_supported n k) Q hQ).mp h
  apply Programme.«20261104-1627-proof-complexity».AxiomExtraction.certificate_extraction hn
    (L.map fun e => (reduce (ontoFPHP n k) e.1, e.2)) Q.eval
  · intro e he
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp he
    have hh := hL b hb
    refine ⟨hh.1, Nat.le_trans (Nat.add_le_add_right (deg_reduce _ _) _) hh.2.1, ?_⟩
    intro t ht
    have ht' := support_reduce (ontoFPHP n k) b.1 t ht
    refine ⟨ht'.2, ht'.1, ?_⟩
    intro x hx
    simpa only [decide_eq_true_eq] using reduce_supported hh.2.2 t ht x hx
  · intro a ha
    have eq : ((L.map fun e => (reduce (ontoFPHP n k) e.1, e.2)).map
        fun e => e.1.eval a * e.2.eval a).sum =
        (L.map fun e => e.1.eval a * e.2.eval a).sum := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro e _
      simp only [Function.comp_def, eval_reduce _ _ a ha]
    rw [eq]
    exact he a ha

/-- The same witness recovers every Safe-support coefficient modulo p. -/
theorem extraction_coefficients {p n k D : Nat} (hn : 0 < n) (Q : Poly Nat)
    (hQ : Supported (fun x => decide (x < (n+k)*n)) Q)
    (h : NSIn p (ontoFPHP n k) D Q.eval) :
    ∃ v : Vector, (∀ z ∈ v, ∃ d, d ≤ D ∧ z.2 ∈ labels (n+k) n d) ∧
      ∀ s, Safe (ontoFPHP n k) s →
        (p : Int) ∣ Programme.«20261104-1627-proof-complexity».SafeDifferences.coefficient s (relations (n+k) n v) -
          Programme.«20261104-1627-proof-complexity».SafeDifferences.coefficient s Q := by
  obtain ⟨v,hv,he⟩ := supported_extraction hn Q hQ h
  exact ⟨v,hv,fun _ hs => Programme.«20261104-1627-proof-complexity».SafeDifferences.coefficient_congruence he hs⟩
end Programme.«20261104-1627-proof-complexity».SupportedExtraction
#print axioms Programme.«20261104-1627-proof-complexity».SupportedExtraction.supported_extraction
#print axioms Programme.«20261104-1627-proof-complexity».SupportedExtraction.extraction_coefficients
