import Programme.«20261104-1627-proof-complexity».MatchingSafety
import Programme.«20261104-1627-proof-complexity».FilteredDecomposition

namespace Programme.«20261104-1627-proof-complexity».SupportedKernelResidual
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC
open Programme.«20261104-1627-proof-complexity».MatchingReduction

/-- On supported targets, reduction and the raw label span give an exact
characterization of canonical NS membership, not only a forward extraction. -/
theorem supported_iff_raw_W {p n k D : Nat} (hn : 0 < n) (Q : Poly Nat)
    (hQ : Programme.«20261104-1627-proof-complexity».SupportedCertificates.Supported
      (fun x => decide (x < (n+k)*n)) Q) :
    NSIn p (ontoFPHP n k) D Q.eval ↔
      W p (n+k) n D (reduce (ontoFPHP n k) Q) := by
  constructor
  · exact Programme.«20261104-1627-proof-complexity».MatchingSafety.supported_raw_W hn Q hQ
  · intro hw
    obtain ⟨L,hL,he⟩ := Programme.«20261104-1627-proof-complexity».BoundedRelationCertificates.W_nsIn hw
    refine ⟨L,hL,?_⟩
    intro a ha
    have h := he a ha
    dsimp only at h ⊢
    rwa [eval_reduce _ _ a ha] at h

/-- The homogeneous Kernel term is the entire remaining obstruction after
supported extraction and removal of the bounded lower-degree relation part. -/
theorem supported_kernel_iff {p n k D : Nat} (hn : 0 < n) (hD : 0 < D)
    (Q : Poly Nat) (hdeg : Q.deg < D)
    (hQ : Programme.«20261104-1627-proof-complexity».SupportedCertificates.Supported
      (fun x => decide (x < (n+k)*n)) Q) :
    NSIn p (ontoFPHP n k) D Q.eval ↔
      ∃ lo hi : Vector, bounded (n+k) n (D-1) lo ∧
        Kernel p (n+k) n D hi ∧
        PEq p (reduce (ontoFPHP n k) Q)
          ((relations (n+k) n lo).sub (rho n hi)) := by
  rw [supported_iff_raw_W hn Q hQ]
  exact filtered_decomposition hD _ (Nat.lt_of_le_of_lt (deg_reduce _ _) hdeg)

/-- A concrete sufficient lowering condition, with the outstanding rho-image
obligation explicit and no divisibility or spanning assumption hidden. -/
theorem supported_lower_of_kernel_image {p n k D : Nat}
    (hn : 0 < n) (hD : 0 < D)
    (hrho : ∀ hi : Vector, Kernel p (n+k) n D hi →
      NSIn p (ontoFPHP n k) (D-1) (rho n hi).eval)
    (Q : Poly Nat) (hdeg : Q.deg < D)
    (hQ : Programme.«20261104-1627-proof-complexity».SupportedCertificates.Supported
      (fun x => decide (x < (n+k)*n)) Q)
    (h : NSIn p (ontoFPHP n k) D Q.eval) :
    NSIn p (ontoFPHP n k) (D-1) Q.eval := by
  obtain ⟨lo,hi,hlo,hhi,he⟩ := (supported_kernel_iff hn hD Q hdeg hQ).mp h
  have hl := Programme.«20261104-1627-proof-complexity».BoundedRelationCertificates.bounded_relations_nsIn (p := p) lo hlo
  obtain ⟨L,hL,hcert⟩ := nsIn_lin 1 (-1) hl (hrho hi hhi)
  refine ⟨L,hL,?_⟩
  intro a ha
  have hc := hcert a ha
  have hp := peq_eval he a
  rw [eval_sub, eval_reduce _ _ a ha] at hp
  dsimp only at hc ⊢
  simp only [Int.one_mul, Int.neg_one_mul] at hc
  have hh := Int.dvd_add hc hp
  have eqn :
      (L.map (fun e => e.1.eval a * e.2.eval a)).sum -
        ((relations (n+k) n lo).eval a + -(rho n hi).eval a) +
        ((relations (n+k) n lo).eval a - (rho n hi).eval a - Q.eval a) =
      (L.map (fun e => e.1.eval a * e.2.eval a)).sum - Q.eval a := by omega
  rwa [eqn] at hh

end Programme.«20261104-1627-proof-complexity».SupportedKernelResidual
#print axioms Programme.«20261104-1627-proof-complexity».SupportedKernelResidual.supported_iff_raw_W
#print axioms Programme.«20261104-1627-proof-complexity».SupportedKernelResidual.supported_kernel_iff

#print axioms Programme.«20261104-1627-proof-complexity».SupportedKernelResidual.supported_lower_of_kernel_image
