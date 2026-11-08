import Work.SyzygyLowering
import Work.CertificateReassembly
import Work.NSSpanRules
import Programme.«20261104-1627-proof-complexity».SupportedKernelResidual
namespace Work.ConcreteDegreeFour
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC

theorem supported_lowering {n k r : Nat} (hk : 9 ∣ k) (hn : 7 ≤ n)
    (hr : 0 < r) (hr4 : r ≤ 4) (span : Spanning 3 (n+k) n r)
    (Q : Poly Nat)
    (hQ : Work.SupportedCertificates.Supported (fun x => decide (x < (n+k)*n)) Q)
    (hd : Q.deg ≤ r-1) (h : NSIn 3 (ontoFPHP n k) r Q.eval) :
    NSIn 3 (ontoFPHP n k) (r-1) Q.eval := by
  exact Programme.«20261104-1627-proof-complexity».SupportedKernelResidual.supported_lower_of_kernel_image
    (by omega) hr (fun _ hv => Work.SyzygyLowering.kernel_lowering hk hr4 (by omega) span hv)
    Q (by omega) hQ h

theorem nodrop {n k D : Nat} (hk : 9 ∣ k) (hn : 7 ≤ n)
    (hD : 0 < D) (hD4 : D ≤ 4)
    (span : ∀ r, 0 < r → r ≤ 4 → Spanning 3 (n+k) n r) :
    NoDrop 3 (ontoFPHP n k) D := by
  apply Work.BooleanReconstruction.nodrop_of_supported
    (Work.SupportedCertificates.onto_supported n k) hD
  intro r hr hrD Q hQ hd h
  exact supported_lowering hk hn hr (by omega) (span r hr (by omega)) Q hQ hd h

theorem zero_exclusion {n k : Nat} (hn : 0 < n) :
    ¬ Work.NSSpanRules.W 3 (ontoFPHP n k) 0 Poly.one := by
  intro h
  have hs : Programme.«20261104-1627-proof-complexity».SupportedCertificates.Supported
      (fun x => decide (x < (n+k)*n)) Poly.one := by
    intro t ht x hx
    simp [Poly.one] at ht
    subst t
    simp at hx
  obtain ⟨v,hv,he⟩ :=
    (Programme.«20261104-1627-proof-complexity».SupportedKernelResidual.supported_iff_raw_W hn Poly.one hs).mp h
  have hempty : v = [] := by
    cases v with
    | nil => rfl
    | cons z zs =>
      obtain ⟨d,hd,hz⟩ := hv z (by simp)
      have : d = 0 := by omega
      subst d
      simp [labels] at hz
  subst v
  have hh := peq_eval he (fun _ => false)
  simp [Programme.«20261104-1627-proof-complexity».MatchingReduction.reduce,
    Programme.«20261104-1627-proof-complexity».MatchingReduction.Safe,
    Poly.one, Poly.eval, monoEval] at hh

/-- Concrete degree-four invariant; board spanning is still an explicit obligation. -/
def invariant {n k : Nat} (hk : 9 ∣ k) (hn : 7 ≤ n)
    (span : ∀ r, 0 < r → r ≤ 4 → Spanning 3 (n+k) n r) :
    Programme.«20261102-0635-proof-complexity».StepSix.Invariant 3 4 (ontoFPHP n k) := by
  apply Work.InvariantAssembly.invariant (Work.NSSpanRules.W 3 (ontoFPHP n k))
    (Work.NSSpanRules.rules 3 4 (ontoFPHP n k)) (zero_exclusion (by omega))
  intro r hr hr4 P hP hd
  exact (Work.NoDropPolynomial.nodrop_iff_polynomial 3 r (ontoFPHP n k)).mp
    (nodrop hk hn hr hr4 span) P hd hP

theorem no_stdpc {n k : Nat} (hk : 9 ∣ k) (hn : 7 ≤ n)
    (span : ∀ r, 0 < r → r ≤ 4 → Spanning 3 (n+k) n r) :
    ¬ Refutes 3 (ontoFPHP n k) 4 :=
  Programme.«20261102-0635-proof-complexity».StepSix.no_refutation (invariant hk hn span)

theorem no_ppc {n k : Nat} (hk : 9 ∣ k) (hn : 7 ≤ n)
    (span : ∀ r, 0 < r → r ≤ 4 → Spanning 3 (n+k) n r) :
    ¬ PPCRefutation 3 (ontoFPHP n k) 4 := by
  intro h
  apply (invariant hk hn span).unit
  apply nsIn_congr (pc_in_ns (nodrop hk hn (by omega) (by omega) span) h)
  intro a
  rw [eval_one]
  simp

end Work.ConcreteDegreeFour
#print axioms Work.ConcreteDegreeFour.nodrop
#print axioms Work.ConcreteDegreeFour.invariant
#print axioms Work.ConcreteDegreeFour.no_stdpc

#print axioms Work.ConcreteDegreeFour.no_ppc
