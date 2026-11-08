import Peer.th.SyzygyLowering
import Peer.th.CertificateReassembly
import Peer.th.NSSpanRules
import Programme.«20261104-1627-proof-complexity».SupportedKernelResidual
import Programme.«20261104-1627-proof-complexity».RectangularOne
namespace Work.K100Reproof
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC

theorem zero {n k : Nat} (hn : 0 < n) :
    ¬ Peer.th.NSSpanRules.W 3 (ontoFPHP n k) 0 Poly.one := by
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

def invariant {n k : Nat} (hk : 9 ∣ k) (hn : 7 ≤ n)
    (s2 : Spanning 3 (n+k) n 2) (s3 : Spanning 3 (n+k) n 3)
    (s4 : Spanning 3 (n+k) n 4) :
    Programme.«20261102-0635-proof-complexity».StepSix.Invariant 3 4 (ontoFPHP n k) := by
  apply Peer.th.InvariantAssembly.invariant (Peer.th.NSSpanRules.W 3 (ontoFPHP n k))
    (Peer.th.NSSpanRules.rules 3 4 (ontoFPHP n k)) (zero (by omega))
  intro r hr hr4 P hP hd
  have span : Spanning 3 (n+k) n r := by
    have hc : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
    rcases hc with h | h | h | h
    · subst r; exact spanning_one (by omega) (by omega)
    · subst r; exact s2
    · subst r; exact s3
    · subst r; exact s4
  have nd : NoDrop 3 (ontoFPHP n k) r := by
    apply Peer.th.BooleanReconstruction.nodrop_of_supported
      (Peer.th.SupportedCertificates.onto_supported n k) hr
    intro e he her Q hQ hdeg hmem
    have se : Spanning 3 (n+k) n e := by
      have hc : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by omega
      rcases hc with h | h | h | h
      · subst e; exact spanning_one (by omega) (by omega)
      · subst e; exact s2
      · subst e; exact s3
      · subst e; exact s4
    exact Programme.«20261104-1627-proof-complexity».SupportedKernelResidual.supported_lower_of_kernel_image
      (by omega) he
      (fun _ hv => Peer.th.SyzygyLowering.kernel_lowering hk (by omega) (by omega) se hv)
      Q (by omega) hQ hmem
  exact (Peer.th.NoDropPolynomial.nodrop_iff_polynomial 3 r (ontoFPHP n k)).mp nd P hd hP

theorem no_stdpc_le {n k d : Nat} (hk : 9 ∣ k) (hn : 7 ≤ n)
    (s2 : Spanning 3 (n+k) n 2) (s3 : Spanning 3 (n+k) n 3)
    (s4 : Spanning 3 (n+k) n 4) (hd : d ≤ 4) :
    ¬ Refutes 3 (ontoFPHP n k) d := by
  intro h
  exact Programme.«20261102-0635-proof-complexity».StepSix.no_refutation
    (invariant hk hn s2 s3 s4) (Peer.th.InvariantAssembly.der_mono hd h)
end Work.K100Reproof
#print axioms Work.K100Reproof.invariant
#print axioms Work.K100Reproof.no_stdpc_le
