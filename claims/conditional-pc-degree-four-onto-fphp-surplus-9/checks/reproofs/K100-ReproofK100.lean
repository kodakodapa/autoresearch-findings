import Peer.th.ConcreteDegreeFour
import Peer.th.RemainingSpanning
import Work.ReproofK93
import Work.ReproofK4
import Work.ReproofK9
import Programme.«20261025-1627-proof-complexity».OntoExt2
import Programme.«20261025-0459-proof-complexity».OntoSubst

namespace Work.ReproofK100
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst
open Programme.«20261025-0459-proof-complexity».MatchQuot
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC
open Programme.«20261102-0635-proof-complexity».StepSix

/-- Own degree-r lowering of supported polynomials from Spanning, via my K93 and the library lemma. -/
theorem lowering {n k r : Nat} (hk : 9 ∣ k) (hn : 7 ≤ n) (hr : 0 < r) (hr4 : r ≤ 4)
    (span : Spanning 3 (n+k) n r) (Q : Poly Nat)
    (hQ : Peer.th.SupportedCertificates.Supported (fun x => decide (x < (n+k)*n)) Q)
    (hd : Q.deg ≤ r-1) (h : NSIn 3 (ontoFPHP n k) r Q.eval) :
    NSIn 3 (ontoFPHP n k) (r-1) Q.eval :=
  Programme.«20261104-1627-proof-complexity».SupportedKernelResidual.supported_lower_of_kernel_image
    (by omega) hr (fun _ hv => Work.ReproofK93.kernel_lowering hk hr4 (by omega) span hv)
    Q (by omega) hQ h

theorem spans {n k : Nat} (hn : 7 ≤ n) (s2 : Spanning 3 (n+k) n 2) (s3 : Spanning 3 (n+k) n 3)
    (s4 : Spanning 3 (n+k) n 4) : ∀ r, 0 < r → r ≤ 4 → Spanning 3 (n+k) n r := by
  intro r hr h4
  rcases (by omega : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4) with h | h | h | h <;> subst h
  · exact spanning_one (by omega) (by omega)
  · exact s2
  · exact s3
  · exact s4

theorem zero_excl {n k : Nat} (hn : 0 < n) :
    ¬ NSIn 3 (ontoFPHP n k) 0 (fun a => Poly.one.eval a) := by
  rintro ⟨L, hL, hs⟩
  have hnil : L = [] := by
    cases L with
    | nil => rfl
    | cons e L =>
      exfalso
      obtain ⟨hmem, hdeg⟩ := hL e (by simp)
      have : 1 ≤ e.2.deg := by
        rcases mem_ontoFPHP hmem with ⟨i, _, h⟩ | ⟨j, hj, h⟩ | hc | hf
        · rw [h]; exact Programme.«20261025-1627-proof-complexity».OntoExt2.sumOne_deg_pos _ _ hn
        · rw [h]; exact Programme.«20261025-1627-proof-complexity».OntoExt2.sumOne_deg_pos _ _ (by omega)
        · obtain ⟨j, i, i', _, _, _, _, h⟩ := mem_collAx.mp hc
          rw [← h, prod2_deg]; omega
        · obtain ⟨i, j, j', _, _, _, _, h⟩ := mem_funcAx.mp hf
          rw [← h, prod2_deg]; omega
      omega
  subst hnil
  have hg : Good (ontoFPHP n k) (fun _ => false) := by
    intro u w _ h; simp at h
  obtain ⟨c, hc⟩ := hs _ hg
  simp [eval_one] at hc
  omega

/-- K100, invariant. -/
def invariant {n k : Nat} (hk : 9 ∣ k) (hn : 7 ≤ n)
    (s2 : Spanning 3 (n+k) n 2) (s3 : Spanning 3 (n+k) n 3)
    (s4 : Spanning 3 (n+k) n 4) : Invariant 3 4 (ontoFPHP n k) := by
  have sp := spans hn s2 s3 s4
  have nd : ∀ D, 0 < D → D ≤ 4 → NoDrop 3 (ontoFPHP n k) D := by
    intro D hD hD4
    apply Peer.th.BooleanReconstruction.nodrop_of_supported
      (Peer.th.SupportedCertificates.onto_supported n k) hD
    intro r hr hrD Q hQ hd h
    exact lowering hk hn hr (by omega) (sp r hr (by omega)) Q hQ hd h
  have R := Work.ReproofK4.rules 3 4 (ontoFPHP n k)
  have ndp : ∀ e, 1 ≤ e → e ≤ 4 → ∀ P : Poly Nat,
      NSIn 3 (ontoFPHP n k) e P.eval → P.deg ≤ e - 1 → NSIn 3 (ontoFPHP n k) (e-1) P.eval :=
    fun e he he4 P hP hd =>
      (Work.ReproofK9.nodrop_iff_polynomial 3 e (ontoFPHP n k)).mp (nd e he he4) P hd hP
  refine
    { top := fun P => NSIn 3 (ontoFPHP n k) 4 P.eval
      lower := fun P => NSIn 3 (ontoFPHP n k) 3 P.eval
      axiom_mem := R.axiom_mem
      boolean_mem := R.boolean_mem
      linear_mem := R.linear_mem
      equal_mem := R.equal_mem
      nodrop := fun P hP hd => ndp 4 (by omega) (Nat.le_refl _) P hP hd
      multiply_mem := R.multiply_mem
      unit := ?_ }
  intro hu
  have chain : ∀ e, e ≤ 4 → ¬ NSIn 3 (ontoFPHP n k) e (fun a => Poly.one.eval a) := by
    intro e
    induction e with
    | zero => intro _; exact zero_excl (by omega)
    | succ e ih =>
      intro he h1
      exact ih (by omega) (ndp (e+1) (by omega) he Poly.one h1 (by rw [deg_one]; omega))
  exact chain 4 (Nat.le_refl _) hu

theorem no_stdpc_le {n k d : Nat} (hk : 9 ∣ k) (hn : 7 ≤ n)
    (s2 : Spanning 3 (n+k) n 2) (s3 : Spanning 3 (n+k) n 3)
    (s4 : Spanning 3 (n+k) n 4) (hd : d ≤ 4) :
    ¬ Refutes 3 (ontoFPHP n k) d := by
  intro h
  exact no_refutation (invariant hk hn s2 s3 s4) (Peer.th.InvariantAssembly.der_mono hd h)
end Work.ReproofK100
#print axioms Work.ReproofK100.invariant
#print axioms Work.ReproofK100.no_stdpc_le
