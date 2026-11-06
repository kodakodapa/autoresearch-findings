import Programme.«20261104-1627-proof-complexity».SupportedExtraction
namespace Programme.«20261104-1627-proof-complexity».SquareFreeCoefficientBridge
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC
open Programme.«20261025-0459-proof-complexity».MatchQuot
open Programme.«20261104-1627-proof-complexity».MatchingReduction Programme.«20261104-1627-proof-complexity».SafeDifferences

def Reduced (A : List (Poly Nat)) (P : Poly Nat) : Prop :=
  ∀ t ∈ P.terms, t.2.Nodup ∧ Safe A t.2

theorem coeff_eq_support {A : List (Poly Nat)} {P : Poly Nat}
    (hP : Reduced A P) (s : List Nat) (hs : s.Nodup) :
    coeff P s = coefficient s P := by
  classical
  unfold coeff cf coefficient
  rw [sum_filter]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  have he : t.2.Perm s ↔ selected s t.2 = true := by
    rw [selected_iff s t.2 hs]
    constructor
    · intro h y; exact h.mem_iff.symm
    · intro h
      exact (List.perm_ext_iff_of_nodup (hP t ht).1 hs).mpr (fun y => (h y).symm)
  by_cases hh : t.2.Perm s <;> simp [hh, ← he]

theorem coeff_zero {A : List (Poly Nat)} {P : Poly Nat}
    (hP : Reduced A P) (s : List Nat)
    (hs : ¬ (s.Nodup ∧ Safe A s)) : coeff P s = 0 := by
  classical
  unfold coeff cf
  have hz : P.terms.filter (fun t => decide (t.2.Perm s)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    simp only [decide_eq_true_eq]
    intro hp
    apply hs
    refine ⟨hp.nodup_iff.mp (hP t ht).1, ?_⟩
    intro x hx y hy
    exact (hP t ht).2 x (hp.mem_iff.mpr hx) y (hp.mem_iff.mpr hy)
  rw [hz]; rfl

theorem peq_of_good {p : Nat} {A : List (Poly Nat)} {P Q : Poly Nat}
    (hP : Reduced A P) (hQ : Reduced A Q)
    (h : ∀ a, Programme.«20261025-0459-proof-complexity».MatchQuot.Good A a →
      (p : Int) ∣ P.eval a - Q.eval a) : PEq p P Q := by
  classical
  intro s
  by_cases hs : s.Nodup ∧ Safe A s
  · rw [coeff_eq_support hP s hs.1, coeff_eq_support hQ s hs.1]
    exact coefficient_congruence h hs.2
  · rw [coeff_zero hP s hs, coeff_zero hQ s hs]
    simp
theorem normalization_peq {p : Nat} {A : List (Poly Nat)} {P Q : Poly Nat}
    (h : ∀ a, Good A a → (p : Int) ∣ P.eval a - Q.eval a) :
    PEq p (reduce A P) (reduce A Q) := by
  apply peq_of_good (support_reduce A P) (support_reduce A Q)
  intro a ha
  simpa only [eval_reduce A P a ha, eval_reduce A Q a ha] using h a ha

theorem extraction_peq {p n k D : Nat} (hn : 0 < n) (Q : Poly Nat)
    (hQ : Programme.«20261104-1627-proof-complexity».SupportedCertificates.Supported (fun x => decide (x < (n+k)*n)) Q)
    (h : Programme.«20261025-1627-proof-complexity».NoDrop.NSIn p
      (Programme.«20261025-0459-proof-complexity».OntoFPHP.ontoFPHP n k) D Q.eval) :
    ∃ v : Programme.«20261104-1627-proof-complexity».MatchingLabels.Vector,
      (∀ z ∈ v, ∃ d, d ≤ D ∧ z.2 ∈
        Programme.«20261104-1627-proof-complexity».MatchingLabels.labels (n+k) n d) ∧
      PEq p (reduce (Programme.«20261025-0459-proof-complexity».OntoFPHP.ontoFPHP n k)
        (Programme.«20261104-1627-proof-complexity».MatchingLabels.relations (n+k) n v))
        (reduce (Programme.«20261025-0459-proof-complexity».OntoFPHP.ontoFPHP n k) Q) := by
  obtain ⟨v,hv,he⟩ := Programme.«20261104-1627-proof-complexity».SupportedExtraction.supported_extraction hn Q hQ h
  exact ⟨v,hv,normalization_peq he⟩

end Programme.«20261104-1627-proof-complexity».SquareFreeCoefficientBridge
#print axioms Programme.«20261104-1627-proof-complexity».SquareFreeCoefficientBridge.peq_of_good

#print axioms Programme.«20261104-1627-proof-complexity».SquareFreeCoefficientBridge.normalization_peq
#print axioms Programme.«20261104-1627-proof-complexity».SquareFreeCoefficientBridge.extraction_peq
