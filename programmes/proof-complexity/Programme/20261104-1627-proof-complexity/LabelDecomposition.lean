import Programme.«20261104-1627-proof-complexity».MatchingLabels

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261029-1156-proof-complexity».StdPC

/-- The actual finite linear combination of inhomogeneous label relations. -/
def relations (m n : Nat) (v : Vector) : Poly Nat :=
  ⟨v.flatMap fun t => (relation m n t.2).terms.map fun a => (t.1*a.1,a.2)⟩

private theorem cf_scale (c : Int) (L : List (Int × List Nat)) (u : List Nat) :
    cf (L.map fun a => (c*a.1,a.2)) u = c * cf L u := by
  induction L with
  | nil => simp [cf]
  | cons a L ih =>
    by_cases h : a.2.Perm u <;>
      simp [cf, h] at ih ⊢ <;>
      simp_all [Int.mul_add]

/-- Exact coefficient identity, before reduction modulo any characteristic. -/
theorem relations_coeff (m n : Nat) (v : Vector) (u : List Nat) :
    coeff (relations m n v) u = coeff (top m n v) u - coeff (rho n v) u := by
  induction v with
  | nil => simp [relations, top, rho, coeff, cf]
  | cons t v ih =>
    have hs : cf ((relation m n t.2).terms.map fun a => (t.1*a.1,a.2)) u =
        t.1 * cf (topLabel m n t.2).terms u -
          (if (mono n t.2.base).Perm u then t.1 else 0) := by
      rw [cf_scale]
      simp only [relation, Poly.sub, cf_append]
      by_cases h : (mono n t.2.base).Perm u <;>
        simp [cf, h, Int.mul_add, Int.mul_neg, Int.sub_eq_add_neg]
    change cf _ u = cf _ u - cf _ u at ih ⊢
    unfold relations top rho at ih
    simp only [relations, top, rho, List.flatMap_cons, List.map_cons, cf_append]
    rw [hs]
    have ht := cf_scale t.1 (topLabel m n t.2).terms u
    rw [ht]
    by_cases h : (mono n t.2.base).Perm u <;>
      simp [cf, h] at ih ⊢ <;> omega

/-- The top vanishes exactly when the relation sum equals minus its lower
part. This is the algebraic cancellation step in Lemma 1. -/
theorem kernel_iff_lower (p m n d : Nat) (v : Vector) :
    Kernel p m n d v ↔ valid m n d v ∧
      PEq p (relations m n v) ((⟨[]⟩ : Poly Nat).sub (rho n v)) := by
  have hn (u) : coeff ((⟨[]⟩ : Poly Nat).sub (rho n v)) u = -coeff (rho n v) u := by
    change cf ([] ++ negT (rho n v).terms) u = -cf (rho n v).terms u
    simp only [List.nil_append, cf_negT]
  simp only [Kernel, PEq]
  constructor
  · rintro ⟨hv, hk⟩
    refine ⟨hv, fun u => ?_⟩
    rw [relations_coeff, hn]
    have h := hk u
    simpa [coeff, cf] using h
  · rintro ⟨hv, hk⟩
    refine ⟨hv, fun u => ?_⟩
    have h := hk u
    rw [relations_coeff, hn] at h
    simpa [coeff, cf] using h

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.relations_coeff
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.kernel_iff_lower
