import Programme.«20261104-1627-proof-complexity».MultiplierLabels
namespace Programme.«20261104-1627-proof-complexity».PolynomialMultiplierLabels
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».MatchQuot
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261104-1627-proof-complexity».BoundedRelationCertificates

theorem append_eval (m n : Nat) (v w : Vector) (a : Nat → Bool) :
    (relations m n (v++w)).eval a = (relations m n v).eval a + (relations m n w).eval a := by
  induction v with
  | nil => simp [relations, Poly.eval]
  | cons t v ih => simp only [List.cons_append, relations_cons_eval, ih, Int.add_assoc]

theorem scale_eval (m n : Nat) (c : Int) (v : Vector) (a : Nat → Bool) :
    (relations m n (v.map fun t => (c*t.1,t.2))).eval a = c*(relations m n v).eval a := by
  induction v with
  | nil => simp [relations, Poly.eval]
  | cons t v ih => simp only [List.map_cons, relations_cons_eval, ih, Int.mul_add, Int.mul_assoc]

theorem assemble {n k D : Nat} (L : List (Int × List Nat)) (F : Poly Nat)
    (h : ∀ t ∈ L, ∃ v : Vector,
      (∀ z ∈ v, ∃ d, d ≤ D ∧ z.2 ∈ labels (n+k) n d) ∧
      ∀ a, Good (ontoFPHP n k) a →
        (relations (n+k) n v).eval a = monoEval a t.2 * F.eval a) :
    ∃ v : Vector, (∀ z ∈ v, ∃ d, d ≤ D ∧ z.2 ∈ labels (n+k) n d) ∧
      ∀ a, Good (ontoFPHP n k) a →
        (relations (n+k) n v).eval a = (Poly.eval a ⟨L⟩) * F.eval a := by
  induction L with
  | nil => exact ⟨[], by simp, by simp [relations, Poly.eval]⟩
  | cons t L ih =>
    obtain ⟨v,hv,he⟩ := h t (by simp)
    obtain ⟨w,hw,hf⟩ := ih (fun z hz => h z (by simp [hz]))
    refine ⟨(v.map fun z => (t.1*z.1,z.2)) ++ w, ?_, ?_⟩
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hz
        exact hv u hu
      · exact hw z hz
    · intro a ha
      rw [append_eval, scale_eval, he a ha, hf a ha]
      simp only [Poly.eval, List.map_cons, List.sum_cons, Int.add_mul, Int.mul_assoc]

theorem polynomial_row {n k D i : Nat} (P : Poly Nat)
    (hs : ∀ t ∈ P.terms, Programme.«20261104-1627-proof-complexity».MatchingReduction.Safe (ontoFPHP n k) t.2 ∧
      t.2.Nodup ∧ (∀ x ∈ t.2, x < (n+k)*n))
    (hd : P.deg + 1 ≤ D) (hi : i < n+k) :
    ∃ v : Vector, (∀ z ∈ v, ∃ d, d ≤ D ∧ z.2 ∈ labels (n+k) n d) ∧
      ∀ a, Good (ontoFPHP n k) a →
        (relations (n+k) n v).eval a = P.eval a * (sumOne (fun j => var n i j) n).eval a := by
  apply assemble P.terms
  intro t ht
  obtain ⟨hS,hN,hB⟩ := hs t ht
  obtain ⟨v,hv,he⟩ := Programme.«20261104-1627-proof-complexity».MultiplierLabels.safe_row_product t.2 hS hN hB hi
  refine ⟨v, ?_, he⟩
  intro z hz
  refine ⟨t.2.length+1, ?_, hv z hz⟩
  have hh := (deg_le_iff P P.deg).mp (Nat.le_refl _) t ht
  omega

theorem polynomial_column {n k D j : Nat} (P : Poly Nat)
    (hs : ∀ t ∈ P.terms, Programme.«20261104-1627-proof-complexity».MatchingReduction.Safe (ontoFPHP n k) t.2 ∧
      t.2.Nodup ∧ (∀ x ∈ t.2, x < (n+k)*n))
    (hd : P.deg + 1 ≤ D) (hj : j < n) :
    ∃ v : Vector, (∀ z ∈ v, ∃ d, d ≤ D ∧ z.2 ∈ labels (n+k) n d) ∧
      ∀ a, Good (ontoFPHP n k) a →
        (relations (n+k) n v).eval a = P.eval a * (sumOne (fun i => var n i j) (n+k)).eval a := by
  apply assemble P.terms
  intro t ht
  obtain ⟨hS,hN,hB⟩ := hs t ht
  obtain ⟨v,hv,he⟩ := Programme.«20261104-1627-proof-complexity».MultiplierLabels.safe_column_product t.2 hS hN hB hj
  refine ⟨v, ?_, he⟩
  intro z hz
  refine ⟨t.2.length+1, ?_, hv z hz⟩
  have hh := (deg_le_iff P P.deg).mp (Nat.le_refl _) t ht
  omega
end Programme.«20261104-1627-proof-complexity».PolynomialMultiplierLabels
#print axioms Programme.«20261104-1627-proof-complexity».PolynomialMultiplierLabels.polynomial_row
#print axioms Programme.«20261104-1627-proof-complexity».PolynomialMultiplierLabels.polynomial_column
