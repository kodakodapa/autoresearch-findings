import Programme.«20261104-1627-proof-complexity».PolynomialMultiplierLabels
namespace Programme.«20261104-1627-proof-complexity».AxiomExtraction
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».MatchQuot
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261104-1627-proof-complexity».PolynomialMultiplierLabels

theorem sumOne_positive_degree (v : Nat → Nat) {m : Nat} (hm : 0 < m) :
    1 ≤ (sumOne v m).deg := by
  have mem : (1, [v 0]) ∈ linTerms v m := by
    cases m with
    | zero => omega
    | succ m =>
      induction m with
      | zero => simp [linTerms]
      | succ m ih => exact List.mem_append_left _ (ih (by omega))
  have h := (deg_le_iff (sumOne v m) (sumOne v m).deg).mp (Nat.le_refl _)
    (1,[v 0]) (List.mem_cons_of_mem _ mem)
  exact h

theorem forbidden_eval {A : List (Poly Nat)} {u w : Nat}
    (h : prod2 u w ∈ A) {a : Nat → Bool} (ha : Good A a) :
    (prod2 u w).eval a = 0 := by
  have hh := ha u w h
  cases hu : a u <;> cases hw : a w <;>
    simp_all [prod2, Poly.eval, monoEval]

/-- Every concrete axiom product has a bounded label witness on Good points. -/
theorem axiom_product {n k D : Nat} (hn : 0 < n) (P F : Poly Nat)
    (hs : ∀ t ∈ P.terms, Programme.«20261104-1627-proof-complexity».MatchingReduction.Safe (ontoFPHP n k) t.2 ∧
      t.2.Nodup ∧ (∀ x ∈ t.2, x < (n+k)*n))
    (hF : F ∈ ontoFPHP n k) (hd : P.deg + F.deg ≤ D) :
    ∃ v : Vector, (∀ z ∈ v, ∃ d, d ≤ D ∧ z.2 ∈ labels (n+k) n d) ∧
      ∀ a, Good (ontoFPHP n k) a →
        (relations (n+k) n v).eval a = P.eval a * F.eval a := by
  have horig := hF
  simp only [ontoFPHP, List.mem_append] at hF
  rcases hF with ((hF | hF) | hF) | hF
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hF
    apply polynomial_row P hs _ (List.mem_range.mp hi)
    have := sumOne_positive_degree (fun j => var n i j) hn
    omega
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hF
    apply polynomial_column P hs _ (List.mem_range.mp hj)
    have := sumOne_positive_degree (fun i => var n i j) (by omega : 0 < n+k)
    omega
  · obtain ⟨j,hj,hF⟩ := List.mem_flatMap.mp hF
    obtain ⟨i,hi,hF⟩ := List.mem_flatMap.mp hF
    obtain ⟨i',hi',hF⟩ := List.mem_filterMap.mp hF
    split at hF <;> simp_all only [Option.some.injEq, reduceCtorEq]
    subst F
    refine ⟨[], by simp, ?_⟩
    intro a ha
    rw [forbidden_eval horig ha]
    simp [relations, Poly.eval]
  · obtain ⟨i,hi,hF⟩ := List.mem_flatMap.mp hF
    obtain ⟨j,hj,hF⟩ := List.mem_flatMap.mp hF
    obtain ⟨j',hj',hF⟩ := List.mem_filterMap.mp hF
    split at hF <;> simp_all only [Option.some.injEq, reduceCtorEq]
    subst F
    refine ⟨[], by simp, ?_⟩
    intro a ha
    rw [forbidden_eval horig ha]
    simp [relations, Poly.eval]
theorem certificate_extraction {p n k D : Nat} (hn : 0 < n)
    (L : List (Poly Nat × Poly Nat)) (f : (Nat → Bool) → Int)
    (hL : ∀ e ∈ L, e.2 ∈ ontoFPHP n k ∧ e.1.deg + e.2.deg ≤ D ∧
      ∀ t ∈ e.1.terms, Programme.«20261104-1627-proof-complexity».MatchingReduction.Safe (ontoFPHP n k) t.2 ∧
        t.2.Nodup ∧ (∀ x ∈ t.2, x < (n+k)*n))
    (he : ∀ a, Good (ontoFPHP n k) a →
      (p : Int) ∣ (L.map fun e => e.1.eval a * e.2.eval a).sum - f a) :
    ∃ v : Vector, (∀ z ∈ v, ∃ d, d ≤ D ∧ z.2 ∈ labels (n+k) n d) ∧
      ∀ a, Good (ontoFPHP n k) a →
        (p : Int) ∣ (relations (n+k) n v).eval a - f a := by
  have assemble : ∀ L : List (Poly Nat × Poly Nat),
      (∀ e ∈ L, e.2 ∈ ontoFPHP n k ∧ e.1.deg + e.2.deg ≤ D ∧
        ∀ t ∈ e.1.terms, Programme.«20261104-1627-proof-complexity».MatchingReduction.Safe (ontoFPHP n k) t.2 ∧
          t.2.Nodup ∧ (∀ x ∈ t.2, x < (n+k)*n)) →
      ∃ v : Vector, (∀ z ∈ v, ∃ d, d ≤ D ∧ z.2 ∈ labels (n+k) n d) ∧
        ∀ a, Good (ontoFPHP n k) a →
          (relations (n+k) n v).eval a =
            (L.map fun e => e.1.eval a * e.2.eval a).sum := by
    intro M
    induction M with
    | nil => exact fun _ => ⟨[], by simp, by simp [relations, Poly.eval]⟩
    | cons e M ih =>
      intro hM
      have h := hM e (by simp)
      obtain ⟨v,hv,he⟩ := axiom_product hn e.1 e.2 h.2.2 h.1 h.2.1
      obtain ⟨w,hw,hf⟩ := ih (fun z hz => hM z (by simp [hz]))
      refine ⟨v++w, ?_, ?_⟩
      · intro z hz
        exact (List.mem_append.mp hz).elim (hv z) (hw z)
      · intro a ha
        rw [append_eval, he a ha, hf a ha]
        simp
  obtain ⟨v,hv,h⟩ := assemble L hL
  exact ⟨v,hv,fun a ha => by rw [h a ha]; exact he a ha⟩
end Programme.«20261104-1627-proof-complexity».AxiomExtraction
#print axioms Programme.«20261104-1627-proof-complexity».AxiomExtraction.axiom_product

#print axioms Programme.«20261104-1627-proof-complexity».AxiomExtraction.certificate_extraction
