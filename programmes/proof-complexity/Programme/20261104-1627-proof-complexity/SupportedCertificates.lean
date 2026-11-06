import Programme.«20261104-1627-proof-complexity».OffboardSections
namespace Programme.«20261104-1627-proof-complexity».SupportedCertificates
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst
open Programme.«20261025-0459-proof-complexity».MatchQuot
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261104-1627-proof-complexity».OffboardSections

def Supported (B : Nat → Bool) (P : Poly Nat) : Prop :=
  ∀ t ∈ P.terms, ∀ x ∈ t.2, B x = true

theorem eval_agree {B : Nat → Bool} {P : Poly Nat} (hP : Supported B P)
    {a b : Nat → Bool} (h : ∀ x, B x = true → a x = b x) : P.eval a = P.eval b := by
  unfold Poly.eval
  congr 1
  apply List.map_congr_left
  intro t ht
  congr 1
  unfold monoEval
  congr 1
  apply List.map_congr_left
  intro x hx
  rw [h x (hP t ht x hx)]

theorem section_supported (B b : Nat → Bool) (P : Poly Nat) :
    Supported B (Poly.subst (sectionSubst B b) P) := by
  intro t ht x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.mp hx
  by_cases hb : B y = true
  · simp [sectionSubst, hb, Lit.vars] at hxy
    subst x
    exact hb
  · simp [sectionSubst, hb, Lit.vars] at hxy

theorem good_section {B : Nat → Bool} {A : List (Poly Nat)}
    (hA : ∀ P ∈ A, Supported B P) (b a : Nat → Bool) (ha : Good A a) :
    Good A (pull (sectionSubst B b) a) := by
  intro u w huw h
  have hu : B u = true := hA _ huw (1, [u,w]) (by simp [prod2]) u (by simp)
  have hw : B w = true := hA _ huw (1, [u,w]) (by simp [prod2]) w (by simp)
  apply ha u w huw
  simpa [pull_section, hu, hw] using h

theorem supported_certificate_iff (p D : Nat) (B : Nat → Bool)
    (A : List (Poly Nat)) (hA : ∀ P ∈ A, Supported B P)
    (Q : Poly Nat) (hQ : Supported B Q) :
    NSIn p A D Q.eval ↔
      ∃ L : List (Poly Nat × Poly Nat),
        (∀ e ∈ L, e.2 ∈ A ∧ e.1.deg + e.2.deg ≤ D ∧ Supported B e.1) ∧
        ∀ a, Good A a →
          (p : Int) ∣ (L.map fun e => e.1.eval a * e.2.eval a).sum - Q.eval a := by
  constructor
  · rintro ⟨L, hL, he⟩
    let σ := sectionSubst B (fun _ => false)
    have hagree (a : Nat → Bool) : ∀ x, B x = true → pull σ a x = a x := by
      intro x hx
      simp [σ, pull_section, hx]
    refine ⟨L.map (fun e => (Poly.subst σ e.1, e.2)), ?_, ?_⟩
    · intro e he
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
      exact ⟨(hL b hb).1, Nat.le_trans
        (Nat.add_le_add_right (subst_deg σ b.1) _) (hL b hb).2,
        section_supported B _ b.1⟩
    · intro a ha
      have hh := he (pull σ a) (good_section hA _ a ha)
      have eq : ((L.map fun e => (Poly.subst σ e.1, e.2)).map
          fun e => e.1.eval a * e.2.eval a).sum =
          (L.map fun e => e.1.eval (pull σ a) * e.2.eval (pull σ a)).sum := by
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro e he
        simp only [Function.comp_def, subst_eval]
        rw [eval_agree (hA e.2 (hL e he).1) (hagree a)]
      rw [eq, ← eval_agree hQ (hagree a)]
      exact hh
  · rintro ⟨L, hL, he⟩
    exact ⟨L, fun e he => ⟨(hL e he).1, (hL e he).2.1⟩, he⟩

theorem supported_sumOne (B : Nat → Bool) (v : Nat → Nat) (m : Nat)
    (hv : ∀ i < m, B (v i) = true) : Supported B (sumOne v m) := by
  have hl : ∀ r, (∀ i < r, B (v i) = true) →
      ∀ t ∈ linTerms v r, ∀ x ∈ t.2, B x = true := by
    intro r
    induction r with
    | zero => simp [linTerms]
    | succ r ih =>
      intro h t ht x hx
      simp only [linTerms, List.mem_append, List.mem_singleton] at ht
      rcases ht with ht | rfl
      · exact ih (fun i hi => h i (by omega)) t ht x hx
      · simp only [List.mem_singleton] at hx
        subst x
        exact h r (by omega)
  intro t ht x hx
  simp only [sumOne, List.mem_cons] at ht
  rcases ht with rfl | ht
  · simp at hx
  · exact hl m hv t ht x hx

theorem onto_supported (n k : Nat) :
    ∀ P ∈ ontoFPHP n k, Supported (fun x => decide (x < (n+k)*n)) P := by
  have hv : ∀ i < n+k, ∀ j < n,
      (fun x => decide (x < (n+k)*n)) (var n i j) = true := by
    intro i hi j hj
    change decide (i*n+j < (n+k)*n) = true
    simp only [decide_eq_true_eq]
    have hh := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul] at hh
    omega
  have hp : ∀ i j i' j', i < n+k → j < n → i' < n+k → j' < n →
      Supported (fun x => decide (x < (n+k)*n)) (prod2 (var n i j) (var n i' j')) := by
    intro i j i' j' hi hj hi' hj' t ht x hx
    simp only [prod2, List.mem_singleton] at ht
    subst t
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hv i hi j hj
    · exact hv i' hi' j' hj'
  intro P hP
  simp only [ontoFPHP, List.mem_append] at hP
  rcases hP with ((hP | hP) | hP) | hP
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hP
    exact supported_sumOne _ _ _ (fun j hj => hv i (List.mem_range.mp hi) j hj)
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hP
    exact supported_sumOne _ _ _ (fun i hi => hv i hi j (List.mem_range.mp hj))
  · obtain ⟨j, hj, hP⟩ := List.mem_flatMap.mp hP
    obtain ⟨i, hi, hP⟩ := List.mem_flatMap.mp hP
    obtain ⟨i', hi', hP⟩ := List.mem_filterMap.mp hP
    split at hP <;> simp_all only [Option.some.injEq, reduceCtorEq]
    subst P
    exact hp i j i' j (List.mem_range.mp hi) (List.mem_range.mp hj)
      (List.mem_range.mp hi') (List.mem_range.mp hj)
  · obtain ⟨i, hi, hP⟩ := List.mem_flatMap.mp hP
    obtain ⟨j, hj, hP⟩ := List.mem_flatMap.mp hP
    obtain ⟨j', hj', hP⟩ := List.mem_filterMap.mp hP
    split at hP <;> simp_all only [Option.some.injEq, reduceCtorEq]
    subst P
    exact hp i j i j' (List.mem_range.mp hi) (List.mem_range.mp hj)
      (List.mem_range.mp hi) (List.mem_range.mp hj')

end Programme.«20261104-1627-proof-complexity».SupportedCertificates
#print axioms Programme.«20261104-1627-proof-complexity».SupportedCertificates.supported_certificate_iff

#print axioms Programme.«20261104-1627-proof-complexity».SupportedCertificates.onto_supported
