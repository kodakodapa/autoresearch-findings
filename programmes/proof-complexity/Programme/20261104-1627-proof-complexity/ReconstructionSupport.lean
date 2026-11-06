import Programme.«20261104-1627-proof-complexity».BooleanReconstruction
namespace Programme.«20261104-1627-proof-complexity».BooleanReconstruction
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoSubst
open Programme.«20261104-1627-proof-complexity».OutsideDifference Programme.«20261104-1627-proof-complexity».SupportedCertificates Programme.«20261104-1627-proof-complexity».OffboardSections

theorem leaf_agree (B : Nat → Bool) (s : List Nat) (f : Fn)
    (hf : ∀ a b, (∀ x, B x = true ∨ x ∈ s → a x = b x) → f a = f b) :
    ∀ e ∈ expand s f, ∀ a b,
      (∀ x, B x = true → a x = b x) → e.2 a = e.2 b := by
  induction s generalizing f with
  | nil =>
    intro e he a b hab
    simp [expand] at he
    subst e
    exact hf a b (by simpa using hab)
  | cons x xs ih =>
    have fixed (a b : Nat → Bool)
        (hab : ∀ y, B y = true ∨ y ∈ xs → a y = b y) (v : Bool) :
        ∀ y, B y = true ∨ y ∈ x :: xs → set a x v y = set b x v y := by
      intro y hy
      by_cases h : y = x
      · simp [Programme.«20261104-1627-proof-complexity».OutsideDifference.set, h]
      · have hy' : B y = true ∨ y ∈ xs := by simpa [List.mem_cons, h] using hy
        simp [Programme.«20261104-1627-proof-complexity».OutsideDifference.set, h, hab y hy']
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact ih _ (fun a b hab => hf _ _ (fixed a b hab false)) e he
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
      exact ih _ (fun a b hab => by
        rw [hf _ _ (fixed a b hab true), hf _ _ (fixed a b hab false)]) u hu

theorem leaf_polynomial (s : List Nat) (P : Poly Nat) :
    ∀ e ∈ expand s P.eval, ∃ Q : Poly Nat, ∀ a, Q.eval a = e.2 a := by
  induction s generalizing P with
  | nil => intro e he; simp [expand] at he; subst e; exact ⟨P, fun _ => rfl⟩
  | cons x xs ih =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · let Q := Poly.subst (fun y => if y = x then Lit.const false else .var y) P
      have hQ : Q.eval = fun a => P.eval (set a x false) := by
        funext a
        rw [subst_eval]
        congr 1
        funext y
        by_cases h : y = x <;> simp [pull, Programme.«20261104-1627-proof-complexity».OutsideDifference.set, h, Lit.val]
      rw [← hQ] at he
      exact ih Q e he
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
      have hQ : (diff x P).eval = fun a => P.eval (set a x true) - P.eval (set a x false) := by
        funext a; exact diff_eval x P a
      rw [← hQ] at hu
      exact ih (diff x P) u hu

theorem leaf_supported (B : Nat → Bool) (s : List Nat) (P : Poly Nat)
    (hP : ∀ t ∈ P.terms, ∀ x ∈ t.2, B x = true ∨ x ∈ s) :
    ∀ e ∈ expand s P.eval, ∃ Q : Poly Nat,
      Supported B Q ∧ ∀ a, Q.eval a = e.2 a := by
  intro e he
  obtain ⟨Q, hQ⟩ := leaf_polynomial s P e he
  refine ⟨Poly.subst (sectionSubst B (fun _ => false)) Q, section_supported B _ Q, ?_⟩
  intro a
  rw [subst_eval, hQ]
  have hf : ∀ a b, (∀ x, B x = true ∨ x ∈ s → a x = b x) → P.eval a = P.eval b := by
    intro a b hab
    apply eval_agree (B := fun x => decide (B x = true ∨ x ∈ s))
    · intro t ht x hx; simpa using hP t ht x hx
    · intro x hx; exact hab x (by simpa using hx)
  exact leaf_agree B s P.eval hf e he _ _ (by
    intro x hx
    simp [pull_section, hx])
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261025-0459-proof-complexity».MatchQuot

theorem leaf_supported_certificate {p D : Nat} (B : Nat → Bool)
    (A : List (Poly Nat)) (hA : ∀ R ∈ A, Supported B R)
    (s : List Nat) (hs : ∀ x ∈ s, B x = false) (P : Poly Nat)
    (hP : ∀ t ∈ P.terms, ∀ x ∈ t.2, B x = true ∨ x ∈ s)
    (hf : NSIn p A D P.eval) :
    ∀ e ∈ expand s P.eval, ∃ Q : Poly Nat,
      Supported B Q ∧ (∀ a, Q.eval a = e.2 a) ∧
      ∃ L : List (Poly Nat × Poly Nat),
        (∀ t ∈ L, t.2 ∈ A ∧ t.1.deg + t.2.deg ≤ D-e.1.length ∧ Supported B t.1) ∧
        ∀ a, Good A a → (p : Int) ∣
          (L.map fun t => t.1.eval a * t.2.eval a).sum - e.2 a := by
  intro e he
  obtain ⟨Q, hQB, hQ⟩ := leaf_supported B s P hP e he
  have hn := leaf_budget hA s hs hf e he
  have heq : Q.eval = e.2 := by funext a; exact hQ a
  rw [← heq] at hn
  obtain ⟨L, hL, hEval⟩ := (supported_certificate_iff p _ B A hA Q hQB).mp hn
  refine ⟨Q, hQB, hQ, L, hL, ?_⟩
  intro a ha
  simpa only [hQ a] using hEval a ha
end Programme.«20261104-1627-proof-complexity».BooleanReconstruction
#print axioms Programme.«20261104-1627-proof-complexity».BooleanReconstruction.leaf_supported
#print axioms Programme.«20261104-1627-proof-complexity».BooleanReconstruction.leaf_agree

#print axioms Programme.«20261104-1627-proof-complexity».BooleanReconstruction.leaf_supported_certificate
