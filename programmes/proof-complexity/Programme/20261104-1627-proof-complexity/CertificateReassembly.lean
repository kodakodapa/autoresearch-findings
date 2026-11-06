import Programme.«20261104-1627-proof-complexity».LeafDegree
import Programme.«20261104-1627-proof-complexity».NoDropPolynomial
namespace Programme.«20261104-1627-proof-complexity».BooleanReconstruction
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261104-1627-proof-complexity».SupportedCertificates

theorem nsIn_mono {p d E : Nat} {A : List (Poly Nat)} {f : Fn}
    (h : NSIn p A d f) (hd : d ≤ E) : NSIn p A E f := by
  obtain ⟨L, hL, he⟩ := h
  exact ⟨L, fun e he => ⟨(hL e he).1, Nat.le_trans (hL e he).2 hd⟩, he⟩

theorem nsIn_monomial {p d : Nat} {A : List (Poly Nat)} {f : Fn}
    (u : List Nat) (h : NSIn p A d f) :
    NSIn p A (d + u.length) (fun a => monoEval a u * f a) := by
  induction u with
  | nil => simpa [monoEval] using h
  | cons x xs ih =>
    have hh := nsIn_xmul (D := d + xs.length + 1) x (by simpa using ih) (by omega)
    simpa [monoEval_cons, Int.mul_assoc, Nat.add_assoc] using hh

theorem nsIn_sum {p E : Nat} {A : List (Poly Nat)}
    (L : List Fn) (h : ∀ f ∈ L, NSIn p A E f) :
    NSIn p A E (fun a => (L.map (fun f => f a)).sum) := by
  induction L with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons f L ih =>
    have hh := nsIn_lin 1 1 (h f (by simp)) (ih (fun g hg => h g (by simp [hg])))
    simpa using hh

theorem reassemble {p E : Nat} {A : List (Poly Nat)} (s : List Nat) (f : Fn)
    (h : ∀ e ∈ expand s f, NSIn p A E (fun a => monoEval a e.1 * e.2 a)) :
    NSIn p A E f := by
  have hh := nsIn_sum ((expand s f).map (fun e => fun a => monoEval a e.1 * e.2 a)) (by
    intro g hg; obtain ⟨e, he, rfl⟩ := List.mem_map.mp hg; exact h e he)
  apply nsIn_congr hh
  intro a
  simp only [List.map_map]
  change (p : Int) ∣ f a - ((expand s f).map (fun e => monoEval a e.1 * e.2 a)).sum
  rw [reconstruction]; simp

theorem polynomial_of_supported {p D : Nat} {A : List (Poly Nat)} {B : Nat → Bool}
    (hA : ∀ P ∈ A, Supported B P)
    (nd : ∀ r, 0 < r → r ≤ D → ∀ Q : Poly Nat, Supported B Q →
      Q.deg ≤ r-1 → NSIn p A r Q.eval → NSIn p A (r-1) Q.eval)
    (P : Poly Nat) (hD : 0 < D) (hd : P.deg ≤ D-1)
    (s : List Nat) (hs : ∀ x ∈ s, B x = false)
    (cover : ∀ t ∈ P.terms, ∀ x ∈ t.2, B x = true ∨ x ∈ s)
    (hf : NSIn p A D P.eval) : NSIn p A (D-1) P.eval := by
  apply reassemble s P.eval
  intro e he
  by_cases hu : e.1.length ≤ P.deg
  · obtain ⟨Q, hQB, hQ, hdeg⟩ := leaf_supported_degree B s P cover e he hu
    have hb := leaf_budget hA s hs hf e he
    have hqmem : NSIn p A (D-e.1.length) Q.eval := by
      apply nsIn_congr hb
      intro a; rw [hQ]; simp
    have hl := nd (D-e.1.length) (by omega) (by omega) Q hQB (by omega) hqmem
    have hm := nsIn_monomial e.1 hl
    have hm' := nsIn_mono hm (E := D-1) (by omega)
    apply nsIn_congr hm'
    intro a; rw [hQ]; simp
  · have hz := leaf_vanish s P e he (by omega)
    refine ⟨[], by simp, ?_⟩
    intro a _; simp [hz a]
/-- Full canonical NoDrop follows from supported lowering at every residual level. -/
theorem nodrop_of_supported {p D : Nat} {A : List (Poly Nat)} {B : Nat → Bool}
    (hA : ∀ P ∈ A, Supported B P) (hD : 0 < D)
    (nd : ∀ r, 0 < r → r ≤ D → ∀ Q : Poly Nat, Supported B Q →
      Q.deg ≤ r-1 → NSIn p A r Q.eval → NSIn p A (r-1) Q.eval) :
    NoDrop p A D := by
  apply (Programme.«20261104-1627-proof-complexity».NoDropPolynomial.nodrop_iff_polynomial p D A).mpr
  intro P hd hf
  let s := (P.terms.flatMap (fun t => t.2)).filter (fun x => !(B x))
  apply polynomial_of_supported hA nd P hD hd s ?_ ?_ hf
  · intro x hx
    have hh := (List.mem_filter.mp hx).2
    simpa using hh
  · intro t ht x hx
    cases hb : B x with
    | true => exact Or.inl rfl
    | false =>
      right
      apply List.mem_filter.mpr
      exact ⟨List.mem_flatMap.mpr ⟨t, ht, hx⟩, by simp [hb]⟩
end Programme.«20261104-1627-proof-complexity».BooleanReconstruction
#print axioms Programme.«20261104-1627-proof-complexity».BooleanReconstruction.reassemble
#print axioms Programme.«20261104-1627-proof-complexity».BooleanReconstruction.polynomial_of_supported

#print axioms Programme.«20261104-1627-proof-complexity».BooleanReconstruction.nodrop_of_supported
