import Programme.«20261025-1627-proof-complexity».DesignExt

/-!
# Class version of the design-extension criterion

`DesignExt.ext_sound` asks every degree-`(D-1)` design to extend to a degree-`D` design. Its proof
only ever extends functionals of the form `xFn E x` with `E` a degree-`D` design already in use.
`class_sound`: it is enough to have a class `C` of degree-`D` designs such that for every `E ∈ C`
and variable `x`, `xFn E x` agrees on monomials of length `≤ D - 1` with some member of `C`, and
some member of `C` has `E(1) ≢ 0 (mod p)`. Then there is no degree-`D` `PPCRefutation`.
The class may consist of non-symmetric designs (needed in characteristic `p ≤ D`, where designs
invariant under all hole or all pigeon permutations have `E(1) ≡ 0`).
-/

namespace Programme.«20261026-1402-proof-complexity».ClassExt

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-1627-proof-complexity».DesignExt

/-- **Class design-extension soundness.** -/
theorem class_sound {p D : Nat} {A : List (Poly Nat)} {S : (Nat → Bool) → Prop} (hD : 1 ≤ D)
    (C : Fn p S → Prop) (hC : ∀ E, C E → IsDesign A D E)
    (hstep : ∀ E, C E → ∀ x : Nat, ∃ E' : Fn p S, C E' ∧ Extends (D - 1) E' (xFn E x))
    (E1 : Fn p S) (hE1 : C E1) (h1 : ¬ (p : Int) ∣ E1.E (fun _ => 1)) :
    ¬ PPCRefutation p A D := by
  intro hR
  have inv : ∀ {g : (Nat → Bool) → Int}, PPCDerivable p A D g →
      ∀ E : Fn p S, C E → (p : Int) ∣ E.E g := by
    intro g hg
    induction hg with
    | ax P hP hd =>
      intro E hE
      have := hC E hE P hP [] (by simpa using hd)
      have e : (fun a => monoEval a [] * P.eval a) = fun a => P.eval a := by
        funext a; simp [monoEval]
      rwa [e] at this
    | lin f g u v _ _ ihf ihg =>
      intro E hE
      have h := E.lin f g u v
      have := Int.dvd_add h (Int.dvd_add (dvd_cmul u (ihf E hE)) (dvd_cmul v (ihg E hE)))
      rwa [show E.E (fun a => u * f a + v * g a) - (u * E.E f + v * E.E g) + (u * E.E f + v * E.E g) =
        E.E (fun a => u * f a + v * g a) by omega] at this
    | mul x g d _ hc hd ih =>
      intro E hE
      obtain ⟨E3, hE3, hx3⟩ := hstep E hE x
      have hc' : CubeDeg p g (D - 1) := by
        obtain ⟨Q, hQ, h⟩ := hc; exact ⟨Q, by omega, h⟩
      have := agree hx3 hc'
      have := Int.dvd_sub (ih E3 hE3) this
      rw [show E3.E g - (E3.E g - (xFn E x).E g) = (xFn E x).E g by omega] at this
      exact this
    | congr f g _ hfg ih =>
      intro E hE
      have := Int.dvd_add (E.congr f g hfg) (ih E hE)
      rwa [show E.E f - E.E g + E.E g = E.E f by omega] at this
  exact h1 (inv hR E1 hE1)

/-- `DesignExt.ext_sound` is the case `C = ` all degree-`D` designs. -/
theorem ext_sound_of_class {p D : Nat} {A : List (Poly Nat)} {S : (Nat → Bool) → Prop} (hD : 1 ≤ D)
    (hext : ∀ E' : Fn p S, IsDesign A (D - 1) E' → ∃ E : Fn p S, IsDesign A D E ∧ Extends (D - 1) E E')
    (E0 : Fn p S) (h0 : IsDesign A (D - 1) E0) (h1 : ¬ (p : Int) ∣ E0.E (fun _ => 1)) :
    ¬ PPCRefutation p A D := by
  obtain ⟨E1, hE1, hx⟩ := hext E0 h0
  refine class_sound hD (fun E => IsDesign A D E) (fun _ h => h)
    (fun E hE x => hext _ (xFn_design hD hE x)) E1 hE1 ?_
  intro hd
  have a2 := hx [] (by simp)
  have e : (fun a => monoEval a ([] : List Nat)) = fun _ => (1 : Int) := by funext a; simp [monoEval]
  rw [e] at a2
  exact h1 (by have := Int.dvd_sub hd a2; rwa [show E1.E (fun _ => 1) - (E1.E (fun _ => 1) - E0.E (fun _ => 1)) =
    E0.E (fun _ => 1) by omega] at this)

end Programme.«20261026-1402-proof-complexity».ClassExt

#print axioms Programme.«20261026-1402-proof-complexity».ClassExt.class_sound
#print axioms Programme.«20261026-1402-proof-complexity».ClassExt.ext_sound_of_class
