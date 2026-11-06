import Programme.«20261025-1627-proof-complexity».DesignExt

namespace Programme.«20261031-1904-proof-complexity».RestrictedClosure
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-1627-proof-complexity».DesignExt

/-- Only variable-conditioned members of Q need extensions back into Q. -/
theorem no_refutation {p D : Nat} {A : List (Poly Nat)}
    {S : (Nat → Bool) → Prop} (Q : Fn p S → Prop)
    (design : ∀ E, Q E → IsDesign A D E)
    (closed : ∀ E, Q E → ∀ x, ∃ F, Q F ∧ Extends (D - 1) F (xFn E x))
    (E0 : Fn p S) (mem0 : Q E0) (unit0 : ¬ (p : Int) ∣ E0.E (fun _ => 1)) :
    ¬ PPCRefutation p A D := by
  have invariant : ∀ {g}, PPCDerivable p A D g → ∀ E, Q E → (p : Int) ∣ E.E g := by
    intro g deriv
    induction deriv with
    | ax P hP hd =>
      intro E hE
      simpa [monoEval] using design E hE P hP [] (by simpa using hd)
    | lin f g u v hf hg ihf ihg =>
      intro E hE
      have h := Int.dvd_add (E.lin f g u v)
        (Int.dvd_add (dvd_cmul u (ihf E hE)) (dvd_cmul v (ihg E hE)))
      simpa only [Int.sub_add_cancel] using h
    | mul x g d hg hc hd ih =>
      intro E hE
      obtain ⟨F, hF, agreement⟩ := closed E hE x
      have degree : CubeDeg p g (D - 1) := by
        obtain ⟨P, hP, hp⟩ := hc
        exact ⟨P, by omega, hp⟩
      have h := Int.dvd_sub (ih F hF) (agree agreement degree)
      change (p : Int) ∣ (xFn E x).E g
      rwa [show F.E g - (F.E g - (xFn E x).E g) = (xFn E x).E g by omega] at h
    | congr f g hg hfg ih =>
      intro E hE
      have h := Int.dvd_add (E.congr f g hfg) (ih E hE)
      simpa only [Int.sub_add_cancel] using h
  intro refutation
  exact unit0 (invariant refutation E0 mem0)
end Programme.«20261031-1904-proof-complexity».RestrictedClosure
#print axioms Programme.«20261031-1904-proof-complexity».RestrictedClosure.no_refutation
