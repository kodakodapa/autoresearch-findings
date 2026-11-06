import Programme.«20261025-0459-proof-complexity».OntoFPHP

/-!
# Design extension excludes polynomial calculus refutations

A *functional* `Fn p S` maps lines `(Nat → Bool) → Int` to `Int`, is linear and respects
congruence mod `p`, and only reads its argument on the points of `S`. It is a *degree-`D` design*
for the axioms `A` (`IsDesign`) if it kills `m · P` mod `p` for every `P ∈ A` and every list of
variables `m` with `|m| + deg P ≤ D`. `E` *extends* `E'` to degree `d` (`Extends`) if both agree
mod `p` on every monomial of length `≤ d`.

`ext_sound`: if some degree-`(D-1)` design has `E(1) ≢ 0` and every degree-`(D-1)` design extends
to a degree-`D` design, there is no degree-`D` `PPCRefutation`. Invariant: every degree-`D`
design kills every line. For `x · g` with `g` of cube degree `≤ D-1`, the functional
`h ↦ E(x·h)` is a degree-`(D-1)` design; its degree-`D` extension kills `g` and agrees with it on
`g`. This is the dual of `Work.NoDrop.pc_ns` and needs no linear algebra.
-/

namespace Programme.«20261025-1627-proof-complexity».DesignExt

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».OntoFPHP

/-- A linear functional on lines mod `p`, reading its argument only on `S`. -/
structure Fn (p : Nat) (S : (Nat → Bool) → Prop) where
  E : ((Nat → Bool) → Int) → Int
  lin : ∀ (f g : (Nat → Bool) → Int) (u v : Int),
    (p : Int) ∣ E (fun a => u * f a + v * g a) - (u * E f + v * E g)
  congr : ∀ f g : (Nat → Bool) → Int, (∀ a, (p : Int) ∣ f a - g a) → (p : Int) ∣ E f - E g
  supp : ∀ f g : (Nat → Bool) → Int, (∀ a, S a → f a = g a) → E f = E g

/-- Degree-`D` design: kills every `m · P` with `|m| + deg P ≤ D`. -/
def IsDesign {p : Nat} {S : (Nat → Bool) → Prop} (A : List (Poly Nat)) (D : Nat) (E : Fn p S) : Prop :=
  ∀ P ∈ A, ∀ m : List Nat, m.length + P.deg ≤ D → (p : Int) ∣ E.E (fun a => monoEval a m * P.eval a)

/-- `E` and `E'` agree mod `p` on all monomials of length `≤ d`. -/
def Extends {p : Nat} {S : (Nat → Bool) → Prop} (d : Nat) (E E' : Fn p S) : Prop :=
  ∀ t : List Nat, t.length ≤ d → (p : Int) ∣ E.E (fun a => monoEval a t) - E'.E (fun a => monoEval a t)

theorem dvd_sub_comm {p a b : Int} (h : p ∣ a - b) : p ∣ b - a := by
  have := Int.dvd_neg.mpr h; rwa [Int.neg_sub] at this

theorem dvd_sub_trans {p a b c : Int} (h1 : p ∣ a - b) (h2 : p ∣ b - c) : p ∣ a - c := by
  have := Int.dvd_add h1 h2; rwa [show a - b + (b - c) = a - c by omega] at this

theorem dvd_cmul {p b : Int} (c : Int) (h : p ∣ b) : p ∣ c * b := by
  obtain ⟨d, rfl⟩ := h; exact ⟨c * d, by rw [Int.mul_left_comm]⟩

theorem Fn.zero {p : Nat} {S : (Nat → Bool) → Prop} (E : Fn p S) : (p : Int) ∣ E.E (fun _ => 0) := by
  have h := E.lin (fun _ => 0) (fun _ => 0) 0 0
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero] at h
  exact h

/-- `E` applied to a polynomial is the combination of its monomial values. -/
theorem Fn.terms {p : Nat} {S : (Nat → Bool) → Prop} (E : Fn p S) (L : List (Int × List Nat)) :
    (p : Int) ∣ E.E (fun a => (L.map fun t => t.1 * monoEval a t.2).sum)
      - (L.map fun t => t.1 * E.E (fun a => monoEval a t.2)).sum := by
  induction L with
  | nil => simpa using E.zero
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons]
    have h := E.lin (fun a => monoEval a t.2) (fun a => (L.map fun t => t.1 * monoEval a t.2).sum) t.1 1
    simp only [Int.one_mul] at h
    have h2 := Int.dvd_add h ih
    rwa [show E.E (fun a => t.1 * monoEval a t.2 + (L.map fun t => t.1 * monoEval a t.2).sum) -
        (t.1 * E.E (fun a => monoEval a t.2) + E.E (fun a => (L.map fun t => t.1 * monoEval a t.2).sum)) +
        (E.E (fun a => (L.map fun t => t.1 * monoEval a t.2).sum) -
          (L.map fun t => t.1 * E.E (fun a => monoEval a t.2)).sum) =
        E.E (fun a => t.1 * monoEval a t.2 + (L.map fun t => t.1 * monoEval a t.2).sum) -
        (t.1 * E.E (fun a => monoEval a t.2) + (L.map fun t => t.1 * E.E (fun a => monoEval a t.2)).sum)
        by omega] at h2

/-- Functionals agreeing on monomials of length `≤ d` agree on lines of cube degree `≤ d`. -/
theorem agree {p : Nat} {S : (Nat → Bool) → Prop} {d : Nat} {E E' : Fn p S} (hx : Extends d E E')
    {h : (Nat → Bool) → Int} (hh : CubeDeg p h d) : (p : Int) ∣ E.E h - E'.E h := by
  obtain ⟨Q, hQd, hQ⟩ := hh
  have c1 := E.congr h (fun a => Q.eval a) (fun a => dvd_sub_comm (hQ a))
  have c2 := E'.congr (fun a => Q.eval a) h hQ
  have t1 := E.terms Q.terms
  have t2 := E'.terms Q.terms
  have hsum : (p : Int) ∣ (Q.terms.map fun t => t.1 * E.E (fun a => monoEval a t.2)).sum
      - (Q.terms.map fun t => t.1 * E'.E (fun a => monoEval a t.2)).sum := by
    have hl : ∀ t ∈ Q.terms, t.2.length ≤ d := by
      intro t ht
      have : t.2.length ≤ Q.deg := by
        unfold Poly.deg
        generalize Q.terms = T at ht
        induction T with
        | nil => simp at ht
        | cons s T ih =>
          simp only [List.map_cons, List.foldr_cons]
          rcases List.mem_cons.mp ht with h | h
          · subst h; exact Nat.le_max_left _ _
          · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)
      omega
    generalize Q.terms = T at hl
    induction T with
    | nil => exact ⟨0, by simp⟩
    | cons s T ih =>
      simp only [List.map_cons, List.sum_cons]
      have a1 := dvd_cmul s.1 (hx s.2 (hl s List.mem_cons_self))
      have a2 := ih (fun t ht => hl t (List.mem_cons_of_mem _ ht))
      have := Int.dvd_add a1 a2
      rwa [Int.mul_sub, show s.1 * E.E (fun a => monoEval a s.2) - s.1 * E'.E (fun a => monoEval a s.2) +
        ((T.map fun t => t.1 * E.E (fun a => monoEval a t.2)).sum -
          (T.map fun t => t.1 * E'.E (fun a => monoEval a t.2)).sum) =
        s.1 * E.E (fun a => monoEval a s.2) + (T.map fun t => t.1 * E.E (fun a => monoEval a t.2)).sum -
        (s.1 * E'.E (fun a => monoEval a s.2) + (T.map fun t => t.1 * E'.E (fun a => monoEval a t.2)).sum)
        by omega] at this
  have e1 : (fun a => Q.eval a) = fun a => (Q.terms.map fun t => t.1 * monoEval a t.2).sum := rfl
  rw [e1] at c1 c2
  exact dvd_sub_trans c1 (dvd_sub_trans t1 (dvd_sub_trans hsum (dvd_sub_trans (dvd_sub_comm t2) c2)))

/-- A degree-`D` design kills `m · P` already when `|m| + deg P ≤ D - 1` and it extends a
degree-`(D-1)` design: only the top level needs checking. -/
theorem low_kill {p : Nat} {S : (Nat → Bool) → Prop} {A : List (Poly Nat)} {D : Nat} {E E' : Fn p S}
    (hE' : IsDesign A (D - 1) E') (hx : Extends (D - 1) E E') {P : Poly Nat} (hP : P ∈ A)
    {m : List Nat} (hm : m.length + P.deg ≤ D - 1) :
    (p : Int) ∣ E.E (fun a => monoEval a m * P.eval a) := by
  have hc : CubeDeg p (fun a => monoEval a m * P.eval a) (D - 1) := by
    refine ⟨⟨P.terms.map fun t => (t.1, m ++ t.2)⟩, ?_, fun a => ⟨0, ?_⟩⟩
    · unfold Poly.deg
      have : ∀ t ∈ P.terms, t.2.length ≤ P.deg := by
        intro t ht; unfold Poly.deg
        generalize P.terms = T at ht
        induction T with
        | nil => simp at ht
        | cons s T ih =>
          simp only [List.map_cons, List.foldr_cons]
          rcases List.mem_cons.mp ht with h | h
          · subst h; exact Nat.le_max_left _ _
          · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)
      generalize P.terms = T at this
      induction T with
      | nil => simp
      | cons s T ih =>
        simp only [List.map_map, List.map_cons, List.foldr_cons, Function.comp, List.length_append] at ih ⊢
        have h1 := this s List.mem_cons_self
        have h2 := ih (fun t ht => this t (List.mem_cons_of_mem _ ht))
        exact Nat.max_le.mpr ⟨by omega, h2⟩
    · simp only [Poly.eval, List.map_map, Int.mul_zero]
      have hme : ∀ a (l1 l2 : List Nat), monoEval a (l1 ++ l2) = monoEval a l1 * monoEval a l2 := by
        intro a l1 l2; simp [monoEval, List.map_append, List.prod_append]
      generalize P.terms = T
      induction T with
      | nil => simp
      | cons s T ih =>
        simp only [List.map_cons, List.sum_cons, Function.comp, hme, Int.mul_add] at ih ⊢
        rw [show s.1 * (monoEval a m * monoEval a s.2) = monoEval a m * (s.1 * monoEval a s.2) by
          rw [Int.mul_left_comm]]
        omega
  have := Int.dvd_add (agree hx hc) (hE' P hP m hm)
  rwa [Int.sub_add_cancel] at this

/-- `h ↦ E(x · h)`. -/
def xFn {p : Nat} {S : (Nat → Bool) → Prop} (E : Fn p S) (x : Nat) : Fn p S where
  E h := E.E (fun a => xv x a * h a)
  lin f g u v := by
    have := E.lin (fun a => xv x a * f a) (fun a => xv x a * g a) u v
    have e : (fun a => u * (xv x a * f a) + v * (xv x a * g a)) = fun a => xv x a * (u * f a + v * g a) := by
      funext a; grind
    rwa [e] at this
  congr f g h := E.congr _ _ (fun a => by rw [← Int.mul_sub]; exact dvd_cmul _ (h a))
  supp f g h := E.supp _ _ (fun a ha => by rw [h a ha])

theorem monoEval_cons (x : Nat) (m : List Nat) (a : Nat → Bool) :
    monoEval a (x :: m) = xv x a * monoEval a m := by
  simp only [monoEval, List.map_cons, List.prod_cons, xv]

theorem xFn_design {p : Nat} {S : (Nat → Bool) → Prop} {A : List (Poly Nat)} {D : Nat} (hD : 1 ≤ D)
    {E : Fn p S} (hE : IsDesign A D E) (x : Nat) : IsDesign A (D - 1) (xFn E x) := by
  intro P hP m hm
  have := hE P hP (x :: m) (by simp only [List.length_cons]; omega)
  show (p : Int) ∣ E.E (fun a => xv x a * (monoEval a m * P.eval a))
  have e : (fun a => xv x a * (monoEval a m * P.eval a)) = fun a => monoEval a (x :: m) * P.eval a := by
    funext a; rw [monoEval_cons, Int.mul_assoc]
  rwa [e]

/-- **Design extension soundness.** -/
theorem ext_sound {p D : Nat} {A : List (Poly Nat)} {S : (Nat → Bool) → Prop} (hD : 1 ≤ D)
    (hext : ∀ E' : Fn p S, IsDesign A (D - 1) E' → ∃ E : Fn p S, IsDesign A D E ∧ Extends (D - 1) E E')
    (E0 : Fn p S) (h0 : IsDesign A (D - 1) E0) (h1 : ¬ (p : Int) ∣ E0.E (fun _ => 1)) :
    ¬ PPCRefutation p A D := by
  intro hR
  have inv : ∀ {g : (Nat → Bool) → Int}, PPCDerivable p A D g →
      ∀ E : Fn p S, IsDesign A D E → (p : Int) ∣ E.E g := by
    intro g hg
    induction hg with
    | ax P hP hd =>
      intro E hE
      have := hE P hP [] (by simpa using hd)
      have e : (fun a => monoEval a [] * P.eval a) = fun a => P.eval a := by
        funext a; simp [monoEval]
      rwa [e] at this
    | lin f g u v _ _ ihf ihg =>
      intro E hE
      have h := E.lin f g u v
      have := Int.dvd_add h (Int.dvd_add (dvd_cmul u (ihf E hE))
        (dvd_cmul v (ihg E hE)))
      rwa [show E.E (fun a => u * f a + v * g a) - (u * E.E f + v * E.E g) + (u * E.E f + v * E.E g) =
        E.E (fun a => u * f a + v * g a) by omega] at this
    | mul x g d _ hc hd ih =>
      intro E hE
      obtain ⟨E3, hE3, hx3⟩ := hext (xFn E x) (xFn_design hD hE x)
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
  obtain ⟨E, hE, hx⟩ := hext E0 h0
  have a1 := inv hR E hE
  have a2 := hx [] (by simp)
  have e : (fun a => monoEval a ([] : List Nat)) = fun _ => (1 : Int) := by funext a; simp [monoEval]
  rw [e] at a2
  exact h1 (by have := Int.dvd_sub a1 a2; rwa [show E.E (fun _ => 1) - (E.E (fun _ => 1) - E0.E (fun _ => 1)) =
    E0.E (fun _ => 1) by omega] at this)

end Programme.«20261025-1627-proof-complexity».DesignExt

#print axioms Programme.«20261025-1627-proof-complexity».DesignExt.ext_sound
#print axioms Programme.«20261025-1627-proof-complexity».DesignExt.low_kill
