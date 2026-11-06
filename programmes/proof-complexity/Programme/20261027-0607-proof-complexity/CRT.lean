import Programme.«20261025-0459-proof-complexity».OntoFPHP

/-!
# Chinese remainder theorem for `PPCRefutation`

For coprime moduli `a, b` and any polynomial axiom list `A`:
`PPCRefutation (a * b) A D ↔ PPCRefutation a A D ∧ PPCRefutation b A D`.

* `down`: a derivation mod `m` is a derivation mod every divisor `q` of `m`.
* `scale`: a derivation of `f` mod `a` gives a derivation of `b * f` mod `a * b`
  (scale every line by `b`).
* glue: with `x * a + y * b = 1`, `y * (b * 1) + x * (a * 1) = 1`.
-/

namespace Programme.«20261027-0607-proof-complexity».CRT

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».OntoFPHP

/-- A derivation mod `m` is a derivation mod any divisor `q` of `m`. -/
theorem down {m q D : Nat} {A : List (Poly Nat)} (hq : q ∣ m) {g : (Nat → Bool) → Int}
    (h : PPCDerivable m A D g) : PPCDerivable q A D g := by
  have hq' : (q : Int) ∣ (m : Int) := Int.natCast_dvd_natCast.mpr hq
  induction h with
  | ax P hP hd => exact PPCDerivable.ax P hP hd
  | lin f g u v _ _ ihf ihg => exact PPCDerivable.lin f g u v ihf ihg
  | mul x g d _ hc hd ih =>
    obtain ⟨Q, hQ, hQe⟩ := hc
    exact PPCDerivable.mul x g d ih ⟨Q, hQ, fun a => Int.dvd_trans hq' (hQe a)⟩ hd
  | congr f g _ hfg ih => exact PPCDerivable.congr f g ih (fun a => Int.dvd_trans hq' (hfg a))

theorem refutation_down {m q D : Nat} {A : List (Poly Nat)} (hq : q ∣ m)
    (h : PPCRefutation m A D) : PPCRefutation q A D := down hq h

/-- Scale a polynomial by an integer. -/
def smulP (c : Int) (P : Poly Nat) : Poly Nat := ⟨P.terms.map fun t => (c * t.1, t.2)⟩

theorem smulP_eval (c : Int) (P : Poly Nat) (a : Nat → Bool) : (smulP c P).eval a = c * P.eval a := by
  obtain ⟨ts⟩ := P
  simp only [smulP, Poly.eval]
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, List.map_map] at ih ⊢
    rw [ih, Int.mul_add, Int.mul_assoc]

theorem smulP_deg (c : Int) (P : Poly Nat) : (smulP c P).deg = P.deg := by
  obtain ⟨ts⟩ := P
  simp only [smulP, Poly.deg, List.map_map]
  rfl

/-- A derivation of `f` mod `a` scales to a derivation of `b * f` mod `a * b`. -/
theorem scale {a b D : Nat} {A : List (Poly Nat)} {g : (Nat → Bool) → Int}
    (h : PPCDerivable a A D g) : PPCDerivable (a * b) A D (fun x => (b : Int) * g x) := by
  induction h with
  | ax P hP hd =>
    have h0 := PPCDerivable.ax (p := a * b) P hP hd
    exact PPCDerivable.congr _ _ (PPCDerivable.lin _ _ (b : Int) 0 h0 h0)
      (fun x => ⟨0, by simp⟩)
  | lin f g u v _ _ ihf ihg =>
    refine PPCDerivable.congr _ _ (PPCDerivable.lin _ _ u v ihf ihg) (fun x => ⟨0, ?_⟩)
    simp only [Int.mul_zero]
    rw [Int.mul_add, Int.mul_left_comm (b : Int) u, Int.mul_left_comm (b : Int) v]; omega
  | mul y g d _ hc hd ih =>
    obtain ⟨Q, hQ, hQe⟩ := hc
    have hc' : CubeDeg (a * b) (fun x => (b : Int) * g x) d := by
      refine ⟨smulP b Q, by rw [smulP_deg]; exact hQ, fun x => ?_⟩
      rw [smulP_eval, ← Int.mul_sub]
      obtain ⟨t, ht⟩ := hQe x
      exact ⟨t, by rw [ht]; push_cast; rw [Int.mul_comm (a : Int) (b : Int), Int.mul_assoc]⟩
    refine PPCDerivable.congr _ _ (PPCDerivable.mul y _ d ih hc' hd) (fun x => ⟨0, ?_⟩)
    simp only [Int.mul_zero]
    rw [Int.mul_left_comm]; omega
  | congr f g _ hfg ih =>
    refine PPCDerivable.congr _ _ ih (fun x => ?_)
    obtain ⟨t, ht⟩ := hfg x
    exact ⟨t, by rw [← Int.mul_sub, ht]; push_cast; rw [Int.mul_comm (a : Int) (b : Int), Int.mul_assoc]⟩

/-- **CRT for polynomial calculus.** For coprime `a, b` and every axiom list `A` and degree `D`:
a degree-`D` `PPCRefutation` mod `a * b` exists iff one exists mod `a` and one mod `b`. -/
theorem crt {a b D : Nat} (A : List (Poly Nat)) (hab : ∃ x y : Int, x * a + y * b = 1) :
    PPCRefutation (a * b) A D ↔ PPCRefutation a A D ∧ PPCRefutation b A D := by
  constructor
  · intro h
    exact ⟨refutation_down (Nat.dvd_mul_right a b) h, refutation_down (Nat.dvd_mul_left b a) h⟩
  · rintro ⟨ha, hb⟩
    obtain ⟨x, y, hxy⟩ := hab
    have h1 : PPCDerivable (a * b) A D (fun _ => (b : Int) * 1) := scale ha
    have h2 : PPCDerivable (b * a) A D (fun _ => (a : Int) * 1) := scale hb
    rw [Nat.mul_comm b a] at h2
    refine PPCDerivable.congr _ _ (PPCDerivable.lin _ _ y x h1 h2) (fun _ => ⟨0, ?_⟩)
    simp only [Int.mul_one, Int.mul_zero]
    have e1 : y * (b : Int) = (b : Int) * y := Int.mul_comm _ _
    have e2 : x * (a : Int) = (a : Int) * x := Int.mul_comm _ _
    omega

end Programme.«20261027-0607-proof-complexity».CRT

#print axioms Programme.«20261027-0607-proof-complexity».CRT.crt
#print axioms Programme.«20261027-0607-proof-complexity».CRT.refutation_down
