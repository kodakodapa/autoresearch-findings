import Programme.«20261025-0459-proof-complexity».MatchQuot
import Programme.«20261025-0459-proof-complexity».OntoLucas

/-!
# No degree drop: polynomial calculus collapses to Nullstellensatz

`NSIn p A D f`: on every good point (no degree-2 monomial axiom of `A` has both variables true),
`f ≡ ∑_e g_e P_e (mod p)` with `P_e ∈ A` and `deg g_e + deg P_e ≤ D`. This is the degree-`D`
Nullstellensatz span read in the matching quotient; `NSIn p A D (fun _ => 1)` is literally the
body of `Work.OntoNS.NSRefutation p A D`.

`NoDrop p A D`: every member of the degree-`D` NS span that agrees mod `p` on the whole cube with a
polynomial of degree `≤ D - 1` already lies in the degree-`(D-1)` NS span.

`pc_in_ns`: under `NoDrop p A D`, every line of a degree-`D` `PPCDerivable` derivation lies in the
degree-`D` NS span (the multiplication rule only multiplies lines of cube degree `≤ D - 1`).
`pc_ns`: so a degree-`D` PC refutation gives a degree-`D` NS refutation; equivalently, a degree-`D`
NS design together with `NoDrop` excludes degree-`D` PC refutations.
-/

namespace Programme.«20261025-1627-proof-complexity».NoDrop

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».MatchQuot

/-- The degree-`D` NS span at the good points, as a predicate on lines. -/
def NSIn (p : Nat) (A : List (Poly Nat)) (D : Nat) (f : (Nat → Bool) → Int) : Prop :=
  ∃ L : List (Poly Nat × Poly Nat), (∀ e ∈ L, e.2 ∈ A ∧ e.1.deg + e.2.deg ≤ D) ∧
    ∀ a, Good A a → (p : Int) ∣ (L.map fun e => e.1.eval a * e.2.eval a).sum - f a

/-- No degree drop at level `D`. -/
def NoDrop (p : Nat) (A : List (Poly Nat)) (D : Nat) : Prop :=
  ∀ f, NSIn p A D f → CubeDeg p f (D - 1) → NSIn p A (D - 1) f

/-- `u · Q`. -/
def smul (u : Int) (Q : Poly Nat) : Poly Nat := ⟨Q.terms.map fun t => (u * t.1, t.2)⟩

/-- `x · Q`. -/
def xmul (x : Nat) (Q : Poly Nat) : Poly Nat := ⟨Q.terms.map fun t => (t.1, x :: t.2)⟩

theorem smul_eval (u : Int) (Q : Poly Nat) (a : Nat → Bool) : (smul u Q).eval a = u * Q.eval a := by
  simp only [smul, Poly.eval, List.map_map]
  generalize Q.terms = T
  induction T with
  | nil => simp
  | cons t T ih => simp only [List.map_cons, List.sum_cons, Function.comp, ih, Int.mul_add, Int.mul_assoc]

theorem monoEval_cons (x : Nat) (m : List Nat) (a : Nat → Bool) :
    monoEval a (x :: m) = xv x a * monoEval a m := by
  simp only [monoEval, List.map_cons, List.prod_cons, xv]

theorem xmul_eval (x : Nat) (Q : Poly Nat) (a : Nat → Bool) : (xmul x Q).eval a = xv x a * Q.eval a := by
  simp only [xmul, Poly.eval, List.map_map]
  generalize Q.terms = T
  induction T with
  | nil => simp
  | cons t T ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, Int.mul_add]
    simp only [Function.comp, monoEval_cons, Int.mul_left_comm]

theorem smul_deg (u : Int) (Q : Poly Nat) : (smul u Q).deg ≤ Q.deg := by
  rw [deg_le_iff]
  intro t ht
  simp only [smul, List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact (deg_le_iff Q Q.deg).mp (Nat.le_refl _) s hs

theorem xmul_deg (x : Nat) (Q : Poly Nat) : (xmul x Q).deg ≤ Q.deg + 1 := by
  rw [deg_le_iff]
  intro t ht
  simp only [xmul, List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  have := (deg_le_iff Q Q.deg).mp (Nat.le_refl _) s hs
  simp only [List.length_cons]; omega

/-- The constant polynomial `1`. -/
def one : Poly Nat := ⟨[(1, [])]⟩

theorem one_eval (a : Nat → Bool) : one.eval a = 1 := by simp [one, Poly.eval, monoEval]

theorem one_deg : one.deg = 0 := rfl

theorem sum_smul (u : Int) (L : List (Poly Nat × Poly Nat)) (a : Nat → Bool) :
    ((L.map fun e => (smul u e.1, e.2)).map fun e => e.1.eval a * e.2.eval a).sum
      = u * (L.map fun e => e.1.eval a * e.2.eval a).sum := by
  induction L with
  | nil => simp
  | cons e L ih =>
    simp only [List.map_cons, List.sum_cons, ih, smul_eval, Int.mul_add, Int.mul_assoc]

theorem sum_xmul (x : Nat) (L : List (Poly Nat × Poly Nat)) (a : Nat → Bool) :
    ((L.map fun e => (xmul x e.1, e.2)).map fun e => e.1.eval a * e.2.eval a).sum
      = xv x a * (L.map fun e => e.1.eval a * e.2.eval a).sum := by
  induction L with
  | nil => simp
  | cons e L ih =>
    simp only [List.map_cons, List.sum_cons, ih, xmul_eval, Int.mul_add, Int.mul_assoc]

theorem nsIn_ax {p D : Nat} {A : List (Poly Nat)} {P : Poly Nat} (hP : P ∈ A) (hd : P.deg ≤ D) :
    NSIn p A D (fun a => P.eval a) :=
  ⟨[(one, P)], fun e he => by
    simp only [List.mem_singleton] at he; subst he; exact ⟨hP, by show one.deg + P.deg ≤ D; rw [one_deg]; omega⟩,
   fun a _ => ⟨0, by simp [one_eval]⟩⟩

theorem nsIn_lin {p D : Nat} {A : List (Poly Nat)} {f g : (Nat → Bool) → Int} (u v : Int)
    (hf : NSIn p A D f) (hg : NSIn p A D g) : NSIn p A D (fun a => u * f a + v * g a) := by
  obtain ⟨L, hL, h⟩ := hf
  obtain ⟨M, hM, h'⟩ := hg
  refine ⟨L.map (fun e => (smul u e.1, e.2)) ++ M.map (fun e => (smul v e.1, e.2)), ?_, ?_⟩
  · intro e he
    simp only [List.mem_append, List.mem_map] at he
    rcases he with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩
    · have := hL d hd; exact ⟨this.1, by have := smul_deg u d.1; dsimp only; omega⟩
    · have := hM d hd; exact ⟨this.1, by have := smul_deg v d.1; dsimp only; omega⟩
  · intro a ha
    rw [List.map_append, List.sum_append, sum_smul, sum_smul]
    obtain ⟨c, hc⟩ := h a ha
    obtain ⟨c', hc'⟩ := h' a ha
    refine ⟨u * c + v * c', ?_⟩
    rw [Int.mul_add, ← Int.mul_assoc, Int.mul_comm (p : Int) u, Int.mul_assoc, ← hc,
      ← Int.mul_assoc, Int.mul_comm (p : Int) v, Int.mul_assoc, ← hc']
    simp only [Int.mul_sub]; omega

theorem nsIn_congr {p D : Nat} {A : List (Poly Nat)} {f g : (Nat → Bool) → Int}
    (hg : NSIn p A D g) (hfg : ∀ a, (p : Int) ∣ f a - g a) : NSIn p A D f := by
  obtain ⟨L, hL, h⟩ := hg
  refine ⟨L, hL, fun a ha => ?_⟩
  have := Int.dvd_sub (h a ha) (hfg a)
  have e : (L.map fun e => e.1.eval a * e.2.eval a).sum - g a - (f a - g a)
      = (L.map fun e => e.1.eval a * e.2.eval a).sum - f a := by omega
  rwa [e] at this

theorem nsIn_xmul {p D : Nat} {A : List (Poly Nat)} {g : (Nat → Bool) → Int} (x : Nat)
    (hg : NSIn p A (D - 1) g) (hD : 1 ≤ D) : NSIn p A D (fun a => xv x a * g a) := by
  obtain ⟨L, hL, h⟩ := hg
  refine ⟨L.map (fun e => (xmul x e.1, e.2)), ?_, fun a ha => ?_⟩
  · intro e he
    simp only [List.mem_map] at he
    obtain ⟨d, hd, rfl⟩ := he
    have := hL d hd; exact ⟨this.1, by have := xmul_deg x d.1; dsimp only; omega⟩
  · rw [sum_xmul]
    obtain ⟨c, hc⟩ := h a ha
    exact ⟨xv x a * c, by rw [← Int.mul_sub, hc, Int.mul_left_comm]⟩

/-- Every line of a degree-`D` PC derivation from `A` lies in the degree-`D` NS span, provided
there is no degree drop at level `D`. -/
theorem pc_in_ns {p D : Nat} {A : List (Poly Nat)} (hND : NoDrop p A D) {g : (Nat → Bool) → Int}
    (h : PPCDerivable p A D g) : NSIn p A D g := by
  induction h with
  | ax P hP hd => exact nsIn_ax hP hd
  | lin f g u v _ _ ihf ihg => exact nsIn_lin u v ihf ihg
  | mul x g d _ hcd hdD ih =>
    exact nsIn_xmul x (hND g ih (Programme.«20261025-0459-proof-complexity».OntoLucas.cd_mono
      (by omega) hcd)) (by omega)
  | congr f g _ hfg ih => exact nsIn_congr ih hfg

/-- Under `NoDrop`, a degree-`D` PC refutation is a degree-`D` NS refutation (the right-hand side is
the body of `Work.OntoNS.NSRefutation p A D`). -/
theorem pc_ns {p D : Nat} {A : List (Poly Nat)} (hND : NoDrop p A D) (h : PPCRefutation p A D) :
    ∃ L : List (Poly Nat × Poly Nat), (∀ e ∈ L, e.2 ∈ A ∧ e.1.deg + e.2.deg ≤ D) ∧
      ∀ a, Good A a → (p : Int) ∣ (L.map fun e => e.1.eval a * e.2.eval a).sum - 1 :=
  pc_in_ns hND h

end Programme.«20261025-1627-proof-complexity».NoDrop

#print axioms Programme.«20261025-1627-proof-complexity».NoDrop.pc_in_ns
#print axioms Programme.«20261025-1627-proof-complexity».NoDrop.pc_ns
