import Programme.«20261024-1633-proof-complexity».PCTseitin
import Programme.«20261024-1633-proof-complexity».NSSeparation

/-!
# Polynomial calculus separations: `F_2` versus odd characteristic for library Tseitin families

* `ns_to_pc`: a degree-`D` Nullstellensatz refutation (`Work.NS.NSRefutation p F D`, `p > 1`)
  gives a degree-`D` polynomial calculus refutation (`Work.PCTseitin.PCRefutation p F D`): each
  term `κ · x_m · f_C` is built by multiplying `f_C` by the variables of `m` one at a time.
* `hc_pc_sep`: the cube-connected-cycles Tseitin formula `HC k` (`k ≥ 2`) has a degree-3 PC
  refutation over `F_2`, and for odd `p > 1` none of degree `D` with `2D < ⌊⌊2^k/3⌋/(k+1)⌋`.
* `hq_pc_sep`: the hypercube Tseitin formula `HQ k` (`k ≥ 2`) has a degree-`k` PC refutation over
  `F_2`, and for odd `p > 1` none of degree `D` with `2D < ⌊2^k/3⌋`.
-/

namespace Programme.«20261024-1633-proof-complexity».PCSeparation

open Programme.«20261024-1633-proof-complexity».NS Programme.«20261024-1633-proof-complexity».NSTseitin Programme.«20261024-1633-proof-complexity».PCTseitin Programme.«20261024-1110-proof-complexity».Haken
open Programme.«20261024-1110-proof-complexity».Tseitin
open Programme.«20261024-1110-proof-complexity».Hypercube
open Programme.«20261024-1110-proof-complexity».CCC

/-! ## Nullstellensatz refutations are polynomial calculus refutations -/

/-- `x_m · f_C` as a polynomial. -/
def monoPoly (m : List Nat) (C : Clause Nat) : Poly Nat :=
  m.foldr (fun x P => P.mulVar x) (clausePoly C)

theorem monoEval_cons (a : Nat → Bool) (x : Nat) (m : List Nat) :
    monoEval a (x :: m) = xv x a * monoEval a m := by
  simp [monoEval, xv]

theorem monoPoly_eval (a : Nat → Bool) (m : List Nat) (C : Clause Nat) :
    (monoPoly m C).eval a = monoEval a m * (clausePoly C).eval a := by
  induction m with
  | nil => simp [monoPoly, monoEval]
  | cons x m ih =>
    simp only [monoPoly, List.foldr_cons] at ih ⊢
    rw [eval_mulVar, ih, monoEval_cons, Int.mul_assoc]; rfl

theorem monoPoly_deg (m : List Nat) (C : Clause Nat) :
    (monoPoly m C).deg ≤ m.length + C.length := by
  induction m with
  | nil => simpa [monoPoly] using clausePoly_deg C
  | cons x m ih =>
    simp only [monoPoly, List.foldr_cons] at ih ⊢
    have := deg_mulVar x (m.foldr (fun x P => P.mulVar x) (clausePoly C))
    simp only [List.length_cons]; omega

section
variable {p : Nat} {F : CNF Nat} {D : Nat}

theorem der_eq {f g : (Nat → Bool) → Int} (hg : PCDerivable p F D g) (h : ∀ a, f a = g a) :
    PCDerivable p F D f :=
  PCDerivable.congr f g hg (fun a => by rw [h a, Int.sub_self]; exact ⟨0, by simp⟩)

theorem der_mono {C : Clause Nat} (hC : C ∈ F) (m : List Nat) (hD : m.length + C.length ≤ D) :
    PCDerivable p F D (fun a => monoEval a m * (clausePoly C).eval a) := by
  induction m with
  | nil =>
    exact der_eq (PCDerivable.ax C hC (by simp at hD; omega)) (fun a => by simp [monoEval])
  | cons x m ih =>
    simp only [List.length_cons] at hD
    have h := PCDerivable.mul x _ (m.length + C.length) (ih (by omega))
      ⟨monoPoly m C, monoPoly_deg m C, fun a => by rw [monoPoly_eval, Int.sub_self]; exact ⟨0, by simp⟩⟩
      (by omega)
    exact der_eq h (fun a => by rw [monoEval_cons, Int.mul_assoc])

theorem der_scale {f : (Nat → Bool) → Int} (k : Int) (hf : PCDerivable p F D f) :
    PCDerivable p F D (fun a => k * f a) :=
  der_eq (PCDerivable.lin f f k 0 hf hf) (fun a => by simp)

theorem der_add {f g : (Nat → Bool) → Int} (hf : PCDerivable p F D f) (hg : PCDerivable p F D g) :
    PCDerivable p F D (fun a => f a + g a) :=
  der_eq (PCDerivable.lin f g 1 1 hf hg) (fun a => by simp)

theorem der_sum {α} {z : (Nat → Bool) → Int} (hz : PCDerivable p F D z) (l : List α)
    (h : α → (Nat → Bool) → Int) (hh : ∀ i ∈ l, PCDerivable p F D (h i)) :
    PCDerivable p F D (fun a => (l.map fun i => h i a).sum) := by
  induction l with
  | nil => exact der_eq (der_scale 0 hz) (fun a => by simp)
  | cons x l ih =>
    have h1 := der_add (hh x List.mem_cons_self) (ih (fun i hi => hh i (List.mem_cons_of_mem _ hi)))
    exact der_eq h1 (fun a => by simp)

end

/-- A degree-`D` Nullstellensatz refutation over `Z/p` (`p > 1`) is a degree-`D` PC refutation. -/
theorem ns_to_pc (p : Nat) (hp : 1 < p) {F : CNF Nat} {D : Nat} (π : NSRefutation p F D) :
    PCRefutation p F D := by
  -- some line is derivable
  have hz : ∃ z, PCDerivable p F D z := by
    cases hF : F with
    | nil =>
      have := π.identity (fun _ => false)
      simp only [hF, List.length_nil, List.range_zero, List.map_nil, List.sum_nil] at this
      have h1 : (1 : Int) % (p : Int) = 1 := Int.emod_eq_of_lt (by omega) (by omega)
      rw [h1] at this; simp at this
    | cons C F' =>
      have := π.deg_le 0 (by simp [hF])
      simp only [hF] at this
      exact ⟨_, PCDerivable.ax C (by simp) (by simp at this; omega)⟩
  obtain ⟨z, hz⟩ := hz
  have hsum := der_sum hz (List.range F.length)
    (fun i a => (π.g i).eval a * (clausePoly (F.getD i [])).eval a) (by
      intro i hi
      have hi' := List.mem_range.mp hi
      have hget : F.getD i [] = F[i] := by simp [List.getD, List.getElem?_eq_getElem hi']
      rw [hget]
      have hdeg := π.deg_le i hi'
      have e : (fun a => (π.g i).eval a * (clausePoly F[i]).eval a)
          = fun a => ((π.g i).terms.map fun t => t.1 * (monoEval a t.2 * (clausePoly F[i]).eval a)).sum := by
        funext a; unfold Poly.eval; rw [sum_mul_right]
        congr 1; apply List.map_congr_left; intro t _; rw [Int.mul_assoc]
      rw [e]
      apply der_sum hz
      intro t ht
      have := (deg_le_iff (π.g i) (π.g i).deg).mp (Nat.le_refl _) t ht
      exact der_scale t.1 (der_mono (List.getElem_mem hi') t.2 (by omega)))
  apply PCDerivable.congr _ _ hsum
  intro a
  have h1 := π.identity a
  have h2 := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h1
  have h3 := Int.dvd_of_emod_eq_zero h2
  have h4 := Int.dvd_neg.mpr h3
  rwa [Int.neg_sub] at h4

/-! ## The separations -/

theorem hc_pc_sep (k : Nat) (hk : 2 ≤ k) :
    PCRefutation 2 (HC k) 3 ∧
    ∀ p D : Nat, p % 2 = 1 → 1 < p → 2 * D < 2 ^ k / 3 / (k + 1) → ¬ PCRefutation p (HC k) D := by
  refine ⟨(Programme.«20261024-1633-proof-complexity».NSFamilies.hc_ns2 k hk).elim (ns_to_pc 2 (by omega)), fun p D hp hp1 hD π => ?_⟩
  exact tseitin_pc_lower (by have := Nat.mul_le_mul (three_le k hk) hk; omega)
    (CC_ends k hk) (hconn' k (by omega)) (hexp' k (by omega)) p hp hp1 hD π

theorem hq_pc_sep (k : Nat) (hk : 2 ≤ k) :
    PCRefutation 2 (HQ k) k ∧
    ∀ p D : Nat, p % 2 = 1 → 1 < p → 2 * D < 2 ^ k / 3 → ¬ PCRefutation p (HQ k) D := by
  refine ⟨(Programme.«20261024-1633-proof-complexity».NSFamilies.hq_ns2 k).elim (ns_to_pc 2 (by omega)), fun p D hp hp1 hD π => ?_⟩
  exact tseitin_pc_lower (three_le k hk)
    (fun p hp => ⟨Nat.lt_trans (Q_ends k p hp).1 (Q_ends k p hp).2, (Q_ends k p hp).2,
      Nat.ne_of_lt (Q_ends k p hp).1⟩)
    (hconn k) (hexp k) p hp hp1 hD π

end Programme.«20261024-1633-proof-complexity».PCSeparation

#print axioms Programme.«20261024-1633-proof-complexity».PCSeparation.ns_to_pc
#print axioms Programme.«20261024-1633-proof-complexity».PCSeparation.hc_pc_sep
#print axioms Programme.«20261024-1633-proof-complexity».PCSeparation.hq_pc_sep
