import Programme.«20261025-0459-proof-complexity».OntoFPHP

/-!
# Audit: standard (syntactic) polynomial calculus over `F_p` maps into `PPCDerivable`

`Der p A D P`: the polynomial `P` (integer coefficients read mod `p`, i.e. a polynomial over
`F_p`, NOT reduced by `x² = x`) is a line of a standard degree-`D` polynomial calculus derivation
from the axioms `A` together with the Boolean axioms `x² - x`. Rules:
* `ax`: an axiom `P ∈ A` of degree `≤ D`;
* `bool`: the Boolean axiom `x·x - x` (degree 2, so only when `2 ≤ D`);
* `lin`: `u P + v Q` for derived `P, Q` (term lists concatenated, coefficients scaled);
* `mul`: `x · P` for derived `P` of degree `≤ D - 1`;
* `eq`: replace a derived `P` by any `Q` of degree `≤ D` that is equal to `P` in `F_p[x]`:
  for every monomial `m` (a multiset of variables, given as a list up to reordering) the
  coefficients of `m` in `P` and `Q` agree mod `p` (`PEq`).
Every line has syntactic degree `≤ D`. `Refutes p A D`: the polynomial `1` is derivable.

`refutes_ppc`: for `p > 1`, every `Refutes p A D` gives `PPCRefutation p A D` (each line is sent to
its value function on the Boolean cube). So every library lower bound `¬ PPCRefutation p A D`
is a lower bound for standard polynomial calculus over `F_p` with Boolean axioms.
-/

namespace Programme.«20261029-1156-proof-complexity».StdPC

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».OntoFPHP

/-- Coefficient of the monomial `m` (up to reordering of its variables) in a term list. -/
def cf (L : List (Int × List Nat)) (m : List Nat) : Int :=
  ((L.filter fun t => decide (t.2.Perm m)).map (·.1)).sum

/-- Coefficient of the monomial `m` in `P`. -/
def coeff (P : Poly Nat) (m : List Nat) : Int := cf P.terms m

/-- `P = Q` in `F_p[x]` (coefficientwise mod `p`; no Boolean reduction). -/
def PEq (p : Nat) (P Q : Poly Nat) : Prop := ∀ m, (p : Int) ∣ coeff P m - coeff Q m

/-- The Boolean axiom `x·x - x`. -/
def boolAx (x : Nat) : Poly Nat := ⟨[(1, [x, x]), (-1, [x])]⟩

/-- `u P + v Q`. -/
def lc (u v : Int) (P Q : Poly Nat) : Poly Nat :=
  ⟨P.terms.map (fun t => (u * t.1, t.2)) ++ Q.terms.map (fun t => (v * t.1, t.2))⟩

/-- Lines of a standard degree-`D` polynomial calculus derivation over `F_p` from `A` and the
Boolean axioms. -/
inductive Der (p : Nat) (A : List (Poly Nat)) (D : Nat) : Poly Nat → Prop
  | ax (P : Poly Nat) : P ∈ A → P.deg ≤ D → Der p A D P
  | bool (x : Nat) : 2 ≤ D → Der p A D (boolAx x)
  | lin (u v : Int) (P Q : Poly Nat) : Der p A D P → Der p A D Q → Der p A D (lc u v P Q)
  | mul (x : Nat) (P : Poly Nat) : Der p A D P → P.deg + 1 ≤ D → Der p A D (P.mulVar x)
  | eq (P Q : Poly Nat) : Der p A D P → PEq p P Q → Q.deg ≤ D → Der p A D Q

/-- A standard degree-`D` refutation over `F_p`: the polynomial `1` is derivable. -/
def Refutes (p : Nat) (A : List (Poly Nat)) (D : Nat) : Prop := Der p A D Poly.one

/-! ## Evaluation respects equality in `F_p[x]` -/

/-- Value of a term list at a Boolean point. -/
def ev (a : Nat → Bool) (L : List (Int × List Nat)) : Int := (L.map fun t => t.1 * monoEval a t.2).sum

theorem monoEval_perm (a : Nat → Bool) {m m' : List Nat} (h : m.Perm m') :
    monoEval a m = monoEval a m' := by
  unfold monoEval
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.map_cons, List.prod_cons, ih]
  | swap x y l => simp only [List.map_cons, List.prod_cons]; exact Int.mul_left_comm _ _ _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem ev_cons (a : Nat → Bool) (t : Int × List Nat) (L : List (Int × List Nat)) :
    ev a (t :: L) = t.1 * monoEval a t.2 + ev a L := by simp [ev]

theorem ev_append (a : Nat → Bool) (L M : List (Int × List Nat)) : ev a (L ++ M) = ev a L + ev a M := by
  simp [ev]

theorem cf_append (L M : List (Int × List Nat)) (m : List Nat) : cf (L ++ M) m = cf L m + cf M m := by
  simp [cf]

/-- Split a term list by a predicate. -/
theorem ev_split (a : Nat → Bool) (q : Int × List Nat → Bool) :
    ∀ L : List (Int × List Nat), ev a L = ev a (L.filter q) + ev a (L.filter fun t => !q t)
  | [] => by simp [ev]
  | t :: L => by
    have ih := ev_split a q L
    cases h : q t <;> simp [List.filter_cons, h, ev_cons, ih] <;> omega

/-- All monomials of `S` are reorderings of `m`: the value is (sum of coefficients)·`m(a)`. -/
theorem ev_same (a : Nat → Bool) (m : List Nat) :
    ∀ S : List (Int × List Nat), (∀ t ∈ S, t.2.Perm m) →
      ev a S = (S.map (·.1)).sum * monoEval a m
  | [] => by simp [ev]
  | t :: S => by
    intro h
    rw [ev_cons, ev_same a m S (fun t ht => h t (List.mem_cons_of_mem _ ht)),
      monoEval_perm a (h t List.mem_cons_self)]
    simp only [List.map_cons, List.sum_cons, Int.add_mul]

theorem cf_filter_not (L : List (Int × List Nat)) (m m' : List Nat) :
    cf (L.filter fun t => !decide (t.2.Perm m)) m' =
      ((L.filter fun t => decide (t.2.Perm m') && !decide (t.2.Perm m)).map (·.1)).sum := by
  unfold cf; rw [List.filter_filter]

theorem ev_dvd (p : Int) (a : Nat → Bool) :
    ∀ (N : Nat) (L : List (Int × List Nat)), L.length ≤ N → (∀ m, p ∣ cf L m) → p ∣ ev a L
  | 0, L, hl, _ => by
    have : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [ev]
  | N + 1, [], _, _ => by simp [ev]
  | N + 1, t :: L, hl, hc => by
    let m := t.2
    rw [ev_split a (fun s => decide (s.2.Perm m))]
    apply Int.dvd_add
    · rw [ev_same a m _ (fun s hs => by simpa using (List.mem_filter.mp hs).2)]
      exact Int.dvd_trans (hc m) (Int.dvd_mul_right _ _)
    · apply ev_dvd p a N
      · have : ((t :: L).filter fun s => !decide (s.2.Perm m)) = L.filter fun s => !decide (s.2.Perm m) := by
          simp [List.filter_cons, m, List.Perm.refl]
        rw [this]
        exact Nat.le_trans (List.length_filter_le _ _) (by simp at hl; omega)
      · intro m'
        rw [cf_filter_not]
        by_cases hm : m'.Perm m
        · have : ((t :: L).filter fun s => decide (s.2.Perm m') && !decide (s.2.Perm m)) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro s _
            by_cases h1 : s.2.Perm m'
            · simp [h1, h1.trans hm]
            · simp [h1]
          rw [this]; simp
        · have : ((t :: L).filter fun s => decide (s.2.Perm m') && !decide (s.2.Perm m)) =
              (t :: L).filter fun s => decide (s.2.Perm m') := by
            apply List.filter_congr
            intro s _
            by_cases h1 : s.2.Perm m'
            · have : ¬ s.2.Perm m := fun h2 => hm (h1.symm.trans h2)
              simp [h1, this]
            · simp [h1]
          rw [this]; exact hc m'

/-- Negated term list. -/
def negT (L : List (Int × List Nat)) : List (Int × List Nat) := L.map fun t => (-t.1, t.2)

theorem ev_negT (a : Nat → Bool) (L : List (Int × List Nat)) : ev a (negT L) = - ev a L := by
  induction L with
  | nil => simp [ev, negT]
  | cons t L ih =>
    have : ev a (negT (t :: L)) = -t.1 * monoEval a t.2 + ev a (negT L) := by simp [ev, negT]
    rw [this, ih, ev_cons, Int.neg_mul]; omega

theorem cf_negT (L : List (Int × List Nat)) (m : List Nat) : cf (negT L) m = - cf L m := by
  induction L with
  | nil => simp [cf, negT]
  | cons t L ih =>
    have e1 : cf (negT (t :: L)) m = (if t.2.Perm m then -t.1 else 0) + cf (negT L) m := by
      by_cases h : t.2.Perm m <;> simp [cf, negT, List.filter_cons, h]
    have e2 : cf (t :: L) m = (if t.2.Perm m then t.1 else 0) + cf L m := by
      by_cases h : t.2.Perm m <;> simp [cf, List.filter_cons, h]
    rw [e1, e2, ih]; split <;> omega

theorem eval_ev (a : Nat → Bool) (P : Poly Nat) : P.eval a = ev a P.terms := rfl

/-- Equal polynomials in `F_p[x]` have values congruent mod `p` at every Boolean point. -/
theorem peq_eval {p : Nat} {P Q : Poly Nat} (h : PEq p P Q) (a : Nat → Bool) :
    (p : Int) ∣ Q.eval a - P.eval a := by
  have := ev_dvd (p : Int) a _ (Q.terms ++ negT P.terms) (Nat.le_refl _) (fun m => by
    rw [cf_append, cf_negT]
    have := h m; unfold coeff at this
    have h2 := Int.dvd_neg.mpr this
    rw [show -(cf P.terms m - cf Q.terms m) = cf Q.terms m + -cf P.terms m by omega] at h2
    exact h2)
  rw [ev_append, ev_negT, ← eval_ev, ← eval_ev] at this
  rw [Int.sub_eq_add_neg]; exact this

/-! ## Values of the rules -/

theorem eval_lc (a : Nat → Bool) (u v : Int) (P Q : Poly Nat) :
    (lc u v P Q).eval a = u * P.eval a + v * Q.eval a := by
  have hs : ∀ (w : Int) (L : List (Int × List Nat)),
      ev a (L.map fun t => (w * t.1, t.2)) = w * ev a L := by
    intro w L
    induction L with
    | nil => simp [ev]
    | cons t L ih =>
      have : ev a ((t :: L).map fun t => (w * t.1, t.2)) =
          w * t.1 * monoEval a t.2 + ev a (L.map fun t => (w * t.1, t.2)) := by simp [ev]
      rw [this, ih, ev_cons, Int.mul_add, Int.mul_assoc]
  rw [eval_ev, eval_ev, eval_ev]
  simp only [lc]; rw [ev_append, hs, hs]

theorem eval_boolAx (a : Nat → Bool) (x : Nat) : (boolAx x).eval a = 0 := by
  simp only [boolAx, Poly.eval, monoEval]
  cases h : a x <;> simp [h]

/-! ## Translation -/

/-- Every standard line, read as a function on the Boolean cube, is either `≡ 0` mod `p`
(e.g. a Boolean axiom) or a `PPCDerivable` line. -/
theorem der_sem {p D : Nat} {A : List (Poly Nat)} {P : Poly Nat} (h : Der p A D P) :
    (∀ a, (p : Int) ∣ P.eval a) ∨ PPCDerivable p A D (fun a => P.eval a) := by
  induction h with
  | ax P hP hd => exact Or.inr (PPCDerivable.ax P hP hd)
  | bool x _ => exact Or.inl (fun a => by rw [eval_boolAx]; exact Int.dvd_zero _)
  | lin u v P Q _ _ ihP ihQ =>
    rcases ihP with hP | hP <;> rcases ihQ with hQ | hQ
    · exact Or.inl (fun a => by rw [eval_lc]; exact Int.dvd_add (dvd_mul_of u (hP a)) (dvd_mul_of v (hQ a)))
    · refine Or.inr (PPCDerivable.congr _ _ (PPCDerivable.lin _ _ 0 v hQ hQ) (fun a => ?_))
      rw [eval_lc]
      have : u * P.eval a + v * Q.eval a - (0 * Q.eval a + v * Q.eval a) = u * P.eval a := by
        rw [Int.zero_mul]; omega
      rw [this]; exact dvd_mul_of u (hP a)
    · refine Or.inr (PPCDerivable.congr _ _ (PPCDerivable.lin _ _ u 0 hP hP) (fun a => ?_))
      rw [eval_lc]
      have : u * P.eval a + v * Q.eval a - (u * P.eval a + 0 * P.eval a) = v * Q.eval a := by
        rw [Int.zero_mul]; omega
      rw [this]; exact dvd_mul_of v (hQ a)
    · refine Or.inr (PPCDerivable.congr _ _ (PPCDerivable.lin _ _ u v hP hQ) (fun a => ?_))
      rw [eval_lc, Int.sub_self]; exact Int.dvd_zero _
  | mul x P _ hd ih =>
    rcases ih with hP | hP
    · exact Or.inl (fun a => by rw [eval_mulVar]; exact dvd_mul_of _ (hP a))
    · have hc : CubeDeg p (fun a => P.eval a) P.deg :=
        ⟨P, Nat.le_refl _, fun a => by rw [Int.sub_self]; exact Int.dvd_zero _⟩
      refine Or.inr (PPCDerivable.congr _ _ (PPCDerivable.mul x _ P.deg hP hc hd) (fun a => ?_))
      rw [eval_mulVar]
      have : (if a x = true then 1 else 0) * P.eval a - xv x a * P.eval a = 0 := by
        unfold xv; rw [Int.sub_self]
      rw [this]; exact Int.dvd_zero _
  | eq P Q _ hPQ _ ih =>
    rcases ih with hP | hP
    · exact Or.inl (fun a => by
        have := Int.dvd_add (peq_eval hPQ a) (hP a)
        rwa [Int.sub_add_cancel] at this)
    · exact Or.inr (PPCDerivable.congr _ _ hP (peq_eval hPQ))

/-- **Audit (a).** For `p > 1`, a standard degree-`D` polynomial calculus refutation of `A` over
`F_p` (with Boolean axioms) gives a library `PPCRefutation p A D`. -/
theorem refutes_ppc {p D : Nat} {A : List (Poly Nat)} (hp : 1 < p) (h : Refutes p A D) :
    PPCRefutation p A D := by
  rcases der_sem h with h1 | h1
  · exfalso
    have := h1 (fun _ => false)
    rw [eval_one] at this
    have := Int.eq_one_of_dvd_one (by omega) this
    omega
  · exact PPCDerivable.congr _ _ h1 (fun a => by rw [eval_one, Int.sub_self]; exact Int.dvd_zero _)

/-- Contrapositive: every library lower bound is a standard PC lower bound. -/
theorem not_refutes {p D : Nat} {A : List (Poly Nat)} (hp : 1 < p) (h : ¬ PPCRefutation p A D) :
    ¬ Refutes p A D := fun hr => h (refutes_ppc hp hr)

end Programme.«20261029-1156-proof-complexity».StdPC

#print axioms Programme.«20261029-1156-proof-complexity».StdPC.refutes_ppc
