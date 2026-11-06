import Programme.«20261025-0459-proof-complexity».OntoFPHP

/-!
# Substitutions in polynomial calculus, and monotonicity of onto-FPHP degree

A substitution `σ : Nat → Lit` sends each variable to a constant or to a variable (not
necessarily injectively). `PPCDerivable.subst`: if every axiom of `A` of degree `≤ D`, pulled back
along `σ`, is derivable from `B` in degree `D`, then so is every line derivable from `A`.

Application `ontoFPHP_restrict`: setting `x_{n+k, n} := 1` (and the rest of its row and column to
`0`) maps a degree-`D` refutation of `onto-FPHP^{n+1+k}_{n+1}` to one of `onto-FPHP^{n+k}_n`.
So for fixed `k` the minimum degree is nondecreasing in `n`.
-/

namespace Programme.«20261025-0459-proof-complexity».OntoSubst

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».OntoFPHP

/-- Image of a variable: a constant or a variable. -/
inductive Lit
  | const (b : Bool)
  | var (y : Nat)

def Lit.val (a : Nat → Bool) : Lit → Bool
  | .const b => b
  | .var y => a y

/-- Coefficient factor of a literal in a monomial (`0` for false). -/
def Lit.coef : Lit → Int
  | .const true => 1
  | .const false => 0
  | .var _ => 1

/-- Variables a literal contributes to a monomial. -/
def Lit.vars : Lit → List Nat
  | .const _ => []
  | .var y => [y]

/-- The assignment pulled back along `σ`. -/
def pull (σ : Nat → Lit) (a : Nat → Bool) : Nat → Bool := fun x => (σ x).val a

def mcoef (σ : Nat → Lit) (m : List Nat) : Int := (m.map fun x => (σ x).coef).prod
def mvars (σ : Nat → Lit) (m : List Nat) : List Nat := m.flatMap fun x => (σ x).vars

def Poly.subst (σ : Nat → Lit) (P : Poly Nat) : Poly Nat :=
  ⟨P.terms.map fun t => (t.1 * mcoef σ t.2, mvars σ t.2)⟩

theorem monoEval_append (a : Nat → Bool) (l₁ l₂ : List Nat) :
    monoEval a (l₁ ++ l₂) = monoEval a l₁ * monoEval a l₂ := by
  simp [monoEval, List.map_append, List.prod_append]

theorem lit_eval (a : Nat → Bool) (L : Lit) :
    L.coef * monoEval a L.vars = if L.val a then 1 else 0 := by
  cases L with
  | const b => cases b <;> simp [Lit.coef, Lit.vars, Lit.val, monoEval]
  | var y => simp [Lit.coef, Lit.vars, Lit.val, monoEval]; rfl

theorem mono_subst (σ : Nat → Lit) (a : Nat → Bool) (m : List Nat) :
    mcoef σ m * monoEval a (mvars σ m) = monoEval (pull σ a) m := by
  induction m with
  | nil => simp [mcoef, mvars, monoEval]
  | cons x m ih =>
    have h1 : mcoef σ (x :: m) = (σ x).coef * mcoef σ m := by simp [mcoef]
    have h2 : mvars σ (x :: m) = (σ x).vars ++ mvars σ m := by simp [mvars]
    have h3 : monoEval (pull σ a) (x :: m) = (if (σ x).val a then 1 else 0) * monoEval (pull σ a) m := by
      simp [monoEval, pull]; rfl
    rw [h1, h2, h3, monoEval_append, ← ih, ← lit_eval a (σ x)]
    simp only [Int.mul_assoc, Int.mul_left_comm]

theorem subst_eval (σ : Nat → Lit) (P : Poly Nat) (a : Nat → Bool) :
    (Poly.subst σ P).eval a = P.eval (pull σ a) := by
  obtain ⟨ts⟩ := P
  simp only [Poly.subst, Poly.eval]
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Int.mul_assoc, mono_subst]

theorem mvars_len (σ : Nat → Lit) (m : List Nat) : (mvars σ m).length ≤ m.length := by
  induction m with
  | nil => simp [mvars]
  | cons x m ih =>
    have h2 : mvars σ (x :: m) = (σ x).vars ++ mvars σ m := by simp [mvars]
    have : (σ x).vars.length ≤ 1 := by cases σ x <;> simp [Lit.vars]
    rw [h2, List.length_append, List.length_cons]; omega

theorem subst_deg (σ : Nat → Lit) (P : Poly Nat) : (Poly.subst σ P).deg ≤ P.deg := by
  obtain ⟨ts⟩ := P
  simp only [Poly.subst, Poly.deg]
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.foldr_cons] at ih ⊢
    have := mvars_len σ t.2
    exact Nat.max_le.mpr ⟨Nat.le_trans this (Nat.le_max_left _ _),
      Nat.le_trans ih (Nat.le_max_right _ _)⟩

theorem cubeDeg_pull {p d : Nat} (σ : Nat → Lit) {g : (Nat → Bool) → Int} (h : CubeDeg p g d) :
    CubeDeg p (fun a => g (pull σ a)) d := by
  obtain ⟨Q, hQ, hg⟩ := h
  exact ⟨Poly.subst σ Q, Nat.le_trans (subst_deg σ Q) hQ, fun a => by rw [subst_eval]; exact hg _⟩

/-- Transport of derivations along a substitution. -/
theorem PPCDerivable.subst {p D : Nat} {A B : List (Poly Nat)} (σ : Nat → Lit)
    (hz : PPCDerivable p B D (fun _ => 0))
    (hA : ∀ P ∈ A, P.deg ≤ D → PPCDerivable p B D (fun a => P.eval (pull σ a)))
    {g : (Nat → Bool) → Int} (h : PPCDerivable p A D g) :
    PPCDerivable p B D (fun a => g (pull σ a)) := by
  induction h with
  | ax P hP hd => exact hA P hP hd
  | lin f g u v _ _ ihf ihg => exact PPCDerivable.lin _ _ u v ihf ihg
  | congr f g _ hfg ih => exact PPCDerivable.congr _ _ ih (fun a => hfg _)
  | mul x g d _ hc hd ih =>
    have hc' := cubeDeg_pull σ hc
    cases hx : σ x with
    | const b =>
      cases b with
      | true =>
        refine PPCDerivable.congr _ _ ih (fun a => ⟨0, ?_⟩)
        simp [xv, pull, hx, Lit.val]
      | false =>
        refine PPCDerivable.congr _ _ hz (fun a => ⟨0, ?_⟩)
        simp [xv, pull, hx, Lit.val]
    | var y =>
      refine PPCDerivable.congr _ _ (PPCDerivable.mul y _ d ih hc' hd) (fun a => ⟨0, ?_⟩)
      simp [xv, pull, hx, Lit.val]


/-! ## Helpers for onto-FPHP -/

theorem of_eq {p D : Nat} {B : List (Poly Nat)} {f g : (Nat → Bool) → Int}
    (hg : PPCDerivable p B D g) (h : ∀ a, f a = g a) : PPCDerivable p B D f :=
  PPCDerivable.congr _ _ hg (fun a => ⟨0, by rw [h a]; simp⟩)

theorem rsum_congr (m : Nat) (f g : Nat → Int) (h : ∀ t < m, f t = g t) : rsum m f = rsum m g := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [rsum]; rw [ih (fun t ht => h t (by omega)), h m (by omega)]

theorem rsum_zero (m : Nat) (f : Nat → Int) (h : ∀ t < m, f t = 0) : rsum m f = 0 := by
  rw [rsum_congr m f (fun _ => 0) h]
  induction m with
  | zero => rfl
  | succ m ih => simp only [rsum]; rw [ih (fun t ht => h t (by omega))]; rfl

theorem prod2_eval (u w : Nat) (b : Nat → Bool) : (prod2 u w).eval b = xv u b * xv w b := by
  simp [prod2, Poly.eval, monoEval, xv]

theorem prod2_deg (u w : Nat) : (prod2 u w).deg = 2 := rfl

theorem mem_collAx {n k : Nat} {P : Poly Nat} : P ∈ collAx n k ↔
    ∃ j i i', j < n ∧ i < n + k ∧ i' < n + k ∧ i < i' ∧ prod2 (var n i j) (var n i' j) = P := by
  simp only [collAx, List.mem_flatMap, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨j, hj, i, hi, i', hi', h⟩
    by_cases hii : i < i'
    · rw [if_pos hii] at h; exact ⟨j, i, i', hj, hi, hi', hii, Option.some.inj h⟩
    · rw [if_neg hii] at h; cases h
  · rintro ⟨j, i, i', hj, hi, hi', hii, rfl⟩
    exact ⟨j, hj, i, hi, i', hi', by rw [if_pos hii]⟩

theorem mem_funcAx {n k : Nat} {P : Poly Nat} : P ∈ funcAx n k ↔
    ∃ i j j', i < n + k ∧ j < n ∧ j' < n ∧ j < j' ∧ prod2 (var n i j) (var n i j') = P := by
  simp only [funcAx, List.mem_flatMap, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, j, hj, j', hj', h⟩
    by_cases hjj : j < j'
    · rw [if_pos hjj] at h; exact ⟨i, j, j', hi, hj, hj', hjj, Option.some.inj h⟩
    · rw [if_neg hjj] at h; cases h
  · rintro ⟨i, j, j', hi, hj, hj', hjj, rfl⟩
    exact ⟨i, hi, j, hj, j', hj', by rw [if_pos hjj]⟩

theorem mem_pig {n k i : Nat} (hi : i < n + k) :
    sumOne (fun j => var n i j) n ∈ ontoFPHP n k := by
  simp only [ontoFPHP, pigeonAx, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl (Or.inl ⟨i, hi, rfl⟩))

theorem mem_hole {n k j : Nat} (hj : j < n) :
    sumOne (fun i => var n i j) (n + k) ∈ ontoFPHP n k := by
  simp only [ontoFPHP, holeAx, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl (Or.inr ⟨j, hj, rfl⟩))

theorem mem_coll {n k : Nat} {P : Poly Nat} (h : P ∈ collAx n k) : P ∈ ontoFPHP n k := by
  simp only [ontoFPHP, List.mem_append]; exact Or.inl (Or.inr h)

theorem mem_func {n k : Nat} {P : Poly Nat} (h : P ∈ funcAx n k) : P ∈ ontoFPHP n k := by
  simp only [ontoFPHP, List.mem_append]; exact Or.inr h

/-- Every axiom of `ontoFPHP n k` is a pigeon, hole, collision or functional axiom. -/
theorem mem_ontoFPHP {n k : Nat} {P : Poly Nat} (h : P ∈ ontoFPHP n k) :
    (∃ i < n + k, P = sumOne (fun j => var n i j) n) ∨
    (∃ j < n, P = sumOne (fun i => var n i j) (n + k)) ∨ P ∈ collAx n k ∨ P ∈ funcAx n k := by
  simp only [ontoFPHP, pigeonAx, holeAx, List.mem_append, List.mem_map, List.mem_range] at h
  rcases h with ((⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩) | h) | h
  · exact Or.inl ⟨i, hi, rfl⟩
  · exact Or.inr (Or.inl ⟨j, hj, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-- The zero line is derivable from `ontoFPHP n k` in degree `D ≥ 1` (when there is a pigeon). -/
theorem zero_der (p n k D : Nat) (hD : 1 ≤ D) (hnk : 0 < n + k) :
    PPCDerivable p (ontoFPHP n k) D (fun _ => 0) := by
  have h := PPCDerivable.ax (p := p) _ (mem_pig hnk) (Nat.le_trans (sumOne_deg _ _) hD)
  exact of_eq (PPCDerivable.lin _ _ 0 0 h h) (fun a => by simp)

theorem var_div (n i j : Nat) (hj : j < n) : var n i j / n = i := by
  unfold var
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]

theorem var_mod (n i j : Nat) (hj : j < n) : var n i j % n = j := by
  unfold var
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-! ## Restriction `(n+1, k) → (n, k)` -/

/-- Set `x_{n+k, n} := 1`, the rest of pigeon `n+k`'s row and hole `n`'s column to `0`, and
rename the other variables. -/
def σR (n k : Nat) (x : Nat) : Lit :=
  if x / (n + 1) = n + k then (if x % (n + 1) = n then .const true else .const false)
  else if x % (n + 1) = n then .const false else .var (var n (x / (n + 1)) (x % (n + 1)))

theorem xv_R (n k i j : Nat) (hj : j < n + 1) (a : Nat → Bool) :
    xv (var (n + 1) i j) (pull (σR n k) a) =
      if i = n + k then (if j = n then 1 else 0) else if j = n then 0 else xv (var n i j) a := by
  simp only [xv, pull, σR, var_div _ _ _ hj, var_mod _ _ _ hj]
  by_cases h1 : i = n + k <;> by_cases h2 : j = n <;> simp [h1, h2, Lit.val]

/-- Restriction: a degree-`D` refutation of `onto-FPHP^{n+1+k}_{n+1}` gives one of
`onto-FPHP^{n+k}_n`. So at fixed `k`, the minimum refutation degree is nondecreasing in `n`. -/
theorem ontoFPHP_restrict (p n k D : Nat) (hD : 1 ≤ D) (hnk : 0 < n + k)
    (h : PPCRefutation p (ontoFPHP (n + 1) k) D) : PPCRefutation p (ontoFPHP n k) D := by
  have hz := zero_der p n k D hD hnk
  refine PPCDerivable.subst (σR n k) hz ?_ h
  intro P hP hPD
  rcases mem_ontoFPHP hP with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩ | hc | hf
  · -- pigeon axiom
    by_cases hik : i = n + k
    · refine of_eq hz (fun a => ?_)
      rw [sumOne_eval]; simp only [rsum]
      rw [rsum_zero n _ (fun t ht => by rw [xv_R _ _ _ _ (by omega)]; simp [hik]; omega),
        xv_R _ _ _ _ (by omega)]
      simp [hik]
    · have hB := PPCDerivable.ax (p := p) _ (mem_pig (n := n) (k := k) (i := i) (by omega))
        (Nat.le_trans (sumOne_deg _ _) hD)
      refine of_eq hB (fun a => ?_)
      rw [sumOne_eval, sumOne_eval]; simp only [rsum]
      rw [rsum_congr n _ (fun j => xv (var n i j) a)
          (fun t ht => by rw [xv_R _ _ _ _ (by omega)]; simp [hik]; omega),
        xv_R _ _ _ _ (by omega)]
      simp [hik]
  · -- hole axiom
    have e : n + 1 + k = (n + k) + 1 := by omega
    by_cases hjn : j = n
    · refine of_eq hz (fun a => ?_)
      rw [sumOne_eval, e]; simp only [rsum]
      rw [rsum_zero (n + k) _ (fun t ht => by rw [xv_R _ _ _ _ (by omega)]; simp [hjn]; omega),
        xv_R _ _ _ _ (by omega)]
      simp [hjn]
    · have hB := PPCDerivable.ax (p := p) _ (mem_hole (n := n) (k := k) (j := j) (by omega))
        (Nat.le_trans (sumOne_deg _ _) hD)
      refine of_eq hB (fun a => ?_)
      rw [sumOne_eval, sumOne_eval, e]; simp only [rsum]
      rw [rsum_congr (n + k) _ (fun i => xv (var n i j) a)
          (fun t ht => by rw [xv_R _ _ _ _ (by omega)]; simp [hjn]; omega),
        xv_R _ _ _ _ (by omega)]
      simp [hjn]
  · -- collision axiom
    obtain ⟨j, i, i', hj, hi, hi', hii, rfl⟩ := mem_collAx.mp hc
    by_cases h0 : j = n ∨ i' = n + k
    · refine of_eq hz (fun a => ?_)
      rw [prod2_eval, xv_R _ _ _ _ hj, xv_R _ _ _ _ hj]
      rcases h0 with h0 | h0
      · simp [h0, show i ≠ n + k by omega]
      · simp only [h0, if_pos, show i ≠ n + k by omega, if_false]
        by_cases hjn : j = n <;> simp [hjn]
    · have hm : prod2 (var n i j) (var n i' j) ∈ ontoFPHP n k :=
        mem_coll (mem_collAx.mpr ⟨j, i, i', by omega, by omega, by omega, hii, rfl⟩)
      have hB := PPCDerivable.ax (p := p) _ hm (by rw [prod2_deg]; rw [prod2_deg] at hPD; exact hPD)
      refine of_eq hB (fun a => ?_)
      rw [prod2_eval, prod2_eval, xv_R _ _ _ _ hj, xv_R _ _ _ _ hj]
      simp [show i ≠ n + k by omega, show i' ≠ n + k by omega, show j ≠ n by omega]
  · -- functional axiom
    obtain ⟨i, j, j', hi, hj, hj', hjj, rfl⟩ := mem_funcAx.mp hf
    by_cases h0 : i = n + k ∨ j' = n
    · refine of_eq hz (fun a => ?_)
      rw [prod2_eval, xv_R _ _ _ _ hj, xv_R _ _ _ _ hj']
      rcases h0 with h0 | h0
      · simp [h0, show j ≠ n by omega]
      · simp only [h0, show j ≠ n by omega, if_false, if_true]
        by_cases hin : i = n + k <;> simp [hin]
    · have hm : prod2 (var n i j) (var n i j') ∈ ontoFPHP n k :=
        mem_func (mem_funcAx.mpr ⟨i, j, j', by omega, by omega, by omega, hjj, rfl⟩)
      have hB := PPCDerivable.ax (p := p) _ hm (by rw [prod2_deg]; rw [prod2_deg] at hPD; exact hPD)
      refine of_eq hB (fun a => ?_)
      rw [prod2_eval, prod2_eval, xv_R _ _ _ _ hj, xv_R _ _ _ _ hj']
      simp [show i ≠ n + k by omega, show j ≠ n by omega, show j' ≠ n by omega]

end Programme.«20261025-0459-proof-complexity».OntoSubst

#print axioms Programme.«20261025-0459-proof-complexity».OntoSubst.ontoFPHP_restrict
#print axioms Programme.«20261025-0459-proof-complexity».OntoSubst.PPCDerivable.subst
