import Programme.«20261025-0459-proof-complexity».MatchQuot
import Programme.«20261025-0459-proof-complexity».OntoDeg1Lower
import Programme.«20261025-0459-proof-complexity».OntoPCLower

/-!
# Upper bound: degree-`t` PC refutations of onto-FPHP from binomial coefficients

`esym f s t` is the elementary symmetric polynomial `e_t(f_0, …, f_{s-1})`. With `r_i = ∑_j x_{ij}`
(pigeon `i`) and `c_j = ∑_i x_{ij}` (hole `j`):
* `esym_pig`: `e_t(r_0, …, r_{s-1}) - C(s,t)` is derivable in degree `t` from the pigeon axioms,
  by `e_t^{(s+1)} - C(s+1,t) = (e_t^{(s)} - C(s,t)) + r_s (e_{t-1}^{(s)} - C(s,t-1)) + C(s,t-1)(r_s - 1)`
  (multiplication by the variables of `r_s` of a line of degree `t-1`); the same for holes;
* at a point satisfying the collision and functional axioms every `r_i, c_j ∈ {0,1}` and
  `∑ r_i = ∑ c_j = N`, so `e_t(r) = C(N,t) = e_t(c)`: by `Work.MatchQuot.quot` the difference
  `e_t(r) - e_t(c)` is derivable in degree `t ≥ 2`.
Together: `C(n+k,t) - C(n,t)` is derivable, a refutation when it is a unit mod `p`
(`ontoFPHP_upper`). Instances: `k = 3` over `Z/3` and `k = 4` over `Z/2` (degree `k`), `k = 2` over
`Z/2` (degree 2). With `Work.OntoPCLower.f3_deg3` (no degree `≤ 2`) and `Work.OntoDeg1Lower` (no
degree 1) this pins the PC degree exactly: 3 for `k = 3` over `Z/3` (`n ≥ 3`), 2 for `k = 2` over
`Z/2` (`n ≥ 1`).
-/

namespace Programme.«20261025-0459-proof-complexity».OntoLucas

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».OntoFPHP Programme.«20261025-0459-proof-complexity».OntoSubst Programme.«20261025-0459-proof-complexity».MatchQuot

/-- Binomial coefficients by Pascal's rule. -/
def bin : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, t + 1 => bin n t + bin n (t + 1)

/-- `e_t(f_0, …, f_{s-1})`. -/
def esym (f : Nat → Int) : Nat → Nat → Int
  | 0, t => if t = 0 then 1 else 0
  | _ + 1, 0 => 1
  | s + 1, t + 1 => esym f s (t + 1) + f s * esym f s t

theorem bin_zero (n : Nat) : bin n 0 = 1 := by cases n <;> rfl

/-! ## Cube degree of combinations -/

theorem cd_lin {p d : Nat} {f g : (Nat → Bool) → Int} (u v : Int) (hf : CubeDeg p f d) (hg : CubeDeg p g d) :
    CubeDeg p (fun a => u * f a + v * g a) d := by
  obtain ⟨P, hP, hPf⟩ := hf
  obtain ⟨Q, hQ, hQg⟩ := hg
  refine ⟨⟨P.terms.map (fun t => (u * t.1, t.2)) ++ Q.terms.map (fun t => (v * t.1, t.2))⟩, ?_, ?_⟩
  · rw [deg_le_iff] at hP hQ ⊢
    intro t ht
    rcases List.mem_append.mp ht with h | h
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h; exact hP s hs
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h; exact hQ s hs
  · intro a
    have hs : ∀ (c : Int) (L : List (Int × List Nat)),
        ((L.map fun t => (c * t.1, t.2)).map fun t => t.1 * monoEval a t.2).sum =
          c * (L.map fun t => t.1 * monoEval a t.2).sum := by
      intro c L
      induction L with
      | nil => simp
      | cons t L ih => simp only [List.map_cons, List.sum_cons, ih, Int.mul_add, Int.mul_assoc]
    have e : Poly.eval a ⟨P.terms.map (fun t => (u * t.1, t.2)) ++ Q.terms.map (fun t => (v * t.1, t.2))⟩
        = u * P.eval a + v * Q.eval a := by
      unfold Poly.eval; simp only [List.map_append, List.sum_append]; rw [hs, hs]
    rw [e]
    have h1 := dvd_mul_of u (hPf a)
    have h2 := dvd_mul_of v (hQg a)
    have := Int.dvd_add h1 h2
    rw [show u * (P.eval a - f a) + v * (Q.eval a - g a) = u * P.eval a + v * Q.eval a - (u * f a + v * g a)
      by simp only [Int.mul_sub]; omega] at this
    exact this

theorem cd_const (p d : Nat) (c : Int) : CubeDeg p (fun _ => c) d :=
  ⟨⟨[(c, [])]⟩, by simp [Poly.deg], fun a => ⟨0, by simp [Poly.eval, monoEval]⟩⟩

theorem cd_mono {p d d' : Nat} {f : (Nat → Bool) → Int} (h : d ≤ d') (hf : CubeDeg p f d) : CubeDeg p f d' := by
  obtain ⟨P, hP, hPf⟩ := hf; exact ⟨P, Nat.le_trans hP h, hPf⟩

theorem cd_mulx {p d : Nat} {f : (Nat → Bool) → Int} (x : Nat) (hf : CubeDeg p f d) :
    CubeDeg p (fun a => xv x a * f a) (d + 1) := by
  obtain ⟨P, hP, hPf⟩ := hf
  refine ⟨P.mulVar x, Nat.le_trans (deg_mulVar x P) (by omega), fun a => ?_⟩
  rw [eval_mulVar]
  have := dvd_mul_of (xv x a) (hPf a)
  rw [Int.mul_sub] at this
  exact this

theorem cd_rsum {p d : Nat} (M : Nat) (F : Nat → (Nat → Bool) → Int) (hF : ∀ j < M, CubeDeg p (F j) d) :
    CubeDeg p (fun a => rsum M (fun j => F j a)) d := by
  induction M with
  | zero => exact cd_const p d 0
  | succ M ih =>
    have := cd_lin 1 1 (ih (fun j hj => hF j (by omega))) (hF M (by omega))
    obtain ⟨P, hP, hPf⟩ := this
    exact ⟨P, hP, fun a => by have := hPf a; simp only [Int.one_mul] at this; exact this⟩

theorem rsum_mul (M : Nat) (f : Nat → Int) (c : Int) : rsum M (fun j => f j * c) = rsum M f * c := by
  induction M with
  | zero => simp [rsum]
  | succ M ih => simp only [rsum, ih, Int.add_mul]

/-- Row sums `r_i = ∑_{j<M} x_{v i j}`. -/
def row (v : Nat → Nat → Nat) (M : Nat) (a : Nat → Bool) (i : Nat) : Int := rsum M (fun j => xv (v i j) a)

theorem cd_row (p : Nat) (v : Nat → Nat → Nat) (M i : Nat) : CubeDeg p (fun a => row v M a i) 1 :=
  cd_rsum M _ (fun j _ => by
    have := cd_mulx (d := 0) (v i j) (cd_const p 0 1)
    obtain ⟨P, hP, hPf⟩ := this
    exact ⟨P, hP, fun a => by have := hPf a; simp only [Int.mul_one] at this; exact this⟩)

theorem cd_esym (p : Nat) (v : Nat → Nat → Nat) (M : Nat) :
    ∀ s t, CubeDeg p (fun a => esym (row v M a) s t) t
  | 0, t => by
    show CubeDeg p (fun _ => if t = 0 then 1 else 0) t
    exact cd_const p t _
  | s + 1, 0 => cd_const p 0 1
  | s + 1, t + 1 => by
    have h1 := cd_esym p v M s (t + 1)
    have h2 : CubeDeg p (fun a => row v M a s * esym (row v M a) s t) (t + 1) := by
      have := cd_rsum (d := t + 1) M (fun j a => xv (v s j) a * esym (row v M a) s t)
        (fun j _ => cd_mulx (v s j) (cd_esym p v M s t))
      obtain ⟨P, hP, hPf⟩ := this
      refine ⟨P, hP, fun a => ?_⟩
      have e : rsum M (fun j => xv (v s j) a * esym (row v M a) s t) = row v M a s * esym (row v M a) s t := by
        unfold row; exact rsum_mul M (fun j => xv (v s j) a) _
      have := hPf a; simp only at this; rw [e] at this; exact this
    obtain ⟨P, hP, hPf⟩ := cd_lin 1 1 h1 h2
    exact ⟨P, hP, fun a => by have := hPf a; simp only [Int.one_mul] at this; exact this⟩

/-! ## The pigeon (or hole) side -/

/-- From the axioms `∑_{j<M} x_{v i j} - 1` (`i < smax`): `e_t(r_0..r_{s-1}) - C(s,t)` is derivable
in degree `D` for `s ≤ smax`, `t ≤ D`. -/
theorem esym_der {p D : Nat} {A : List (Poly Nat)} (v : Nat → Nat → Nat) (M smax : Nat) (hD : 1 ≤ D)
    (hz : PPCDerivable p A D (fun _ => 0)) (hax : ∀ i < smax, sumOne (v i) M ∈ A) :
    ∀ s, s ≤ smax → ∀ t, t ≤ D →
      PPCDerivable p A D (fun a => esym (row v M a) s t - bin s t)
  | 0, _, t, _ => of_eq hz (fun a => by cases t <;> simp [esym, bin])
  | s + 1, _, 0, _ => of_eq hz (fun a => by simp [esym, bin])
  | s + 1, hs, t + 1, ht => by
    have h1 := esym_der v M smax hD hz hax s (by omega) (t + 1) ht
    have h0 := esym_der v M smax hD hz hax s (by omega) t (by omega)
    have hc : CubeDeg p (fun a => esym (row v M a) s t - bin s t) t := by
      obtain ⟨P, hP, hPf⟩ := cd_lin 1 (-1) (cd_esym p v M s t) (cd_const p t (bin s t))
      exact ⟨P, hP, fun a => by have := hPf a; simp only [Int.one_mul, Int.neg_one_mul] at this
                                rw [Int.sub_eq_add_neg]; exact this⟩
    have hx : ∀ j < M, PPCDerivable p A D
        (fun a => xv (v s j) a * (esym (row v M a) s t - bin s t)) :=
      fun j _ => PPCDerivable.mul (v s j) _ t h0 hc ht
    have hr := der_rsum _ _ hz M hx
    have hP := PPCDerivable.ax (p := p) (D := D) _ (hax s (by omega)) (Nat.le_trans (sumOne_deg _ _) hD)
    have := PPCDerivable.lin _ _ 1 (bin s t) (PPCDerivable.lin _ _ 1 1 h1 hr) hP
    refine of_eq this (fun a => ?_)
    simp only [esym, bin, sumOne_eval, Int.zero_add, Int.one_mul, Int.mul_zero, Int.add_zero]
    have e : rsum M (fun j => xv (v s j) a * (esym (row v M a) s t - bin s t)) =
        row v M a s * (esym (row v M a) s t - bin s t) := by
      unfold row; rw [rsum_mul]
    rw [e]
    have e2 : rsum M (fun t => xv (v s t) a) = row v M a s := rfl
    rw [e2]
    generalize row v M a s = R
    generalize esym (row v M a) s t = E0
    generalize esym (row v M a) s (t + 1) = E1
    have e3 : (bin s t : Int) * (R - 1) = R * bin s t - bin s t := by
      rw [Int.mul_sub, Int.mul_comm, Int.mul_one]
    rw [e3, Int.natCast_add, Int.mul_sub]
    omega

/-! ## Good points -/

def cnt (f : Nat → Int) : Nat → Nat
  | 0 => 0
  | s + 1 => cnt f s + (if f s = 1 then 1 else 0)

theorem esym_01 (f : Nat → Int) : ∀ s, (∀ i < s, f i = 0 ∨ f i = 1) →
    (rsum s f = cnt f s ∧ ∀ t, esym f s t = bin (cnt f s) t)
  | 0, _ => ⟨rfl, fun t => by cases t <;> rfl⟩
  | s + 1, h => by
    obtain ⟨ih1, ih2⟩ := esym_01 f s (fun i hi => h i (by omega))
    rcases h s (by omega) with e | e
    · refine ⟨by simp [rsum, cnt, ih1, e], fun t => ?_⟩
      cases t with
      | zero => simp [esym, bin_zero]
      | succ t => simp [esym, cnt, e, ih2]
    · refine ⟨by simp [rsum, cnt, ih1, e], fun t => ?_⟩
      cases t with
      | zero => simp [esym, bin_zero]
      | succ t => simp only [esym, cnt, e, ih2, if_pos, bin]; simp; omega

theorem rsum01 (M : Nat) (b : Nat → Bool) (h : ∀ j j', j < j' → j' < M → ¬ (b j = true ∧ b j' = true)) :
    rsum M (fun j => if b j then 1 else 0) = 0 ∨ rsum M (fun j => if b j then 1 else 0) = 1 := by
  induction M with
  | zero => exact Or.inl rfl
  | succ M ih =>
    simp only [rsum]
    by_cases hb : b M = true
    · have : rsum M (fun j => if b j then 1 else 0) = 0 :=
        rsum_zero M _ (fun j hj => by
          have := h j M hj (by omega)
          have : b j = false := by cases e : b j <;> simp_all
          simp [this])
      rw [this]; simp [hb]
    · have := ih (fun j j' h1 h2 => h j j' h1 (by omega))
      simp [hb]; exact this

theorem var_inj {n i j i' j' : Nat} (hj : j < n) (hj' : j' < n) (h : var n i j = var n i' j') :
    i = i' ∧ j = j' := by
  have e1 := var_div n i j hj; have e2 := var_div n i' j' hj'
  have e3 := var_mod n i j hj; have e4 := var_mod n i' j' hj'
  rw [h] at e1 e3; exact ⟨e1.symm.trans e2, e3.symm.trans e4⟩

theorem prod2_inj {x y u w : Nat} (h : prod2 x y = prod2 u w) : x = u ∧ y = w := by
  simp [prod2] at h; exact h

theorem prod2_ne (n k : Nat) : ∀ u w, prod2 u w ∈ ontoFPHP n k → u ≠ w := by
  intro u w h
  rcases mem_ontoFPHP h with ⟨i, _, e⟩ | ⟨j, _, e⟩ | h | h
  · simp [prod2, sumOne] at e
  · simp [prod2, sumOne] at e
  · obtain ⟨j, i, i', hj, _, _, hii, e⟩ := mem_collAx.mp h
    obtain ⟨e1, e2⟩ := prod2_inj e
    intro h'; rw [← e1, ← e2] at h'; have := (var_inj hj hj h').1; omega
  · obtain ⟨i, j, j', _, hj, hj', hjj, e⟩ := mem_funcAx.mp h
    obtain ⟨e1, e2⟩ := prod2_inj e
    intro h'; rw [← e1, ← e2] at h'; have := (var_inj hj hj' h').2; omega

/-- At a good point, `e_t` of the pigeon sums equals `e_t` of the hole sums. -/
theorem good_eq (n k t : Nat) (a : Nat → Bool) (ha : Good (ontoFPHP n k) a) :
    esym (row (fun i j => var n i j) n a) (n + k) t = esym (row (fun j i => var n i j) (n + k) a) n t := by
  have hP : ∀ i < n + k, row (fun i j => var n i j) n a i = 0 ∨ row (fun i j => var n i j) n a i = 1 :=
    fun i hi => rsum01 n (fun j => a (var n i j)) (fun j j' h1 h2 hb =>
      ha _ _ (mem_func (mem_funcAx.mpr ⟨i, j, j', hi, by omega, h2, h1, rfl⟩)) hb)
  have hH : ∀ j < n, row (fun j i => var n i j) (n + k) a j = 0 ∨ row (fun j i => var n i j) (n + k) a j = 1 :=
    fun j hj => rsum01 (n + k) (fun i => a (var n i j)) (fun i i' h1 h2 hb =>
      ha _ _ (mem_coll (mem_collAx.mpr ⟨j, i, i', hj, by omega, h2, h1, rfl⟩)) hb)
  obtain ⟨p1, p2⟩ := esym_01 _ (n + k) hP
  obtain ⟨h1, h2⟩ := esym_01 _ n hH
  rw [p2, h2]
  have : rsum (n + k) (row (fun i j => var n i j) n a) = rsum n (row (fun j i => var n i j) (n + k) a) :=
    rsum_comm (n + k) n (fun i j => xv (var n i j) a)
  rw [p1, h1] at this
  rw [Int.ofNat_inj.mp this]

/-! ## The refutation -/

/-- For `2 ≤ t`, `0 < n + k`: if `C(n+k,t) - C(n,t)` is a unit mod `p`, onto-FPHP^{n+k}_n has a
degree-`t` polynomial calculus refutation over `Z/p`. -/
theorem ontoFPHP_upper (p n k t : Nat) (ht : 2 ≤ t) (hnk : 0 < n + k)
    (hu : ∃ u : Int, (p : Int) ∣ u * ((bin (n + k) t : Int) - bin n t) - 1) :
    PPCRefutation p (ontoFPHP n k) t := by
  obtain ⟨u, hu⟩ := hu
  have hz := zero_der p n k t (by omega) hnk
  have hP := esym_der (fun i j => var n i j) n (n + k) (by omega) hz (fun i hi => mem_pig hi)
    (n + k) (Nat.le_refl _) t (Nat.le_refl _)
  have hH := esym_der (fun j i => var n i j) (n + k) n (by omega) hz (fun j hj => mem_hole hj)
    n (Nat.le_refl _) t (Nat.le_refl _)
  have hG := quot hz (prod2_ne n k)
    (fun a => esym (row (fun i j => var n i j) n a) (n + k) t - esym (row (fun j i => var n i j) (n + k) a) n t)
    (by
      obtain ⟨P, hP, hPf⟩ := cd_lin 1 (-1) (cd_esym p (fun i j => var n i j) n (n + k) t)
        (cd_esym p (fun j i => var n i j) (n + k) n t)
      exact ⟨P, hP, fun a => by have := hPf a; simp only [Int.one_mul, Int.neg_one_mul] at this
                                rw [Int.sub_eq_add_neg]; exact this⟩)
    (fun a ha => by rw [good_eq n k t a ha, Int.sub_self]; exact Int.dvd_zero _)
  have hL := PPCDerivable.lin _ _ 1 (-1) (PPCDerivable.lin _ _ 1 (-1) hP hH) hG
  have hL := PPCDerivable.lin _ _ (-u) 0 hL hz
  refine PPCDerivable.congr _ _ hL (fun a => ?_)
  have := Int.dvd_neg.mpr hu
  refine Int.dvd_trans this ⟨1, ?_⟩
  simp only [Int.mul_one, Int.mul_zero, Int.add_zero, Int.one_mul, Int.neg_one_mul]
  generalize esym (row (fun i j => var n i j) n a) (n + k) t = E1
  generalize esym (row (fun j i => var n i j) (n + k) a) n t = E2
  generalize (bin (n + k) t : Int) = B1
  generalize (bin n t : Int) = B2
  simp only [Int.mul_sub, Int.mul_add, Int.mul_neg, Int.neg_mul]
  omega

/-! ## Instances -/

theorem bin3 (n : Nat) : bin (n + 3) 3 = bin n 3 + 3 * bin n 2 + 3 * bin n 1 + 1 := by
  simp only [bin, bin_zero, Nat.reduceAdd, Nat.zero_add]; omega

theorem bin4 (n : Nat) : bin (n + 4) 4 = bin n 4 + 4 * bin n 3 + 6 * bin n 2 + 4 * bin n 1 + 1 := by
  simp only [bin, bin_zero, Nat.reduceAdd, Nat.zero_add]; omega

theorem bin2 (n : Nat) : bin (n + 2) 2 = bin n 2 + 2 * bin n 1 + 1 := by
  simp only [bin, bin_zero, Nat.reduceAdd, Nat.zero_add]; omega

/-- Over `Z/3`, onto-FPHP^{n+3}_n has a degree-3 PC refutation for every `n`. -/
theorem f3_k3_upper (n : Nat) : PPCRefutation 3 (ontoFPHP n 3) 3 :=
  ontoFPHP_upper 3 n 3 3 (by decide) (by omega) ⟨1, ⟨bin n 2 + bin n 1, by rw [bin3]; push_cast; omega⟩⟩

/-- Over `Z/2`, onto-FPHP^{n+4}_n has a degree-4 PC refutation for every `n`. -/
theorem f2_k4_upper (n : Nat) : PPCRefutation 2 (ontoFPHP n 4) 4 :=
  ontoFPHP_upper 2 n 4 4 (by decide) (by omega)
    ⟨1, ⟨2 * bin n 3 + 3 * bin n 2 + 2 * bin n 1, by rw [bin4]; push_cast; omega⟩⟩

/-- Over `Z/2`, onto-FPHP^{n+2}_n has a degree-2 PC refutation for every `n`. -/
theorem f2_k2_upper (n : Nat) : PPCRefutation 2 (ontoFPHP n 2) 2 :=
  ontoFPHP_upper 2 n 2 2 (by decide) (by omega) ⟨1, ⟨bin n 1, by rw [bin2]; push_cast; omega⟩⟩

/-- Exact PC degree 3 over `Z/3` at `k = 3`: for `n ≥ 3`, onto-FPHP^{n+3}_n has a degree-`D`
`PPCRefutation 3` iff `D ≥ 3`. -/
theorem f3_k3_exact (n D : Nat) (hn : 3 ≤ n) : PPCRefutation 3 (ontoFPHP n 3) D ↔ 3 ≤ D := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hD
    exact Programme.«20261025-0459-proof-complexity».OntoPCLower.f3_deg3 1 n D (by decide) (by omega) (by omega) h
  · intro hD; exact Programme.«20261025-0459-proof-complexity».OntoPCLower.PPCDerivable.mono hD (f3_k3_upper n)

/-- Exact PC degree 2 over `Z/2` at `k = 2`: for `n ≥ 1`, onto-FPHP^{n+2}_n has a degree-`D`
`PPCRefutation 2` iff `D ≥ 2`. -/
theorem f2_k2_exact (n D : Nat) (hn : 1 ≤ n) : PPCRefutation 2 (ontoFPHP n 2) D ↔ 2 ≤ D := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hD
    have h1 : PPCRefutation 2 (ontoFPHP n 2) 1 := Programme.«20261025-0459-proof-complexity».OntoPCLower.PPCDerivable.mono (by omega) h
    exact Programme.«20261025-0459-proof-complexity».OntoDeg1Lower.ontoFPHP_no_deg1 2 n 2 (by decide) hn ⟨1, rfl⟩ h1
  · intro hD; exact Programme.«20261025-0459-proof-complexity».OntoPCLower.PPCDerivable.mono hD (f2_k2_upper n)

/-- Conditional `l = 1 → 2` step over `Z/3`: if onto-FPHP^{5+9}_5 has no degree-3 `PPCRefutation 3`
(a fixed-size fact, computed in K6), then for every `n ≥ 5` onto-FPHP^{n+3}_n has a degree-3
refutation and onto-FPHP^{n+9}_n has none. -/
theorem f3_sep_of (h59 : ¬ PPCRefutation 3 (ontoFPHP 5 9) 3) (n : Nat) (hn : 5 ≤ n) :
    PPCRefutation 3 (ontoFPHP n 3) 3 ∧ ¬ PPCRefutation 3 (ontoFPHP n 9) 3 := by
  refine ⟨f3_k3_upper n, fun h => ?_⟩
  exact Programme.«20261025-0459-proof-complexity».OntoBlowup.ontoFPHP_lift 3 1 5 9 3 (by decide) (by decide) (by decide) h59 n (by omega)
    (by simpa using h)

/-- Conditional exact value over `Z/2` at `k = 4`: if onto-FPHP^{5+4}_5 has no degree-3
`PPCRefutation 2` (computed in K6), then for `n ≥ 5` the PC degree is exactly 4. -/
theorem f2_k4_exact_of (h54 : ¬ PPCRefutation 2 (ontoFPHP 5 4) 3) (n D : Nat) (hn : 5 ≤ n) :
    PPCRefutation 2 (ontoFPHP n 4) D ↔ 4 ≤ D := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hD
    have h3 : PPCRefutation 2 (ontoFPHP n (1 * 4)) 3 := Programme.«20261025-0459-proof-complexity».OntoPCLower.PPCDerivable.mono (by omega) h
    exact Programme.«20261025-0459-proof-complexity».OntoBlowup.ontoFPHP_lift 2 1 5 4 3 (by decide) (by decide) (by decide) h54 n (by omega) h3
  · intro hD; exact Programme.«20261025-0459-proof-complexity».OntoPCLower.PPCDerivable.mono hD (f2_k4_upper n)

end Programme.«20261025-0459-proof-complexity».OntoLucas

#print axioms Programme.«20261025-0459-proof-complexity».OntoLucas.ontoFPHP_upper
#print axioms Programme.«20261025-0459-proof-complexity».OntoLucas.f3_k3_exact
#print axioms Programme.«20261025-0459-proof-complexity».OntoLucas.f2_k2_exact
#print axioms Programme.«20261025-0459-proof-complexity».OntoLucas.f2_k4_upper
#print axioms Programme.«20261025-0459-proof-complexity».OntoLucas.f3_sep_of
#print axioms Programme.«20261025-0459-proof-complexity».OntoLucas.f2_k4_exact_of
