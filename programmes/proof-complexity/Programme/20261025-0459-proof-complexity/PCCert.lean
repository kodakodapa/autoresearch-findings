import Programme.«20261025-0459-proof-complexity».FinDiff
import Programme.«20261025-0459-proof-complexity».OntoFPHP

/-!
# Certified polynomial calculus degree lower bounds (R-operator certificates)

A certificate `C` lists monomials `t` (lists of distinct variables) with a vector `row C t`, the
image `R(t)` of a linear operator `R` (think: normal form modulo the degree-`D` PC closure). For
a line `g`, `Rv C g = ∑_t cf g t • R(t)`, with `cf` the multilinear coefficient (`Work.FinDiff`).
`check` verifies by computation that
* `R` kills every axiom of degree `≤ D`,
* `R(x·m_s) = R(x·R(m_s))` for every monomial `s` of degree `< D` and every variable `x`,
* `R(1) ≢ 0 (mod p)`,
plus bookkeeping (monomials distinct and duplicate-free, closed under erasing a variable, rows
supported on listed monomials). `cert_sound`: if `check` passes, every degree-`D` line `g` has
`Rv C g ≡ 0`, so `1` is not derivable: there is no degree-`D` refutation.
-/

namespace Programme.«20261025-0459-proof-complexity».PCCert

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».FinDiff Programme.«20261025-0459-proof-complexity».OntoFPHP

/-! ## Finite sums -/

def lsum {α : Type} : List α → (α → Int) → Int
  | [], _ => 0
  | a :: l, f => f a + lsum l f

theorem lsum_add {α : Type} (l : List α) (f g : α → Int) :
    lsum l (fun a => f a + g a) = lsum l f + lsum l g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [lsum, ih]; omega

theorem lsum_mul {α : Type} (l : List α) (c : Int) (f : α → Int) :
    lsum l (fun a => c * f a) = c * lsum l f := by
  induction l with
  | nil => simp [lsum]
  | cons a l ih => simp only [lsum, ih, Int.mul_add]

theorem lsum_congr {α : Type} (l : List α) (f g : α → Int) (h : ∀ a ∈ l, f a = g a) :
    lsum l f = lsum l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [lsum]
    rw [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem lsum_dvd {α : Type} (p : Int) (l : List α) (f : α → Int) (h : ∀ a ∈ l, p ∣ f a) :
    p ∣ lsum l f := by
  induction l with
  | nil => exact ⟨0, by simp [lsum]⟩
  | cons a l ih =>
    exact Int.dvd_add (h a List.mem_cons_self) (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

theorem lsum_zero {α : Type} (l : List α) (f : α → Int) (h : ∀ a ∈ l, f a = 0) : lsum l f = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [lsum]
    rw [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]; rfl

theorem lsum_sub {α : Type} (l : List α) (f g : α → Int) :
    lsum l (fun a => f a - g a) = lsum l f - lsum l g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [lsum, ih]; omega

theorem lsum_swap {α β : Type} (l : List α) (m : List β) (F : α → β → Int) :
    lsum l (fun a => lsum m (fun b => F a b)) = lsum m (fun b => lsum l (fun a => F a b)) := by
  induction l with
  | nil => simp only [lsum]; exact (lsum_zero m _ (fun _ _ => rfl)).symm
  | cons a l ih => simp only [lsum]; rw [ih, ← lsum_add]

theorem lsum_ite_eq {α : Type} [DecidableEq α] (l : List α) (v : α) (f : α → Int) (hl : l.Nodup)
    (hv : v ∈ l) : lsum l (fun s => if s = v then f s else 0) = f v := by
  induction l with
  | nil => simp at hv
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    simp only [lsum]
    by_cases hav : a = v
    · subst hav
      rw [if_pos rfl, lsum_zero l _ (fun b hb => by rw [if_neg (fun (e : b = a) => hl.1 (e ▸ hb))])]; omega
    · rw [if_neg hav, ih hl.2 (by
        rcases List.mem_cons.mp hv with h | h
        · exact absurd h.symm hav
        · exact h)]; omega

/-! ## Sparse vectors indexed by monomials -/

abbrev Vec := List (Int × List Nat)

def coef (v : Vec) (u : List Nat) : Int := lsum v (fun e => if e.2 = u then e.1 else 0)

def smul (c : Int) (v : Vec) : Vec := if c = 0 then [] else v.map fun e => (c * e.1, e.2)

def vsum {α : Type} : List α → (α → Vec) → Vec
  | [], _ => []
  | a :: l, F => F a ++ vsum l F

theorem coef_nil (u : List Nat) : coef [] u = 0 := rfl

theorem coef_append (v w : Vec) (u : List Nat) : coef (v ++ w) u = coef v u + coef w u := by
  induction v with
  | nil => simp [coef, lsum]
  | cons e v ih => simp only [List.cons_append, coef, lsum] at ih ⊢; rw [ih]; omega

theorem coef_smul (c : Int) (v : Vec) (u : List Nat) : coef (smul c v) u = c * coef v u := by
  by_cases hc : c = 0
  · subst hc; simp [smul, coef, lsum]
  have : smul c v = v.map fun e => (c * e.1, e.2) := if_neg hc
  rw [this]; clear this
  induction v with
  | nil => simp [coef, lsum]
  | cons e v ih =>
    simp only [List.map_cons, coef, lsum] at ih ⊢
    rw [ih, Int.mul_add]; congr 1; split <;> simp

theorem coef_vsum {α : Type} (l : List α) (F : α → Vec) (u : List Nat) :
    coef (vsum l F) u = lsum l (fun a => coef (F a) u) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [vsum, lsum, coef_append, ih]

theorem lsum_row (v : Vec) (M : List (List Nat)) (F : List Nat → Int) (hM : M.Nodup)
    (hv : ∀ e ∈ v, e.2 ∈ M) : lsum v (fun e => e.1 * F e.2) = lsum M (fun u => coef v u * F u) := by
  induction v with
  | nil => simp only [lsum]; exact (lsum_zero M _ (fun u _ => by simp [coef, lsum])).symm
  | cons e v ih =>
    simp only [lsum]
    rw [ih (fun e' he' => hv e' (List.mem_cons_of_mem _ he'))]
    have : ∀ u, coef (e :: v) u * F u = (if u = e.2 then e.1 * F u else 0) + coef v u * F u := by
      intro u; simp only [coef, lsum]
      by_cases h : e.2 = u
      · subst h; simp [Int.add_mul]
      · rw [if_neg h, if_neg (fun h' => h h'.symm)]; simp
    rw [lsum_congr M _ _ (fun u _ => this u), lsum_add, lsum_ite_eq M e.2 _ hM (hv e List.mem_cons_self)]

/-- Every coefficient is `≡ 0 (mod p)`. -/
def zeroCheck (p : Nat) (v : Vec) : Bool := v.all fun e => coef v e.2 % (p : Int) == 0

theorem zeroCheck_spec (p : Nat) (v : Vec) (h : zeroCheck p v = true) (u : List Nat) :
    (p : Int) ∣ coef v u := by
  by_cases hu : ∃ e ∈ v, e.2 = u
  · obtain ⟨e, he, rfl⟩ := hu
    simp only [zeroCheck, List.all_eq_true, beq_iff_eq] at h
    exact Int.dvd_of_emod_eq_zero (h e he)
  · have : coef v u = 0 := lsum_zero v _ (fun e he => by
      rw [if_neg (fun h' => hu ⟨e, he, h'⟩)])
    rw [this]; exact ⟨0, by simp⟩

/-! ## Certificates -/

abbrev Cert := List (List Nat × Vec)

def mons (C : Cert) : List (List Nat) := C.map Prod.fst

def row (C : Cert) (t : List Nat) : Vec := (C.lookup t).getD []

/-- `R(x · m_s)` written through `R` of the monomials `t` with `t.erase x = s`. -/
def Nv (C : Cert) (x : Nat) (s : List Nat) : Vec :=
  vsum (mons C) (fun t => if x ∈ t ∧ t.erase x = s then row C t else []) ++
    (if x ∈ s then row C s else [])

/-- `R(g) = ∑_t cf g t • R(t)`. -/
def Rv (C : Cert) (g : (Nat → Bool) → Int) : Vec := vsum (mons C) (fun t => smul (cf g t) (row C t))

/-- Variables of `P`. -/
def pv (P : Poly Nat) : List Nat := P.terms.flatMap (·.2)

/-- `R(P)`, skipping monomials with a variable outside `P` (their coefficient is `0`). -/
def RvA (C : Cert) (P : Poly Nat) : Vec :=
  vsum (mons C) (fun t => if t.all (· ∈ pv P) then smul (cf (fun a => P.eval a) t) (row C t) else [])

def check (p D : Nat) (A : List (Poly Nat)) (C : Cert) (xs : List Nat) : Bool :=
  decide (mons C).Nodup && decide ([] ∈ mons C) &&
  (mons C).all (fun t => decide t.Nodup && t.all (fun x => decide (t.erase x ∈ mons C) && decide (x ∈ xs))) &&
  (mons C).all (fun t => (row C t).all (fun e => decide (e.2 ∈ mons C))) &&
  A.all (fun P => !decide (P.deg ≤ D) || zeroCheck p (RvA C P)) &&
  xs.all (fun x => (mons C).all (fun s => !decide (s.length < D) ||
    zeroCheck p (Nv C x s ++ smul (-1) (vsum (row C s) (fun e => smul e.1 (Nv C x e.2)))))) &&
  (row C []).any (fun e => coef (row C []) e.2 % (p : Int) != 0)

theorem eval_indep (P : Poly Nat) (y : Nat) (hy : y ∉ pv P) : Indep y (fun a => P.eval a) := by
  intro a b
  show (P.terms.map fun t => t.1 * monoEval (upd a y b) t.2).sum = (P.terms.map fun t => t.1 * monoEval a t.2).sum
  rw [List.map_congr_left (fun e he => by
    have hye : y ∉ e.2 := fun h => hy (List.mem_flatMap.mpr ⟨e, he, h⟩)
    show e.1 * monoEval (upd a y b) e.2 = e.1 * monoEval a e.2
    have h := monoEval_indep y e.2 hye a b
    simp only at h
    rw [h])]

theorem coef_RvA (C : Cert) (P : Poly Nat) (u : List Nat) :
    coef (RvA C P) u = coef (Rv C (fun a => P.eval a)) u := by
  unfold RvA Rv; rw [coef_vsum, coef_vsum]
  refine lsum_congr _ _ _ (fun t ht => ?_)
  split
  · rfl
  · rename_i h
    rw [coef_nil, coef_smul]
    simp only [List.all_eq_true, decide_eq_true_eq] at h
    have : ∃ y ∈ t, y ∉ pv P := by
      apply Classical.byContradiction; intro hn; apply h; intro x hx
      apply Classical.byContradiction; intro hxn; exact hn ⟨x, hx, hxn⟩
    obtain ⟨y, hy, hyP⟩ := this
    have : cf (fun a => P.eval a) t = 0 := by
      unfold cf; exact dt_mem_zero (eval_indep P y hyP) t hy z0
    rw [this, Int.zero_mul]

theorem coef_Rv (C : Cert) (g : (Nat → Bool) → Int) (u : List Nat) :
    coef (Rv C g) u = lsum (mons C) (fun t => cf g t * coef (row C t) u) := by
  unfold Rv; rw [coef_vsum]; simp only [coef_smul]

theorem coef_Nv (C : Cert) (x : Nat) (s u : List Nat) :
    coef (Nv C x s) u = lsum (mons C) (fun t => if x ∈ t ∧ t.erase x = s then coef (row C t) u else 0) +
      (if x ∈ s then coef (row C s) u else 0) := by
  unfold Nv; rw [coef_append, coef_vsum]
  congr 1
  · exact lsum_congr _ _ _ (fun t _ => by split <;> rfl)
  · split <;> rfl

/-- The invariant: `R(g) ≡ 0`. -/
def Inv (p : Nat) (C : Cert) (g : (Nat → Bool) → Int) : Prop := ∀ u, (p : Int) ∣ coef (Rv C g) u

theorem cert_sound (p D : Nat) (A : List (Poly Nat)) (C : Cert) (xs : List Nat)
    (hc : check p D A C xs = true) : ¬ PPCRefutation p A D := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, List.any_eq_true, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hnd, hnil⟩, hmon⟩, hrow⟩, hax⟩, hmul⟩, hone⟩ := hc
  -- every derivable line satisfies the invariant
  have key : ∀ g, PPCDerivable p A D g → Inv p C g := by
    intro g hg
    induction hg with
    | ax P hP hd =>
      intro u
      rcases hax P hP with h | h
      · exact absurd hd h
      · have := zeroCheck_spec p _ h u
        rwa [coef_RvA C P u] at this
    | lin f g u v _ _ ihf ihg =>
      intro w
      rw [coef_Rv]
      simp only [cf_lin, Int.add_mul, Int.mul_assoc]
      rw [lsum_add, lsum_mul, lsum_mul, ← coef_Rv, ← coef_Rv]
      exact Int.dvd_add (dvd_mul_of u (ihf w)) (dvd_mul_of v (ihg w))
    | congr f g _ hfg ih =>
      intro u
      have e : coef (Rv C f) u = coef (Rv C g) u +
          lsum (mons C) (fun t => (cf f t - cf g t) * coef (row C t) u) := by
        rw [coef_Rv, coef_Rv, ← lsum_add]
        exact lsum_congr _ _ _ (fun t _ => by rw [Int.sub_mul]; omega)
      rw [e]
      exact Int.dvd_add (ih u) (lsum_dvd _ _ _ (fun t _ =>
        Int.dvd_trans (cf_congr p f g hfg t) (Int.dvd_mul_right _ _)))
    | mul x g d _ hcd hdD ih =>
      intro u
      have hM := hnd
      -- step 1: coefficients of `x · g`
      have s1 : coef (Rv C (fun a => xv x a * g a)) u =
          lsum (mons C) (fun t => (if x ∈ t then cf g (t.erase x) + cf g t else 0) * coef (row C t) u) := by
        rw [coef_Rv]
        exact lsum_congr _ _ _ (fun t ht => by rw [cf_mul x g t (hmon t ht).1])
      -- step 2: regroup through `Nv`
      have s2 : lsum (mons C) (fun t => (if x ∈ t then cf g (t.erase x) + cf g t else 0) * coef (row C t) u)
          = lsum (mons C) (fun s => cf g s * coef (Nv C x s) u) := by
        have e1 : ∀ s, cf g s * coef (Nv C x s) u =
            lsum (mons C) (fun t => if x ∈ t ∧ t.erase x = s then cf g s * coef (row C t) u else 0) +
              (if x ∈ s then cf g s * coef (row C s) u else 0) := by
          intro s; rw [coef_Nv, Int.mul_add, ← lsum_mul]
          congr 1
          · exact lsum_congr _ _ _ (fun t _ => by split <;> simp)
          · split <;> simp
        rw [lsum_congr _ _ _ (fun s _ => e1 s), lsum_add, lsum_swap]
        have e2 : ∀ t ∈ mons C, lsum (mons C)
            (fun s => if x ∈ t ∧ t.erase x = s then cf g s * coef (row C t) u else 0) =
            if x ∈ t then cf g (t.erase x) * coef (row C t) u else 0 := by
          intro t ht
          by_cases hxt : x ∈ t
          · rw [if_pos hxt]
            have hmem : t.erase x ∈ mons C := ((hmon t ht).2 x hxt).1
            rw [← lsum_ite_eq (mons C) (t.erase x) (fun s => cf g s * coef (row C t) u) hM hmem]
            exact lsum_congr _ _ _ (fun s _ => by
              by_cases hs : t.erase x = s
              · subst hs; simp [hxt]
              · rw [if_neg (fun h => hs h.2), if_neg (fun h => hs h.symm)])
          · rw [if_neg hxt]; exact lsum_zero _ _ (fun s _ => by rw [if_neg (fun h => hxt h.1)])
        rw [lsum_congr _ _ _ e2, ← lsum_add]
        exact lsum_congr _ _ _ (fun t _ => by split <;> simp [Int.add_mul])
      rw [s1, s2]
      by_cases hx : x ∈ xs
      · -- step 3: replace `Nv x s` by `∑ R(s)_{s'} Nv x s'`, using the certificate
        have s3 : (p : Int) ∣ lsum (mons C) (fun s => cf g s * coef (Nv C x s) u) -
            lsum (mons C) (fun s => cf g s *
              coef (vsum (row C s) (fun e => smul e.1 (Nv C x e.2))) u) := by
          have e : lsum (mons C) (fun s => cf g s * coef (Nv C x s) u) -
              lsum (mons C) (fun s => cf g s * coef (vsum (row C s) (fun e => smul e.1 (Nv C x e.2))) u)
              = lsum (mons C) (fun s => cf g s * coef (Nv C x s ++
                  smul (-1) (vsum (row C s) (fun e => smul e.1 (Nv C x e.2)))) u) := by
            rw [← lsum_sub]
            exact lsum_congr _ _ _ (fun s _ => by
              rw [coef_append, coef_smul, Int.mul_add, Int.neg_one_mul, Int.mul_neg]; omega)
          rw [e]
          refine lsum_dvd _ _ _ (fun s hs => ?_)
          by_cases hsD : s.length < D
          · rcases hmul x hx s hs with h | h
            · exact absurd hsD h
            · exact Int.dvd_trans (zeroCheck_spec p _ h u) (Int.dvd_mul_left _ _)
          · exact Int.dvd_trans (cf_cubeDeg hcd s (hmon s hs).1 (by omega)) (Int.dvd_mul_right _ _)
        -- step 4: that sum is a combination of `Inv g`
        have s4 : lsum (mons C) (fun s => cf g s *
              coef (vsum (row C s) (fun e => smul e.1 (Nv C x e.2))) u) =
            lsum (mons C) (fun u' => coef (Nv C x u') u * coef (Rv C g) u') := by
          have e : ∀ s ∈ mons C, cf g s * coef (vsum (row C s) (fun e => smul e.1 (Nv C x e.2))) u =
              lsum (mons C) (fun u' => coef (Nv C x u') u * (cf g s * coef (row C s) u')) := by
            intro s hs
            rw [coef_vsum]; simp only [coef_smul]
            rw [lsum_row (row C s) (mons C) (fun w => coef (Nv C x w) u) hM (hrow s hs), ← lsum_mul]
            exact lsum_congr _ _ _ (fun w _ => by
              rw [Int.mul_comm (coef (Nv C x w) u), Int.mul_assoc])
          rw [lsum_congr _ _ _ e, lsum_swap]
          exact lsum_congr _ _ _ (fun w _ => by rw [lsum_mul, coef_Rv])
        have h4 : (p : Int) ∣ lsum (mons C) (fun u' => coef (Nv C x u') u * coef (Rv C g) u') :=
          lsum_dvd _ _ _ (fun w _ => Int.dvd_trans (ih w) (Int.dvd_mul_left _ _))
        rw [← s4] at h4
        have := Int.dvd_add s3 h4
        rwa [Int.sub_add_cancel] at this
      · -- `x` occurs in no listed monomial
        rw [lsum_zero _ _ (fun s hs => ?_)]
        · exact ⟨0, by simp⟩
        have : coef (Nv C x s) u = 0 := by
          rw [coef_Nv, lsum_zero _ _ (fun t ht => by
            rw [if_neg (fun h => hx ((hmon t ht).2 x h.1).2)])]
          rw [if_neg (fun h => hx ((hmon s hs).2 x h).2)]; rfl
        rw [this, Int.mul_zero]
  intro hr
  have h1 := key _ hr
  obtain ⟨e, _, he⟩ := hone
  apply he
  have : coef (Rv C (fun _ => 1)) e.2 = coef (row C []) e.2 := by
    rw [coef_Rv]
    rw [← lsum_ite_eq (mons C) [] (fun t => coef (row C t) e.2) hnd hnil]
    exact lsum_congr _ _ _ (fun t _ => by rw [cf_const]; split <;> simp)
  rw [← this]
  exact Int.emod_eq_zero_of_dvd (h1 e.2)

end Programme.«20261025-0459-proof-complexity».PCCert
