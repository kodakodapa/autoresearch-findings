import Programme.«20261025-0459-proof-complexity».OntoSubst
import Programme.«20261025-0459-proof-complexity».FinDiff

/-!
# Lines vanishing on the "good" points are derivable

Let `A` be a list of polynomial axioms whose degree-2 monomial axioms `x_u x_w` (`prod2 u w ∈ A`)
all have `u ≠ w`. A Boolean point is *good* if it satisfies every such monomial axiom (no two
variables of a forbidden pair are both true). Theorem `quot`: if the zero line is derivable, then
every function `g` agreeing mod `p` with a polynomial of degree `≤ D` and vanishing mod `p` at every
good point is a line of a degree-`D` `PPCDerivable` derivation from `A`.

Proof: write `Q = Q|_{v=0} + x_v ∂_v Q` variable by variable and carry a monomial prefix `S`
(the variables already set to `1`). When no variable is left, `x_S · Q` is `x_S` times a constant:
if `S` contains a forbidden pair, it is a monomial axiom times `|S| - 2` variables; otherwise the
indicator point of `S` is good, so the constant is `≡ 0`.
-/

namespace Programme.«20261025-0459-proof-complexity».MatchQuot

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».OntoFPHP Programme.«20261025-0459-proof-complexity».OntoSubst Programme.«20261025-0459-proof-complexity».FinDiff

/-- `a` satisfies every degree-2 monomial axiom of `A`. -/
def Good (A : List (Poly Nat)) (a : Nat → Bool) : Prop :=
  ∀ u w, prod2 u w ∈ A → ¬ (a u = true ∧ a w = true)

/-- `Q` with `x_v := 0`. -/
def pz (v : Nat) (Q : Poly Nat) : Poly Nat := ⟨Q.terms.filter fun t => !(t.2.contains v)⟩

/-- `∂_v Q`: the terms containing `v`, with `v` removed. -/
def pd (v : Nat) (Q : Poly Nat) : Poly Nat :=
  ⟨(Q.terms.filter fun t => t.2.contains v).map fun t => (t.1, t.2.filter fun x => x != v)⟩

def Vars (Q : Poly Nat) (V : List Nat) : Prop := ∀ t ∈ Q.terms, ∀ x ∈ t.2, x ∈ V

theorem monoEval_all (a : Nat → Bool) (l : List Nat) :
    monoEval a l = if (∀ x ∈ l, a x = true) then 1 else 0 := by
  induction l with
  | nil => simp [monoEval]
  | cons y l ih =>
    have : monoEval a (y :: l) = (if a y then 1 else 0) * monoEval a l := by
      simp [monoEval]
    rw [this, ih]
    by_cases hy : a y = true <;> by_cases hl : (∀ x ∈ l, a x = true) <;> simp_all

theorem monoEval_cons (a : Nat → Bool) (y : Nat) (l : List Nat) :
    monoEval a (y :: l) = xv y a * monoEval a l := by
  simp [monoEval, xv]

theorem sum_filter {α : Type} (L : List α) (P : α → Bool) (f : α → Int) :
    ((L.filter P).map f).sum = (L.map fun t => if P t then f t else 0).sum := by
  induction L with
  | nil => rfl
  | cons t L ih =>
    by_cases h : P t = true
    · simp [List.filter_cons, h, ih]
    · simp [List.filter_cons, h, ih]

theorem mono_filter (a : Nat → Bool) (v : Nat) (l : List Nat) (hv : v ∈ l) :
    monoEval a l = xv v a * monoEval a (l.filter fun x => x != v) := by
  rw [monoEval_all, monoEval_all]
  unfold xv
  by_cases hav : a v = true
  · have e : (∀ x ∈ l, a x = true) ↔ (∀ x ∈ l.filter (fun x => x != v), a x = true) := by
      constructor
      · intro h x hx; exact h x (List.mem_filter.mp hx).1
      · intro h x hx
        by_cases hxv : x = v
        · subst hxv; exact hav
        · exact h x (List.mem_filter.mpr ⟨hx, by simp [hxv]⟩)
    simp only [hav, ite_true, Int.one_mul]
    by_cases h : (∀ x ∈ l, a x = true)
    · rw [if_pos h, if_pos (e.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (e.mpr h'))]
  · have : ¬ (∀ x ∈ l, a x = true) := fun h => hav (h v hv)
    simp [hav, this]

/-- `Q = Q|_{v=0} + x_v ∂_v Q` on the cube. -/
theorem eval_split (v : Nat) (Q : Poly Nat) (a : Nat → Bool) :
    Q.eval a = (pz v Q).eval a + xv v a * (pd v Q).eval a := by
  unfold Poly.eval pz pd
  simp only
  rw [sum_filter, List.map_map, sum_filter]
  have : ∀ L : List (Int × List Nat),
      (L.map fun t => t.1 * monoEval a t.2).sum =
        (L.map fun t => if !(t.2.contains v) then t.1 * monoEval a t.2 else 0).sum +
        xv v a * (L.map fun t => if t.2.contains v then
          ((fun t : Int × List Nat => t.1 * monoEval a t.2) ∘
            fun t : Int × List Nat => (t.1, t.2.filter fun x => x != v)) t else 0).sum := by
    intro L
    induction L with
    | nil => simp
    | cons t L ih =>
      simp only [List.map_cons, List.sum_cons, ih, Function.comp]
      by_cases h : t.2.contains v = true
      · have hv : v ∈ t.2 := by simpa using h
        rw [mono_filter a v t.2 hv]
        simp only [h, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
        rw [Int.mul_add]
        generalize monoEval a (t.2.filter fun x => x != v) = M
        generalize xv v a = X
        rw [Int.mul_left_comm]; omega
      · have h' : t.2.contains v = false := by simpa using h
        simp only [h', Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
        rw [Int.mul_add]; omega
  exact this Q.terms

theorem eval_pz (v : Nat) (Q : Poly Nat) (a : Nat → Bool) :
    (pz v Q).eval a = Q.eval (upd a v false) := by
  rw [eval_split v Q (upd a v false)]
  have h1 : xv v (upd a v false) = 0 := by simp [xv, upd]
  rw [h1, Int.zero_mul, Int.add_zero]
  unfold Poly.eval pz
  simp only
  rw [sum_filter, sum_filter]
  congr 1
  apply List.map_congr_left
  intro t _
  by_cases h : t.2.contains v = true
  · have hv : v ∈ t.2 := by simpa using h
    simp [hv]
  · have hv : v ∉ t.2 := by simpa using h
    have := monoEval_indep v t.2 hv a false
    simp only at this
    simp [h, this]

theorem deg_pz (v : Nat) (Q : Poly Nat) (d : Nat) (h : Q.deg ≤ d) : (pz v Q).deg ≤ d := by
  rw [deg_le_iff] at h ⊢
  intro t ht
  exact h t (List.mem_filter.mp ht).1

theorem deg_pd (v : Nat) (Q : Poly Nat) (d : Nat) (h : Q.deg ≤ d + 1) : (pd v Q).deg ≤ d := by
  rw [deg_le_iff] at h ⊢
  intro t ht
  simp only [pd, List.mem_map, List.mem_filter] at ht
  obtain ⟨s, ⟨hs, hc⟩, rfl⟩ := ht
  have hv : v ∈ s.2 := by simpa using hc
  have hlt : (s.2.filter fun x => x != v).length < s.2.length := by
    rw [List.length_filter_lt_length_iff_exists]
    exact ⟨v, hv, by simp⟩
  have := h s hs
  simp only; omega

theorem pd_deg0 (v : Nat) (Q : Poly Nat) (h : Q.deg ≤ 0) (a : Nat → Bool) : (pd v Q).eval a = 0 := by
  rw [deg_le_iff] at h
  have : (Q.terms.filter fun t => t.2.contains v) = [] := by
    rw [List.filter_eq_nil_iff]
    intro t ht
    have := h t ht
    have e : t.2 = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [e]
  unfold pd Poly.eval; rw [this]; rfl

theorem vars_pz {v : Nat} {V : List Nat} {Q : Poly Nat} (h : Vars Q (v :: V)) : Vars (pz v Q) V := by
  intro t ht x hx
  have ht' := List.mem_filter.mp ht
  rcases List.mem_cons.mp (h t ht'.1 x hx) with e | e
  · subst e; simp at ht'; exact absurd hx ht'.2
  · exact e

theorem vars_pd {v : Nat} {V : List Nat} {Q : Poly Nat} (h : Vars Q (v :: V)) : Vars (pd v Q) V := by
  intro t ht x hx
  simp only [pd, List.mem_map, List.mem_filter] at ht
  obtain ⟨s, ⟨hs, _⟩, rfl⟩ := ht
  have hx' := List.mem_filter.mp hx
  rcases List.mem_cons.mp (h s hs x hx'.1) with e | e
  · subst e; simp at hx'
  · exact e

/-- A usable axiom times a monomial is derivable. -/
theorem mulMono {p D : Nat} {A : List (Poly Nat)} {P : Poly Nat} (hP : P ∈ A) :
    ∀ m : List Nat, P.deg + m.length ≤ D →
      PPCDerivable p A D (fun a => monoEval a m * P.eval a)
  | [], h => of_eq (PPCDerivable.ax P hP (by simpa using h)) (fun a => by simp [monoEval])
  | x :: m, h => by
    have ih := mulMono (p := p) (D := D) hP m (by simp at h; omega)
    have hc : CubeDeg p (fun a => monoEval a m * P.eval a) (P.deg + m.length) := by
      refine ⟨⟨P.terms.map fun t => (t.1, m ++ t.2)⟩, ?_, fun a => ⟨0, ?_⟩⟩
      · have hP' := (deg_le_iff P P.deg).mp (Nat.le_refl _)
        rw [deg_le_iff]
        intro t ht
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
        have := hP' s hs
        simp only [List.length_append]; omega
      · simp only [Poly.eval, List.map_map]
        have : ∀ L : List (Int × List Nat),
            (L.map ((fun t => t.1 * monoEval a t.2) ∘ fun t => (t.1, m ++ t.2))).sum =
              monoEval a m * (L.map fun t => t.1 * monoEval a t.2).sum := by
          intro L
          induction L with
          | nil => simp
          | cons t L ih =>
            simp only [List.map_cons, List.sum_cons, ih, Function.comp, monoEval_append, Int.mul_add]
            rw [Int.mul_left_comm]
        rw [this]; simp
    have := PPCDerivable.mul x _ (P.deg + m.length) ih hc (by simp at h; omega)
    exact of_eq this (fun a => by rw [monoEval_cons, Int.mul_assoc])

theorem mono_pair (a : Nat → Bool) (S : List Nat) (u w : Nat) (hu : u ∈ S) (hw : w ∈ S) :
    monoEval a S = monoEval a ((S.erase u).erase w) * (xv u a * xv w a) := by
  rw [monoEval_all, monoEval_all]
  unfold xv
  have hsub : ∀ x ∈ (S.erase u).erase w, x ∈ S :=
    fun x hx => List.mem_of_mem_erase (List.mem_of_mem_erase hx)
  by_cases h : (∀ x ∈ S, a x = true)
  · rw [if_pos h, if_pos (fun x hx => h x (hsub x hx)), if_pos (h u hu), if_pos (h w hw)]; rfl
  · rw [if_neg h]
    by_cases hau : a u = true
    · by_cases haw : a w = true
      · have : ¬ ∀ x ∈ (S.erase u).erase w, a x = true := by
          intro h'
          apply h; intro x hx
          by_cases e1 : x = u
          · subst e1; exact hau
          by_cases e2 : x = w
          · subst e2; exact haw
          exact h' x (List.mem_erase_of_ne e2 |>.mpr (List.mem_erase_of_ne e1 |>.mpr hx))
        simp [this]
      · simp [haw]
    · simp [hau]

section
variable {p D : Nat} {A : List (Poly Nat)}

theorem quot_aux (hz : PPCDerivable p A D (fun _ => 0)) (hA : ∀ u w, prod2 u w ∈ A → u ≠ w) :
    ∀ V : List Nat, V.Nodup → ∀ (Q : Poly Nat) (S : List Nat) (d : Nat), Vars Q V →
      (∀ s ∈ S, s ∉ V) → Q.deg ≤ d → S.length + d ≤ D →
      (∀ a, Good A a → (∀ s ∈ S, a s = true) → (p : Int) ∣ Q.eval a) →
      PPCDerivable p A D (fun a => monoEval a S * Q.eval a)
  | [], _, Q, S, d, hV, _, hd, hSD, hvan => by
    have hc : ∀ a, Q.eval a = Q.eval z0 := by
      intro a
      unfold Poly.eval
      congr 1
      apply List.map_congr_left
      intro t ht
      have : t.2 = [] := List.eq_nil_iff_forall_not_mem.mpr (fun x hx => by simpa using hV t ht x hx)
      simp [this, monoEval]
    by_cases hbad : ∃ u ∈ S, ∃ w ∈ S, prod2 u w ∈ A
    · obtain ⟨u, hu, w, hw, hP⟩ := hbad
      have huw := hA u w hP
      have hw' : w ∈ S.erase u := List.mem_erase_of_ne (Ne.symm huw) |>.mpr hw
      have l1 := List.length_erase_of_mem hu
      have l2 := List.length_erase_of_mem hw'
      have l3 := List.length_pos_of_mem hw'
      have h := mulMono (p := p) (D := D) hP ((S.erase u).erase w)
        (by rw [prod2_deg, l2, l1]; rw [l1] at l3; omega)
      refine of_eq (PPCDerivable.lin _ _ (Q.eval z0) 0 h hz) (fun a => ?_)
      rw [hc a, mono_pair a S u w hu hw, prod2_eval]
      simp only [Int.mul_zero, Int.add_zero]; rw [Int.mul_comm]
    · have hb : Good A (fun x => decide (x ∈ S)) := by
        intro u w hP ⟨h1, h2⟩
        exact hbad ⟨u, by simpa using h1, w, by simpa using h2, hP⟩
      have := hvan _ hb (fun s hs => by simpa using hs)
      rw [hc] at this
      refine PPCDerivable.congr _ _ hz (fun a => ?_)
      rw [hc a, Int.sub_zero]
      exact dvd_mul_of _ this
  | v :: V, hN, Q, S, d, hV, hS, hd, hSD, hvan => by
    have hvV : v ∉ V := (List.nodup_cons.mp hN).1
    have hN' : V.Nodup := (List.nodup_cons.mp hN).2
    have hvS : v ∉ S := fun h => hS v h List.mem_cons_self
    have hgood : ∀ a, Good A a → Good A (upd a v false) := by
      intro a ha u w hP ⟨h1, h2⟩
      apply ha u w hP
      simp only [upd] at h1 h2
      constructor
      · by_cases e : u = v
        · simp [e] at h1
        · simpa [e] using h1
      · by_cases e : w = v
        · simp [e] at h2
        · simpa [e] using h2
    have hSupd : ∀ a, (∀ s ∈ S, a s = true) → ∀ s ∈ S, upd a v false s = true := by
      intro a h s hs
      have : s ≠ v := fun e => hvS (e ▸ hs)
      simp [upd, this, h s hs]
    have h0 := quot_aux hz hA V hN' (pz v Q) S d (vars_pz hV)
      (fun s hs h => hS s hs (List.mem_cons_of_mem _ h)) (deg_pz v Q d hd) hSD
      (fun a ha hSa => by rw [eval_pz]; exact hvan _ (hgood a ha) (hSupd a hSa))
    have h1 : PPCDerivable p A D (fun a => monoEval a (v :: S) * (pd v Q).eval a) := by
      cases d with
      | zero => exact of_eq hz (fun a => by rw [pd_deg0 v Q hd a, Int.mul_zero])
      | succ d =>
        refine quot_aux hz hA V hN' (pd v Q) (v :: S) d (vars_pd hV) ?_ (deg_pd v Q d hd)
          (by simp; omega) ?_
        · intro s hs h
          rcases List.mem_cons.mp hs with e | e
          · subst e; exact hvV h
          · exact hS s e (List.mem_cons_of_mem _ h)
        · intro a ha hSa
          have hav : a v = true := hSa v List.mem_cons_self
          have hS' : ∀ s ∈ S, a s = true := fun s hs => hSa s (List.mem_cons_of_mem _ hs)
          have e1 := hvan a ha hS'
          have e2 := hvan _ (hgood a ha) (hSupd a hS')
          rw [← eval_pz] at e2
          rw [eval_split v Q a] at e1
          have hx : xv v a = 1 := by simp [xv, hav]
          rw [hx, Int.one_mul] at e1
          have := Int.dvd_sub e1 e2
          rw [show ∀ x y : Int, x + y - x = y from fun x y => by omega] at this
          exact this
    refine of_eq (PPCDerivable.lin _ _ 1 1 h0 h1) (fun a => ?_)
    rw [eval_split v Q a, monoEval_cons, Int.mul_add, Int.one_mul, Int.one_mul, Int.mul_left_comm]
    simp only [Int.mul_assoc]

/-- Every function of cube-degree `≤ D` vanishing mod `p` at the good points is derivable. -/
theorem quot (hz : PPCDerivable p A D (fun _ => 0)) (hA : ∀ u w, prod2 u w ∈ A → u ≠ w)
    (g : (Nat → Bool) → Int) (hg : CubeDeg p g D) (hvan : ∀ a, Good A a → (p : Int) ∣ g a) :
    PPCDerivable p A D g := by
  obtain ⟨Q, hQ, hQg⟩ := hg
  have hV : Vars Q (List.range ((Q.terms.flatMap Prod.snd).foldr max 0 + 1)) := by
    intro t ht x hx
    have := le_foldr_max (Q.terms.flatMap Prod.snd) x (List.mem_flatMap.mpr ⟨t, ht, hx⟩)
    exact List.mem_range.mpr (by omega)
  have h := quot_aux hz hA (List.range _) List.nodup_range Q [] D hV (by simp) hQ (by simp)
    (fun a ha _ => by have := Int.dvd_add (hQg a) (hvan a ha); simpa using this)
  refine PPCDerivable.congr _ _ h (fun a => ?_)
  have := hQg a
  rw [show monoEval a [] = 1 from rfl, Int.one_mul]
  have := Int.dvd_neg.mpr this
  simpa [Int.neg_sub] using this

end

end Programme.«20261025-0459-proof-complexity».MatchQuot

#print axioms Programme.«20261025-0459-proof-complexity».MatchQuot.quot
