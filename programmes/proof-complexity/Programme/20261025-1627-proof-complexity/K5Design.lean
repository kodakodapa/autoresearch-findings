import Programme.«20261025-1627-proof-complexity».K5Chk
import Programme.«20261025-1627-proof-complexity».OntoNS
import Programme.«20261025-1627-proof-complexity».OntoExt3

/-!
# K5 as a theorem: no degree-4 Nullstellensatz refutation of onto-FPHP^{15}_7 over `ℤ/2`

The functional `E = sumWFn 2 105 4 (Wt sup)` reads a line `g` as `∑_S Wt(S) · cf g S` over sets
`S` of at most 4 variables, so `E(x_S) = Wt(S)` (`E_mono`). `Wt` is th's `ℤ₁₅ × ℤ₇`-invariant
K5 design (supported on matchings), checked in the kernel (`Work.K5Chk`) on the sets containing
the variable `0` and extended to all sets by translation (`Work.K5Lem`).

* `design`: `E` kills `m · P` mod 2 for every axiom `P` of `ontoFPHP 7 8` with `|m| + deg P ≤ 4`.
* `E_good`: `E` only reads a line at good points (`cf g S` for a matching `S` only uses points
  supported on `S`, which satisfy every monomial axiom).
* `E(1) = Wt [] = 1`.

`no_ns4`: hence `ontoFPHP 7 8` has no degree-4 `NSRefutation 2`.
-/

set_option maxRecDepth 100000

namespace Programme.«20261025-1627-proof-complexity».K5Design

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».FinDiff
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».MatchQuot (Good)
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr prod2_eval mem_ontoFPHP mem_collAx
  mem_funcAx prod2_deg monoEval_append)
open Programme.«20261025-1627-proof-complexity».DesignExt
open Programme.«20261025-1627-proof-complexity».OntoExt2 (SN not_dvd_one sumOne_deg_pos)
open Programme.«20261025-1627-proof-complexity».OntoExt3 (Fn_rsum Fn_sub mono_split)
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261025-1627-proof-complexity».K5Defs

/-- The K5 design as a functional on lines. -/
def E : Fn 2 (SN 105) := sumWFn 2 105 4 (Wt sup)

theorem E_mono (xs : List Nat) (hx : ∀ x ∈ xs, x < 105) (hl : xs.length ≤ 4) :
    E.E (fun a => monoEval a xs) = Wt sup xs := by
  have e : E.E = sumW 105 4 (Wt sup) := rfl
  rw [e, sumW_mono 105 4 _ xs hx (Nat.le_trans (canon_length_le 105 xs) hl)]
  exact Wt_congr sup (fun x => by rw [mem_canon]; exact ⟨fun h => h.1, fun h => ⟨h, hx x h⟩⟩)

theorem matchB_conf {l : List Nat} {u w : Nat} (hu : u ∈ l) (hw : w ∈ l) (hne : u ≠ w)
    (hc : u / 7 = w / 7 ∨ u % 7 = w % 7) : matchB l = false := by
  rw [Bool.eq_false_iff]; intro h
  unfold matchB at h
  rw [List.all_eq_true] at h
  have h1 := h u hu
  rw [Bool.and_eq_true, List.all_eq_true] at h1
  have h2 := h1.2 w hw
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, bne_iff_ne, ne_eq] at h2
  rcases h2 with h3 | ⟨h3, h4⟩
  · exact hne h3
  · rcases hc with h5 | h5
    · exact h3 h5
    · exact h4 h5

theorem not_sumOne {u w : Nat} {v : Nat → Nat} {n : Nat} (e : prod2 u w = sumOne v n) : False := by
  simp [prod2, sumOne] at e

theorem conf_of_mem {u w : Nat} (h : prod2 u w ∈ ontoFPHP 7 8) :
    u < 105 ∧ w < 105 ∧ u ≠ w ∧ (u / 7 = w / 7 ∨ u % 7 = w % 7) := by
  rcases mem_ontoFPHP h with ⟨i, _, e⟩ | ⟨j, _, e⟩ | hc | hf
  · exact (not_sumOne e).elim
  · exact (not_sumOne e).elim
  · obtain ⟨j, i, i', hj, hi, hi', hii, e⟩ := mem_collAx.mp hc
    simp only [prod2, Poly.mk.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at e
    obtain ⟨e1, e2⟩ := e
    subst e1 e2; unfold var; omega
  · obtain ⟨i, j, j', hi, hj, hj', hjj, e⟩ := mem_funcAx.mp hf
    simp only [prod2, Poly.mk.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at e
    obtain ⟨e1, e2⟩ := e
    subst e1 e2; unfold var; omega

theorem E_vanish (f : (Nat → Bool) → Int) (h : ∀ a, SN 105 a → f a = 0) : (2 : Int) ∣ E.E f := by
  rw [E.supp f (fun _ => 0) h]; exact E.zero

/-- A pigeon or hole axiom `∑_j x_{v j} - 1` against `m`: `E(m · P) ≡ ∑_j Wt(v j :: m) - Wt m`. -/
theorem lin_case (v : Nat → Nat) (n : Nat) (m : List Nat) (hm : ∀ x ∈ m, x < 105) (hl : m.length ≤ 3)
    (hv : ∀ j < n, v j < 105) :
    (2 : Int) ∣ E.E (fun a => monoEval a m * (sumOne v n).eval a)
      - (rsum n (fun j => Wt sup (v j :: m)) - Wt sup m) := by
  have e : (fun a => monoEval a m * (sumOne v n).eval a) =
      fun a => rsum n (fun j => monoEval a (m ++ [v j])) - monoEval a m := by
    funext a; exact mono_split m v n a
  rw [e]
  have h2 := Fn_sub E (fun a => rsum n (fun j => monoEval a (m ++ [v j]))) (fun a => monoEval a m)
  have h3 := Fn_rsum E n (fun j a => monoEval a (m ++ [v j]))
  have h4 : rsum n (fun j => E.E (fun a => monoEval a (m ++ [v j]))) = rsum n (fun j => Wt sup (v j :: m)) :=
    rsum_congr _ _ _ (fun j hj => by
      rw [E_mono _ (by
        intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hm x h
        · rw [List.mem_singleton] at h; subst h; exact hv j hj) (by simp; omega)]
      exact Wt_congr sup (fun x => by simp; exact Or.comm))
  rw [E_mono m hm (by omega)] at h2
  rw [h4] at h3
  have := Int.dvd_add h2 h3
  rwa [show E.E (fun a => rsum n (fun j => monoEval a (m ++ [v j])) - monoEval a m) -
      (E.E (fun a => rsum n (fun j => monoEval a (m ++ [v j]))) - Wt sup m) +
      (E.E (fun a => rsum n (fun j => monoEval a (m ++ [v j]))) - rsum n (fun j => Wt sup (v j :: m))) =
      E.E (fun a => rsum n (fun j => monoEval a (m ++ [v j])) - monoEval a m) -
      (rsum n (fun j => Wt sup (v j :: m)) - Wt sup m) by omega] at this

theorem dvd_of_sub {a b : Int} (h1 : (2 : Int) ∣ a - b) (h2 : (2 : Int) ∣ b) : (2 : Int) ∣ a := by
  have := Int.dvd_add h1 h2; rwa [Int.sub_add_cancel] at this

/-- A collision or functional axiom `x_u x_w` against `m`: the product is not a matching. -/
theorem quad_case (u w : Nat) (hP : prod2 u w ∈ ontoFPHP 7 8) (m : List Nat) (hmv : ∀ x ∈ m, x < 105)
    (hm : m.length ≤ 2) : (2 : Int) ∣ E.E (fun a => monoEval a m * (prod2 u w).eval a) := by
  obtain ⟨hu, hw, hne, hcf⟩ := conf_of_mem hP
  have e : (fun a => monoEval a m * (prod2 u w).eval a) = fun a => monoEval a (m ++ [u, w]) := by
    funext a; rw [prod2_eval, monoEval_append]; simp [monoEval, xv, Int.mul_assoc]
  rw [e, E_mono _ (by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hmv x h
    · simp at h; rcases h with h | h <;> subst h <;> assumption) (by simp; omega)]
  rw [Wt_nm sup (matchB_conf (by simp) (by simp) hne hcf)]
  exact ⟨0, rfl⟩

/-- **The design property.** -/
theorem design : IsDesign (ontoFPHP 7 8) 4 E := by
  intro P hP m hm
  by_cases hbig : ∃ x ∈ m, 105 ≤ x
  · obtain ⟨x, hx, hx'⟩ := hbig
    apply E_vanish
    intro a ha
    rw [monoEval_zero ha m x hx hx', Int.zero_mul]
  · have hmv : ∀ x ∈ m, x < 105 := fun x hx => by
      apply Classical.byContradiction; intro h; exact hbig ⟨x, hx, by omega⟩
    rcases mem_ontoFPHP hP with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩ | hc | hf
    · have hd := sumOne_deg_pos (fun j => var 7 i j) 7 (by decide)
      have hl : m.length ≤ 3 := by omega
      have h1 := lin_case (fun j => var 7 i j) 7 m hmv hl (fun j hj => by unfold var; omega)
      exact dvd_of_sub h1 ((lin_all sup chk_all chk_empty m hmv hl).1 i (by omega))
    · have hd := sumOne_deg_pos (fun i => var 7 i j) (7 + 8) (by decide)
      have hl : m.length ≤ 3 := by omega
      have h1 := lin_case (fun i => var 7 i j) (7 + 8) m hmv hl (fun i hi => by unfold var; omega)
      exact dvd_of_sub h1 ((lin_all sup chk_all chk_empty m hmv hl).2 j hj)
    · obtain ⟨j, i, i', _, _, _, _, rfl⟩ := mem_collAx.mp hc
      exact quad_case _ _ hP m hmv (by rw [prod2_deg] at hm; omega)
    · obtain ⟨i, j, j', _, _, _, _, rfl⟩ := mem_funcAx.mp hf
      exact quad_case _ _ hP m hmv (by rw [prod2_deg] at hm; omega)

/-! ## Reading only good points -/

theorem dt_good (p : Int) (g : (Nat → Bool) → Int) : ∀ (t : List Nat) (a : Nat → Bool),
    (∀ b : Nat → Bool, (∀ v, b v = true → a v = true ∨ v ∈ t) → p ∣ g b) → p ∣ dt t g a
  | [], a, h => h a (fun v hv => Or.inl hv)
  | y :: t, a, h => by
    show p ∣ dt t g (upd a y true) - dt t g (upd a y false)
    have k : ∀ c : Bool, p ∣ dt t g (upd a y c) := fun c => dt_good p g t _ (fun b hb => h b (fun v hv => by
      rcases hb v hv with h1 | h1
      · unfold upd at h1
        by_cases e : v = y
        · exact Or.inr (by simp [e])
        · rw [if_neg e] at h1; exact Or.inl h1
      · exact Or.inr (List.mem_cons_of_mem _ h1)))
    exact Int.dvd_sub (k true) (k false)

theorem E_good (f : (Nat → Bool) → Int) (h : ∀ a, Good (ontoFPHP 7 8) a → (2 : Int) ∣ f a) :
    (2 : Int) ∣ E.E f := by
  show (2 : Int) ∣ sumW 105 4 (Wt sup) f
  unfold sumW
  apply lsum_dvd
  intro S _
  cases hm : matchB S with
  | false => rw [Wt_nm sup hm]; exact ⟨0, by simp⟩
  | true =>
    apply dvd_cmul
    apply dt_good 2 f S z0
    intro b hb
    apply h b
    intro u w hP ⟨h1, h2⟩
    have hu : u ∈ S := (hb u h1).resolve_left (by simp [z0])
    have hw : w ∈ S := (hb w h2).resolve_left (by simp [z0])
    obtain ⟨_, _, hne, hcf⟩ := conf_of_mem hP
    rw [matchB_conf hu hw hne hcf] at hm
    cases hm

/-! ## No degree-4 NS refutation -/

theorem E_poly {P : Poly Nat} (hP : P ∈ ontoFPHP 7 8) :
    ∀ (L : List (Int × List Nat)), (∀ t ∈ L, t.2.length + P.deg ≤ 4) →
      (2 : Int) ∣ E.E (fun a => (L.map fun t => t.1 * monoEval a t.2).sum * P.eval a)
  | [], _ => by
    have e : (fun a => (([] : List (Int × List Nat)).map fun t => t.1 * monoEval a t.2).sum * P.eval a) =
        fun _ => 0 := by funext a; simp
    rw [e]; exact E.zero
  | t :: L, h => by
    have ih := E_poly hP L (fun s hs => h s (List.mem_cons_of_mem _ hs))
    have ht := design P hP t.2 (h t List.mem_cons_self)
    have hl := E.lin (fun a => monoEval a t.2 * P.eval a)
      (fun a => (L.map fun t => t.1 * monoEval a t.2).sum * P.eval a) t.1 1
    have e : (fun a => t.1 * (monoEval a t.2 * P.eval a) + 1 * ((L.map fun t => t.1 * monoEval a t.2).sum * P.eval a)) =
        fun a => ((t :: L).map fun t => t.1 * monoEval a t.2).sum * P.eval a := by
      funext a; simp only [List.map_cons, List.sum_cons, Int.add_mul, Int.one_mul, Int.mul_assoc]
    rw [e] at hl
    exact (Int.dvd_iff_dvd_of_dvd_sub hl).mpr (Int.dvd_add (dvd_cmul t.1 ht) (dvd_cmul 1 ih))

theorem E_sum : ∀ (L : List (Poly Nat × Poly Nat)), (∀ e ∈ L, e.2 ∈ ontoFPHP 7 8 ∧ e.1.deg + e.2.deg ≤ 4) →
    (2 : Int) ∣ E.E (fun a => (L.map fun e => e.1.eval a * e.2.eval a).sum)
  | [], _ => by
    have e : (fun a => (([] : List (Poly Nat × Poly Nat)).map fun e => e.1.eval a * e.2.eval a).sum) =
        fun _ => 0 := by funext a; simp
    rw [e]; exact E.zero
  | e :: L, h => by
    have ih := E_sum L (fun f hf => h f (List.mem_cons_of_mem _ hf))
    have he := h e List.mem_cons_self
    have hg := E_poly he.1 e.1.terms (fun t ht => by
      have := (deg_le_iff e.1 e.1.deg).mp (Nat.le_refl _) t ht; omega)
    have hl := E.lin (fun a => e.1.eval a * e.2.eval a) (fun a => (L.map fun e => e.1.eval a * e.2.eval a).sum) 1 1
    have q : (fun a => 1 * (e.1.eval a * e.2.eval a) + 1 * (L.map fun e => e.1.eval a * e.2.eval a).sum) =
        fun a => ((e :: L).map fun e => e.1.eval a * e.2.eval a).sum := by
      funext a; simp
    rw [q] at hl
    have hg' : (2 : Int) ∣ E.E (fun a => e.1.eval a * e.2.eval a) := hg
    exact (Int.dvd_iff_dvd_of_dvd_sub hl).mpr (Int.dvd_add (dvd_cmul 1 hg') (dvd_cmul 1 ih))

/-- **K5 in Lean.** Over `ℤ/2`, `ontoFPHP 7 8` (onto-FPHP^{15}_7) has no degree-4
Nullstellensatz refutation (`Work.OntoNS.NSRefutation`). -/
theorem no_ns4 : ¬ Programme.«20261025-1627-proof-complexity».OntoNS.NSRefutation 2 (ontoFPHP 7 8) 4 := by
  rintro ⟨L, hL, h1⟩
  have hs := E_sum L hL
  have hg := E_good (fun a => (L.map fun e => e.1.eval a * e.2.eval a).sum - 1) h1
  have hsub := Fn_sub E (fun a => (L.map fun e => e.1.eval a * e.2.eval a).sum) (fun _ => 1)
  have h0 : E.E (fun _ => (1 : Int)) = 1 := by
    have := E_mono [] (by simp) (by simp)
    rw [chk_W0] at this
    have e1 : (fun a => monoEval a ([] : List Nat)) = fun _ => (1 : Int) := by funext a; simp [monoEval]
    rwa [e1] at this
  rw [h0] at hsub
  have := Int.dvd_sub hs (Int.dvd_sub hg hsub)
  obtain ⟨c, hc⟩ := this
  exact not_dvd_one (p := 2) (by decide) ⟨c, by omega⟩

end Programme.«20261025-1627-proof-complexity».K5Design

#print axioms Programme.«20261025-1627-proof-complexity».K5Design.no_ns4
