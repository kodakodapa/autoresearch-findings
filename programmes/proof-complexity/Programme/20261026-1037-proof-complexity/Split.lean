import Programme.«20261025-1627-proof-complexity».NoDrop
import Programme.«20261025-1627-proof-complexity».Hard234ND

/-!
# In-instance no-drop implies `NoDrop` (the external-variable split, board P28 / P41)

`NoDropOn p A I D`: the no-drop property at level `D` with every multiplier and the low-degree
witness `Q` restricted to the variables in the list `I`. This is the statement a finite linear-algebra
check over the instance variables computes: `NS_D ∩ R_{≤ D-1} ⊆ NS_{D-1}` on the good points.

`noDrop_of_on`: if every axiom of `A` uses only variables of `I` and `NoDropOn p A I D'` holds for
every `D' ≤ D`, then `NoDrop p A D` (the library predicate, multipliers over all variables).
Proof: split off the finitely many outside variables one at a time,
`g = g|_{z=0} + x_z ∂_z g`; the `∂_z` parts live one level lower.

`hard234_on`: `Hard234ND.hard234_nd` with its hypothesis replaced by in-instance no-drop at levels
`1..4` for `ontoFPHP 7 8` on its 105 variables.
-/

namespace Programme.«20261026-1037-proof-complexity».Split

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».FinDiff
open Programme.«20261025-0459-proof-complexity».MatchQuot
open Programme.«20261025-1627-proof-complexity».NoDrop

/-- `∑_e g_e P_e` at `a`. -/
def S (L : List (Poly Nat × Poly Nat)) (a : Nat → Bool) : Int :=
  (L.map fun e => e.1.eval a * e.2.eval a).sum

/-- No degree drop at level `D`, multipliers and witness over the variables `I` only. -/
def NoDropOn (p : Nat) (A : List (Poly Nat)) (I : List Nat) (D : Nat) : Prop :=
  ∀ (L : List (Poly Nat × Poly Nat)) (Q : Poly Nat),
    (∀ e ∈ L, e.2 ∈ A ∧ e.1.deg + e.2.deg ≤ D ∧ Vars e.1 I) → Vars Q I → Q.deg ≤ D - 1 →
    (∀ a, Good A a → (p : Int) ∣ S L a - Q.eval a) → NSIn p A (D - 1) (fun a => Q.eval a)

theorem eval_indep (z : Nat) (Q : Poly Nat) (hQ : ∀ t ∈ Q.terms, z ∉ t.2) (a : Nat → Bool) (b : Bool) :
    Q.eval (upd a z b) = Q.eval a := by
  unfold Poly.eval
  congr 1
  apply List.map_congr_left
  intro t ht
  have := monoEval_indep z t.2 (hQ t ht) a b
  simp only at this
  rw [this]

theorem pz_free (z : Nat) (Q : Poly Nat) : ∀ t ∈ (pz z Q).terms, z ∉ t.2 := by
  intro t ht
  have := (List.mem_filter.mp ht).2
  simpa using this

theorem pd_free (z : Nat) (Q : Poly Nat) : ∀ t ∈ (pd z Q).terms, z ∉ t.2 := by
  intro t ht
  simp only [pd, List.mem_map] at ht
  obtain ⟨s, _, rfl⟩ := ht
  simp

theorem good_upd {A : List (Poly Nat)} {I : List Nat} (hA : ∀ P ∈ A, Vars P I) {z : Nat}
    (hz : z ∉ I) {a : Nat → Bool} (ha : Good A a) (b : Bool) : Good A (upd a z b) := by
  intro u w huw
  have hv := hA _ huw
  have hu : u ∈ I := hv (1, [u, w]) (by simp [prod2]) u (by simp)
  have hw : w ∈ I := hv (1, [u, w]) (by simp [prod2]) w (by simp)
  have hu' : u ≠ z := fun e => hz (e ▸ hu)
  have hw' : w ≠ z := fun e => hz (e ▸ hw)
  simp only [upd, hu', hw', ite_false]
  exact ha u w huw

theorem ax_free {A : List (Poly Nat)} {I : List Nat} (hA : ∀ P ∈ A, Vars P I) {z : Nat}
    (hz : z ∉ I) {P : Poly Nat} (hP : P ∈ A) : ∀ t ∈ P.terms, z ∉ t.2 :=
  fun t ht hzt => hz (hA P hP t ht z hzt)

theorem S_split (z : Nat) (L : List (Poly Nat × Poly Nat)) (a : Nat → Bool) :
    S L a = S (L.map fun e => (pz z e.1, e.2)) a + xv z a * S (L.map fun e => (pd z e.1, e.2)) a := by
  unfold S
  induction L with
  | nil => simp
  | cons e L ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, eval_split z e.1 a, Int.mul_add, Int.add_mul]
    generalize (pz z e.1).eval a = X
    generalize (pd z e.1).eval a = Y
    generalize xv z a = W
    generalize e.2.eval a = P
    rw [Int.mul_assoc W Y P]
    omega

theorem S_filter (z : Nat) (L : List (Poly Nat × Poly Nat)) (a : Nat → Bool) :
    S (L.map fun e => (pd z e.1, e.2)) a
      = S ((L.filter fun e => decide (0 < e.1.deg)).map fun e => (pd z e.1, e.2)) a := by
  unfold S
  induction L with
  | nil => simp
  | cons e L ih =>
    simp only [List.map_cons, List.sum_cons, List.filter_cons] at ih ⊢
    by_cases h : 0 < e.1.deg
    · simp only [h, decide_true, ite_true, List.map_cons, List.sum_cons, ih]
    · simp only [h, decide_false, Bool.false_eq_true, ite_false, ih]
      rw [pd_deg0 z e.1 (by omega) a, Int.zero_mul, Int.zero_add]

theorem S_indep {A : List (Poly Nat)} {I : List Nat} (hA : ∀ P ∈ A, Vars P I) {z : Nat}
    (hz : z ∉ I) (L : List (Poly Nat × Poly Nat)) (hL : ∀ e ∈ L, e.2 ∈ A)
    (hf : ∀ e ∈ L, ∀ t ∈ e.1.terms, z ∉ t.2) (a : Nat → Bool) (b : Bool) :
    S L (upd a z b) = S L a := by
  unfold S
  congr 1
  apply List.map_congr_left
  intro e he
  rw [eval_indep z e.1 (hf e he), eval_indep z e.2 (ax_free hA hz (hL e he))]

theorem vars_weaken {Q : Poly Nat} {z : Nat} {V : List Nat} (h : Vars Q (z :: V)) (hz : z ∈ V) :
    Vars Q V := by
  intro t ht x hx
  rcases List.mem_cons.mp (h t ht x hx) with e | e
  · exact e ▸ hz
  · exact e

theorem split_aux {p : Nat} {A : List (Poly Nat)} {I : List Nat} {D : Nat}
    (hA : ∀ P ∈ A, Vars P I) (hI : ∀ D', D' ≤ D → NoDropOn p A I D') :
    ∀ (Z : List Nat) (D' : Nat), D' ≤ D → ∀ (L : List (Poly Nat × Poly Nat)) (Q : Poly Nat),
      (∀ e ∈ L, e.2 ∈ A ∧ e.1.deg + e.2.deg ≤ D' ∧ Vars e.1 (Z ++ I)) → Vars Q (Z ++ I) →
      Q.deg ≤ D' - 1 → (∀ a, Good A a → (p : Int) ∣ S L a - Q.eval a) →
      NSIn p A (D' - 1) (fun a => Q.eval a) := by
  intro Z
  induction Z with
  | nil => intro D' hD' L Q hL hQ hQd h; exact hI D' hD' L Q hL hQ hQd h
  | cons z Z ih =>
    intro D' hD' L Q hL hQ hQd h
    by_cases hz : z ∈ I
    · have hz' : z ∈ Z ++ I := List.mem_append_right Z hz
      exact ih D' hD' L Q (fun e he => ⟨(hL e he).1, (hL e he).2.1, vars_weaken (hL e he).2.2 hz'⟩)
        (vars_weaken hQ hz') hQd h
    · -- the `x_z = 0` parts
      let L0 := L.map fun e => (pz z e.1, e.2)
      let L1 := (L.filter fun e => decide (0 < e.1.deg)).map fun e => (pd z e.1, e.2)
      have hL0A : ∀ e ∈ L0, e.2 ∈ A := by
        intro e he; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he; exact (hL d hd).1
      have hL1A : ∀ e ∈ L1, e.2 ∈ A := by
        intro e he; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
        exact (hL d (List.mem_filter.mp hd).1).1
      have hL0f : ∀ e ∈ L0, ∀ t ∈ e.1.terms, z ∉ t.2 := by
        intro e he; obtain ⟨d, _, rfl⟩ := List.mem_map.mp he; exact pz_free z d.1
      have hL1f : ∀ e ∈ L1, ∀ t ∈ e.1.terms, z ∉ t.2 := by
        intro e he; obtain ⟨d, _, rfl⟩ := List.mem_map.mp he; exact pd_free z d.1
      have hsplit : ∀ a, S L a = S L0 a + xv z a * S L1 a := by
        intro a; rw [S_split z L a, S_filter z L a]
      have hgood0 : ∀ a, Good A a → (p : Int) ∣ S L0 a - (pz z Q).eval a := by
        intro a ha
        have h0 := h (upd a z false) (good_upd hA hz ha false)
        rw [hsplit, S_indep hA hz L0 hL0A hL0f, eval_split z Q (upd a z false),
          eval_indep z (pz z Q) (pz_free z Q)] at h0
        have hx : xv z (upd a z false) = 0 := by simp [xv, upd]
        rw [hx, Int.zero_mul, Int.zero_mul, Int.add_zero, Int.add_zero] at h0
        exact h0
      have hgood1 : ∀ a, Good A a → (p : Int) ∣ S L1 a - (pd z Q).eval a := by
        intro a ha
        have h0 := h (upd a z false) (good_upd hA hz ha false)
        have h1 := h (upd a z true) (good_upd hA hz ha true)
        rw [hsplit, S_indep hA hz L0 hL0A hL0f, S_indep hA hz L1 hL1A hL1f,
          eval_split z Q (upd a z true), eval_indep z (pz z Q) (pz_free z Q),
          eval_indep z (pd z Q) (pd_free z Q)] at h1
        rw [hsplit, S_indep hA hz L0 hL0A hL0f, eval_split z Q (upd a z false),
          eval_indep z (pz z Q) (pz_free z Q)] at h0
        have hx0 : xv z (upd a z false) = 0 := by simp [xv, upd]
        have hx1 : xv z (upd a z true) = 1 := by simp [xv, upd]
        rw [hx0, Int.zero_mul, Int.zero_mul, Int.add_zero, Int.add_zero] at h0
        rw [hx1, Int.one_mul, Int.one_mul] at h1
        have := Int.dvd_sub h1 h0
        have e : S L0 a + S L1 a - ((pz z Q).eval a + (pd z Q).eval a) - (S L0 a - (pz z Q).eval a)
            = S L1 a - (pd z Q).eval a := by omega
        rwa [e] at this
      have r0 : NSIn p A (D' - 1) (fun a => (pz z Q).eval a) := by
        refine ih D' hD' L0 (pz z Q) ?_ (vars_pz hQ) (deg_pz z Q _ hQd) hgood0
        intro e he
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
        have := hL d hd
        exact ⟨this.1, by have := deg_pz z d.1 _ (Nat.le_refl _); dsimp only; omega, vars_pz this.2.2⟩
      by_cases hD2 : 2 ≤ D'
      · have r1 : NSIn p A (D' - 1 - 1) (fun a => (pd z Q).eval a) := by
          refine ih (D' - 1) (by omega) L1 (pd z Q) ?_ (vars_pd hQ) (deg_pd z Q _ (by omega)) hgood1
          intro e he
          obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
          have hd' := List.mem_filter.mp hd
          have := hL d hd'.1
          have hpos : 0 < d.1.deg := by simpa using hd'.2
          have := deg_pd z d.1 (d.1.deg - 1) (by omega)
          exact ⟨(hL d hd'.1).1, by dsimp only; omega, vars_pd (hL d hd'.1).2.2⟩
        have r2 := nsIn_xmul (D := D' - 1) z r1 (by omega)
        have r3 := nsIn_lin 1 1 r0 r2
        refine nsIn_congr r3 (fun a => ⟨0, ?_⟩)
        rw [eval_split z Q a]; simp
      · have hQ0 : Q.deg ≤ 0 := by omega
        refine nsIn_congr r0 (fun a => ⟨0, ?_⟩)
        rw [eval_split z Q a, pd_deg0 z Q hQ0 a]; simp

/-- In-instance no-drop at every level `≤ D` gives the library's `NoDrop` at level `D`. -/
theorem noDrop_of_on {p : Nat} {A : List (Poly Nat)} {I : List Nat} {D : Nat}
    (hA : ∀ P ∈ A, Vars P I) (hI : ∀ D', D' ≤ D → NoDropOn p A I D') : NoDrop p A D := by
  intro f ⟨L, hL, hS⟩ ⟨Q, hQd, hQ⟩
  let Z := (L.flatMap fun e => e.1.terms.flatMap fun t => t.2) ++ Q.terms.flatMap fun t => t.2
  have r := split_aux hA hI Z D (Nat.le_refl _) L Q ?_ ?_ hQd ?_
  · exact nsIn_congr r (fun a => by
      have := hQ a
      have e : f a - Q.eval a = -(Q.eval a - f a) := by omega
      rw [e]; exact Int.dvd_neg.mpr this)
  · intro e he
    refine ⟨(hL e he).1, (hL e he).2, ?_⟩
    intro t ht x hx
    refine List.mem_append_left _ (List.mem_append_left _ ?_)
    exact List.mem_flatMap.mpr ⟨e, he, List.mem_flatMap.mpr ⟨t, ht, hx⟩⟩
  · intro t ht x hx
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨t, ht, hx⟩))
  · intro a ha
    have := Int.dvd_sub (hS a ha) (hQ a)
    have e : S L a - Q.eval a
        = (L.map fun e => e.1.eval a * e.2.eval a).sum - f a - (Q.eval a - f a) := by
      unfold S; omega
    rw [e]; exact this

/-- Level 0 is automatic. -/
theorem noDropOn_zero (p : Nat) (A : List (Poly Nat)) (I : List Nat) : NoDropOn p A I 0 := by
  intro L Q hL _ _ h
  exact ⟨L, fun e he => ⟨(hL e he).1, (hL e he).2.1⟩, fun a ha => by
    have := h a ha
    have e : (L.map fun e => e.1.eval a * e.2.eval a).sum - Q.eval a = S L a - Q.eval a := rfl
    rw [e]; exact this⟩

theorem linTerms_mem (v : Nat → Nat) (m : Nat) (t : Int × List Nat) (ht : t ∈ linTerms v m) :
    ∃ s, s < m ∧ t = (1, [v s]) := by
  induction m with
  | zero => simp [linTerms] at ht
  | succ m ih =>
    simp only [linTerms, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | ht
    · obtain ⟨s, hs, e⟩ := ih ht; exact ⟨s, by omega, e⟩
    · exact ⟨m, by omega, ht⟩

theorem vars_sumOne (v : Nat → Nat) (m B : Nat) (hv : ∀ s, s < m → v s < B) :
    Vars (sumOne v m) (List.range B) := by
  intro t ht x hx
  simp only [sumOne, List.mem_cons] at ht
  rcases ht with rfl | ht
  · simp at hx
  · obtain ⟨s, hs, rfl⟩ := linTerms_mem v m t ht
    simp only [List.mem_singleton] at hx
    subst hx; exact List.mem_range.mpr (hv s hs)

theorem vars_prod2 (u w B : Nat) (hu : u < B) (hw : w < B) : Vars (prod2 u w) (List.range B) := by
  intro t ht x hx
  simp only [prod2, List.mem_singleton] at ht
  subst ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> exact List.mem_range.mpr ‹_›

theorem var_lt {n k i j : Nat} (hi : i < n + k) (hj : j < n) : var n i j < (n + k) * n := by
  unfold var
  have : i * n + j < (i + 1) * n := by rw [Nat.succ_mul]; omega
  have : (i + 1) * n ≤ (n + k) * n := Nat.mul_le_mul_right _ hi
  omega

theorem vars_onto (n k : Nat) : ∀ P ∈ ontoFPHP n k, Vars P (List.range ((n + k) * n)) := by
  intro P hP
  simp only [ontoFPHP, List.mem_append] at hP
  rcases hP with ((hP | hP) | hP) | hP
  · simp only [pigeonAx, List.mem_map, List.mem_range] at hP
    obtain ⟨i, hi, rfl⟩ := hP
    exact vars_sumOne _ _ _ (fun s hs => var_lt hi hs)
  · simp only [holeAx, List.mem_map, List.mem_range] at hP
    obtain ⟨j, hj, rfl⟩ := hP
    exact vars_sumOne _ _ _ (fun s hs => var_lt hs hj)
  · simp only [collAx, List.mem_flatMap, List.mem_filterMap, List.mem_range] at hP
    obtain ⟨j, hj, i, hi, i', hi', hP⟩ := hP
    by_cases h : i < i'
    · simp only [h, ite_true, Option.some.injEq] at hP
      subst hP; exact vars_prod2 _ _ _ (var_lt hi hj) (var_lt hi' hj)
    · simp [h] at hP
  · simp only [funcAx, List.mem_flatMap, List.mem_filterMap, List.mem_range] at hP
    obtain ⟨i, hi, j, hj, j', hj', hP⟩ := hP
    by_cases h : j < j'
    · simp only [h, ite_true, Option.some.injEq] at hP
      subst hP; exact vars_prod2 _ _ _ (var_lt hi hj) (var_lt hi hj')
    · simp [h] at hP

theorem vars_onto78 : ∀ P ∈ ontoFPHP 7 8, Vars P (List.range 105) := vars_onto 7 8

/-- `Hard234ND.hard234_nd` with `NoDrop 2 (ontoFPHP 7 8) 4` replaced by in-instance no-drop at
levels `1..4` on the 105 variables of `ontoFPHP 7 8`. -/
theorem hard234_on
    (h : ∀ D, 1 ≤ D → D ≤ 4 → NoDropOn 2 (ontoFPHP 7 8) (List.range 105) D) :
    (∀ n, 7 ≤ n → ¬ PPCRefutation 2 (ontoFPHP n 8) 4) ∧
    (∀ l, 3 ≤ l → Programme.«20261025-1627-proof-complexity».OntoQ7.Hard 2 l 4) :=
  Programme.«20261025-1627-proof-complexity».Hard234ND.hard234_nd
    (noDrop_of_on vars_onto78 (fun D hD => by
      rcases Nat.eq_zero_or_pos D with rfl | hpos
      · exact noDropOn_zero _ _ _
      · exact h D hpos hD))

end Programme.«20261026-1037-proof-complexity».Split

#print axioms Programme.«20261026-1037-proof-complexity».Split.noDrop_of_on
#print axioms Programme.«20261026-1037-proof-complexity».Split.hard234_on
