import Programme.«20261025-1627-proof-complexity».MomGen
import Programme.«20261025-1627-proof-complexity».Ext3Alg

/-!
# Degree-3 design extension for onto-FPHP when `6·n(n-1)(n-2)(n-3)(n-4)` is invertible mod `p`

Given a degree-2 design `F` of `ontoFPHP n k` (`p ∣ k`), the extension `Ext` is the subset-moment
functional (`Work.MomGen.sumW`, subsets of size `≤ 3`) with moments `F(x_S)` for `|S| ≤ 2` and, on
a 3-matching, `u · S3` (`Work.Ext3Alg`) built from `c = F(1)`, `y_v = F(x_v)` and `z_{vw} = F(x_v x_w)`
(set to `0` on conflicting pairs). Non-matchings of size 3 get `0`. Every level-3 pigeon and hole
equation holds: the summation lemmas reduce it to `pig_ident` / `hole_ident`. With
`Work.DesignExt.ext_sound`: no degree-3 PC refutation; restriction gives all `n ≥ 5` when
`gcd(p, 30) = 1`.
-/

namespace Programme.«20261025-1627-proof-complexity».OntoExt3

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».FinDiff
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero prod2_eval mem_ontoFPHP
  mem_collAx mem_funcAx var_div var_mod prod2_deg mem_pig mem_hole mem_coll mem_func)
open Programme.«20261025-1627-proof-complexity».DesignExt
open Programme.«20261025-1627-proof-complexity».OntoExt2 (SN rsum_dvd rsum_pick rsum_const rsum_cmul rsum_skip var_lt var_decode var_inj
  sumOne_deg_pos linTerms_sum not_dvd_one)
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261025-1627-proof-complexity».Ext3Alg

variable {p : Nat}

/-! ## Moments of a functional -/

section
variable {S : (Nat → Bool) → Prop} (F : Fn p S)

def cc : Int := F.E (fun a => monoEval a [])
def yy (v : Nat) : Int := F.E (fun a => monoEval a [v])

def conf (n v w : Nat) : Prop := v ≠ w ∧ (v / n = w / n ∨ v % n = w % n)

instance (n v w : Nat) : Decidable (conf n v w) := by unfold conf; infer_instance

def zz (n : Nat) (v w : Nat) : Int := if conf n v w then 0 else F.E (fun a => monoEval a [v, w])

theorem conf_symm (n v w : Nat) : conf n v w ↔ conf n w v := by
  unfold conf; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨Ne.symm h1, by omega⟩

theorem F_swap (v w : Nat) : F.E (fun a => monoEval a [v, w]) = F.E (fun a => monoEval a [w, v]) := by
  congr 1; funext a; exact monoEval_congr a _ _ (fun x => by simp; omega)

theorem zz_symm (n v w : Nat) : zz F n v w = zz F n w v := by
  unfold zz
  by_cases h : conf n v w
  · rw [if_pos h, if_pos ((conf_symm n v w).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((conf_symm n v w).mpr h')), F_swap]

theorem zz_cp (n a a' b : Nat) (hb : b < n) (h : a ≠ a') : zz F n (var n a b) (var n a' b) = 0 := by
  unfold zz
  rw [if_pos]
  refine ⟨fun e => h (var_inj n _ _ _ _ hb hb e).1, Or.inr ?_⟩
  rw [var_mod n _ _ hb, var_mod n _ _ hb]

theorem zz_ch (n a b b' : Nat) (hb : b < n) (hb' : b' < n) (h : b ≠ b') :
    zz F n (var n a b) (var n a b') = 0 := by
  unfold zz
  rw [if_pos]
  refine ⟨fun e => h (var_inj n _ _ _ _ hb hb' e).2, Or.inl ?_⟩
  rw [var_div n _ _ hb, var_div n _ _ hb']

theorem Fn_rsum (m : Nat) (G : Nat → (Nat → Bool) → Int) :
    (p : Int) ∣ F.E (fun a => rsum m (fun j => G j a)) - rsum m (fun j => F.E (G j)) := by
  induction m with
  | zero => simpa [rsum] using F.zero
  | succ m ih =>
    have h := F.lin (fun a => rsum m (fun j => G j a)) (G m) 1 1
    simp only [Int.one_mul] at h
    have := Int.dvd_add h ih
    simp only [rsum]
    rwa [show F.E (fun a => rsum m (fun j => G j a) + G m a) - (F.E (fun a => rsum m (fun j => G j a)) + F.E (G m)) +
      (F.E (fun a => rsum m (fun j => G j a)) - rsum m (fun j => F.E (G j))) =
      F.E (fun a => rsum m (fun j => G j a) + G m a) - (rsum m (fun j => F.E (G j)) + F.E (G m)) by omega] at this

theorem Fn_sub (f g : (Nat → Bool) → Int) :
    (p : Int) ∣ F.E (fun a => f a - g a) - (F.E f - F.E g) := by
  have h := F.lin f g 1 (-1)
  have e : (fun a => 1 * f a + -1 * g a) = fun a => f a - g a := by funext a; omega
  rw [e] at h
  rwa [show 1 * F.E f + -1 * F.E g = F.E f - F.E g by omega] at h

end

theorem mono_split (x : List Nat) (v : Nat → Nat) (m : Nat) (a : Nat → Bool) :
    monoEval a x * (sumOne v m).eval a = rsum m (fun j => monoEval a (x ++ [v j])) - monoEval a x := by
  rw [sumOne_eval, Int.mul_sub, Int.mul_one, rsum_cmul]
  congr 1
  refine rsum_congr _ _ _ (fun j _ => ?_)
  simp [monoEval, List.map_append, List.prod_append, xv]

theorem rsum_sub' (m : Nat) (f g : Nat → Int) : rsum m (fun j => f j - g j) = rsum m f - rsum m g := by
  induction m with
  | zero => simp [rsum]
  | succ m ih => simp only [rsum, ih]; omega

/-! ## Facts from a degree-2 design -/

section
variable {n k : Nat} (F : Fn p (SN ((n + k) * n))) (hF : IsDesign (ontoFPHP n k) 2 F)
include hF

theorem design1 : IsDesign (ontoFPHP n k) 1 F := fun P hP m hm => hF P hP m (by omega)

/-- `F(x_v x_w) ≡ 0` for conflicting `v, w`. -/
theorem F_conf (hn : 0 < n) (v w : Nat) (h : conf n v w) : (p : Int) ∣ F.E (fun a => monoEval a [v, w]) := by
  by_cases hv : v < (n + k) * n
  · by_cases hw : w < (n + k) * n
    · have hav : v / n < n + k := (Nat.div_lt_iff_lt_mul hn).mpr hv
      have haw : w / n < n + k := (Nat.div_lt_iff_lt_mul hn).mpr hw
      have hbv : v % n < n := Nat.mod_lt _ hn
      have hbw : w % n < n := Nat.mod_lt _ hn
      have ev := var_decode n v; have ew := var_decode n w
      obtain ⟨hne, hc⟩ := h
      -- the pair is (up to order) a collision or functional axiom
      have key : ∀ x y : Nat, x < (n + k) * n → y < (n + k) * n → x ≠ y →
          (x / n = y / n ∨ x % n = y % n) → x < y → (p : Int) ∣ F.E (fun a => monoEval a [x, y]) := by
        intro x y hx hy hxy hc hlt
        have hax : x / n < n + k := (Nat.div_lt_iff_lt_mul hn).mpr hx
        have hay : y / n < n + k := (Nat.div_lt_iff_lt_mul hn).mpr hy
        have hbx : x % n < n := Nat.mod_lt _ hn
        have hby : y % n < n := Nat.mod_lt _ hn
        have ex := var_decode n x; have ey := var_decode n y
        have e : ∀ P : Poly Nat, P = prod2 x y →
            (fun a => monoEval a [] * P.eval a) = fun a => monoEval a [x, y] := by
          intro P hP; subst hP; funext a; rw [prod2_eval]; simp [monoEval, xv]
        rcases hc with hc | hc
        · -- same pigeon: functional axiom
          have hb : x % n < y % n := by
            rcases Nat.lt_or_ge (x % n) (y % n) with h | h
            · exact h
            · exfalso
              have : x % n ≠ y % n := fun h' => hxy (by rw [← ex, ← ey, hc, h'])
              have h2 : y % n < x % n := by omega
              have : var n (y / n) (y % n) < var n (x / n) (x % n) := by unfold var; rw [hc]; omega
              rw [ex, ey] at this; omega
          have hP : prod2 (var n (x / n) (x % n)) (var n (x / n) (y % n)) ∈ ontoFPHP n k :=
            mem_func (mem_funcAx.mpr ⟨x / n, x % n, y % n, hax, hbx, hby, hb, rfl⟩)
          have := hF _ hP [] (by rw [prod2_deg]; simp)
          rwa [e _ (by rw [show var n (x / n) (y % n) = y by rw [hc, ey], ex])] at this
        · -- same hole: collision axiom
          have ha : x / n < y / n := by
            rcases Nat.lt_or_ge (x / n) (y / n) with h | h
            · exact h
            · exfalso
              have : x / n ≠ y / n := fun h' => hxy (by rw [← ex, ← ey, hc, h'])
              have h2 : y / n < x / n := by omega
              have : var n (y / n) (y % n) < var n (x / n) (x % n) := by
                unfold var; rw [hc]
                have : (y / n + 1) * n ≤ x / n * n := Nat.mul_le_mul_right _ h2
                rw [Nat.succ_mul] at this; omega
              rw [ex, ey] at this; omega
          have hP : prod2 (var n (x / n) (x % n)) (var n (y / n) (x % n)) ∈ ontoFPHP n k :=
            mem_coll (mem_collAx.mpr ⟨x % n, x / n, y / n, hbx, hax, hay, ha, rfl⟩)
          have := hF _ hP [] (by rw [prod2_deg]; simp)
          rwa [e _ (by rw [show var n (y / n) (x % n) = y by rw [hc, ey], ex])] at this
      rcases Nat.lt_or_ge v w with hl | hl
      · exact key v w hv hw hne hc hl
      · rw [F_swap]; exact key w v hw hv (Ne.symm hne) (by omega) (by omega)
    · have : F.E (fun a => monoEval a [v, w]) = F.E (fun _ => 0) :=
        F.supp _ _ (fun a ha => monoEval_zero ha _ w (by simp) (by omega))
      rw [this]; exact F.zero
  · have : F.E (fun a => monoEval a [v, w]) = F.E (fun _ => 0) :=
      F.supp _ _ (fun a ha => monoEval_zero ha _ v (by simp) (by omega))
    rw [this]; exact F.zero

theorem F_zz (hn : 0 < n) (v w : Nat) : (p : Int) ∣ F.E (fun a => monoEval a [v, w]) - zz F n v w := by
  unfold zz
  by_cases h : conf n v w
  · rw [if_pos h, Int.sub_zero]; exact F_conf F hF hn v w h
  · rw [if_neg h, Int.sub_self]; exact ⟨0, by simp⟩

/-- Row/column sums at level 2: `∑_j F(x_v x_{v j}) ≡ F(x_v)` for a pigeon or hole axiom. -/
theorem sum2 (hn : 0 < n) (v : Nat) (w : Nat → Nat) (m : Nat) (hP : sumOne w m ∈ ontoFPHP n k) :
    (p : Int) ∣ rsum m (fun j => zz F n v (w j)) - yy F v := by
  have h1 := hF _ hP [v] (by have := sumOne_deg w m; simp; omega)
  have e : (fun a => monoEval a [v] * (sumOne w m).eval a) =
      fun a => rsum m (fun j => monoEval a ([v] ++ [w j])) - monoEval a [v] := by
    funext a; exact mono_split [v] w m a
  rw [e] at h1
  have h2 := Fn_sub F (fun a => rsum m (fun j => monoEval a ([v] ++ [w j]))) (fun a => monoEval a [v])
  have h3 := Fn_rsum F m (fun j a => monoEval a ([v] ++ [w j]))
  have h4 : (p : Int) ∣ rsum m (fun j => F.E (fun a => monoEval a ([v] ++ [w j]))) - rsum m (fun j => zz F n v (w j)) := by
    have := rsum_dvd p m (fun j => F.E (fun a => monoEval a ([v] ++ [w j])) - zz F n v (w j))
      (fun j _ => F_zz F hF hn v (w j))
    rwa [rsum_sub'] at this
  have := Int.dvd_sub (Int.dvd_sub h1 h2) (Int.dvd_add h3 h4)
  unfold yy
  refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mp this
  exact ⟨0, by omega⟩

theorem hR1 (hn : 0 < n) : ∀ i < n + k, (p : Int) ∣ rsum n (fun j => yy F (var n i j)) - cc F :=
  fun i hi => Programme.«20261025-1627-proof-complexity».OntoExt2.design_sum F (design1 F hF) (fun j => var n i j) n (mem_pig hi)

theorem hC1 : ∀ j < n, (p : Int) ∣ rsum (n + k) (fun i => yy F (var n i j)) - cc F :=
  fun j hj => Programme.«20261025-1627-proof-complexity».OntoExt2.design_sum F (design1 F hF) (fun i => var n i j) (n + k) (mem_hole hj)

theorem hR2 (hn : 0 < n) : ∀ v, ∀ i < n + k, (p : Int) ∣ rsum n (fun j => zz F n v (var n i j)) - yy F v :=
  fun v i hi => sum2 F hF hn v (fun j => var n i j) n (mem_pig hi)

theorem hC2 (hn : 0 < n) : ∀ v, ∀ j < n, (p : Int) ∣ rsum (n + k) (fun i => zz F n v (var n i j)) - yy F v :=
  fun v j hj => sum2 F hF hn v (fun i => var n i j) (n + k) (mem_hole hj)

end

/-! ## The extension functional -/

def isM (n x1 x2 x3 : Nat) : Prop :=
  x1 / n ≠ x2 / n ∧ x1 / n ≠ x3 / n ∧ x2 / n ≠ x3 / n ∧ x1 % n ≠ x2 % n ∧ x1 % n ≠ x3 % n ∧ x2 % n ≠ x3 % n

instance (n x1 x2 x3 : Nat) : Decidable (isM n x1 x2 x3) := by unfold isM; infer_instance

section
variable {S : (Nat → Bool) → Prop} (F : Fn p S) (n : Nat) (u : Int)

/-- Level-3 moment of `{x₁, x₂, x₃}`. -/
def W3 (x1 x2 x3 : Nat) : Int :=
  if isM n x1 x2 x3 then
    u * S3 n (cc F) (yy F) (zz F n) (x1 / n) (x2 / n) (x3 / n) (x1 % n) (x2 % n) (x3 % n)
  else 0

/-- All moments: `F` up to size 2, `W3` at size 3. -/
def WW (T : List Nat) : Int :=
  if T.length ≤ 2 then F.E (fun a => monoEval a T) else
    match T with
    | [x1, x2, x3] => W3 F n u x1 x2 x3
    | _ => 0

theorem W3_swap12 (x1 x2 x3 : Nat) : W3 F n u x1 x2 x3 = W3 F n u x2 x1 x3 := by
  unfold W3
  by_cases h : isM n x1 x2 x3
  · have h' : isM n x2 x1 x3 := by unfold isM at *; omega
    rw [if_pos h, if_pos h', S3_swap12]
  · have h' : ¬ isM n x2 x1 x3 := by unfold isM at *; omega
    rw [if_neg h, if_neg h']

theorem W3_swap23 (x1 x2 x3 : Nat) : W3 F n u x1 x2 x3 = W3 F n u x1 x3 x2 := by
  unfold W3
  by_cases h : isM n x1 x2 x3
  · have h' : isM n x1 x3 x2 := by unfold isM at *; omega
    rw [if_pos h, if_pos h', S3_swap23]
  · have h' : ¬ isM n x1 x3 x2 := by unfold isM at *; omega
    rw [if_neg h, if_neg h']

end

theorem perm3 (f : Nat → Nat → Nat → Int) (h12 : ∀ a b c, f a b c = f b a c)
    (h23 : ∀ a b c, f a b c = f a c b) (x1 x2 x3 s1 s2 s3 : Nat) (hs : [s1, s2, s3].Nodup)
    (hm : ∀ x, x ∈ [s1, s2, s3] ↔ x ∈ [x1, x2, x3]) : f s1 s2 s3 = f x1 x2 x3 := by
  have m1 := (hm s1).mp (by simp); have m2 := (hm s2).mp (by simp); have m3 := (hm s3).mp (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at m1 m2 m3
  rcases m1 with h1 | h1 | h1 <;> rcases m2 with h2 | h2 | h2 <;> rcases m3 with h3 | h3 | h3 <;>
    rw [h1, h2, h3] at hs ⊢ <;>
    first
    | rfl
    | (simp at hs; done)
    | exact h12 _ _ _
    | exact h23 _ _ _
    | exact (h23 _ _ _).trans (h12 _ _ _)
    | exact (h12 _ _ _).trans (h23 _ _ _)
    | exact (h12 _ _ _).trans ((h23 _ _ _).trans (h12 _ _ _))

theorem nodup3_mem {l : List Nat} (hl : l.Nodup) (h3 : l.length = 3) :
    ∃ s1 s2 s3, l = [s1, s2, s3] := by
  match l, h3 with
  | [s1, s2, s3], _ => exact ⟨s1, s2, s3, rfl⟩

section
variable {n k : Nat} (F : Fn p (SN ((n + k) * n))) (u : Int)

/-- The extension. -/
def Ext : Fn p (SN ((n + k) * n)) := sumWFn p ((n + k) * n) 3 (WW F n u)

theorem E_mono (xs : List Nat) (hx : ∀ x ∈ xs, x < (n + k) * n) (hl : xs.length ≤ 3) :
    (Ext F u).E (fun a => monoEval a xs) = WW F n u (canon ((n + k) * n) xs) :=
  sumW_mono _ 3 _ xs hx (Nat.le_trans (canon_length_le _ xs) hl)

theorem E_low (xs : List Nat) (hx : ∀ x ∈ xs, x < (n + k) * n) (hl : (canon ((n + k) * n) xs).length ≤ 2) :
    (Ext F u).E (fun a => monoEval a xs) = F.E (fun a => monoEval a xs) := by
  show sumW _ 3 _ _ = _
  rw [sumW_mono _ 3 _ xs hx (by omega)]
  unfold WW; rw [if_pos hl]
  congr 1; funext a; exact (monoEval_canon _ a xs hx).symm

theorem E_vanish (xs : List Nat) (x : Nat) (hx : x ∈ xs) (hxN : (n + k) * n ≤ x) :
    (Ext F u).E (fun a => monoEval a xs) = (Ext F u).E (fun _ => 0) :=
  (Ext F u).supp _ _ (fun a ha => monoEval_zero ha xs x hx hxN)

theorem E_extends : Extends 2 (Ext F u) F := by
  intro t ht
  by_cases hx : ∀ x ∈ t, x < (n + k) * n
  · rw [E_low F u t hx (Nat.le_trans (canon_length_le _ t) ht), Int.sub_self]; exact ⟨0, by simp⟩
  · have : ∃ x ∈ t, (n + k) * n ≤ x := by
      apply Classical.byContradiction; intro h; apply hx; intro x hxt
      apply Classical.byContradiction; intro h'; exact h ⟨x, hxt, by omega⟩
    obtain ⟨x, hxt, hxN⟩ := this
    rw [E_vanish F u t x hxt hxN, F.supp _ (fun _ => 0) (fun a ha => monoEval_zero ha t x hxt hxN)]
    exact Int.dvd_sub (Ext F u).zero F.zero

theorem canon3 (x1 x2 x3 : Nat) (hd : [x1, x2, x3].Nodup) (hx : ∀ x ∈ [x1, x2, x3], x < (n + k) * n) :
    ∃ s1 s2 s3, canon ((n + k) * n) [x1, x2, x3] = [s1, s2, s3] ∧ [s1, s2, s3].Nodup ∧
      ∀ x, x ∈ [s1, s2, s3] ↔ x ∈ [x1, x2, x3] := by
  have hmem : ∀ x, x ∈ canon ((n + k) * n) [x1, x2, x3] ↔ x ∈ [x1, x2, x3] := fun x => by
    rw [mem_canon]; constructor <;> intro h <;> (try exact h.1) <;> exact ⟨h, hx x h⟩
  have hl1 := canon_length_le ((n + k) * n) [x1, x2, x3]
  have hl2 := nodup_len [x1, x2, x3] _ hd (fun x h => (hmem x).mpr h)
  simp only [List.length_cons, List.length_nil] at hl1 hl2
  obtain ⟨s1, s2, s3, e⟩ := nodup3_mem (l := canon ((n + k) * n) [x1, x2, x3]) (canon_nodup _ _) (by omega)
  refine ⟨s1, s2, s3, e, e ▸ canon_nodup _ _, fun x => ?_⟩
  rw [← e]; exact hmem x

theorem E_three (x1 x2 x3 : Nat) (hd : [x1, x2, x3].Nodup) (hx : ∀ x ∈ [x1, x2, x3], x < (n + k) * n) :
    (Ext F u).E (fun a => monoEval a [x1, x2, x3]) = W3 F n u x1 x2 x3 := by
  rw [E_mono F u _ hx (by simp)]
  obtain ⟨s1, s2, s3, e, hs, hm⟩ := canon3 x1 x2 x3 hd hx
  rw [e]
  unfold WW; simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  exact perm3 (W3 F n u) (W3_swap12 F n u) (W3_swap23 F n u) x1 x2 x3 s1 s2 s3 hs hm

end

/-! ## Level-3 equations -/

theorem small2 {l : List Nat} (hl : l.Nodup) (h2 : l.length ≤ 2) {v w x : Nat} (hv : v ∈ l) (hw : w ∈ l)
    (hvw : v ≠ w) (hx : x ∈ l) : x = v ∨ x = w := by
  match l, h2 with
  | [], _ => simp at hv
  | [a], _ => simp at hv hw; omega
  | [a, b], _ => simp at hv hw hx; omega

theorem rsum_skip2 (m b1 b2 : Nat) (h1 : b1 < m) (h2 : b2 < m) (hb : b1 ≠ b2) (G : Nat → Int) :
    rsum m (fun j => if j = b1 ∨ j = b2 then 0 else G j) = rsum m G - G b1 - G b2 := by
  have e : rsum m (fun j => if j = b1 ∨ j = b2 then 0 else G j) =
      rsum m (fun j => if j = b2 then 0 else (fun j => if j = b1 then 0 else G j) j) :=
    rsum_congr _ _ _ (fun j _ => by by_cases a : j = b1 <;> by_cases b : j = b2 <;> simp [a, b])
  rw [e, rsum_skip m b2 h2, rsum_skip m b1 h1]
  simp [Ne.symm hb]

theorem rsum_pick_dvd (m b : Nat) (hb : b < m) (f : Nat → Int) (Z : Int)
    (h : ∀ j < m, (p : Int) ∣ f j - (if j = b then Z else 0)) : (p : Int) ∣ rsum m f - Z := by
  have h1 := rsum_dvd p m _ h
  rw [rsum_sub', rsum_pick, if_pos hb] at h1
  exact h1

section
variable {n k : Nat} (F : Fn p (SN ((n + k) * n))) (u : Int)

theorem E_rsum (m : Nat) (G : Nat → (Nat → Bool) → Int) (g : (Nat → Bool) → Int) :
    (Ext F u).E (fun a => rsum m (fun j => G j a) - g a) = rsum m (fun j => (Ext F u).E (G j)) - (Ext F u).E g := by
  show sumW ((n + k) * n) 3 (WW F n u) _ = rsum m (fun j => sumW ((n + k) * n) 3 (WW F n u) (G j)) - sumW ((n + k) * n) 3 (WW F n u) g
  have : sumW ((n + k) * n) 3 (WW F n u) (fun a => rsum m (fun j => G j a)) =
      rsum m (fun j => sumW ((n + k) * n) 3 (WW F n u) (G j)) := by
    induction m with
    | zero =>
      have := sumW_lin ((n + k) * n) 3 (WW F n u) (fun _ => 0) (fun _ => 0) 0 0
      simpa [rsum] using this
    | succ m ih =>
      have := sumW_lin ((n + k) * n) 3 (WW F n u) (fun a => rsum m (fun j => G j a)) (G m) 1 1
      simp only [Int.one_mul] at this
      simp only [rsum]; rw [this, ih]
  have e : (fun a => rsum m (fun j => G j a) - g a) = fun a => 1 * rsum m (fun j => G j a) + (-1) * g a := by
    funext a; omega
  rw [e, sumW_lin]
  rw [this]; omega

variable (hF : IsDesign (ontoFPHP n k) 2 F)
include hF

theorem E_conf (hn : 0 < n) (xs : List Nat) (hx : ∀ x ∈ xs, x < (n + k) * n) (hl : xs.length ≤ 3)
    (v w : Nat) (hv : v ∈ xs) (hw : w ∈ xs) (hc : conf n v w) :
    (p : Int) ∣ (Ext F u).E (fun a => monoEval a xs) := by
  have hmem : ∀ x, x ∈ canon ((n + k) * n) xs ↔ x ∈ xs := fun x => by
    rw [mem_canon]; constructor <;> intro h <;> (try exact h.1) <;> exact ⟨h, hx x h⟩
  by_cases hl2 : (canon ((n + k) * n) xs).length ≤ 2
  · rw [E_low F u xs hx hl2]
    have e : (fun a => monoEval a xs) = fun a => monoEval a [v, w] := by
      funext a; apply monoEval_congr; intro x
      constructor
      · intro h
        have := small2 (canon_nodup _ xs) hl2 ((hmem v).mpr hv) ((hmem w).mpr hw) hc.1 ((hmem x).mpr h)
        simp; omega
      · intro h; simp at h; rcases h with rfl | rfl; exact hv; exact hw
    rw [e]; exact F_conf F hF hn v w hc
  · rw [E_mono F u xs hx hl]
    have hl3 := Nat.le_trans (canon_length_le ((n + k) * n) xs) hl
    obtain ⟨s1, s2, s3, e⟩ := nodup3_mem (l := canon ((n + k) * n) xs) (canon_nodup _ _) (by omega)
    rw [e]
    have mv := (hmem v).mpr hv; have mw := (hmem w).mpr hw
    rw [e] at mv mw
    unfold WW; simp only [List.length_cons, List.length_nil]
    rw [if_neg (by omega)]
    unfold W3
    rw [if_neg]
    · exact ⟨0, by simp⟩
    · intro hM
      unfold conf at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mv mw
      rcases mv with rfl | rfl | rfl <;> rcases mw with rfl | rfl | rfl <;> unfold isM at hM <;> omega

theorem E_pair (xs : List Nat) (hx : ∀ x ∈ xs, x < (n + k) * n) (x1 x2 : Nat) (hm : ∀ x, x ∈ xs ↔ x ∈ [x1, x2]) :
    (Ext F u).E (fun a => monoEval a xs) = F.E (fun a => monoEval a [x1, x2]) := by
  have hmem : ∀ x, x ∈ canon ((n + k) * n) xs ↔ x ∈ xs := fun x => by
    rw [mem_canon]; constructor <;> intro h <;> (try exact h.1) <;> exact ⟨h, hx x h⟩
  have hl : (canon ((n + k) * n) xs).length ≤ 2 := by
    have := nodup_len _ [x1, x2] (canon_nodup _ xs) (fun x h => (hm x).mp ((hmem x).mp h))
    simpa using this
  rw [E_low F u xs hx hl]
  congr 1; funext a; exact monoEval_congr a _ _ hm

theorem pig3 (hn : 0 < n) (hu : (p : Int) ∣ u * M3 n - 1) (i : Nat) (hi : i < n + k) (x1 x2 : Nat) :
    (p : Int) ∣ (Ext F u).E (fun a => monoEval a [x1, x2] * (sumOne (fun j => var n i j) n).eval a) := by
  let N := (n + k) * n
  by_cases hN : x1 < N ∧ x2 < N
  case neg =>
    have : (Ext F u).E (fun a => monoEval a [x1, x2] * (sumOne (fun j => var n i j) n).eval a) = (Ext F u).E (fun _ => 0) := by
      apply (Ext F u).supp; intro a ha
      by_cases h1 : x1 < N
      · rw [monoEval_zero ha _ x2 (by simp) (by omega), Int.zero_mul]
      · rw [monoEval_zero ha _ x1 (by simp) (by omega), Int.zero_mul]
    rw [this]; exact (Ext F u).zero
  obtain ⟨hx1, hx2⟩ := hN
  by_cases heq : x1 = x2
  · subst heq
    have e : (fun a => monoEval a [x1, x1] * (sumOne (fun j => var n i j) n).eval a) =
        fun a => monoEval a [x1] * (sumOne (fun j => var n i j) n).eval a := by
      funext a; rw [monoEval_congr a [x1, x1] [x1] (fun x => by simp)]
    rw [e]
    exact low_kill (D := 3) hF (E_extends F u) (mem_pig hi) (by have := sumOne_deg (fun j => var n i j) n; simp; omega)
  have hsplit := E_rsum F u n (fun j a => monoEval a [x1, x2, var n i j]) (fun a => monoEval a [x1, x2])
  have e0 : (fun a => monoEval a [x1, x2] * (sumOne (fun j => var n i j) n).eval a) =
      fun a => rsum n (fun j => monoEval a [x1, x2, var n i j]) - monoEval a [x1, x2] := by
    funext a; rw [mono_split]; simp
  rw [e0, hsplit]
  have hvl : ∀ j < n, var n i j < N := fun j hj => var_lt n k i j hi hj
  by_cases hc : conf n x1 x2
  · apply Int.dvd_sub
    · exact rsum_dvd _ _ _ (fun j hj => E_conf F u hF hn _ (by simp; exact ⟨hx1, hx2, hvl j hj⟩) (by simp) x1 x2 (by simp) (by simp) hc)
    · exact E_conf F u hF hn _ (by simp; omega) (by simp) x1 x2 (by simp) (by simp) hc
  -- a matching pair
  have ha1 : x1 / n < n + k := (Nat.div_lt_iff_lt_mul hn).mpr hx1
  have ha2 : x2 / n < n + k := (Nat.div_lt_iff_lt_mul hn).mpr hx2
  have hb1 : x1 % n < n := Nat.mod_lt _ hn
  have hb2 : x2 % n < n := Nat.mod_lt _ hn
  have hab : x1 / n ≠ x2 / n ∧ x1 % n ≠ x2 % n := by unfold conf at hc; omega
  have e1 := var_decode n x1; have e2 := var_decode n x2
  have hpair : (Ext F u).E (fun a => monoEval a [x1, x2]) = F.E (fun a => monoEval a [x1, x2]) :=
    E_pair F u hF _ (by simp; omega) x1 x2 (fun _ => Iff.rfl)
  have hz : F.E (fun a => monoEval a [x1, x2]) = zz F n x1 x2 := by unfold zz; rw [if_neg hc]
  -- the new pigeon is the pigeon of x1 or x2
  have side : ∀ y1 y2 : Nat, y1 < N → y2 < N → (∀ x, x ∈ [y1, y2] ↔ x ∈ [x1, x2]) → i = y1 / n →
      (p : Int) ∣ rsum n (fun j => (Ext F u).E (fun a => monoEval a [x1, x2, var n i j])) - F.E (fun a => monoEval a [x1, x2]) := by
    intro y1 y2 hy1 hy2 hy hiy
    have ey := var_decode n y1
    have hby : y1 % n < n := Nat.mod_lt _ hn
    apply rsum_pick_dvd n (y1 % n) hby
    intro j hj
    by_cases hjb : j = y1 % n
    · rw [if_pos hjb]
      have hv : var n i j = y1 := by rw [hjb, hiy, ey]
      rw [hv, E_pair F u hF [x1, x2, y1] (by simp; omega) x1 x2 (fun x => by have := hy x; simp at this ⊢; omega),
        Int.sub_self]
      exact ⟨0, by simp⟩
    · rw [if_neg hjb, Int.sub_zero]
      have hy1m : y1 ∈ [x1, x2, var n i j] := by have := (hy y1).mp (by simp); simp at this ⊢; omega
      refine E_conf F u hF hn _ (by simp; exact ⟨hx1, hx2, hvl j hj⟩) (by simp) y1 (var n i j) hy1m (by simp) ⟨?_, Or.inl ?_⟩
      · intro h; apply hjb; rw [h, var_mod n _ _ hj]
      · rw [var_div n _ _ hj, hiy]
  by_cases hi1 : i = x1 / n
  · rw [hpair]; exact side x1 x2 hx1 hx2 (fun _ => Iff.rfl) hi1
  by_cases hi2 : i = x2 / n
  · rw [hpair]; exact side x2 x1 hx2 hx1 (fun x => by simp; omega) hi2
  -- main case: a new pigeon
  have hthree : ∀ j < n, (Ext F u).E (fun a => monoEval a [x1, x2, var n i j]) =
      if j = x1 % n ∨ j = x2 % n then 0 else
        u * S3 n (cc F) (yy F) (zz F n) (x1 / n) (x2 / n) i (x1 % n) (x2 % n) j := by
    intro j hj
    have h1 : x1 ≠ var n i j := fun h => hi1 (by rw [h, var_div n _ _ hj])
    have h2 : x2 ≠ var n i j := fun h => hi2 (by rw [h, var_div n _ _ hj])
    have hd : [x1, x2, var n i j].Nodup := by simp [heq, h1, h2]
    rw [E_three F u _ _ _ hd (by simp; exact ⟨hx1, hx2, hvl j hj⟩)]
    have hM : isM n x1 x2 (var n i j) ↔ ¬ (j = x1 % n ∨ j = x2 % n) := by
      unfold isM; rw [var_div n _ _ hj, var_mod n _ _ hj]; omega
    unfold W3
    by_cases hj' : j = x1 % n ∨ j = x2 % n
    · rw [if_pos hj', if_neg (fun h => (hM.mp h) hj')]
    · rw [if_neg hj', if_pos (hM.mpr hj'), var_div n _ _ hj, var_mod n _ _ hj]
  rw [rsum_congr n _ _ hthree, rsum_skip2 n _ _ hb1 hb2 hab.2, hpair, hz]
  -- sums of the six orderings
  generalize x1 / n = a1 at *
  generalize x2 / n = a2 at *
  generalize x1 % n = b1 at *
  generalize x2 % n = b2 at *
  subst e1 e2
  have hzs := zz_symm F n
  have s1 := pos3 n (cc F) (yy F) (zz F n) (n + k) (hR2 F hF hn) a1 a2 b1 b2 ha2
  have s2 := pos2 n (cc F) (yy F) (zz F n) hzs (n + k) (hR1 F hF hn) (hR2 F hF hn) a1 i b1 b2 hi ha1
  have s3 := pos3 n (cc F) (yy F) (zz F n) (n + k) (hR2 F hF hn) a2 a1 b2 b1 ha1
  have s4 := pos2 n (cc F) (yy F) (zz F n) hzs (n + k) (hR1 F hF hn) (hR2 F hF hn) a2 i b2 b1 hi ha2
  have s5 := pos1 n (cc F) (yy F) (zz F n) hzs (n + k) (hR1 F hF hn) (hR2 F hF hn) i a1 b1 b2 hi ha1
  have s6 := pos1 n (cc F) (yy F) (zz F n) hzs (n + k) (hR1 F hF hn) (hR2 F hF hn) i a2 b2 b1 hi ha2
  have hid := pig_ident n (cc F) (yy F) (zz F n) hzs (fun a a' b hb h => zz_cp F n a a' b hb h)
    (fun a b b' hb hb' h => zz_ch F n a b b' hb hb' h) a1 a2 i b1 b2 hab.1 (Ne.symm hi1) (Ne.symm hi2) hab.2 hb1 hb2
  have hsum : rsum n (fun j => S3 n (cc F) (yy F) (zz F n) a1 a2 i b1 b2 j) =
      rsum n (fun j => Gp n (cc F) (yy F) (zz F n) a1 a2 b1 b2 j) + rsum n (fun j => Gp n (cc F) (yy F) (zz F n) a1 i b1 j b2) +
      rsum n (fun j => Gp n (cc F) (yy F) (zz F n) a2 a1 b2 b1 j) + rsum n (fun j => Gp n (cc F) (yy F) (zz F n) a2 i b2 j b1) +
      rsum n (fun j => Gp n (cc F) (yy F) (zz F n) i a1 j b1 b2) + rsum n (fun j => Gp n (cc F) (yy F) (zz F n) i a2 j b2 b1) := by
    unfold S3; simp only [rsum_add]
  rw [← rsum_cmul]
  have hT := Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add s1 s2) s3) s4) s5) s6
  have hT' : (p : Int) ∣ rsum n (fun j => S3 n (cc F) (yy F) (zz F n) a1 a2 i b1 b2 j) -
      (R3 n (cc F) (yy F) (zz F n) a1 a2 b1 b2 + R2 n (cc F) (yy F) (zz F n) a1 i b1 b2 +
        R3 n (cc F) (yy F) (zz F n) a2 a1 b2 b1 + R2 n (cc F) (yy F) (zz F n) a2 i b2 b1 +
        R1 n (cc F) (yy F) (zz F n) i a1 b1 b2 + R1 n (cc F) (yy F) (zz F n) i a2 b2 b1) := by
    refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mp hT
    exact ⟨0, by rw [hsum]; unfold R3 R2 R1; grind⟩
  obtain ⟨q, hq⟩ := hu
  have hfin := Int.dvd_add (dvd_cmul u hT') (⟨q * zz F n (var n a1 b1) (var n a2 b2), rfl⟩ :
    (p : Int) ∣ (p : Int) * (q * zz F n (var n a1 b1) (var n a2 b2)))
  refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mp hfin
  refine ⟨0, ?_⟩
  rw [Int.mul_zero]
  have e3 : (p : Int) * (q * zz F n (var n a1 b1) (var n a2 b2)) = (u * M3 n - 1) * zz F n (var n a1 b1) (var n a2 b2) := by
    rw [← Int.mul_assoc, ← hq]
  rw [e3]
  grind

theorem hole3 (hn : 0 < n) (hk : (p : Int) ∣ (k : Int)) (hu : (p : Int) ∣ u * M3 n - 1) (j : Nat) (hj : j < n)
    (x1 x2 : Nat) :
    (p : Int) ∣ (Ext F u).E (fun a => monoEval a [x1, x2] * (sumOne (fun i => var n i j) (n + k)).eval a) := by
  let N := (n + k) * n
  by_cases hN : x1 < N ∧ x2 < N
  case neg =>
    have : (Ext F u).E (fun a => monoEval a [x1, x2] * (sumOne (fun i => var n i j) (n + k)).eval a) =
        (Ext F u).E (fun _ => 0) := by
      apply (Ext F u).supp; intro a ha
      by_cases h1 : x1 < N
      · rw [monoEval_zero ha _ x2 (by simp) (by omega), Int.zero_mul]
      · rw [monoEval_zero ha _ x1 (by simp) (by omega), Int.zero_mul]
    rw [this]; exact (Ext F u).zero
  obtain ⟨hx1, hx2⟩ := hN
  by_cases heq : x1 = x2
  · subst heq
    have e : (fun a => monoEval a [x1, x1] * (sumOne (fun i => var n i j) (n + k)).eval a) =
        fun a => monoEval a [x1] * (sumOne (fun i => var n i j) (n + k)).eval a := by
      funext a; rw [monoEval_congr a [x1, x1] [x1] (fun x => by simp)]
    rw [e]
    exact low_kill (D := 3) hF (E_extends F u) (mem_hole hj)
      (by have := sumOne_deg (fun i => var n i j) (n + k); simp; omega)
  have hsplit := E_rsum F u (n + k) (fun i a => monoEval a [x1, x2, var n i j]) (fun a => monoEval a [x1, x2])
  have e0 : (fun a => monoEval a [x1, x2] * (sumOne (fun i => var n i j) (n + k)).eval a) =
      fun a => rsum (n + k) (fun i => monoEval a [x1, x2, var n i j]) - monoEval a [x1, x2] := by
    funext a; rw [mono_split]; simp
  rw [e0, hsplit]
  have hvl : ∀ i < n + k, var n i j < N := fun i hi => var_lt n k i j hi hj
  by_cases hc : conf n x1 x2
  · apply Int.dvd_sub
    · exact rsum_dvd _ _ _ (fun i hi => E_conf F u hF hn _ (by simp; exact ⟨hx1, hx2, hvl i hi⟩) (by simp) x1 x2
        (by simp) (by simp) hc)
    · exact E_conf F u hF hn _ (by simp; omega) (by simp) x1 x2 (by simp) (by simp) hc
  have ha1 : x1 / n < n + k := (Nat.div_lt_iff_lt_mul hn).mpr hx1
  have ha2 : x2 / n < n + k := (Nat.div_lt_iff_lt_mul hn).mpr hx2
  have hb1 : x1 % n < n := Nat.mod_lt _ hn
  have hb2 : x2 % n < n := Nat.mod_lt _ hn
  have hab : x1 / n ≠ x2 / n ∧ x1 % n ≠ x2 % n := by unfold conf at hc; omega
  have e1 := var_decode n x1; have e2 := var_decode n x2
  have hpair : (Ext F u).E (fun a => monoEval a [x1, x2]) = F.E (fun a => monoEval a [x1, x2]) :=
    E_pair F u hF _ (by simp; omega) x1 x2 (fun _ => Iff.rfl)
  have hz : F.E (fun a => monoEval a [x1, x2]) = zz F n x1 x2 := by unfold zz; rw [if_neg hc]
  have side : ∀ y1 y2 : Nat, y1 < N → y2 < N → (∀ x, x ∈ [y1, y2] ↔ x ∈ [x1, x2]) → j = y1 % n →
      (p : Int) ∣ rsum (n + k) (fun i => (Ext F u).E (fun a => monoEval a [x1, x2, var n i j])) -
        F.E (fun a => monoEval a [x1, x2]) := by
    intro y1 y2 hy1 hy2 hy hjy
    have ey := var_decode n y1
    have hay : y1 / n < n + k := (Nat.div_lt_iff_lt_mul hn).mpr hy1
    apply rsum_pick_dvd (n + k) (y1 / n) hay
    intro i hi
    by_cases hia : i = y1 / n
    · rw [if_pos hia]
      have hv : var n i j = y1 := by rw [hia, hjy, ey]
      rw [hv, E_pair F u hF [x1, x2, y1] (by simp; omega) x1 x2 (fun x => by have := hy x; simp at this ⊢; omega),
        Int.sub_self]
      exact ⟨0, by simp⟩
    · rw [if_neg hia, Int.sub_zero]
      have hy1m : y1 ∈ [x1, x2, var n i j] := by have := (hy y1).mp (by simp); simp at this ⊢; omega
      refine E_conf F u hF hn _ (by simp; exact ⟨hx1, hx2, hvl i hi⟩) (by simp) y1 (var n i j) hy1m (by simp) ⟨?_, Or.inr ?_⟩
      · intro h; apply hia; rw [h, var_div n _ _ hj]
      · rw [var_mod n _ _ hj, hjy]
  by_cases hj1 : j = x1 % n
  · rw [hpair]; exact side x1 x2 hx1 hx2 (fun _ => Iff.rfl) hj1
  by_cases hj2 : j = x2 % n
  · rw [hpair]; exact side x2 x1 hx2 hx1 (fun x => by simp; omega) hj2
  have hthree : ∀ i < n + k, (Ext F u).E (fun a => monoEval a [x1, x2, var n i j]) =
      if i = x1 / n ∨ i = x2 / n then 0 else
        u * S3 n (cc F) (yy F) (zz F n) (x1 / n) (x2 / n) i (x1 % n) (x2 % n) j := by
    intro i hi
    have h1 : x1 ≠ var n i j := fun h => hj1 (by rw [h, var_mod n _ _ hj])
    have h2 : x2 ≠ var n i j := fun h => hj2 (by rw [h, var_mod n _ _ hj])
    have hd : [x1, x2, var n i j].Nodup := by simp [heq, h1, h2]
    rw [E_three F u _ _ _ hd (by simp; exact ⟨hx1, hx2, hvl i hi⟩)]
    have hM : isM n x1 x2 (var n i j) ↔ ¬ (i = x1 / n ∨ i = x2 / n) := by
      unfold isM; rw [var_div n _ _ hj, var_mod n _ _ hj]; omega
    unfold W3
    by_cases hi' : i = x1 / n ∨ i = x2 / n
    · rw [if_pos hi', if_neg (fun h => (hM.mp h) hi')]
    · rw [if_neg hi', if_pos (hM.mpr hi'), var_div n _ _ hj, var_mod n _ _ hj]
  rw [rsum_congr (n + k) _ _ hthree, rsum_skip2 (n + k) _ _ ha1 ha2 hab.1, hpair, hz]
  generalize x1 / n = a1 at *
  generalize x2 / n = a2 at *
  generalize x1 % n = b1 at *
  generalize x2 % n = b2 at *
  subst e1 e2
  have hzs := zz_symm F n
  have s1 := pos3h n (cc F) (yy F) (zz F n) k hk a1 a2 b1 b2 j
  have s2 := pos2h n (cc F) (yy F) (zz F n) k hk (hC1 F hF) (hC2 F hF hn) a1 b1 j b2 hj hb2 hb1
  have s3 := pos3h n (cc F) (yy F) (zz F n) k hk a2 a1 b2 b1 j
  have s4 := pos2h n (cc F) (yy F) (zz F n) k hk (hC1 F hF) (hC2 F hF hn) a2 b2 j b1 hj hb1 hb2
  have s5 := pos1h n (cc F) (yy F) (zz F n) hzs k hk (hC1 F hF) (hC2 F hF hn) a1 j b1 b2 hj hb1
  have s6 := pos1h n (cc F) (yy F) (zz F n) hzs k hk (hC1 F hF) (hC2 F hF hn) a2 j b2 b1 hj hb2
  have hid := hole_ident n (cc F) (yy F) (zz F n) hzs (fun a a' b hb h => zz_cp F n a a' b hb h)
    (fun a b b' hb hb' h => zz_ch F n a b b' hb hb' h) a1 a2 b1 b2 j hab.1 hab.2 (Ne.symm hj1) (Ne.symm hj2) hb1 hb2 hj
  have hsum : rsum (n + k) (fun i => S3 n (cc F) (yy F) (zz F n) a1 a2 i b1 b2 j) =
      rsum (n + k) (fun _ => Gp n (cc F) (yy F) (zz F n) a1 a2 b1 b2 j) +
      rsum (n + k) (fun i => Gp n (cc F) (yy F) (zz F n) a1 i b1 j b2) +
      rsum (n + k) (fun _ => Gp n (cc F) (yy F) (zz F n) a2 a1 b2 b1 j) +
      rsum (n + k) (fun i => Gp n (cc F) (yy F) (zz F n) a2 i b2 j b1) +
      rsum (n + k) (fun i => Gp n (cc F) (yy F) (zz F n) i a1 j b1 b2) +
      rsum (n + k) (fun i => Gp n (cc F) (yy F) (zz F n) i a2 j b2 b1) := by
    unfold S3; simp only [rsum_add]
  rw [← rsum_cmul]
  have hT := Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add s1 s2) s3) s4) s5) s6
  have hT' : (p : Int) ∣ rsum (n + k) (fun i => S3 n (cc F) (yy F) (zz F n) a1 a2 i b1 b2 j) -
      ((n : Int) * Gp n (cc F) (yy F) (zz F n) a1 a2 b1 b2 j + R2h n (cc F) (yy F) a1 b1 j +
        (n : Int) * Gp n (cc F) (yy F) (zz F n) a2 a1 b2 b1 j + R2h n (cc F) (yy F) a2 b2 j +
        R1h n (cc F) (yy F) a1 j b1 b2 + R1h n (cc F) (yy F) a2 j b2 b1) := by
    refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mp hT
    exact ⟨0, by rw [hsum]; unfold R2h R1h; grind⟩
  obtain ⟨q, hq⟩ := hu
  have hfin := Int.dvd_add (dvd_cmul u hT') (⟨q * zz F n (var n a1 b1) (var n a2 b2), rfl⟩ :
    (p : Int) ∣ (p : Int) * (q * zz F n (var n a1 b1) (var n a2 b2)))
  refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mp hfin
  refine ⟨0, ?_⟩
  rw [Int.mul_zero]
  have e3 : (p : Int) * (q * zz F n (var n a1 b1) (var n a2 b2)) = (u * M3 n - 1) * zz F n (var n a1 b1) (var n a2 b2) := by
    rw [← Int.mul_assoc, ← hq]
  rw [e3]
  grind

/-- Collision and functional axioms at level 3. -/
theorem prod3 (hn : 0 < n) (x v w : Nat) (hv : v < (n + k) * n) (hw : w < (n + k) * n) (hc : conf n v w) :
    (p : Int) ∣ (Ext F u).E (fun a => monoEval a [x] * (prod2 v w).eval a) := by
  have e : (fun a => monoEval a [x] * (prod2 v w).eval a) = fun a => monoEval a [x, v, w] := by
    funext a; rw [prod2_eval]; simp [monoEval, xv]
  rw [e]
  by_cases hx : x < (n + k) * n
  · exact E_conf F u hF hn _ (by simp; omega) (by simp) v w (by simp) (by simp) hc
  · rw [E_vanish F u _ x (by simp) (by omega)]; exact (Ext F u).zero

/-- **Extension.** -/
theorem ext3 (hn : 0 < n) (hk : (p : Int) ∣ (k : Int)) (hu : (p : Int) ∣ u * M3 n - 1) :
    IsDesign (ontoFPHP n k) 3 (Ext F u) := by
  intro P hP m hm
  by_cases hlow : m.length + P.deg ≤ 2
  · exact low_kill (D := 3) hF (E_extends F u) hP hlow
  rcases mem_ontoFPHP hP with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩ | hc | hf
  · have h1 := sumOne_deg (fun j => var n i j) n
    match m, hm with
    | [x1, x2], _ => exact pig3 F u hF hn hu i hi x1 x2
    | [], _ => simp at hlow; omega
    | [_], _ => simp at hlow; omega
    | _ :: _ :: _ :: _, hm => have := sumOne_deg_pos (fun j => var n i j) n hn; simp at hm; omega
  · have h1 := sumOne_deg (fun i => var n i j) (n + k)
    match m, hm with
    | [x1, x2], _ => exact hole3 F u hF hn hk hu j hj x1 x2
    | [], _ => simp at hlow; omega
    | [_], _ => simp at hlow; omega
    | _ :: _ :: _ :: _, hm => have := sumOne_deg_pos (fun i => var n i j) (n + k) (by omega); simp at hm; omega
  · obtain ⟨j, i, i', hj, hi, hi', hii, rfl⟩ := mem_collAx.mp hc
    rw [prod2_deg] at hm hlow
    match m, hm with
    | [x], _ =>
      refine prod3 F u hF hn x _ _ (var_lt n k i j hi hj) (var_lt n k i' j hi' hj) ⟨fun h => ?_, Or.inr ?_⟩
      · have := (var_inj n _ _ _ _ hj hj h).1; omega
      · rw [var_mod n _ _ hj, var_mod n _ _ hj]
    | [], _ => simp at hlow
    | _ :: _ :: _, hm => simp at hm
  · obtain ⟨i, j, j', hi, hj, hj', hjj, rfl⟩ := mem_funcAx.mp hf
    rw [prod2_deg] at hm hlow
    match m, hm with
    | [x], _ =>
      refine prod3 F u hF hn x _ _ (var_lt n k i j hi hj) (var_lt n k i j' hi hj') ⟨fun h => ?_, Or.inl ?_⟩
      · have := (var_inj n _ _ _ _ hj hj' h).2; omega
      · rw [var_div n _ _ hj, var_div n _ _ hj']
    | [], _ => simp at hlow
    | _ :: _ :: _, hm => simp at hm

end

/-! ## No degree-3 refutation -/

open Programme.«20261025-1627-proof-complexity».OntoExt2 (momFn mom mom_mono0 mom_mono1 mom_terms) in
/-- The symmetric degree-1 design `c = 1`, `y ≡ 1/n` (as in `Work.OntoExt2`). -/
theorem base1 (n k : Nat) (hn : 0 < n) (hk : (p : Int) ∣ (k : Int)) (u : Int)
    (hu : (p : Int) ∣ u * ((n : Int) * ((n : Int) - 1) * ((n : Int) - 2)) - 1) :
    IsDesign (ontoFPHP n k) 1 (momFn p ((n + k) * n) 1 (fun _ => u * ((n : Int) - 1) * ((n : Int) - 2)) (fun _ _ => 0)) := by
  let N := (n + k) * n
  let w : Int := u * ((n : Int) - 1) * ((n : Int) - 2)
  have hsum : ∀ (v : Nat → Nat) (m : Nat), (∀ j < m, v j < N) →
      mom N 1 (fun _ => w) (fun _ _ => 0) (fun a => monoEval a [] * (sumOne v m).eval a) = -1 + (m : Int) * w := by
    intro v m hv
    have e : (fun a => monoEval a [] * (sumOne v m).eval a) =
        fun a => ((sumOne v m).terms.map fun t => t.1 * monoEval a t.2).sum := by
      funext a; simp [monoEval, Poly.eval]
    rw [e, mom_terms]
    have hl := linTerms_sum v m (fun l => mom N 1 (fun _ => w) (fun _ _ => 0) (fun a => monoEval a l))
    simp only [sumOne, List.map_cons, List.sum_cons, hl, mom_mono0]
    rw [rsum_congr m _ (fun _ => w) (fun j hj => by rw [mom_mono1, if_pos (hv j hj)])]
    rw [rsum_const]; omega
  intro P hP m hm
  rcases mem_ontoFPHP hP with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩ | hc | hf
  · have h2 := sumOne_deg_pos (fun j => var n i j) n hn
    match m, hm with
    | [], _ =>
      show (p : Int) ∣ mom N 1 (fun _ => w) (fun _ _ => 0) _
      rw [hsum _ _ (fun j hj => var_lt n k i j hi hj)]
      obtain ⟨q, hq⟩ := hu
      exact ⟨q, by grind⟩
    | _ :: _, hm => simp at hm; omega
  · have h2 := sumOne_deg_pos (fun i => var n i j) (n + k) (by omega)
    match m, hm with
    | [], _ =>
      show (p : Int) ∣ mom N 1 (fun _ => w) (fun _ _ => 0) _
      rw [hsum _ _ (fun i hi => var_lt n k i j hi hj)]
      obtain ⟨q, hq⟩ := hu
      obtain ⟨q', hq'⟩ := hk
      exact ⟨q + q' * w, by push_cast; grind⟩
    | _ :: _, hm => simp at hm; omega
  · obtain ⟨_, _, _, _, _, _, _, rfl⟩ := mem_collAx.mp hc
    rw [prod2_deg] at hm; omega
  · obtain ⟨_, _, _, _, _, _, _, rfl⟩ := mem_funcAx.mp hf
    rw [prod2_deg] at hm; omega

open Programme.«20261025-1627-proof-complexity».OntoExt2 (momFn mom mom_mono0) in
/-- **No degree-3 refutation.** For `p > 1`, `p ∣ k`, `n > 0`, `6n(n-1)(n-2)(n-3)(n-4)` and
`n(n-1)(n-2)` invertible mod `p`: `onto-FPHP^{n+k}_n` has no degree-3 PC refutation over `Z/p`. -/
theorem ontoFPHP_no_deg3 (n k : Nat) (hp : 1 < p) (hn : 0 < n) (hk : (p : Int) ∣ (k : Int)) (u u2 : Int)
    (hu : (p : Int) ∣ u * M3 n - 1)
    (hu2 : (p : Int) ∣ u2 * ((n : Int) * ((n : Int) - 1) * ((n : Int) - 2)) - 1) :
    ¬ PPCRefutation p (ontoFPHP n k) 3 := by
  let E0 := momFn p ((n + k) * n) 1 (fun _ => u2 * ((n : Int) - 1) * ((n : Int) - 2)) (fun _ _ => 0)
  have h0 : IsDesign (ontoFPHP n k) 1 E0 := base1 n k hn hk u2 hu2
  obtain ⟨E1, hE1, hx1⟩ := Programme.«20261025-1627-proof-complexity».OntoExt2.ext2 n k hn hk u2 hu2 E0 h0
  have h1 : ¬ (p : Int) ∣ E1.E (fun _ => 1) := by
    intro h
    have a := hx1 [] (by simp)
    have e : (fun a => monoEval a ([] : List Nat)) = fun _ => (1 : Int) := by funext a; simp [monoEval]
    rw [e] at a
    have hE0 : E0.E (fun _ => 1) = 1 := by
      show mom _ 1 _ _ (fun _ => 1) = 1
      rw [← e, mom_mono0]
    rw [hE0] at a
    have := Int.dvd_sub h a
    rw [show E1.E (fun _ => 1) - (E1.E (fun _ => 1) - 1) = 1 by omega] at this
    exact not_dvd_one hp this
  exact ext_sound (D := 3) (by decide) (fun F hF => ⟨Ext F u, ext3 F u hF hn hk hu, E_extends F u⟩) E1 hE1 h1

/-- With restriction (K83): for `p > 1` coprime to `30` (`720` invertible mod `p`) and `p ∣ k`,
onto-FPHP^{n+k}_n has no PC refutation of degree `≤ 3` over `Z/p`, for every `n ≥ 5`. -/
theorem ontoFPHP_no_deg3_all (n k D : Nat) (hp : 1 < p) (hk : (p : Int) ∣ (k : Int))
    (h720 : ∃ u : Int, (p : Int) ∣ 720 * u - 1) (hn : 5 ≤ n) (hD : D ≤ 3) :
    ¬ PPCRefutation p (ontoFPHP n k) D := by
  intro h
  have h3 : PPCRefutation p (ontoFPHP n k) 3 :=
    Programme.«20261025-0459-proof-complexity».OntoPCLower.PPCDerivable.mono hD h
  obtain ⟨u, hu⟩ := h720
  have base := ontoFPHP_no_deg3 (p := p) 5 k hp (by decide) hk u (12 * u)
    (by have e : u * M3 5 - 1 = 720 * u - 1 := by unfold M3; push_cast; grind
        rw [e]; exact hu)
    (by have e : 12 * u * (((5 : Nat) : Int) * (((5 : Nat) : Int) - 1) * (((5 : Nat) : Int) - 2)) - 1 = 720 * u - 1 := by
          push_cast; grind
        rw [e]; exact hu)
  apply base
  clear h
  obtain ⟨d, rfl⟩ : ∃ d, n = 5 + d := ⟨n - 5, by omega⟩
  clear hn
  induction d with
  | zero => exact h3
  | succ d ih =>
    apply ih
    exact Programme.«20261025-0459-proof-complexity».OntoSubst.ontoFPHP_restrict p (5 + d) k 3
      (by decide) (by omega) (by rwa [show 5 + d + 1 = 5 + (d + 1) by omega])

end Programme.«20261025-1627-proof-complexity».OntoExt3

#print axioms Programme.«20261025-1627-proof-complexity».OntoExt3.ontoFPHP_no_deg3
#print axioms Programme.«20261025-1627-proof-complexity».OntoExt3.ontoFPHP_no_deg3_all
