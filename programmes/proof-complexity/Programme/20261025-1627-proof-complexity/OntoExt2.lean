import Programme.«20261025-1627-proof-complexity».DesignExt
import Programme.«20261025-1627-proof-complexity».PCCertCore
import Programme.«20261025-0459-proof-complexity».OntoSubst
import Programme.«20261025-0459-proof-complexity».OntoPCLower

/-!
# Degree-2 design extension for onto-FPHP when `n(n-1)(n-2)` is invertible mod `p`

Moment functional `mom N c y z`: `g ↦ c·cf g ∅ + ∑_v y_v cf g {v} + ∑_{w<v} z_{wv} cf g {w,v}`
(variables `< N`). Given a degree-1 design `F` of `ontoFPHP n k` with moments `c = F(1)`,
`y_v = F(x_v)`, the degree-2 moments on a matching pair `e = (a,b)`, `f = (c,d)` are
`z(e,f) = α(y_e + y_f) + β(y_{(a,d)} + y_{(c,b)}) + γ c` with
`α = (n-1)²u`, `β = (n-1)u`, `γ = -nu`, `u·n(n-1)(n-2) ≡ 1`, and `0` on non-matching pairs.
The pigeon identity `∑_{d≠b} z(e,(c,d)) = y_e` uses only the degree-1 design equations; the hole
identity uses in addition `p ∣ k`. With `Work.DesignExt.ext_sound`: no degree-2 PC refutation.
-/

namespace Programme.«20261025-1627-proof-complexity».OntoExt2

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».FinDiff
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero prod2_eval mem_ontoFPHP
  mem_collAx mem_funcAx var_div var_mod prod2_deg mem_pig mem_hole)
open Programme.«20261025-1627-proof-complexity».PCCertCore (cf_mono sameSet sameSet_iff)
open Programme.«20261025-1627-proof-complexity».DesignExt

/-- Points with every variable `≥ N` false. -/
def SN (N : Nat) (a : Nat → Bool) : Prop := ∀ v, N ≤ v → a v = false

def mom (N : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) (g : (Nat → Bool) → Int) : Int :=
  c * cf g [] + rsum N (fun v => y v * cf g [v]) + rsum N (fun v => rsum v (fun w => z w v * cf g [w, v]))

theorem rsum_lin (m : Nat) (f g : Nat → Int) (s t : Int) :
    rsum m (fun i => s * f i + t * g i) = s * rsum m f + t * rsum m g := by
  induction m with
  | zero => simp [rsum]
  | succ m ih => simp only [rsum, ih]; grind

@[simp] theorem rsum_zero' (m : Nat) : rsum m (fun _ => (0 : Int)) = 0 := rsum_zero m _ (fun _ _ => rfl)

theorem rsum_dvd (p : Int) (m : Nat) (f : Nat → Int) (h : ∀ i < m, p ∣ f i) : p ∣ rsum m f := by
  induction m with
  | zero => exact ⟨0, by simp [rsum]⟩
  | succ m ih => exact Int.dvd_add (ih (fun i hi => h i (by omega))) (h m (by omega))

theorem mom_lin (N : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) (f g : (Nat → Bool) → Int)
    (s t : Int) : mom N c y z (fun a => s * f a + t * g a) = s * mom N c y z f + t * mom N c y z g := by
  unfold mom
  simp only [cf_lin]
  have h1 : rsum N (fun v => y v * (s * cf f [v] + t * cf g [v])) =
      s * rsum N (fun v => y v * cf f [v]) + t * rsum N (fun v => y v * cf g [v]) := by
    rw [← rsum_lin]; exact rsum_congr _ _ _ (fun i _ => by grind)
  have h2 : rsum N (fun v => rsum v (fun w => z w v * (s * cf f [w, v] + t * cf g [w, v]))) =
      s * rsum N (fun v => rsum v (fun w => z w v * cf f [w, v])) +
      t * rsum N (fun v => rsum v (fun w => z w v * cf g [w, v])) := by
    rw [← rsum_lin]; refine rsum_congr _ _ _ (fun i _ => ?_)
    rw [← rsum_lin]; exact rsum_congr _ _ _ (fun j _ => by grind)
  rw [h1, h2]; grind

theorem mom_zero (N : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) :
    mom N c y z (fun _ => 0) = 0 := by
  have := mom_lin N c y z (fun _ => 0) (fun _ => 0) 0 0
  simpa using this

theorem mom_sub (N : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) (f g : (Nat → Bool) → Int) :
    mom N c y z (fun a => f a - g a) = mom N c y z f - mom N c y z g := by
  have := mom_lin N c y z f g 1 (-1)
  have e : (fun a => 1 * f a + -1 * g a) = fun a => f a - g a := by funext a; omega
  rw [e] at this; rw [this]; omega

theorem mom_rsum (N : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) (m : Nat)
    (G : Nat → (Nat → Bool) → Int) :
    mom N c y z (fun a => rsum m (fun j => G j a)) = rsum m (fun j => mom N c y z (G j)) := by
  induction m with
  | zero => exact mom_zero N c y z
  | succ m ih =>
    have := mom_lin N c y z (fun a => rsum m (fun j => G j a)) (G m) 1 1
    simp only [Int.one_mul] at this
    simp only [rsum]; rw [this, ih]

theorem mom_terms (N : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) (L : List (Int × List Nat)) :
    mom N c y z (fun a => (L.map fun t => t.1 * monoEval a t.2).sum) =
      (L.map fun t => t.1 * mom N c y z (fun a => monoEval a t.2)).sum := by
  induction L with
  | nil => exact mom_zero N c y z
  | cons t L ih =>
    have := mom_lin N c y z (fun a => monoEval a t.2) (fun a => (L.map fun t => t.1 * monoEval a t.2).sum) t.1 1
    simp only [Int.one_mul] at this
    simp only [List.map_cons, List.sum_cons]; rw [this, ih]

theorem dt_supp (N : Nat) (f g : (Nat → Bool) → Int) (h : ∀ b, SN N b → f b = g b) :
    ∀ t : List Nat, (∀ x ∈ t, x < N) → ∀ a, SN N a → dt t f a = dt t g a := by
  intro t
  induction t with
  | nil => intro _ a ha; exact h a ha
  | cons x t ih =>
    intro ht a ha
    have hx := ht x List.mem_cons_self
    have ht' : ∀ w ∈ t, w < N := fun w hw => ht w (List.mem_cons_of_mem _ hw)
    have hu : ∀ b, SN N (upd a x b) := by
      intro b v hv; simp only [upd]; rw [if_neg (by omega)]; exact ha v hv
    simp only [dt, dlt]; rw [ih ht' _ (hu true), ih ht' _ (hu false)]

theorem mom_supp (N : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) (f g : (Nat → Bool) → Int)
    (h : ∀ b, SN N b → f b = g b) : mom N c y z f = mom N c y z g := by
  have hz : SN N z0 := fun _ _ => rfl
  have e := fun t ht => dt_supp N f g h t ht z0 hz
  unfold mom cf
  rw [e [] (by simp)]
  rw [rsum_congr N (fun v => y v * dt [v] f z0) (fun v => y v * dt [v] g z0)
    (fun i hi => by rw [e [i] (by simpa using hi)])]
  rw [rsum_congr N (fun v => rsum v (fun w => z w v * dt [w, v] f z0)) (fun v => rsum v (fun w => z w v * dt [w, v] g z0))
    (fun i hi => rsum_congr _ _ _ (fun j hj => by rw [e [j, i] (by simp; omega)]))]

theorem mom_congr (p : Nat) (N : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) (f g : (Nat → Bool) → Int)
    (h : ∀ a, (p : Int) ∣ f a - g a) : (p : Int) ∣ mom N c y z f - mom N c y z g := by
  rw [← mom_sub]
  have hc : ∀ t, (p : Int) ∣ cf (fun a => f a - g a) t := by
    intro t
    have e : (fun a => f a - g a) = fun a => 1 * f a + (-1) * g a := by funext a; omega
    rw [e, cf_lin]
    have := cf_congr p f g h t
    rwa [show 1 * cf f t + -1 * cf g t = cf f t - cf g t by omega]
  unfold mom
  exact Int.dvd_add (Int.dvd_add (dvd_cmul _ (hc [])) (rsum_dvd _ _ _ (fun i _ => dvd_cmul _ (hc [i]))))
    (rsum_dvd _ _ _ (fun i _ => rsum_dvd _ _ _ (fun j _ => dvd_cmul _ (hc [j, i]))))

/-- The moment functional as a `Fn`. -/
def momFn (p N : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) : Fn p (SN N) where
  E := mom N c y z
  lin f g s t := by rw [mom_lin, Int.sub_self]; exact ⟨0, by simp⟩
  congr f g h := mom_congr p N c y z f g h
  supp f g h := mom_supp N c y z f g h

/-! ## Moments of monomials -/

theorem rsum_pick (m x : Nat) (F : Nat → Int) :
    rsum m (fun v => if v = x then F v else 0) = if x < m then F x else 0 := by
  induction m with
  | zero => simp [rsum]
  | succ m ih =>
    simp only [rsum, ih]
    by_cases h1 : x < m
    · have h2 : m ≠ x := by omega
      have h3 : x < m + 1 := by omega
      simp [h1, h2, h3]
    · by_cases h2 : m = x
      · subst h2; simp
      · have h3 : ¬ x < m + 1 := by omega
        simp [h1, h2, h3]

theorem mom_mono0 (N : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) :
    mom N c y z (fun a => monoEval a []) = c := by
  unfold mom
  rw [cf_mono [] List.nodup_nil [] List.nodup_nil]
  rw [rsum_zero N _ (fun i _ => by rw [cf_mono [] List.nodup_nil [i] (by simp)]; simp [sameSet])]
  rw [rsum_zero N _ (fun i _ => rsum_zero _ _ (fun j hj => by
    rw [cf_mono [] List.nodup_nil [j, i] (by simp; omega)]; simp [sameSet]))]
  simp [sameSet]

theorem mom_mono1 (N : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) (x : Nat) :
    mom N c y z (fun a => monoEval a [x]) = if x < N then y x else 0 := by
  unfold mom
  have hx : [x].Nodup := by simp
  rw [cf_mono [x] hx [] List.nodup_nil]
  rw [rsum_congr N _ (fun v => if v = x then y v else 0) (fun i _ => by
    rw [cf_mono [x] hx [i] (by simp)]; by_cases h : i = x <;> simp [sameSet, h])]
  rw [rsum_zero N (fun v => rsum v (fun w => z w v * cf (fun a => monoEval a [x]) [w, v]))
    (fun i _ => rsum_zero _ _ (fun j hj => by
      rw [cf_mono [x] hx [j, i] (by simp; omega)]
      have : sameSet [j, i] [x] = false := by
        cases h : sameSet [j, i] [x]
        · rfl
        · have := (sameSet_iff _ _).mp h
          have a1 := (this j).mp (by simp); have a2 := (this i).mp (by simp)
          simp at a1 a2; omega
      simp [this]))]
  rw [rsum_pick]; simp [sameSet]

theorem mom_mono2 (N : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) (hz : ∀ a b, z a b = z b a)
    (x x' : Nat) (hne : x ≠ x') :
    mom N c y z (fun a => monoEval a [x, x']) = if x < N ∧ x' < N then z x x' else 0 := by
  unfold mom
  have hx : [x, x'].Nodup := by simp [hne]
  rw [cf_mono [x, x'] hx [] List.nodup_nil]
  rw [rsum_zero N (fun v => y v * cf (fun a => monoEval a [x, x']) [v]) (fun i _ => by
    rw [cf_mono [x, x'] hx [i] (by simp)]
    have : sameSet [i] [x, x'] = false := by
      cases h : sameSet [i] [x, x']
      · rfl
      · have := (sameSet_iff _ _).mp h
        have a1 := (this x).mpr (by simp); have a2 := (this x').mpr (by simp)
        simp at a1 a2; omega
    simp [this])]
  have key : ∀ i j, j < i → z j i * cf (fun a => monoEval a [x, x']) [j, i] =
      (if i = x' then (if j = x then z x x' else 0) else 0) + (if i = x then (if j = x' then z x' x else 0) else 0) := by
    intro i j hji
    rw [cf_mono [x, x'] hx [j, i] (by simp; omega)]
    by_cases h1 : j = x ∧ i = x'
    · obtain ⟨rfl, rfl⟩ := h1
      have : sameSet [j, i] [j, i] = true := (sameSet_iff _ _).mpr (fun _ => Iff.rfl)
      simp [this, hne, Ne.symm hne]
    · by_cases h2 : j = x' ∧ i = x
      · obtain ⟨rfl, rfl⟩ := h2
        have : sameSet [j, i] [i, j] = true := (sameSet_iff _ _).mpr (fun w => by simp; omega)
        simp [this, hne]
      · have : sameSet [j, i] [x, x'] = false := by
          cases h : sameSet [j, i] [x, x']
          · rfl
          · have := (sameSet_iff _ _).mp h
            have a1 := (this j).mp (by simp); have a2 := (this i).mp (by simp)
            have a3 := (this x).mpr (by simp); have a4 := (this x').mpr (by simp)
            simp at a1 a2 a3 a4; omega
        rw [this]
        by_cases h3 : i = x' <;> by_cases h4 : i = x
        · omega
        · have : j ≠ x := by omega
          simp [h3, h4, this, Ne.symm hne]
        · have : j ≠ x' := by omega
          simp [h3, h4, this, hne]
        · simp [h3, h4]
  rw [rsum_congr N _ (fun i => rsum i (fun j => (if i = x' then (if j = x then z x x' else 0) else 0) +
      (if i = x then (if j = x' then z x' x else 0) else 0))) (fun i _ => rsum_congr _ _ _ (fun j hj => key i j hj))]
  rw [rsum_congr N _ (fun i => (if i = x' then rsum i (fun j => if j = x then z x x' else 0) else 0) +
      (if i = x then rsum i (fun j => if j = x' then z x' x else 0) else 0)) (fun i _ => by
        rw [rsum_add]; by_cases h3 : i = x' <;> by_cases h4 : i = x
        · omega
        all_goals first
          | (subst h3; simp [Ne.symm hne, rsum_zero'])
          | (subst h4; simp [hne, rsum_zero'])
          | simp [h3, h4, rsum_zero'])]
  rw [rsum_add, rsum_pick N x' (fun i => rsum i (fun j => if j = x then z x x' else 0)),
    rsum_pick N x (fun i => rsum i (fun j => if j = x' then z x' x else 0)), rsum_pick, rsum_pick, hz x' x]
  simp only [sameSet, List.all_nil, List.all_cons]
  by_cases h1 : x < N <;> by_cases h2 : x' < N <;> by_cases h3 : x < x' <;> simp [h1, h2, h3] <;> omega


/-! ## Sums -/

theorem rsum_kab (m : Nat) (K A B : Int) (f g : Nat → Int) :
    rsum m (fun i => K + A * f i + B * g i) = (m : Int) * K + A * rsum m f + B * rsum m g := by
  induction m with
  | zero => simp [rsum]
  | succ m ih => simp only [rsum, ih]; push_cast; grind

theorem rsum_const (m : Nat) (w : Int) : rsum m (fun _ => w) = (m : Int) * w := by
  induction m with
  | zero => simp [rsum]
  | succ m ih => simp only [rsum, ih]; push_cast; grind

theorem rsum_cmul (m : Nat) (s : Int) (f : Nat → Int) : s * rsum m f = rsum m (fun j => s * f j) := by
  induction m with
  | zero => simp [rsum]
  | succ m ih => simp only [rsum, ← ih]; grind

theorem rsum_skip (m b : Nat) (hb : b < m) (F : Nat → Int) :
    rsum m (fun j => if j = b then 0 else F j) = rsum m F - F b := by
  have h := rsum_pick m b F
  rw [if_pos hb] at h
  have e : rsum m F = rsum m (fun j => if j = b then 0 else F j) + rsum m (fun j => if j = b then F j else 0) := by
    rw [← rsum_add]; exact rsum_congr _ _ _ (fun j _ => by by_cases h : j = b <;> simp [h])
  rw [e, h]; omega

theorem linTerms_sum (v : Nat → Nat) (m : Nat) (G : List Nat → Int) :
    ((linTerms v m).map fun t => t.1 * G t.2).sum = rsum m (fun j => G [v j]) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [linTerms, List.map_append, List.sum_append, ih]
    simp [rsum]

theorem sumOne_deg_pos (v : Nat → Nat) (m : Nat) (hm : 0 < m) : 1 ≤ (sumOne v m).deg := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  unfold Poly.deg
  apply le_foldr_max
  simp only [sumOne, List.map_cons, List.mem_cons, List.mem_map]
  exact Or.inr ⟨(1, [v m']), by simp [linTerms], rfl⟩

theorem var_lt (n k i j : Nat) (hi : i < n + k) (hj : j < n) : var n i j < (n + k) * n := by
  unfold var
  have : (i + 1) * n ≤ (n + k) * n := Nat.mul_le_mul_right _ hi
  rw [Nat.succ_mul] at this; omega

theorem var_decode (n x : Nat) : var n (x / n) (x % n) = x := by
  unfold var; have := Nat.div_add_mod x n; rw [Nat.mul_comm] at this; exact this

theorem var_inj (n i j i' j' : Nat) (hj : j < n) (hj' : j' < n) (h : var n i j = var n i' j') :
    i = i' ∧ j = j' := by
  have h1 := var_div n i j hj; have h2 := var_mod n i j hj
  rw [h] at h1 h2; rw [var_div n i' j' hj'] at h1; rw [var_mod n i' j' hj'] at h2
  exact ⟨h1.symm, h2.symm⟩

theorem mono_vanish {N : Nat} {a : Nat → Bool} (ha : SN N a) {x : Nat} (hx : N ≤ x) (m : List Nat) :
    monoEval a (x :: m) = 0 := by
  simp [monoEval, ha x hx]

/-! ## The degree-2 moments -/

def form (n : Nat) (u c : Int) (y : Nat → Int) (v w : Nat) : Int :=
  ((n : Int) - 1) * ((n : Int) - 1) * u * (y v + y w) +
    ((n : Int) - 1) * u * (y (var n (v / n) (w % n)) + y (var n (w / n) (v % n))) - (n : Int) * u * c

def Z (n : Nat) (u c : Int) (y : Nat → Int) (v w : Nat) : Int :=
  if v / n ≠ w / n ∧ v % n ≠ w % n then form n u c y v w else 0

theorem Z_symm (n : Nat) (u c : Int) (y : Nat → Int) (v w : Nat) : Z n u c y v w = Z n u c y w v := by
  unfold Z
  by_cases h : v / n ≠ w / n ∧ v % n ≠ w % n
  · have h' : w / n ≠ v / n ∧ w % n ≠ v % n := ⟨Ne.symm h.1, Ne.symm h.2⟩
    rw [if_pos h, if_pos h']; unfold form; grind
  · have h' : ¬ (w / n ≠ v / n ∧ w % n ≠ v % n) := fun h' => h ⟨Ne.symm h'.1, Ne.symm h'.2⟩
    rw [if_neg h, if_neg h']

theorem mom_G (N : Nat) (c : Int) (y : Nat → Int) (z : Nat → Nat → Int) (hz : ∀ a b, z a b = z b a)
    (x w : Nat) (hx : x < N) (hw : w < N) :
    mom N c y z (fun a => if w = x then monoEval a [x] else monoEval a [x, w]) =
      if w = x then y x else z x w := by
  by_cases h : w = x
  · simp only [h, if_true]; rw [mom_mono1]; simp [hx]
  · simp only [h, if_false]; rw [mom_mono2 N c y z hz x w (Ne.symm h)]; simp [hx, hw]

theorem split_fun (x : Nat) (m : Nat) (v : Nat → Nat) :
    (fun a => monoEval a [x] * rsum m (fun j => xv (v j) a)) =
      fun a => rsum m (fun j => (fun a => if v j = x then monoEval a [x] else monoEval a [x, v j]) a) := by
  funext a
  have e1 : monoEval a [x] = xv x a := by simp [monoEval, xv]
  rw [e1, rsum_cmul]
  refine rsum_congr _ _ _ (fun j _ => ?_)
  by_cases h : v j = x
  · simp only [h, if_true, e1]; unfold xv; cases a x <;> simp
  · simp only [h, if_false]; simp [monoEval, xv]

variable {p : Nat}

/-- Pigeon identity at `x · P_{i'}`. -/
theorem pig_kill (n k : Nat) (hn : 0 < n) (u c : Int) (y : Nat → Int)
    (hu : (p : Int) ∣ u * ((n : Int) * ((n : Int) - 1) * ((n : Int) - 2)) - 1)
    (hR : ∀ i < n + k, (p : Int) ∣ rsum n (fun j => y (var n i j)) - c)
    (i' x : Nat) (hi' : i' < n + k) (hx : x < (n + k) * n) :
    (p : Int) ∣ mom ((n + k) * n) c y (Z n u c y)
      (fun a => monoEval a [x] * (sumOne (fun j => var n i' j) n).eval a) := by
  have ha0 : x / n < n + k := (Nat.div_lt_iff_lt_mul hn).mpr hx
  have hb0 : x % n < n := Nat.mod_lt _ hn
  have hxv := var_decode n x
  generalize x / n = a0 at ha0 hxv
  generalize x % n = b0 at hb0 hxv
  subst hxv
  have e : (fun a => monoEval a [var n a0 b0] * (sumOne (fun j => var n i' j) n).eval a) =
      fun a => rsum n (fun j => (fun a => if var n i' j = var n a0 b0 then monoEval a [var n a0 b0]
        else monoEval a [var n a0 b0, var n i' j]) a) - monoEval a [var n a0 b0] := by
    funext a
    rw [sumOne_eval, Int.mul_sub, Int.mul_one]
    have := congrFun (split_fun (var n a0 b0) n (fun j => var n i' j)) a
    simp only at this; rw [this]
  rw [e, mom_sub, mom_rsum, mom_mono1, if_pos hx]
  rw [rsum_congr n _ _ (fun j hj => mom_G _ c y _ (Z_symm n u c y) _ _ hx (var_lt n k i' j hi' hj))]
  by_cases hia : i' = a0
  · subst hia
    rw [rsum_congr n _ (fun j => if j = b0 then y (var n i' b0) else 0) (fun j hj => by
      by_cases hjb : j = b0
      · subst hjb; simp
      · have h1 : var n i' j ≠ var n i' b0 := fun h => hjb (var_inj n _ _ _ _ hj hb0 h).2
        rw [if_neg h1, if_neg hjb]; unfold Z
        rw [var_div n _ _ hb0, var_div n _ _ hj]; simp)]
    rw [rsum_pick, if_pos hb0, Int.sub_self]; exact ⟨0, by simp⟩
  · rw [rsum_congr n _ (fun j => if j = b0 then 0 else form n u c y (var n a0 b0) (var n i' j)) (fun j hj => by
      have h1 : var n i' j ≠ var n a0 b0 := fun h => hia (var_inj n _ _ _ _ hj hb0 h).1
      rw [if_neg h1]; unfold Z
      rw [var_div n _ _ hb0, var_div n _ _ hj, var_mod n _ _ hb0, var_mod n _ _ hj]
      by_cases hjb : j = b0
      · subst hjb; simp
      · rw [if_neg hjb, if_pos ⟨Ne.symm hia, Ne.symm hjb⟩])]
    rw [rsum_skip n b0 hb0]
    unfold form
    simp only [var_div n _ _ hb0, var_div n _ _ hb0, var_mod n _ _ hb0]
    rw [rsum_congr n _ (fun j => (((n : Int) - 1) * ((n : Int) - 1) * u * y (var n a0 b0) +
        ((n : Int) - 1) * u * y (var n i' b0) - (n : Int) * u * c) +
        ((n : Int) - 1) * ((n : Int) - 1) * u * y (var n i' j) + ((n : Int) - 1) * u * y (var n a0 j)) (fun j hj => by
      rw [var_div n _ _ hj, var_mod n _ _ hj]; grind)]
    rw [rsum_kab]
    have hRi := hR i' hi'
    have hRa := hR a0 ha0
    generalize rsum n (fun j => y (var n i' j)) = Ri at hRi
    generalize rsum n (fun j => y (var n a0 j)) = Ra at hRa
    obtain ⟨q1, hq1⟩ := hu; obtain ⟨q2, hq2⟩ := hRi; obtain ⟨q3, hq3⟩ := hRa
    refine ⟨q1 * y (var n a0 b0) + ((n : Int) - 1) * ((n : Int) - 1) * u * q2 + ((n : Int) - 1) * u * q3, ?_⟩
    have e1 : Ri = c + p * q2 := by omega
    have e2 : Ra = c + p * q3 := by omega
    have e3 : u * ((n : Int) * ((n : Int) - 1) * ((n : Int) - 2)) = 1 + p * q1 := by omega
    subst e1 e2
    grind


/-- Hole identity at `x · H_{j'}`; uses `p ∣ k`. -/
theorem hole_kill (n k : Nat) (hn : 0 < n) (hk : (p : Int) ∣ (k : Int)) (u c : Int) (y : Nat → Int)
    (hu : (p : Int) ∣ u * ((n : Int) * ((n : Int) - 1) * ((n : Int) - 2)) - 1)
    (hC : ∀ j < n, (p : Int) ∣ rsum (n + k) (fun i => y (var n i j)) - c)
    (j' x : Nat) (hj' : j' < n) (hx : x < (n + k) * n) :
    (p : Int) ∣ mom ((n + k) * n) c y (Z n u c y)
      (fun a => monoEval a [x] * (sumOne (fun i => var n i j') (n + k)).eval a) := by
  have ha0 : x / n < n + k := (Nat.div_lt_iff_lt_mul hn).mpr hx
  have hb0 : x % n < n := Nat.mod_lt _ hn
  have hxv := var_decode n x
  generalize x / n = a0 at ha0 hxv
  generalize x % n = b0 at hb0 hxv
  subst hxv
  have e : (fun a => monoEval a [var n a0 b0] * (sumOne (fun i => var n i j') (n + k)).eval a) =
      fun a => rsum (n + k) (fun i => (fun a => if var n i j' = var n a0 b0 then monoEval a [var n a0 b0]
        else monoEval a [var n a0 b0, var n i j']) a) - monoEval a [var n a0 b0] := by
    funext a
    rw [sumOne_eval, Int.mul_sub, Int.mul_one]
    have := congrFun (split_fun (var n a0 b0) (n + k) (fun i => var n i j')) a
    simp only at this; rw [this]
  rw [e, mom_sub, mom_rsum, mom_mono1, if_pos hx]
  rw [rsum_congr (n + k) _ _ (fun i hi => mom_G _ c y _ (Z_symm n u c y) _ _ hx (var_lt n k i j' hi hj'))]
  by_cases hjb : j' = b0
  · subst hjb
    rw [rsum_congr (n + k) _ (fun i => if i = a0 then y (var n a0 j') else 0) (fun i hi => by
      by_cases hia : i = a0
      · subst hia; simp
      · have h1 : var n i j' ≠ var n a0 j' := fun h => hia (var_inj n _ _ _ _ hj' hj' h).1
        rw [if_neg h1, if_neg hia]; unfold Z
        rw [var_mod n _ _ hj', var_mod n _ _ hj']; simp)]
    rw [rsum_pick, if_pos ha0, Int.sub_self]; exact ⟨0, by simp⟩
  · rw [rsum_congr (n + k) _ (fun i => if i = a0 then 0 else form n u c y (var n a0 b0) (var n i j')) (fun i hi => by
      have h1 : var n i j' ≠ var n a0 b0 := fun h => hjb (var_inj n _ _ _ _ hj' hb0 h).2
      rw [if_neg h1]; unfold Z
      rw [var_div n _ _ hb0, var_div n _ _ hj', var_mod n _ _ hb0, var_mod n _ _ hj']
      by_cases hia : i = a0
      · subst hia; simp
      · rw [if_neg hia, if_pos ⟨Ne.symm hia, Ne.symm hjb⟩])]
    rw [rsum_skip (n + k) a0 ha0]
    unfold form
    simp only [var_div n _ _ hb0, var_mod n _ _ hb0, var_div n _ _ hj', var_mod n _ _ hj']
    rw [rsum_congr (n + k) _ (fun i => (((n : Int) - 1) * ((n : Int) - 1) * u * y (var n a0 b0) +
        ((n : Int) - 1) * u * y (var n a0 j') - (n : Int) * u * c) +
        ((n : Int) - 1) * ((n : Int) - 1) * u * y (var n i j') + ((n : Int) - 1) * u * y (var n i b0)) (fun i hi => by
      grind)]
    rw [rsum_kab]
    have hCj := hC j' hj'
    have hCb := hC b0 hb0
    generalize rsum (n + k) (fun i => y (var n i j')) = Cj at hCj
    generalize rsum (n + k) (fun i => y (var n i b0)) = Cb at hCb
    obtain ⟨q1, hq1⟩ := hu; obtain ⟨q2, hq2⟩ := hCj; obtain ⟨q3, hq3⟩ := hCb; obtain ⟨q4, hq4⟩ := hk
    refine ⟨q1 * y (var n a0 b0) + q4 * (((n : Int) - 1) * ((n : Int) - 1) * u * y (var n a0 b0) +
      ((n : Int) - 1) * u * y (var n a0 j') - (n : Int) * u * c) +
      ((n : Int) - 1) * ((n : Int) - 1) * u * q2 + ((n : Int) - 1) * u * q3, ?_⟩
    have e1 : Cj = c + p * q2 := by omega
    have e2 : Cb = c + p * q3 := by omega
    have e3 : u * ((n : Int) * ((n : Int) - 1) * ((n : Int) - 2)) = 1 + p * q1 := by omega
    subst e1 e2
    push_cast
    rw [hq4]
    grind


/-! ## Assembly -/

/-- A degree-1 design of a list containing `sumOne v m` gives the row-sum equation for its moments. -/
theorem design_sum {S : (Nat → Bool) → Prop} {A : List (Poly Nat)} (F : Fn p S) (hF : IsDesign A 1 F)
    (v : Nat → Nat) (m : Nat) (hP : sumOne v m ∈ A) :
    (p : Int) ∣ rsum m (fun j => F.E (fun a => monoEval a [v j])) - F.E (fun a => monoEval a []) := by
  have h1 := hF _ hP [] (by have := sumOne_deg v m; simp; omega)
  have e : (fun a => monoEval a [] * (sumOne v m).eval a) =
      fun a => ((sumOne v m).terms.map fun t => t.1 * monoEval a t.2).sum := by
    funext a; simp [monoEval, Poly.eval]
  rw [e] at h1
  have h2 := F.terms (sumOne v m).terms
  have h3 := Int.dvd_sub h1 h2
  have hl := linTerms_sum v m (fun l => F.E (fun a => monoEval a l))

  simp only [sumOne, List.map_cons, List.sum_cons, hl] at h3
  rw [show ∀ X Y : Int, X - (X - (-1 * F.E (fun a => monoEval a []) + Y)) = Y - F.E (fun a => monoEval a []) by
    intros; omega] at h3
  simpa using h3

theorem not_dvd_one (hp : 1 < p) : ¬ (p : Int) ∣ 1 := by
  intro h
  have := Int.le_of_dvd (by decide) h
  omega

/-- **Extension.** If `p ∣ k` and `u·n(n-1)(n-2) ≡ 1 (mod p)`, every degree-1 design of
`ontoFPHP n k` (on points with all variables `≥ (n+k)n` false) extends to a degree-2 design. -/
theorem ext2 (n k : Nat) (hn : 0 < n) (hk : (p : Int) ∣ (k : Int)) (u : Int)
    (hu : (p : Int) ∣ u * ((n : Int) * ((n : Int) - 1) * ((n : Int) - 2)) - 1)
    (F : Fn p (SN ((n + k) * n))) (hF : IsDesign (ontoFPHP n k) 1 F) :
    ∃ E : Fn p (SN ((n + k) * n)), IsDesign (ontoFPHP n k) 2 E ∧ Extends 1 E F := by
  let N := (n + k) * n
  let c := F.E (fun a => monoEval a [])
  let y : Nat → Int := fun v => F.E (fun a => monoEval a [v])
  have hR : ∀ i < n + k, (p : Int) ∣ rsum n (fun j => y (var n i j)) - c :=
    fun i hi => design_sum F hF (fun j => var n i j) n (mem_pig hi)
  have hC : ∀ j < n, (p : Int) ∣ rsum (n + k) (fun i => y (var n i j)) - c :=
    fun j hj => design_sum F hF (fun i => var n i j) (n + k) (mem_hole hj)
  let E := momFn p N c y (Z n u c y)
  have hx : Extends 1 E F := by
    intro t ht
    match t, ht with
    | [], _ =>
      show (p : Int) ∣ mom N c y (Z n u c y) (fun a => monoEval a []) - c
      rw [mom_mono0, Int.sub_self]; exact ⟨0, by simp⟩
    | [x], _ =>
      show (p : Int) ∣ mom N c y (Z n u c y) (fun a => monoEval a [x]) - y x
      rw [mom_mono1]
      by_cases hxN : x < N
      · rw [if_pos hxN, Int.sub_self]; exact ⟨0, by simp⟩
      · rw [if_neg hxN]
        have : y x = F.E (fun _ => 0) := F.supp _ _ (fun a ha => mono_vanish ha (by omega) [])
        rw [this]; have := F.zero; simpa using Int.dvd_neg.mpr this
  refine ⟨E, ?_, hx⟩
  intro P hP m hm
  by_cases hlow : m.length + P.deg ≤ 1
  · exact low_kill (D := 2) hF hx hP hlow
  have vanish : ∀ x, N ≤ x → ∀ (Q : Poly Nat) (m' : List Nat),
      (p : Int) ∣ E.E (fun a => monoEval a (x :: m') * Q.eval a) := by
    intro x hxN Q m'
    have : E.E (fun a => monoEval a (x :: m') * Q.eval a) = E.E (fun _ => 0) :=
      E.supp _ _ (fun a ha => by rw [mono_vanish ha hxN, Int.zero_mul])
    rw [this]; exact E.zero
  rcases mem_ontoFPHP hP with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩ | hc | hf
  · have h1 := sumOne_deg (fun j => var n i j) n
    have h2 := sumOne_deg_pos (fun j => var n i j) n hn
    match m, hm with
    | [x], _ =>
      by_cases hxN : x < N
      · exact pig_kill n k hn u c y hu hR i x hi hxN
      · exact vanish x (by omega) _ []
    | [], _ => simp at hlow; omega
    | _ :: _ :: _, hm => simp at hm; omega
  · have h1 := sumOne_deg (fun i => var n i j) (n + k)
    have h2 := sumOne_deg_pos (fun i => var n i j) (n + k) (by omega)
    match m, hm with
    | [x], _ =>
      by_cases hxN : x < N
      · exact hole_kill n k hn hk u c y hu hC j x hj hxN
      · exact vanish x (by omega) _ []
    | [], _ => simp at hlow; omega
    | _ :: _ :: _, hm => simp at hm; omega
  · obtain ⟨j, i, i', hj, hi, hi', hii, rfl⟩ := mem_collAx.mp hc
    rw [prod2_deg] at hm
    match m, hm with
    | [], _ =>
      show (p : Int) ∣ mom N c y (Z n u c y) (fun a => monoEval a [] * (prod2 (var n i j) (var n i' j)).eval a)
      have e : (fun a => monoEval a [] * (prod2 (var n i j) (var n i' j)).eval a) =
          fun a => monoEval a [var n i j, var n i' j] := by
        funext a; rw [prod2_eval]; simp [monoEval, xv]
      have hne : var n i j ≠ var n i' j := fun h => by have := (var_inj n _ _ _ _ hj hj h).1; omega
      rw [e, mom_mono2 N c y _ (Z_symm n u c y) _ _ hne]
      unfold Z; rw [var_mod n _ _ hj, var_mod n _ _ hj]; simp
  · obtain ⟨i, j, j', hi, hj, hj', hjj, rfl⟩ := mem_funcAx.mp hf
    rw [prod2_deg] at hm
    match m, hm with
    | [], _ =>
      show (p : Int) ∣ mom N c y (Z n u c y) (fun a => monoEval a [] * (prod2 (var n i j) (var n i j')).eval a)
      have e : (fun a => monoEval a [] * (prod2 (var n i j) (var n i j')).eval a) =
          fun a => monoEval a [var n i j, var n i j'] := by
        funext a; rw [prod2_eval]; simp [monoEval, xv]
      have hne : var n i j ≠ var n i j' := fun h => by have := (var_inj n _ _ _ _ hj hj' h).2; omega
      rw [e, mom_mono2 N c y _ (Z_symm n u c y) _ _ hne]
      unfold Z; rw [var_div n _ _ hj, var_div n _ _ hj']; simp

/-- **No degree-2 refutation.** For `p > 1`, `p ∣ k`, `n > 0` and `n(n-1)(n-2)` invertible mod `p`,
`onto-FPHP^{n+k}_n` has no degree-2 polynomial calculus refutation over `Z/p`. -/
theorem ontoFPHP_no_deg2 (n k : Nat) (hp : 1 < p) (hn : 0 < n) (hk : (p : Int) ∣ (k : Int)) (u : Int)
    (hu : (p : Int) ∣ u * ((n : Int) * ((n : Int) - 1) * ((n : Int) - 2)) - 1) :
    ¬ PPCRefutation p (ontoFPHP n k) 2 := by
  let N := (n + k) * n
  let w : Int := u * ((n : Int) - 1) * ((n : Int) - 2)
  let E0 := momFn p N 1 (fun _ => w) (fun _ _ => 0)
  have hsum : ∀ (v : Nat → Nat) (m : Nat), (∀ j < m, v j < N) →
      E0.E (fun a => monoEval a [] * (sumOne v m).eval a) = -1 + (m : Int) * w := by
    intro v m hv
    have e : (fun a => monoEval a [] * (sumOne v m).eval a) =
        fun a => ((sumOne v m).terms.map fun t => t.1 * monoEval a t.2).sum := by
      funext a; simp [monoEval, Poly.eval]
    show mom N 1 (fun _ => w) (fun _ _ => 0) _ = _
    rw [e, mom_terms]
    have hl := linTerms_sum v m (fun l => mom N 1 (fun _ => w) (fun _ _ => 0) (fun a => monoEval a l))

    simp only [sumOne, List.map_cons, List.sum_cons, hl, mom_mono0]
    rw [rsum_congr m _ (fun _ => w) (fun j hj => by rw [mom_mono1, if_pos (hv j hj)])]
    have := rsum_const m w
    rw [this]; omega
  have h0 : IsDesign (ontoFPHP n k) 1 E0 := by
    intro P hP m hm
    rcases mem_ontoFPHP hP with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩ | hc | hf
    · have h2 := sumOne_deg_pos (fun j => var n i j) n hn
      match m, hm with
      | [], _ =>
        rw [hsum _ _ (fun j hj => var_lt n k i j hi hj)]
        obtain ⟨q, hq⟩ := hu
        exact ⟨q, by grind⟩
      | _ :: _, hm => simp at hm; omega
    · have h2 := sumOne_deg_pos (fun i => var n i j) (n + k) (by omega)
      match m, hm with
      | [], _ =>
        rw [hsum _ _ (fun i hi => var_lt n k i j hi hj)]
        obtain ⟨q, hq⟩ := hu
        obtain ⟨q', hq'⟩ := hk
        exact ⟨q + q' * w, by push_cast; grind⟩
      | _ :: _, hm => simp at hm; omega
    · obtain ⟨_, _, _, _, _, _, _, rfl⟩ := mem_collAx.mp hc
      rw [prod2_deg] at hm; omega
    · obtain ⟨_, _, _, _, _, _, _, rfl⟩ := mem_funcAx.mp hf
      rw [prod2_deg] at hm; omega
  have h1 : ¬ (p : Int) ∣ E0.E (fun _ => 1) := by
    have : E0.E (fun _ => 1) = 1 := by
      show mom N 1 (fun _ => w) (fun _ _ => 0) (fun _ => 1) = 1
      have e : (fun _ => (1 : Int)) = fun a => monoEval a ([] : List Nat) := by funext a; simp [monoEval]
      rw [e, mom_mono0]
    rw [this]; exact not_dvd_one hp
  exact ext_sound (D := 2) (by decide) (fun F hF => ext2 n k hn hk u hu F hF) E0 h0 h1

/-- With restriction (K83): for `p > 1` with `6` invertible mod `p` and `p ∣ k`, onto-FPHP^{n+k}_n
has no PC refutation of degree `≤ 2` over `Z/p`, for every `n ≥ 3`. -/
theorem ontoFPHP_no_deg2_all (n k D : Nat) (hp : 1 < p) (hk : (p : Int) ∣ (k : Int))
    (h6 : ∃ u : Int, (p : Int) ∣ 6 * u - 1) (hn : 3 ≤ n) (hD : D ≤ 2) :
    ¬ PPCRefutation p (ontoFPHP n k) D := by
  intro h
  have h2 : PPCRefutation p (ontoFPHP n k) 2 :=
    Programme.«20261025-0459-proof-complexity».OntoPCLower.PPCDerivable.mono hD h
  obtain ⟨u, hu⟩ := h6
  have base := ontoFPHP_no_deg2 (p := p) 3 k hp (by decide) hk u (by
    have e : u * (((3 : Nat) : Int) * (((3 : Nat) : Int) - 1) * (((3 : Nat) : Int) - 2)) - 1 = 6 * u - 1 := by
      push_cast; grind
    rw [e]; exact hu)
  apply base
  clear h
  obtain ⟨d, rfl⟩ : ∃ d, n = 3 + d := ⟨n - 3, by omega⟩
  clear hn
  induction d with
  | zero => exact h2
  | succ d ih =>
    apply ih
    exact Programme.«20261025-0459-proof-complexity».OntoSubst.ontoFPHP_restrict p (3 + d) k 2
      (by decide) (by omega) (by rwa [show 3 + d + 1 = 3 + (d + 1) by omega])

end Programme.«20261025-1627-proof-complexity».OntoExt2

#print axioms Programme.«20261025-1627-proof-complexity».OntoExt2.ontoFPHP_no_deg2
#print axioms Programme.«20261025-1627-proof-complexity».OntoExt2.ontoFPHP_no_deg2_all
