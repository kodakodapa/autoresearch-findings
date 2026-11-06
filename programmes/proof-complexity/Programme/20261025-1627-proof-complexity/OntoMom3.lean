import Programme.«20261025-1627-proof-complexity».OntoExt3

/-!
# Level-3 moments of a degree-3 design for onto-FPHP

`mulFn F x` is the functional `h ↦ F(x_x · h)`; it turns a degree-`(D+1)` design into a degree-`D`
design, so the level-2 facts of `Work.OntoExt3` (conflicts vanish, row and column sums) give the
level-3 facts for `tt`, the third moment `F(x_u x_v x_w)` set to `0` on conflicting triples.
-/

namespace Programme.«20261025-1627-proof-complexity».OntoMom3

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr mem_pig mem_hole var_div var_mod)
open Programme.«20261025-1627-proof-complexity».DesignExt
open Programme.«20261025-1627-proof-complexity».OntoExt2 (SN rsum_dvd var_inj)
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261025-1627-proof-complexity».OntoExt3 (cc yy zz conf conf_symm zz_symm F_conf F_zz sum2 rsum_sub' hR2 hC2 F_swap)

variable {p : Nat}

section
variable {S : (Nat → Bool) → Prop} (F : Fn p S)

/-- `h ↦ F(x_x · h)`. -/
def mulFn (x : Nat) : Fn p S where
  E f := F.E (fun a => monoEval a [x] * f a)
  lin f g u v := by
    have h := F.lin (fun a => monoEval a [x] * f a) (fun a => monoEval a [x] * g a) u v
    have e : (fun a => monoEval a [x] * (u * f a + v * g a)) =
        fun a => u * (monoEval a [x] * f a) + v * (monoEval a [x] * g a) := by
      funext a; rw [Int.mul_add, Int.mul_left_comm, Int.mul_left_comm (monoEval a [x]) v]
    rw [e]; exact h
  congr f g h := F.congr _ _ (fun a => by rw [← Int.mul_sub]; exact dvd_cmul _ (h a))
  supp f g h := F.supp _ _ (fun a ha => by rw [h a ha])

theorem mono_cons (x : Nat) (m : List Nat) (a : Nat → Bool) :
    monoEval a [x] * monoEval a m = monoEval a (x :: m) := by
  simp [monoEval]

theorem mulFn_mono (x : Nat) (m : List Nat) :
    (mulFn F x).E (fun a => monoEval a m) = F.E (fun a => monoEval a (x :: m)) := by
  show F.E _ = F.E _
  congr 1; funext a; exact mono_cons x m a

theorem mulFn_design {A : List (Poly Nat)} {D : Nat} (x : Nat) (hF : IsDesign A (D + 1) F) :
    IsDesign A D (mulFn F x) := by
  intro P hP m hm
  have h := hF P hP (x :: m) (by simp; omega)
  show (p : Int) ∣ F.E _
  have e : (fun a => monoEval a [x] * (monoEval a m * P.eval a)) = fun a => monoEval a (x :: m) * P.eval a := by
    funext a; rw [← Int.mul_assoc, mono_cons]
  rw [e]; exact h

/-- Third moment, `0` on conflicting triples. -/
def tt (n u v w : Nat) : Int :=
  if conf n u v ∨ conf n u w ∨ conf n v w then 0 else F.E (fun a => monoEval a [u, v, w])

theorem tt_12 (n u v w : Nat) : tt F n u v w = tt F n v u w := by
  unfold tt
  have hc : (conf n u v ∨ conf n u w ∨ conf n v w) ↔ (conf n v u ∨ conf n v w ∨ conf n u w) := by
    unfold conf; constructor <;> intro h <;> omega
  by_cases h : conf n u v ∨ conf n u w ∨ conf n v w
  · rw [if_pos h, if_pos (hc.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hc.mpr h'))]
    congr 1; funext a; exact monoEval_congr a _ _ (fun x => by simp; omega)

theorem tt_23 (n u v w : Nat) : tt F n u v w = tt F n u w v := by
  unfold tt
  have hc : (conf n u v ∨ conf n u w ∨ conf n v w) ↔ (conf n u w ∨ conf n u v ∨ conf n w v) := by
    unfold conf; constructor <;> intro h <;> omega
  by_cases h : conf n u v ∨ conf n u w ∨ conf n v w
  · rw [if_pos h, if_pos (hc.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hc.mpr h'))]
    congr 1; funext a; exact monoEval_congr a _ _ (fun x => by simp; omega)

theorem confC (n a a' b : Nat) (hb : b < n) (h : a ≠ a') : conf n (var n a b) (var n a' b) :=
  ⟨fun e => h (var_inj n _ _ _ _ hb hb e).1, Or.inr (by rw [var_mod n _ _ hb, var_mod n _ _ hb])⟩

theorem confR (n a b b' : Nat) (hb : b < n) (hb' : b' < n) (h : b ≠ b') : conf n (var n a b) (var n a b') :=
  ⟨fun e => h (var_inj n _ _ _ _ hb hb' e).2, Or.inl (by rw [var_div n _ _ hb, var_div n _ _ hb'])⟩

theorem ttC12 (n a a' b x : Nat) (hb : b < n) (h : a ≠ a') : tt F n (var n a b) (var n a' b) x = 0 := by
  unfold tt; rw [if_pos (Or.inl (confC n a a' b hb h))]
theorem ttC13 (n a a' b x : Nat) (hb : b < n) (h : a ≠ a') : tt F n (var n a b) x (var n a' b) = 0 := by
  unfold tt; rw [if_pos (Or.inr (Or.inl (confC n a a' b hb h)))]
theorem ttC23 (n a a' b x : Nat) (hb : b < n) (h : a ≠ a') : tt F n x (var n a b) (var n a' b) = 0 := by
  unfold tt; rw [if_pos (Or.inr (Or.inr (confC n a a' b hb h)))]
theorem ttR12 (n a b b' x : Nat) (hb : b < n) (hb' : b' < n) (h : b ≠ b') : tt F n (var n a b) (var n a b') x = 0 := by
  unfold tt; rw [if_pos (Or.inl (confR n a b b' hb hb' h))]
theorem ttR13 (n a b b' x : Nat) (hb : b < n) (hb' : b' < n) (h : b ≠ b') : tt F n (var n a b) x (var n a b') = 0 := by
  unfold tt; rw [if_pos (Or.inr (Or.inl (confR n a b b' hb hb' h)))]
theorem ttR23 (n a b b' x : Nat) (hb : b < n) (hb' : b' < n) (h : b ≠ b') : tt F n x (var n a b) (var n a b') = 0 := by
  unfold tt; rw [if_pos (Or.inr (Or.inr (confR n a b b' hb hb' h)))]

end

/-! ## Facts from a degree-3 design -/

section
variable {n k : Nat} (F : Fn p (SN ((n + k) * n))) (hF : IsDesign (ontoFPHP n k) 3 F)
include hF

theorem design2 : IsDesign (ontoFPHP n k) 2 F := fun P hP m hm => hF P hP m (by omega)

theorem mdesign (x : Nat) : IsDesign (ontoFPHP n k) 2 (mulFn F x) := mulFn_design F x hF

/-- `F(x_x x_v x_w) ≡ 0` for conflicting `v, w`. -/
theorem F_conf3 (hn : 0 < n) (x v w : Nat) (h : conf n v w) : (p : Int) ∣ F.E (fun a => monoEval a [x, v, w]) := by
  have := F_conf (mulFn F x) (mdesign F hF x) hn v w h
  rwa [mulFn_mono] at this

theorem F_tt (hn : 0 < n) (u v w : Nat) : (p : Int) ∣ F.E (fun a => monoEval a [u, v, w]) - tt F n u v w := by
  unfold tt
  by_cases h : conf n u v ∨ conf n u w ∨ conf n v w
  · rw [if_pos h, Int.sub_zero]
    rcases h with h | h | h
    · have e : F.E (fun a => monoEval a [u, v, w]) = F.E (fun a => monoEval a [w, u, v]) := by
        congr 1; funext a; exact monoEval_congr a _ _ (fun x => by simp; omega)
      rw [e]; exact F_conf3 F hF hn w u v h
    · have e : F.E (fun a => monoEval a [u, v, w]) = F.E (fun a => monoEval a [v, u, w]) := by
        congr 1; funext a; exact monoEval_congr a _ _ (fun x => by simp; omega)
      rw [e]; exact F_conf3 F hF hn v u w h
    · exact F_conf3 F hF hn u v w h
  · rw [if_neg h, Int.sub_self]; exact ⟨0, by simp⟩

/-- Row/column sums at level 3: `∑_j tt(v, w, w_j) ≡ zz(v, w)` for a pigeon or hole axiom. -/
theorem sum3 (hn : 0 < n) (v w : Nat) (wf : Nat → Nat) (m : Nat) (hP : sumOne wf m ∈ ontoFPHP n k) :
    (p : Int) ∣ rsum m (fun j => tt F n v w (wf j)) - zz F n v w := by
  have h := sum2 (mulFn F v) (mdesign F hF v) hn w wf m hP
  have h1 : (p : Int) ∣ rsum m (fun j => tt F n v w (wf j)) - rsum m (fun j => zz (mulFn F v) n w (wf j)) := by
    have := rsum_dvd p m (fun j => tt F n v w (wf j) - zz (mulFn F v) n w (wf j)) (fun j _ => by
      have a1 := F_zz (mulFn F v) (mdesign F hF v) hn w (wf j)
      rw [mulFn_mono] at a1
      have a2 := F_tt F hF hn v w (wf j)
      have := Int.dvd_sub a1 a2
      refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mp this
      exact ⟨0, by omega⟩)
    rwa [rsum_sub'] at this
  have h2 : (p : Int) ∣ yy (mulFn F v) w - zz F n v w := by
    unfold yy; rw [mulFn_mono]; exact F_zz F (design2 F hF) hn v w
  have := Int.dvd_add (Int.dvd_add h1 h) h2
  refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mp this
  exact ⟨0, by omega⟩

theorem hR3c (hn : 0 < n) : ∀ v w, ∀ i < n + k, (p : Int) ∣ rsum n (fun j => tt F n v w (var n i j)) - zz F n v w :=
  fun v w i hi => sum3 F hF hn v w (fun j => var n i j) n (mem_pig hi)

theorem hC3c (hn : 0 < n) : ∀ v w, ∀ j < n, (p : Int) ∣ rsum (n + k) (fun i => tt F n v w (var n i j)) - zz F n v w :=
  fun v w j hj => sum3 F hF hn v w (fun i => var n i j) (n + k) (mem_hole hj)

theorem hR3b (hn : 0 < n) : ∀ v w, ∀ i < n + k, (p : Int) ∣ rsum n (fun j => tt F n v (var n i j) w) - zz F n v w := by
  intro v w i hi
  rw [rsum_congr n _ _ (fun j _ => tt_23 F n v (var n i j) w)]; exact hR3c F hF hn v w i hi

theorem hR3a (hn : 0 < n) : ∀ v w, ∀ i < n + k, (p : Int) ∣ rsum n (fun j => tt F n (var n i j) v w) - zz F n v w := by
  intro v w i hi
  rw [rsum_congr n _ _ (fun j _ => (tt_12 F n (var n i j) v w).trans (tt_23 F n v (var n i j) w))]
  exact hR3c F hF hn v w i hi

theorem hC3b (hn : 0 < n) : ∀ v w, ∀ j < n, (p : Int) ∣ rsum (n + k) (fun i => tt F n v (var n i j) w) - zz F n v w := by
  intro v w j hj
  rw [rsum_congr (n + k) _ _ (fun i _ => tt_23 F n v (var n i j) w)]; exact hC3c F hF hn v w j hj

theorem hC3a (hn : 0 < n) : ∀ v w, ∀ j < n, (p : Int) ∣ rsum (n + k) (fun i => tt F n (var n i j) v w) - zz F n v w := by
  intro v w j hj
  rw [rsum_congr (n + k) _ _ (fun i _ => (tt_12 F n (var n i j) v w).trans (tt_23 F n v (var n i j) w))]
  exact hC3c F hF hn v w j hj

theorem hR2a (hn : 0 < n) : ∀ v, ∀ i < n + k, (p : Int) ∣ rsum n (fun j => zz F n (var n i j) v) - yy F v := by
  intro v i hi
  rw [rsum_congr n _ _ (fun j _ => zz_symm F n (var n i j) v)]; exact hR2 F (design2 F hF) hn v i hi

theorem hC2a (hn : 0 < n) : ∀ v, ∀ j < n, (p : Int) ∣ rsum (n + k) (fun i => zz F n (var n i j) v) - yy F v := by
  intro v j hj
  rw [rsum_congr (n + k) _ _ (fun i _ => zz_symm F n (var n i j) v)]; exact hC2 F (design2 F hF) hn v j hj

end

end Programme.«20261025-1627-proof-complexity».OntoMom3
