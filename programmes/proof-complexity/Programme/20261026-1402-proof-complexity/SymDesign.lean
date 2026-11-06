import Programme.«20261026-1402-proof-complexity».ExtLemma

/-!
# Symmetric designs for onto-FPHP

For `ontoFPHP n k` with `p ∣ k`, the functional whose value on every canonical `s`-matching is
`c_s = (n-s)(n-s-1)⋯(n-D+1)` (falling factorial `ff (n-s) (D-s)`) and `0` on non-matchings is a
degree-`D` design with `E(1) ≡ ff n D = n(n-1)⋯(n-D+1)`. The pigeon equation at a free pigeon of
an `s`-matching reads `(n-s) c_{s+1} = c_s` (exactly), the hole equation `(n+k-s) c_{s+1} ≡ c_s`
(mod `p`, since `p ∣ k`). For `n = D` this is the symmetric window `c_{s+1} = c_s/(D-s)` (th, P89),
with `E(1) ≡ D!`, so it is non-trivial when `D! ≢ 0` mod `p`.

The design is built level by level with `Work.ExtLemma.Ext` (constant top values), so no
EXT hypothesis is used.
-/

namespace Programme.«20261026-1402-proof-complexity».SymDesign

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero prod2_eval mem_ontoFPHP
  mem_collAx mem_funcAx var_div var_mod prod2_deg mem_pig mem_hole mem_coll mem_func)
open Programme.«20261025-1627-proof-complexity».DesignExt
open Programme.«20261025-1627-proof-complexity».OntoExt2 (SN rsum_dvd rsum_pick var_lt var_decode
  sumOne_deg_pos not_dvd_one rsum_const)
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261025-1627-proof-complexity».OntoExt3 (rsum_sub')
open Programme.«20261026-1402-proof-complexity».ExtLemma

/-- Falling factorial `x (x-1) ⋯ (x-r+1)`. -/
def ff (x : Int) : Nat → Int
  | 0 => 1
  | r + 1 => x * ff (x - 1) r

/-- Symmetric value on `s`-matchings for degree `D`. -/
def cv (n D s : Nat) : Int := ff ((n : Int) - s) (D - s)

theorem cv_step (n D s : Nat) (hs : s < D) : cv n D s = ((n : Int) - s) * cv n D (s + 1) := by
  unfold cv
  obtain ⟨r, hr⟩ : ∃ r, D - s = r + 1 := ⟨D - s - 1, by omega⟩
  rw [hr, show D - (s + 1) = r by omega, ff]
  congr 2; push_cast; omega

/-- Generic degree step: a degree-`d` design `F` and values `y` on `(d+1)`-matchings balanced
against `F` at level `d` give the degree-`(d+1)` design `Ext F y d`. -/
theorem ext_step_y {p n k d : Nat} (hn : 0 < n) (F : Fn p (SN ((n + k) * n)))
    (hF : IsDesign (ontoFPHP n k) d F) (y : List Nat → Int)
    (hy : Bal p n k y (fun t => F.E (fun a => monoEval a t)) d) :
    IsDesign (ontoFPHP n k) (d + 1) (Ext F y d) ∧ Extends d (Ext F y d) F := by
  refine ⟨?_, Ext_extends F y d⟩
  intro P hP m hm
  by_cases hlow : m.length + P.deg ≤ d
  · exact low_kill (D := d + 1) (E' := F) (by simpa using hF) (by simpa using Ext_extends F y d) hP (by simpa using hlow)
  rcases mem_ontoFPHP hP with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩ | hc | hf
  · have h1 := sumOne_deg (fun j => var n i j) n
    have h2 := sumOne_deg_pos (fun j => var n i j) n hn
    refine Ext_line F y d hn hF _ n (mem_pig hi) (fun j hj => var_lt n k i j hi hj) pig_cfl ?_ m (by omega)
    intro s hs hsl hfr
    exact (hy s hs hsl).1 i hi (pfree_of hn hfr)
  · have h1 := sumOne_deg (fun i => var n i j) (n + k)
    have h2 := sumOne_deg_pos (fun i => var n i j) (n + k) (by omega)
    refine Ext_line F y d hn hF _ (n + k) (mem_hole hj) (fun i hi => var_lt n k i j hi hj) (hole_cfl hj) ?_ m (by omega)
    intro s hs hsl hfr
    exact (hy s hs hsl).2 j hj (hfree_of hn (fun x hx => CM_lt hs hx) hfr)
  · obtain ⟨j, i, i', hj, hi, hi', hii, rfl⟩ := mem_collAx.mp hc
    rw [prod2_deg] at hm
    have e : (fun a => monoEval a m * (prod2 (var n i j) (var n i' j)).eval a) =
        fun a => monoEval a (m ++ [var n i j, var n i' j]) := by
      funext a; rw [prod2_eval, monoEval_append]; simp [monoEval, xv]
    rw [e]
    exact Ext_kill F y d hn hF _ (by simp; omega) (var n i j) (by simp) (var n i' j) (by simp)
      (hole_cfl (k := k) hj i hi i' hi' (by omega))
  · obtain ⟨i, j, j', hi, hj, hj', hjj, rfl⟩ := mem_funcAx.mp hf
    rw [prod2_deg] at hm
    have e : (fun a => monoEval a m * (prod2 (var n i j) (var n i j')).eval a) =
        fun a => monoEval a (m ++ [var n i j, var n i j']) := by
      funext a; rw [prod2_eval, monoEval_append]; simp [monoEval, xv]
    rw [e]
    exact Ext_kill F y d hn hF _ (by simp; omega) (var n i j) (by simp) (var n i j') (by simp)
      (pig_cfl (i := i) j hj j' hj' (by omega))

/-! ## Counting free lines -/

theorem rsum_mulc (M : Nat) (f : Nat → Int) (c : Int) : rsum M (fun j => f j * c) = rsum M f * c := by
  induction M with
  | zero => simp [rsum]
  | succ M ih => simp only [rsum, ih, Int.add_mul]

theorem count_free (h : Nat → Nat) (M : Nat) : ∀ g : List Nat, (g.map h).Nodup → (∀ v ∈ g, h v < M) →
    rsum M (fun t => if ∀ v ∈ g, h v ≠ t then 1 else 0) = (M : Int) - g.length := by
  intro g
  induction g with
  | nil => intro _ _; simpa using rsum_const M 1
  | cons v g ih =>
    intro hnd hlt
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have hfree : ∀ w ∈ g, h w ≠ h v := fun w hw e => hnd.1 ⟨w, hw, e⟩
    have e : ∀ t, (if ∀ w ∈ v :: g, h w ≠ t then (1 : Int) else 0) =
        (if ∀ w ∈ g, h w ≠ t then 1 else 0) - (if t = h v then 1 else 0) := by
      intro t
      by_cases ht : t = h v
      · subst ht; rw [if_neg (by simp), if_pos hfree, if_pos rfl]; rfl
      · rw [if_neg ht]
        by_cases hg : ∀ w ∈ g, h w ≠ t
        · rw [if_pos hg, if_pos (by
            intro w hw; simp only [List.mem_cons] at hw
            rcases hw with rfl | hw; exact fun e => ht e.symm; exact hg w hw)]; rfl
        · rw [if_neg hg, if_neg (fun H => hg (fun w hw => H w (by simp [hw])))]; rfl
    rw [rsum_congr M _ _ (fun t _ => e t), rsum_sub', ih hnd.2 (fun w hw => hlt w (by simp [hw])),
      rsum_pick M (h v) (fun _ => 1), if_pos (hlt v (by simp))]
    simp; omega

theorem isMatch_cons (n v : Nat) (g : List Nat) :
    isMatch n (v :: g) = true ↔ isMatch n g = true ∧ ∀ w ∈ g, cfl n v w = false := by
  rw [isMatch_iff, isMatch_iff]
  have hvv : cfl n v v = false := by simp [cfl]
  constructor
  · intro H
    exact ⟨fun a ha b hb => H a (by simp [ha]) b (by simp [hb]), fun w hw => H v (by simp) w (by simp [hw])⟩
  · rintro ⟨H1, H2⟩ a ha b hb
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact hvv
    · exact H2 b hb
    · rw [cfl_symm]; exact H2 a ha
    · exact H1 a ha b hb

theorem match_nodup_mod {n k : Nat} {g : List Nat} (hg : CM n k g) : (g.map (· % n)).Nodup := by
  unfold List.Nodup; rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ (CM_nodup hg)
  intro x y hx hy hne e
  have := (isMatch_iff n g).mp hg.2 x hx y hy
  simp [cfl, hne, e] at this

theorem match_nodup_div {n k : Nat} {g : List Nat} (hg : CM n k g) : (g.map (· / n)).Nodup := by
  unfold List.Nodup; rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ (CM_nodup hg)
  intro x y hx hy hne e
  have := (isMatch_iff n g).mp hg.2 x hx y hy
  simp [cfl, hne, e] at this

theorem rowS_const {n k : Nat} (hn : 0 < n) (c : Int) {g : List Nat} (hg : CM n k g) {i : Nat}
    (hfr : pfree n g i) : rowS n k (fun _ => c) g i = ((n : Int) - g.length) * c := by
  unfold rowS lineS
  have e : ∀ j < n, (if isMatch n (var n i j :: g) then c else 0) =
      (if ∀ w ∈ g, w % n ≠ j then 1 else 0) * c := by
    intro j hj
    have key : isMatch n (var n i j :: g) = true ↔ ∀ w ∈ g, w % n ≠ j := by
      rw [isMatch_cons]
      constructor
      · rintro ⟨_, H⟩ w hw e
        have := H w hw
        simp [cfl, var_mod n i j hj, e] at this
        exact hfr w hw (by rw [← this, var_div n i j hj])
      · intro H
        refine ⟨hg.2, fun w hw => ?_⟩
        have h1 := hfr w hw; have h2 := H w hw
        simp only [cfl, Bool.and_eq_false_iff, bne_eq_false_iff_eq, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
          var_div n i j hj, var_mod n i j hj]
        right; exact ⟨fun e => h1 e.symm, fun e => h2 e.symm⟩
    by_cases hm : isMatch n (var n i j :: g) = true
    · rw [if_pos hm, if_pos (key.mp hm), Int.one_mul]
    · rw [if_neg hm, if_neg (fun H => hm (key.mpr H)), Int.zero_mul]
  rw [rsum_congr n _ _ e, rsum_mulc, count_free (· % n) n g (match_nodup_mod hg)
    (fun v _ => Nat.mod_lt _ hn)]

theorem colS_const {n k : Nat} (hn : 0 < n) (c : Int) {g : List Nat} (hg : CM n k g) {j : Nat}
    (hj : j < n) (hfr : hfree n g j) : colS n k (fun _ => c) g j = ((n + k : Nat) - (g.length : Int)) * c := by
  unfold colS lineS
  have e : ∀ i < n + k, (if isMatch n (var n i j :: g) then c else 0) =
      (if ∀ w ∈ g, w / n ≠ i then 1 else 0) * c := by
    intro i _
    have key : isMatch n (var n i j :: g) = true ↔ ∀ w ∈ g, w / n ≠ i := by
      rw [isMatch_cons]
      constructor
      · rintro ⟨_, H⟩ w hw e
        have := H w hw
        simp [cfl, var_div n i j hj, e] at this
        exact hfr w hw (by rw [← this, var_mod n i j hj])
      · intro H
        refine ⟨hg.2, fun w hw => ?_⟩
        have h1 := hfr w hw; have h2 := H w hw
        simp only [cfl, Bool.and_eq_false_iff, bne_eq_false_iff_eq, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
          var_div n i j hj, var_mod n i j hj]
        right; exact ⟨fun e => h2 e.symm, fun e => h1 e.symm⟩
    by_cases hm : isMatch n (var n i j :: g) = true
    · rw [if_pos hm, if_pos (key.mp hm), Int.one_mul]
    · rw [if_neg hm, if_neg (fun H => hm (key.mpr H)), Int.zero_mul]
  rw [rsum_congr (n + k) _ _ e, rsum_mulc, count_free (· / n) (n + k) g (match_nodup_div hg)
    (fun v hv => (Nat.div_lt_iff_lt_mul hn).mpr (CM_lt hg hv))]

/-! ## The symmetric design -/

theorem sym_designs {p n k D : Nat} (hn : 0 < n) (hk : p ∣ k) : ∀ s, s ≤ D →
    ∃ E : Fn p (SN ((n + k) * n)), IsDesign (ontoFPHP n k) s E ∧
      (p : Int) ∣ E.E (fun _ => 1) - cv n D 0 ∧
      ∀ g, CM n k g → g.length = s → (p : Int) ∣ E.E (fun a => monoEval a g) - cv n D s := by
  intro s
  induction s with
  | zero =>
    intro _
    have hc : canon ((n + k) * n) ([] : List Nat) = [] :=
      List.eq_nil_iff_forall_not_mem.mpr (fun x h => by simp [mem_canon] at h)
    have e : (fun _ => (1 : Int)) = fun a => monoEval a ([] : List Nat) := by funext a; simp [monoEval]
    have v0 : (sumWFn p ((n + k) * n) 0 (fun _ => cv n D 0)).E (fun _ => 1) = cv n D 0 := by
      show sumW _ 0 _ (fun _ => (1 : Int)) = _
      rw [e, sumW_mono _ 0 _ [] (by simp) (by rw [hc]; simp)]
    refine ⟨sumWFn p ((n + k) * n) 0 (fun _ => cv n D 0), ?_, by rw [v0]; exact ⟨0, by simp⟩, ?_⟩
    · intro P hP m hm
      exfalso
      rcases mem_ontoFPHP hP with ⟨i, _, rfl⟩ | ⟨j, _, rfl⟩ | hc | hf
      · have := sumOne_deg_pos (fun j => var n i j) n hn; omega
      · have := sumOne_deg_pos (fun i => var n i j) (n + k) (by omega); omega
      · obtain ⟨_, _, _, _, _, _, _, rfl⟩ := mem_collAx.mp hc; rw [prod2_deg] at hm; omega
      · obtain ⟨_, _, _, _, _, _, _, rfl⟩ := mem_funcAx.mp hf; rw [prod2_deg] at hm; omega
    · intro g _ hl
      rw [List.length_eq_zero_iff.mp hl, ← e, v0]; exact ⟨0, by simp⟩
  | succ s ih =>
    intro hs
    obtain ⟨F, hF, h1, hv⟩ := ih (by omega)
    let y : List Nat → Int := fun _ => cv n D (s + 1)
    have hy : Bal p n k y (fun t => F.E (fun a => monoEval a t)) s := by
      intro g hg hgl
      have hst := cv_step n D s (by omega)
      have hvg := hv g hg hgl
      refine ⟨fun i _ hfr => ?_, fun j hj hfr => ?_⟩
      · dsimp only
        rw [rowS_const hn _ hg hfr, hgl]
        have := Int.dvd_neg.mpr hvg
        rw [hst] at this
        refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mp this; exact ⟨0, by omega⟩
      · dsimp only
        rw [colS_const hn _ hg hj hfr, hgl]
        have hkc : (p : Int) ∣ (k : Int) * cv n D (s + 1) :=
          Int.dvd_trans (Int.natCast_dvd_natCast.mpr hk) ⟨cv n D (s + 1), rfl⟩
        have := Int.dvd_add hkc (Int.dvd_neg.mpr hvg)
        rw [hst] at this
        refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mp this
        refine ⟨0, ?_⟩
        generalize cv n D (s + 1) = C
        push_cast
        rw [Int.sub_mul, Int.sub_mul, Int.add_mul]
        omega
    obtain ⟨hE, hx⟩ := ext_step_y hn F hF y hy
    refine ⟨Ext F y s, hE, ?_, ?_⟩
    · have a := hx [] (by simp)
      have e : (fun a => monoEval a ([] : List Nat)) = fun _ => (1 : Int) := by funext a; simp [monoEval]
      rw [e] at a
      have := Int.dvd_add a h1
      rwa [show (Ext F y s).E (fun _ => 1) - F.E (fun _ => 1) + (F.E (fun _ => 1) - cv n D 0) =
        (Ext F y s).E (fun _ => 1) - cv n D 0 by omega] at this
    · intro g hg hgl
      rw [Ext_top F y s g (fun x hx => CM_lt hg hx) hg.2 (by rw [hg.1]; exact hgl)]
      exact ⟨0, by simp [y]⟩

/-- **Symmetric design.** For `n > 0` and `p ∣ k`, `ontoFPHP n k` has a degree-`D` design `E`
with `E(1) ≡ n(n-1)⋯(n-D+1)` mod `p`. -/
theorem sym_design {p n k : Nat} (D : Nat) (hn : 0 < n) (hk : p ∣ k) :
    ∃ E : Fn p (SN ((n + k) * n)), IsDesign (ontoFPHP n k) D E ∧ (p : Int) ∣ E.E (fun _ => 1) - ff n D := by
  obtain ⟨E, hE, h1, _⟩ := sym_designs (D := D) hn hk D (Nat.le_refl D)
  exact ⟨E, hE, by simpa [cv] using h1⟩

/-- Degree three on three holes (th's window `c_{s+1} = c_s/(3-s)`): for `p > 1` coprime to `6`
and `p ∣ k`, `ontoFPHP 3 k` has a degree-3 design `E` with `E(1) ≢ 0` mod `p`. -/
theorem design3 {p k : Nat} (hp : 1 < p) (hp6 : Nat.gcd p 6 = 1) (hk : p ∣ k) :
    ∃ E : Fn p (SN ((3 + k) * 3)), IsDesign (ontoFPHP 3 k) 3 E ∧ ¬ (p : Int) ∣ E.E (fun _ => 1) := by
  obtain ⟨E, hE, h1⟩ := sym_design (p := p) (n := 3) (k := k) 3 (by omega) hk
  refine ⟨E, hE, fun h => ?_⟩
  have h6 : (p : Int) ∣ 6 := by
    have := Int.dvd_sub h h1
    simp only [ff] at this
    rwa [show E.E (fun _ => 1) - (E.E (fun _ => 1) - ((3 : Nat) : Int) * ((((3 : Nat) : Int) - 1) * ((((3 : Nat) : Int) - 1 - 1) * 1))) = 6 by
      push_cast; omega] at this
  have h6' : p ∣ 6 := by exact_mod_cast h6
  have := Nat.dvd_gcd (Nat.dvd_refl p) h6'
  rw [hp6] at this
  have := Nat.le_of_dvd (by omega) this
  omega

end Programme.«20261026-1402-proof-complexity».SymDesign

#print axioms Programme.«20261026-1402-proof-complexity».SymDesign.sym_design
#print axioms Programme.«20261026-1402-proof-complexity».SymDesign.design3
