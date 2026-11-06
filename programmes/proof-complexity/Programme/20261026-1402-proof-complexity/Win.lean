import Programme.«20261026-1402-proof-complexity».RectExt
import Programme.«20261026-1402-proof-complexity».SymDesign

/-!
# Window products (L3, th's K28)

A *window* is a function `T` on matchings with `Bal T T e` (every free row and column sum at a
canonical `e`-matching is `≡ T` there). `bal_win`: a three-block product `Prod bp bh n φ` is a
window at level `e` as soon as each factor is a local window at the restrictions of
`e`-matchings to its block. Local windows used here: the symmetric design `cv m 3 |σ|` on block 2
(`p ∣ k`), the constant `1` on a `1 × 1` block, and on a `2 × 2` block the rectangle window
`(0, r, det)` and the symmetric design `(2, 1, 1)`.
-/

set_option linter.unusedSimpArgs false

namespace Programme.«20261026-1402-proof-complexity».Win

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero var_div var_mod)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt var_decode rsum_pick rsum_const)
open Programme.«20261025-1627-proof-complexity».OntoExt3 (rsum_sub')
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261026-1402-proof-complexity».ExtLemma Programme.«20261026-1402-proof-complexity».ExtLin Programme.«20261026-1402-proof-complexity».ProdExt Programme.«20261026-1402-proof-complexity».RectBlock Programme.«20261026-1402-proof-complexity».RectExt Programme.«20261026-1402-proof-complexity».SymDesign

variable {n k : Nat}

/-! ## Products of local windows -/

theorem bal_win (p : Nat) (bp bh : Nat → Nat) (hbp : ∀ i, bp i < 3) (hbh : ∀ j, bh j < 3)
    (φ : Nat → List Nat → Int) (hφ : ∀ c, SL (φ c)) (e : Nat)
    (hr : ∀ g, CM n k g → g.length = e → okL bp bh n g = true → ∀ i < n + k, pfree n g i →
      (p : Int) ∣ locL n (φ (bp i)) (fl bp bh n (bp i) g) (var n i) n (fun t => bh t = bp i) -
        φ (bp i) (fl bp bh n (bp i) g))
    (hc : ∀ g, CM n k g → g.length = e → okL bp bh n g = true → ∀ j < n, hfree n g j →
      (p : Int) ∣ locL n (φ (bh j)) (fl bp bh n (bh j) g) (fun s => var n s j) (n + k)
        (fun s => bp s = bh j) - φ (bh j) (fl bp bh n (bh j) g)) :
    Bal p n k (ProdExt.Prod bp bh n φ) (ProdExt.Prod bp bh n φ) e := by
  have fac : ∀ g (b : Nat), b < 3 → ProdExt.Prod bp bh n φ g =
      if okL bp bh n g then φ b (fl bp bh n b g) * oth bp bh n φ b g else 0 := by
    intro g b hb; unfold ProdExt.Prod oth
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
      split <;> simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  intro g hg hl
  refine ⟨fun i hi hf => ?_, fun j hj hf => ?_⟩
  · unfold rowS
    rw [line_Prod bp bh φ hφ hg (var n i) n (bp i) (hbp i) (fun t => bh t = bp i)
      (fun t ht => ⟨var_lt n k i t hi ht, notin_of_pfree hf t ht⟩)
      (fun t ht => by rw [blk_var bp bh ht]; by_cases h : bp i = bh t <;> simp [h, eq_comm]),
      fac g (bp i) (hbp i)]
    split
    · rename_i hok
      have := hr g hg hl hok i hi hf
      unfold locL at this
      rw [← Int.sub_mul]; exact Int.dvd_trans this (Int.dvd_mul_right _ _)
    · simp
  · unfold colS
    rw [line_Prod bp bh φ hφ hg (fun s => var n s j) (n + k) (bh j) (hbh j) (fun s => bp s = bh j)
      (fun t ht => ⟨var_lt n k t j ht hj, notin_of_hfree hf t hj⟩)
      (fun t ht => by rw [blk_var bp bh hj]; by_cases h : bp t = bh j <;> simp [h]),
      fac g (bh j) (hbh j)]
    split
    · rename_i hok
      have := hc g hg hl hok j hj hf
      unfold locL at this
      rw [← Int.sub_mul]; exact Int.dvd_trans this (Int.dvd_mul_right _ _)
    · simp

/-! ## Restrictions of a matching to a block -/

theorem fl_props (bp bh : Nat → Nat) {g : List Nat} (hg : CM n k g) (b : Nat) :
    (fl bp bh n b g).Nodup ∧ isMatch n (fl bp bh n b g) = true ∧
      (∀ w ∈ fl bp bh n b g, blk bp bh n w = b ∧ w ∈ g) ∧ (fl bp bh n b g).length ≤ g.length := by
  refine ⟨fl_nodup bp bh n b (CM_nodup hg), ?_, fun w hw => ?_, List.length_filter_le _ _⟩
  · rw [isMatch_iff]; intro v hv w hw
    exact (isMatch_iff n g).mp hg.2 v ((mem_fl ..).mp hv).1 w ((mem_fl ..).mp hw).1
  · have := (mem_fl ..).mp hw; exact ⟨this.2, this.1⟩

theorem blk_eq {bp bh : Nat → Nat} {w b : Nat} (h : blk bp bh n w = b) (hb : b < 3) :
    bp (w / n) = b ∧ bh (w % n) = b := by
  unfold blk at h; split at h
  · rename_i e; exact ⟨h, e ▸ h⟩
  · omega

theorem nodup_mod {σ : List Nat} (hn : σ.Nodup) (hm : isMatch n σ = true) : (σ.map (· % n)).Nodup := by
  unfold List.Nodup; rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ hn
  intro x y hx hy hne e
  have := (isMatch_iff n σ).mp hm x hx y hy
  simp [cfl, hne, e] at this

theorem nodup_div {σ : List Nat} (hn : σ.Nodup) (hm : isMatch n σ = true) : (σ.map (· / n)).Nodup := by
  unfold List.Nodup; rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ hn
  intro x y hx hy hne e
  have := (isMatch_iff n σ).mp hm x hx y hy
  simp [cfl, hne, e] at this

theorem match_row {σ : List Nat} (hm : isMatch n σ = true) {i t : Nat} (ht : t < n)
    (hf : ∀ w ∈ σ, w / n ≠ i) : isMatch n (var n i t :: σ) = true ↔ ∀ w ∈ σ, w % n ≠ t := by
  rw [isMatch_cons]
  constructor
  · rintro ⟨_, H⟩ w hw e
    have := H w hw
    simp [cfl, var_mod n i t ht, e] at this
    exact hf w hw (by rw [← this, var_div n i t ht])
  · intro H
    refine ⟨hm, fun w hw => ?_⟩
    have h1 := hf w hw; have h2 := H w hw
    simp only [cfl, Bool.and_eq_false_iff, bne_eq_false_iff_eq, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
      var_div n i t ht, var_mod n i t ht]
    right; exact ⟨fun e => h1 e.symm, fun e => h2 e.symm⟩

theorem match_col {σ : List Nat} (hm : isMatch n σ = true) {s j : Nat} (hj : j < n)
    (hf : ∀ w ∈ σ, w % n ≠ j) : isMatch n (var n s j :: σ) = true ↔ ∀ w ∈ σ, w / n ≠ s := by
  rw [isMatch_cons]
  constructor
  · rintro ⟨_, H⟩ w hw e
    have := H w hw
    simp [cfl, var_div n s j hj, e] at this
    exact hf w hw (by rw [← this, var_mod n s j hj])
  · intro H
    refine ⟨hm, fun w hw => ?_⟩
    have h1 := hf w hw; have h2 := H w hw
    simp only [cfl, Bool.and_eq_false_iff, bne_eq_false_iff_eq, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
      var_div n s j hj, var_mod n s j hj]
    right; exact ⟨fun e => h2 e.symm, fun e => h1 e.symm⟩

/-- Counting the free lines of a block. -/
theorem count_freeQ (Q : Nat → Prop) [DecidablePred Q] (h : Nat → Nat) (M : Nat) :
    ∀ g : List Nat, (g.map h).Nodup → (∀ v ∈ g, h v < M ∧ Q (h v)) →
    rsum M (fun t => if Q t ∧ ∀ v ∈ g, h v ≠ t then 1 else 0) =
      rsum M (fun t => if Q t then 1 else 0) - g.length := by
  intro g
  induction g with
  | nil => intro _ _; simp
  | cons v g ih =>
    intro hnd hlt
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have hfree : ∀ w ∈ g, h w ≠ h v := fun w hw e => hnd.1 ⟨w, hw, e⟩
    have e : ∀ t, (if Q t ∧ ∀ w ∈ v :: g, h w ≠ t then (1 : Int) else 0) =
        (if Q t ∧ ∀ w ∈ g, h w ≠ t then 1 else 0) - (if t = h v then 1 else 0) := by
      intro t
      by_cases ht : t = h v
      · subst ht
        have hq := (hlt v (by simp)).2
        rw [if_neg (by simp), if_pos ⟨hq, hfree⟩, if_pos rfl]; rfl
      · rw [if_neg ht]
        by_cases hg : Q t ∧ ∀ w ∈ g, h w ≠ t
        · rw [if_pos hg, if_pos ⟨hg.1, by
            intro w hw; simp only [List.mem_cons] at hw
            rcases hw with rfl | hw; exact fun e => ht e.symm; exact hg.2 w hw⟩]; rfl
        · rw [if_neg hg, if_neg (fun H => hg ⟨H.1, fun w hw => H.2 w (by simp [hw])⟩)]; rfl
    rw [rsum_congr M _ _ (fun t _ => e t), rsum_sub', ih hnd.2 (fun w hw => hlt w (by simp [hw])),
      rsum_pick M (h v) (fun _ => 1), if_pos (hlt v (by simp)).1]
    simp; omega

/-! ## Symmetric design on block 2 -/

/-- Symmetric value depending on the length. -/
def cvf (m D : Nat) (l : List Nat) : Int := cv m D l.length

theorem SL_cvf (m D : Nat) : SL (cvf m D) := by
  intro l l' hl hl' hm; unfold cvf; rw [len_eq hl hl' hm]

theorem sym_row (p : Nat) (bp bh : Nat → Nat) (m : Nat) (hn : 0 < n)
    (hm : rsum n (fun t => if bh t = 2 then 1 else 0) = (m : Int))
    {σ : List Nat} (hσ : σ.Nodup) (hσm : isMatch n σ = true) (hσb : ∀ w ∈ σ, blk bp bh n w = 2)
    (hlen : σ.length ≤ 2) {i : Nat} (hf : ∀ w ∈ σ, w / n ≠ i) :
    (p : Int) ∣ locL n (cvf m 3) σ (var n i) n (fun t => bh t = 2) - cvf m 3 σ :=  by
  have e : ∀ t < n, (if bh t = 2 ∧ isMatch n (var n i t :: σ) = true then cvf m 3 (var n i t :: σ) else 0) =
      (if bh t = 2 ∧ ∀ w ∈ σ, w % n ≠ t then 1 else 0) * cv m 3 (σ.length + 1) := by
    intro t ht
    have key := match_row hσm ht hf
    by_cases h2 : ∀ w ∈ σ, w % n ≠ t
    · have h3 := key.mpr h2; by_cases h1 : bh t = 2
      · rw [if_pos ⟨h1, h3⟩, if_pos ⟨h1, h2⟩]; simp [cvf]
      · rw [if_neg (fun h => h1 h.1), if_neg (fun h => h1 h.1)]; simp
    · have h3 : isMatch n (var n i t :: σ) = false := by
        cases h : isMatch n (var n i t :: σ)
        · rfl
        · exact absurd (key.mp h) h2
      rw [if_neg (fun h => by rw [h3] at h; exact absurd h.2 (by simp)), if_neg (fun h => h2 h.2)]; simp
  unfold locL
  rw [rsum_congr _ _ _ e, rsum_mulc, count_freeQ (fun t => bh t = 2) (· % n) n σ (nodup_mod hσ hσm)
    (fun w hw => ⟨Nat.mod_lt _ hn, (blk_eq (hσb w hw) (by omega)).2⟩),
    hm, cvf, cv_step m 3 σ.length (by omega)]
  simp

theorem sym_col (p : Nat) (bp bh : Nat → Nat) (m P2 : Nat) (hn : 0 < n)
    (hP : rsum (n + k) (fun s => if bp s = 2 then 1 else 0) = (P2 : Int)) (hPm : (p : Int) ∣ (P2 : Int) - m)
    {σ : List Nat} (hσ : σ.Nodup) (hσm : isMatch n σ = true) (hσb : ∀ w ∈ σ, blk bp bh n w = 2 ∧ w < (n + k) * n)
    (hlen : σ.length ≤ 2) {j : Nat} (hj : j < n) (hf : ∀ w ∈ σ, w % n ≠ j) :
    (p : Int) ∣ locL n (cvf m 3) σ (fun s => var n s j) (n + k) (fun s => bp s = 2) - cvf m 3 σ :=  by
  have e : ∀ t < n + k, (if bp t = 2 ∧ isMatch n (var n t j :: σ) = true then cvf m 3 (var n t j :: σ) else 0) =
      (if bp t = 2 ∧ ∀ w ∈ σ, w / n ≠ t then 1 else 0) * cv m 3 (σ.length + 1) := by
    intro t _
    have key := match_col (s := t) hσm hj hf
    by_cases h2 : ∀ w ∈ σ, w / n ≠ t
    · have h3 := key.mpr h2; by_cases h1 : bp t = 2
      · rw [if_pos ⟨h1, h3⟩, if_pos ⟨h1, h2⟩]; simp [cvf]
      · rw [if_neg (fun h => h1 h.1), if_neg (fun h => h1 h.1)]; simp
    · have h3 : isMatch n (var n t j :: σ) = false := by
        cases h : isMatch n (var n t j :: σ)
        · rfl
        · exact absurd (key.mp h) h2
      rw [if_neg (fun h => by rw [h3] at h; exact absurd h.2 (by simp)), if_neg (fun h => h2 h.2)]; simp
  unfold locL
  rw [rsum_congr _ _ _ e, rsum_mulc, count_freeQ (fun t => bp t = 2) (· / n) (n + k) σ (nodup_div hσ hσm)
    (fun w hw => ⟨(Nat.div_lt_iff_lt_mul hn).mpr (hσb w hw).2, (blk_eq (hσb w hw).1 (by omega)).1⟩),
    hP, cvf, cv_step m 3 σ.length (by omega)]
  have : ((P2 : Int) - σ.length) * cv m 3 (σ.length + 1) - ((m : Int) - σ.length) * cv m 3 (σ.length + 1) =
      ((P2 : Int) - m) * cv m 3 (σ.length + 1) := by rw [← Int.sub_mul]; congr 1; omega
  rw [this]; exact Int.dvd_trans hPm (Int.dvd_mul_right _ _)


/-! ## Blocks: `{a,a'} × {b,b'}`, `{x} × {h}`, rest -/

def bq (a a' x : Nat) (i : Nat) : Nat := if i = a ∨ i = a' then 0 else if i = x then 1 else 2

theorem bq_lt (a a' x i : Nat) : bq a a' x i < 3 := by unfold bq; split <;> (try split) <;> omega

theorem bq0 (a a' x i : Nat) : bq a a' x i = 0 ↔ i = a ∨ i = a' := by
  unfold bq; by_cases h : i = a ∨ i = a'
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; split <;> simp_all

theorem bq1 {a a' x : Nat} (h1 : x ≠ a) (h2 : x ≠ a') (i : Nat) : bq a a' x i = 1 ↔ i = x := by
  unfold bq; by_cases h : i = a ∨ i = a'
  · simp only [h, if_true]; constructor
    · intro e; omega
    · rintro rfl; omega
  · simp only [h, if_false]; split <;> simp_all

theorem bq2 (a a' x i : Nat) : bq a a' x i = 2 ↔ ¬(i = a ∨ i = a') ∧ i ≠ x := by
  unfold bq; by_cases h : i = a ∨ i = a'
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; by_cases h' : i = x
    · rw [if_pos h']; simp [h, h']
    · rw [if_neg h']; simp [h, h']

theorem rsum2 {M b b2 : Nat} (hb : b < M) (hb2 : b2 < M) (d1 : b ≠ b2)
    (Q : Nat → Prop) [DecidablePred Q] (hQ : ∀ t, Q t ↔ t = b ∨ t = b2)
    (C : Nat → Prop) [DecidablePred C] (F : Nat → Int) :
    rsum M (fun t => if Q t ∧ C t then F t else 0) =
      (if C b then F b else 0) + (if C b2 then F b2 else 0) := by
  have e : ∀ t < M, (if Q t ∧ C t then F t else 0) =
      (if t = b then (if C t then F t else 0) else 0) + (if t = b2 then (if C t then F t else 0) else 0) := by
    intro t _
    by_cases q1 : t = b
    · subst q1; simp [hQ, d1]
    · by_cases q2 : t = b2
      · subst q2; simp [hQ, Ne.symm d1]
      · simp [hQ, q1, q2]
  rw [rsum_congr _ _ _ e, rsum_add, rsum_pick, rsum_pick]
  simp [hb, hb2]

theorem rsum1 {M h : Nat} (hh : h < M) (Q : Nat → Prop) [DecidablePred Q] (hQ : ∀ t, Q t ↔ t = h)
    (C : Nat → Prop) [DecidablePred C] (F : Nat → Int) :
    rsum M (fun t => if Q t ∧ C t then F t else 0) = if C h then F h else 0 := by
  have e : ∀ t < M, (if Q t ∧ C t then F t else 0) = (if t = h then (if C t then F t else 0) else 0) := by
    intro t _; by_cases q1 : t = h
    · subst q1; simp [hQ]
    · simp [hQ, q1]
  rw [rsum_congr _ _ _ e, rsum_pick]; simp [hh]

/-- The `1 × 1` block: constant `1`. -/
theorem one_row {bp bh : Nat → Nat} {x h : Nat} (hh : h < n) (hx : ∀ i, bp i = 1 ↔ i = x)
    (hhq : ∀ j, bh j = 1 ↔ j = h) {σ : List Nat} (hσb : ∀ w ∈ σ, blk bp bh n w = 1) {i : Nat}
    (hi : bp i = 1) (hf : ∀ w ∈ σ, w / n ≠ i) :
    locL n (fun _ => (1 : Int)) σ (var n i) n (fun t => bh t = 1) = 1 := by
  have hσ : σ = [] := List.eq_nil_iff_forall_not_mem.mpr (fun w hw =>
    hf w hw (by rw [(hx _).mp (blk_eq (hσb w hw) (by omega)).1, (hx i).mp hi]))
  subst hσ; unfold locL
  rw [rsum1 hh _ hhq]; simp [isMatch_one]

theorem one_col {bp bh : Nat → Nat} {x h : Nat} (hxl : x < n + k) (hx : ∀ i, bp i = 1 ↔ i = x)
    (hhq : ∀ j, bh j = 1 ↔ j = h) {σ : List Nat} (hσb : ∀ w ∈ σ, blk bp bh n w = 1) {j : Nat}
    (hj : bh j = 1) (hf : ∀ w ∈ σ, w % n ≠ j) :
    locL n (fun _ => (1 : Int)) σ (fun s => var n s j) (n + k) (fun s => bp s = 1) = 1 := by
  have hσ : σ = [] := List.eq_nil_iff_forall_not_mem.mpr (fun w hw =>
    hf w hw (by rw [(hhq _).mp (blk_eq (hσb w hw) (by omega)).2, (hhq j).mp hj]))
  subst hσ; unfold locL
  rw [rsum1 hxl _ hx]; simp [isMatch_one]

/-- Rectangle window on the `2 × 2` block: levels `0, r, det`. -/
def Aw (n a a' b b' : Nat) (l : List Nat) : Int :=
  one (rect n a a' b b') l + (tprod (dl n a b) (dl n a' b') l - tprod (dl n a b') (dl n a' b) l)

theorem SL_Aw (n a a' b b' : Nat) : SL (Aw n a a' b b') := by
  intro l l' hl hl' hm; unfold Aw
  rw [SL_one _ l l' hl hl' hm, SL_tprod _ _ l l' hl hl' hm, SL_tprod _ _ l l' hl hl' hm]

/-- Shape of the restriction of a matching to the `2 × 2` block when a block pigeon is free. -/
theorem shape0_row {bp bh : Nat → Nat} {a a' b b' : Nat} (hP : ∀ i, bp i = 0 ↔ i = a ∨ i = a')
    (hH : ∀ j, bh j = 0 ↔ j = b ∨ j = b') (hn : 0 < n) {σ : List Nat} (hσ : σ.Nodup)
    (hσm : isMatch n σ = true) (hσb : ∀ w ∈ σ, blk bp bh n w = 0) {i : Nat} (hi : bp i = 0)
    (hf : ∀ w ∈ σ, w / n ≠ i) :
    σ = [] ∨ ∃ i' j', σ = [var n i' j'] ∧ (i' = a ∨ i' = a') ∧ (j' = b ∨ j' = b') ∧ i' ≠ i ∧ j' < n := by
  have dec : ∀ w ∈ σ, w = var n (w / n) (w % n) ∧ (w / n = a ∨ w / n = a') ∧ (w % n = b ∨ w % n = b') := by
    intro w hw
    obtain ⟨e1, e2⟩ := blk_eq (hσb w hw) (by omega)
    exact ⟨(var_decode n w).symm, (hP _).mp e1, (hH _).mp e2⟩
  have hiq := (hP i).mp hi
  match σ, hσ, hσm with
  | [], _, _ => exact Or.inl rfl
  | [v], _, _ =>
    obtain ⟨e, h1, h2⟩ := dec v (by simp)
    exact Or.inr ⟨v / n, v % n, by rw [← e], h1, h2, hf v (by simp), Nat.mod_lt _ hn⟩
  | v :: w :: _, hnd, hm =>
    exfalso
    have hv := (dec v (by simp)).2.1; have hw := (dec w (by simp)).2.1
    have fv := hf v (by simp); have fw := hf w (by simp)
    have hvw : v / n ≠ w / n := by
      have := (nodup_div hnd hm); simp only [List.map_cons, List.nodup_cons, List.mem_cons] at this
      exact fun e => this.1 (Or.inl e)
    omega


theorem shape0_col {bp bh : Nat → Nat} {a a' b b' : Nat} (hP : ∀ i, bp i = 0 ↔ i = a ∨ i = a')
    (hH : ∀ j, bh j = 0 ↔ j = b ∨ j = b') (hn : 0 < n) {σ : List Nat} (hσ : σ.Nodup)
    (hσm : isMatch n σ = true) (hσb : ∀ w ∈ σ, blk bp bh n w = 0) {j : Nat} (hj : bh j = 0)
    (hf : ∀ w ∈ σ, w % n ≠ j) :
    σ = [] ∨ ∃ i' j', σ = [var n i' j'] ∧ (i' = a ∨ i' = a') ∧ (j' = b ∨ j' = b') ∧ j' ≠ j ∧ j' < n := by
  have dec : ∀ w ∈ σ, w = var n (w / n) (w % n) ∧ (w / n = a ∨ w / n = a') ∧ (w % n = b ∨ w % n = b') := by
    intro w hw
    obtain ⟨e1, e2⟩ := blk_eq (hσb w hw) (by omega)
    exact ⟨(var_decode n w).symm, (hP _).mp e1, (hH _).mp e2⟩
  have hjq := (hH j).mp hj
  match σ, hσ, hσm with
  | [], _, _ => exact Or.inl rfl
  | [v], _, _ =>
    obtain ⟨e, h1, h2⟩ := dec v (by simp)
    exact Or.inr ⟨v / n, v % n, by rw [← e], h1, h2, hf v (by simp), Nat.mod_lt _ hn⟩
  | v :: w :: _, hnd, hm =>
    exfalso
    have hv := (dec v (by simp)).2.2; have hw := (dec w (by simp)).2.2
    have fv := hf v (by simp); have fw := hf w (by simp)
    have hvw : v % n ≠ w % n := by
      have := (nodup_mod hnd hm); simp only [List.map_cons, List.nodup_cons, List.mem_cons] at this
      exact fun e => this.1 (Or.inl e)
    omega

section B0
variable {a a' b b' : Nat}

theorem blk0_row (hb : b < n) (hb' : b' < n) (p1 : a ≠ a') (q1 : b ≠ b') {bp bh : Nat → Nat}
    (hP : ∀ i, bp i = 0 ↔ i = a ∨ i = a') (hH : ∀ j, bh j = 0 ↔ j = b ∨ j = b')
    {σ : List Nat} (hσ : σ.Nodup) (hσm : isMatch n σ = true) (hσb : ∀ w ∈ σ, blk bp bh n w = 0)
    {i : Nat} (hi : bp i = 0) (hf : ∀ w ∈ σ, w / n ≠ i) (φ : List Nat → Int)
    (hφ : φ = Aw n a a' b b' ∨ φ = cvf 2 2) :
    locL n φ σ (var n i) n (fun t => bh t = 0) = φ σ := by
  have hiq := (hP i).mp hi
  rcases shape0_row hP hH (by omega) hσ hσm hσb hi hf with rfl | ⟨i', j', rfl, hi', hj', hne, hj'n⟩
  · unfold locL
    rw [rsum2 hb hb' q1 _ hH]
    simp only [isMatch_one, if_true]
    rcases hφ with rfl | rfl <;> rcases hiq with rfl | rfl <;>
      simp [Aw, one, tprod, dl, rect, cvf, cv, ff, var_eq_iff, hb, hb', p1, q1, Ne.symm p1, Ne.symm q1]
  · unfold locL
    rw [rsum2 hb hb' q1 _ hH]
    simp only [isMatch_pair hb hj'n, isMatch_pair hb' hj'n]
    rcases hφ with rfl | rfl <;> rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;>
      rcases hiq with rfl | rfl <;> simp at hne <;>
      simp [Aw, one, tprod, dl, rect, cvf, cv, ff, var_eq_iff, hb, hb', p1, q1, Ne.symm p1, Ne.symm q1]

theorem blk0_col (ha : a < n + k) (ha' : a' < n + k) (hb : b < n) (hb' : b' < n) (p1 : a ≠ a')
    (q1 : b ≠ b') {bp bh : Nat → Nat}
    (hP : ∀ i, bp i = 0 ↔ i = a ∨ i = a') (hH : ∀ j, bh j = 0 ↔ j = b ∨ j = b')
    {σ : List Nat} (hσ : σ.Nodup) (hσm : isMatch n σ = true) (hσb : ∀ w ∈ σ, blk bp bh n w = 0)
    {j : Nat} (hj : bh j = 0) (hf : ∀ w ∈ σ, w % n ≠ j) (φ : List Nat → Int)
    (hφ : φ = Aw n a a' b b' ∨ φ = cvf 2 2) :
    locL n φ σ (fun s => var n s j) (n + k) (fun s => bp s = 0) = φ σ := by
  have hjq := (hH j).mp hj
  have hjn : j < n := by rcases hjq with rfl | rfl <;> assumption
  rcases shape0_col hP hH (by omega) hσ hσm hσb hj hf with rfl | ⟨i', j', rfl, hi', hj', hne, hj'n⟩
  · unfold locL
    rw [rsum2 ha ha' p1 _ hP]
    simp only [isMatch_one, if_true]
    rcases hφ with rfl | rfl <;> rcases hjq with rfl | rfl <;>
      simp [Aw, one, tprod, dl, rect, cvf, cv, ff, var_eq_iff, hb, hb', p1, q1, Ne.symm p1, Ne.symm q1]
  · unfold locL
    rw [rsum2 ha ha' p1 _ hP]
    simp only [isMatch_pair hjn hj'n]
    rcases hφ with rfl | rfl <;> rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;>
      rcases hjq with rfl | rfl <;> simp at hne <;>
      simp [Aw, one, tprod, dl, rect, cvf, cv, ff, var_eq_iff, hb, hb', p1, q1, Ne.symm p1, Ne.symm q1]

end B0


theorem count3 {N a a' x : Nat} (d1 : a ≠ a') (d2 : x ≠ a) (d3 : x ≠ a') (ha : a < N) (ha' : a' < N)
    (hx : x < N) : rsum N (fun t => if bq a a' x t = 2 then (1 : Int) else 0) = (N : Int) - 3 := by
  have pt : ∀ t, (if bq a a' x t = 2 then (1 : Int) else 0) =
      1 - ((if t = a then 1 else 0) + (if t = a' then 1 else 0) + (if t = x then 1 else 0)) := by
    intro t
    simp only [bq2]
    by_cases q1 : t = a
    · subst q1; simp [d1, Ne.symm d2]
    by_cases q2 : t = a'
    · subst q2; simp [q1, Ne.symm d3]
    by_cases q3 : t = x
    · subst q3; simp [q1, q2]
    simp [q1, q2, q3]
  rw [rsum_congr _ _ _ (fun t _ => pt t), rsum_sub', rsum_const, rsum_add, rsum_add,
    rsum_pick, rsum_pick, rsum_pick]
  simp [ha, ha', hx]

/-- **Window product on the three blocks.** For `φ₀ = Aw` (rectangle window) or `φ₀ = cvf 2 2`
(symmetric design on the `2 × 2` block), `Prod (φ₀, 1, cvf (n-3) 3)` is a window at levels `0, 1, 2`. -/
theorem win3 {p : Nat} (hk : (p : Int) ∣ k) {a a' x b b' h : Nat} (p1 : a ≠ a') (p2 : x ≠ a) (p3 : x ≠ a')
    (q1 : b ≠ b') (q2 : h ≠ b) (q3 : h ≠ b') (ha : a < n + k) (ha' : a' < n + k) (hx : x < n + k)
    (hb : b < n) (hb' : b' < n) (hh : h < n) (φ0 : List Nat → Int)
    (hφ : φ0 = Aw n a a' b b' ∨ φ0 = cvf 2 2) (e : Nat) (he : e ≤ 2) :
    Bal p n k (ProdExt.Prod (bq a a' x) (bq b b' h) n (tri φ0 (fun _ => 1) (cvf (n - 3) 3)))
      (ProdExt.Prod (bq a a' x) (bq b b' h) n (tri φ0 (fun _ => 1) (cvf (n - 3) 3))) e := by
  have hn : 0 < n := by omega
  have sφ0 : SL φ0 := by rcases hφ with rfl | rfl; exact SL_Aw _ _ _ _ _; exact SL_cvf _ _
  have hm : rsum n (fun t => if bq b b' h t = 2 then 1 else 0) = ((n - 3 : Nat) : Int) := by
    rw [count3 q1 q2 q3 hb hb' hh]; omega
  have hP : rsum (n + k) (fun s => if bq a a' x s = 2 then 1 else 0) = ((n + k - 3 : Nat) : Int) := by
    rw [count3 p1 p2 p3 ha ha' hx]; omega
  have hPm : (p : Int) ∣ ((n + k - 3 : Nat) : Int) - ((n - 3 : Nat) : Int) := by
    rw [show ((n + k - 3 : Nat) : Int) - ((n - 3 : Nat) : Int) = k by omega]; exact hk
  have dz : ∀ {A B : Int}, A = B → (p : Int) ∣ A - B := fun e => by rw [e, Int.sub_self]; exact Int.dvd_zero _
  apply bal_win p _ _ (bq_lt a a' x) (bq_lt b b' h) _ (SL_tri sφ0 (fun _ _ _ _ _ => rfl) (SL_cvf _ _)) e
  · intro g hg hl _ i hi hf
    obtain ⟨hnd, hmt, hmem, hlen⟩ := fl_props (bq a a' x) (bq b b' h) hg (bq a a' x i)
    have hf' : ∀ w ∈ fl (bq a a' x) (bq b b' h) n (bq a a' x i) g, w / n ≠ i :=
      fun w hw => hf w (hmem w hw).2
    have hmem' := fun w hw => (hmem w hw).1
    rcases (by have := bq_lt a a' x i; omega : bq a a' x i = 0 ∨ bq a a' x i = 1 ∨ bq a a' x i = 2)
      with h0 | h0 | h0 <;> rw [h0] at hf' hmem' hnd hmt hlen ⊢
    · exact dz (blk0_row hb hb' p1 q1 (bq0 a a' x) (bq0 b b' h) hnd hmt hmem' h0 hf' φ0 hφ)
    · exact dz (one_row hh (bq1 p2 p3) (bq1 q2 q3) hmem' h0 hf')
    · exact sym_row p _ _ (n - 3) hn hm hnd hmt hmem' (by omega) hf'
  · intro g hg hl _ j hj hf
    obtain ⟨hnd, hmt, hmem, hlen⟩ := fl_props (bq a a' x) (bq b b' h) hg (bq b b' h j)
    have hf' : ∀ w ∈ fl (bq a a' x) (bq b b' h) n (bq b b' h j) g, w % n ≠ j :=
      fun w hw => hf w (hmem w hw).2
    have hmem2 : ∀ w ∈ fl (bq a a' x) (bq b b' h) n (bq b b' h j) g,
        blk (bq a a' x) (bq b b' h) n w = bq b b' h j ∧ w < (n + k) * n :=
      fun w hw => ⟨(hmem w hw).1, CM_lt hg (hmem w hw).2⟩
    have hmem' := fun w hw => (hmem w hw).1
    rcases (by have := bq_lt b b' h j; omega : bq b b' h j = 0 ∨ bq b b' h j = 1 ∨ bq b b' h j = 2)
      with h0 | h0 | h0 <;> rw [h0] at hf' hmem' hmem2 hnd hmt hlen ⊢
    · exact dz (blk0_col ha ha' hb hb' p1 q1 (bq0 a a' x) (bq0 b b' h) hnd hmt hmem' h0 hf' φ0 hφ)
    · exact dz (one_col hx (bq1 p2 p3) (bq1 q2 q3) hmem' h0 hf')
    · exact sym_col p _ _ (n - 3) (n + k - 3) hn hP hPm hnd hmt hmem2 (by omega) hj hf'

end Programme.«20261026-1402-proof-complexity».Win
