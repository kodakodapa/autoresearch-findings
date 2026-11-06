import Programme.«20261026-1402-proof-complexity».Win

/-!
# The `F₂` extra generator `T` extends at level 2 (th's K31, extension part)

Over `𝔽₂` the zero-link space at level 2 is spanned by rectangle products and one extra
function `T`, the indicator of the 2-matchings inside the `3 × 3` block of pigeons `0,1,2` and
holes `0,1,2`. Here `T` gets an explicit level-2 extension when `n ≥ 4` and `2 ∣ k`: the
two-block product `Y = (0,0,1,1)_block ⊗ d`, with `d` a 1-design on the outside board
(pigeon `i < n` to hole `i`, extra pigeons to hole `3`). `Y` agrees with `T` on 2-matchings.
The product is not a window block by block (the outside factor fails at one edge), so
`bal_win'` weights each local condition by the other factors.
-/

set_option linter.unusedSimpArgs false

namespace Programme.«20261026-1402-proof-complexity».TExt

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero var_div var_mod)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt var_decode rsum_pick rsum_const)
open Programme.«20261025-1627-proof-complexity».OntoExt3 (rsum_sub')
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261026-1402-proof-complexity».ExtLemma Programme.«20261026-1402-proof-complexity».ExtLin Programme.«20261026-1402-proof-complexity».ProdExt Programme.«20261026-1402-proof-complexity».RectBlock Programme.«20261026-1402-proof-complexity».RectExt Programme.«20261026-1402-proof-complexity».SymDesign Programme.«20261026-1402-proof-complexity».Win

variable {n k : Nat}

/-- `bal_win` with each local condition multiplied by the other block factors. -/
theorem bal_win' (p : Nat) (bp bh : Nat → Nat) (hbp : ∀ i, bp i < 3) (hbh : ∀ j, bh j < 3)
    (φ : Nat → List Nat → Int) (hφ : ∀ c, SL (φ c)) (e : Nat)
    (hr : ∀ g, CM n k g → g.length = e → okL bp bh n g = true → ∀ i < n + k, pfree n g i →
      (p : Int) ∣ (locL n (φ (bp i)) (fl bp bh n (bp i) g) (var n i) n (fun t => bh t = bp i) -
        φ (bp i) (fl bp bh n (bp i) g)) * oth bp bh n φ (bp i) g)
    (hc : ∀ g, CM n k g → g.length = e → okL bp bh n g = true → ∀ j < n, hfree n g j →
      (p : Int) ∣ (locL n (φ (bh j)) (fl bp bh n (bh j) g) (fun s => var n s j) (n + k)
        (fun s => bp s = bh j) - φ (bh j) (fl bp bh n (bh j) g)) * oth bp bh n φ (bh j) g) :
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
      rw [← Int.sub_mul]; exact this
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
      rw [← Int.sub_mul]; exact this
    · simp

/-! ## Length-only local factors -/

def lf (G : Nat → Int) (l : List Nat) : Int := G l.length

theorem SL_lf (G : Nat → Int) : SL (lf G) := by
  intro l l' hl hl' hm; unfold lf; rw [len_eq hl hl' hm]

theorem gsym_row (bp bh : Nat → Nat) (b m : Nat) (G : Nat → Int) (hn : 0 < n) (hb : b < 3)
    (hm : rsum n (fun t => if bh t = b then 1 else 0) = (m : Int))
    {σ : List Nat} (hσ : σ.Nodup) (hσm : isMatch n σ = true) (hσb : ∀ w ∈ σ, blk bp bh n w = b)
    {i : Nat} (hf : ∀ w ∈ σ, w / n ≠ i) :
    locL n (lf G) σ (var n i) n (fun t => bh t = b) = ((m : Int) - σ.length) * G (σ.length + 1) := by
  have e : ∀ t < n, (if bh t = b ∧ isMatch n (var n i t :: σ) = true then lf G (var n i t :: σ) else 0) =
      (if bh t = b ∧ ∀ w ∈ σ, w % n ≠ t then 1 else 0) * G (σ.length + 1) := by
    intro t ht
    have key := match_row hσm ht hf
    by_cases h2 : ∀ w ∈ σ, w % n ≠ t
    · have h3 := key.mpr h2; by_cases h1 : bh t = b
      · rw [if_pos ⟨h1, h3⟩, if_pos ⟨h1, h2⟩]; simp [lf]
      · rw [if_neg (fun h => h1 h.1), if_neg (fun h => h1 h.1)]; simp
    · have h3 : isMatch n (var n i t :: σ) = false := by
        cases h : isMatch n (var n i t :: σ)
        · rfl
        · exact absurd (key.mp h) h2
      rw [if_neg (fun h => by rw [h3] at h; exact absurd h.2 (by simp)), if_neg (fun h => h2 h.2)]; simp
  unfold locL
  rw [rsum_congr _ _ _ e, rsum_mulc, count_freeQ (fun t => bh t = b) (· % n) n σ (nodup_mod hσ hσm)
    (fun w hw => ⟨Nat.mod_lt _ hn, (blk_eq (hσb w hw) hb).2⟩), hm]

theorem gsym_col (bp bh : Nat → Nat) (b P2 : Nat) (G : Nat → Int) (hn : 0 < n) (hb : b < 3)
    (hP : rsum (n + k) (fun s => if bp s = b then 1 else 0) = (P2 : Int))
    {σ : List Nat} (hσ : σ.Nodup) (hσm : isMatch n σ = true)
    (hσb : ∀ w ∈ σ, blk bp bh n w = b ∧ w < (n + k) * n)
    {j : Nat} (hj : j < n) (hf : ∀ w ∈ σ, w % n ≠ j) :
    locL n (lf G) σ (fun s => var n s j) (n + k) (fun s => bp s = b) =
      ((P2 : Int) - σ.length) * G (σ.length + 1) := by
  have e : ∀ t < n + k, (if bp t = b ∧ isMatch n (var n t j :: σ) = true then lf G (var n t j :: σ) else 0) =
      (if bp t = b ∧ ∀ w ∈ σ, w / n ≠ t then 1 else 0) * G (σ.length + 1) := by
    intro t _
    have key := match_col (s := t) hσm hj hf
    by_cases h2 : ∀ w ∈ σ, w / n ≠ t
    · have h3 := key.mpr h2; by_cases h1 : bp t = b
      · rw [if_pos ⟨h1, h3⟩, if_pos ⟨h1, h2⟩]; simp [lf]
      · rw [if_neg (fun h => h1 h.1), if_neg (fun h => h1 h.1)]; simp
    · have h3 : isMatch n (var n t j :: σ) = false := by
        cases h : isMatch n (var n t j :: σ)
        · rfl
        · exact absurd (key.mp h) h2
      rw [if_neg (fun h => by rw [h3] at h; exact absurd h.2 (by simp)), if_neg (fun h => h2 h.2)]; simp
  unfold locL
  rw [rsum_congr _ _ _ e, rsum_mulc, count_freeQ (fun t => bp t = b) (· / n) (n + k) σ (nodup_div hσ hσm)
    (fun w hw => ⟨(Nat.div_lt_iff_lt_mul hn).mpr (hσb w hw).2, (blk_eq (hσb w hw).1 hb).1⟩), hP]

/-! ## Counting -/

theorem cnt_lt (a : Nat) : ∀ M, rsum M (fun t => if t < a then 1 else 0) = (min a M : Nat)
  | 0 => by simp [rsum]
  | M + 1 => by simp only [rsum]; rw [cnt_lt a M]; split <;> omega

theorem cnt_ge (a : Nat) : ∀ M, rsum M (fun t => if t < a then 0 else 1) = ((M - min a M : Nat) : Int)
  | 0 => by simp [rsum]
  | M + 1 => by simp only [rsum]; rw [cnt_ge a M]; split <;> omega

/-! ## The blocks and the factors -/

/-- Block 0 = indices `0,1,2`; block 2 = the rest; block 1 is empty. -/
def bt (i : Nat) : Nat := if i < 3 then 0 else 2

theorem bt_lt (i : Nat) : bt i < 3 := by unfold bt; split <;> omega

/-- `(0,0,1,1)` by length. -/
def G0 (s : Nat) : Int := if 2 ≤ s then 1 else 0

/-- Outside 1-design: pigeon `i < n` to hole `i`, extra pigeons `i ≥ n` to hole `3`. -/
def dd (n w : Nat) : Int := if w / n = w % n ∨ (n ≤ w / n ∧ w % n = 3) then 1 else 0

def dl (n : Nat) : List Nat → Int
  | [] => 1
  | [w] => dd n w
  | _ :: _ :: _ => 0

theorem SL_dl (n : Nat) : SL (dl n) := by
  intro l l' hl hl' hm
  have hlen := len_eq hl hl' hm
  rcases l with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> rcases l' with _ | ⟨c, _ | ⟨d, s⟩⟩ <;> simp at hlen <;> try rfl
  have := (hm a).mp (by simp); simp at this; subst this; rfl

/-- The extension `Y`. -/
def Y (n : Nat) : List Nat → Int := ProdExt.Prod bt bt n (tri (lf G0) (fun _ => 1) (dl n))

/-- `T`: indicator of the 2-matchings inside the `3 × 3` block. -/
def T (n : Nat) (l : List Nat) : Int := if l.length = 2 ∧ ∀ w ∈ l, w / n < 3 ∧ w % n < 3 then 1 else 0

theorem blk_bt (w : Nat) : blk bt bt n w = 0 ↔ w / n < 3 ∧ w % n < 3 := by
  unfold blk bt; split <;> split at * <;> (try split at *) <;> omega

theorem blk_bt' (w : Nat) : blk bt bt n w ≠ 1 := by
  unfold blk bt; split <;> split <;> (try split) <;> omega

theorem len_fl02 (bp bh : Nat → Nat) (g : List Nat) :
    (fl bp bh n 0 g).length + (fl bp bh n 2 g).length ≤ g.length := by
  induction g with
  | nil => simp [fl]
  | cons v g ih =>
    simp only [fl, List.filter_cons] at *
    split <;> split <;> simp_all <;> omega

theorem G0_small {g : List Nat} (hl : g.length = 2) (h2 : fl bt bt n 2 g ≠ []) :
    lf G0 (fl bt bt n 0 g) = 0 := by
  have := len_fl02 (n := n) bt bt g
  have : (fl bt bt n 2 g).length ≠ 0 := by simpa using h2
  unfold lf G0; rw [if_neg (by omega)]

theorem one_match (v : Nat) : isMatch n [v] = true := by simp [isMatch, cfl]

/-! ## Local conditions -/

theorem cnt_bt0 (M : Nat) (hM : 3 ≤ M) : rsum M (fun t => if bt t = 0 then 1 else 0) = ((3 : Nat) : Int) := by
  rw [rsum_congr M _ (fun t => if t < 3 then 1 else 0) (fun t _ => by unfold bt; split <;> simp_all),
    cnt_lt]; congr 1; omega

theorem row_out (hn : 4 ≤ n) {i : Nat} (hi : i < n + k) (h3 : 3 ≤ i) :
    locL n (dl n) [] (var n i) n (fun t => bt t = 2) = 1 := by
  unfold locL
  rw [rsum_congr n _ (fun t => if t = (if i < n then i else 3) then 1 else 0) (fun t ht => by
    simp only [one_match, and_true, dl, dd, var_div n i t ht, var_mod n i t ht, bt]
    by_cases hin : i < n <;> simp only [hin, if_true, if_false] <;> (split <;> split <;> (try split) <;> omega)),
    rsum_pick]
  rw [if_pos (by split <;> omega)]

theorem col_out (hn : 4 ≤ n) (hk : (2 : Int) ∣ k) {j : Nat} (hj : j < n) (h3 : 3 ≤ j) :
    (2 : Int) ∣ locL n (dl n) [] (fun s => var n s j) (n + k) (fun s => bt s = 2) - 1 := by
  unfold locL
  rw [rsum_congr (n + k) _ (fun s => (if s = j then 1 else 0) + (if j = 3 then (if s < n then 0 else 1) else 0))
    (fun s hs => by
      simp only [one_match, and_true, dl, dd, var_div n s j hj, var_mod n s j hj, bt]
      by_cases a1 : s < 3 <;> by_cases a2 : s = j <;> by_cases a3 : s < n <;> by_cases a4 : j = 3 <;>
        simp [a1, a2, a3, a4] <;> omega),
    rsum_add, rsum_pick, if_pos (by omega)]
  by_cases hj3 : j = 3
  · simp only [hj3, if_true]; rw [cnt_ge]
    rw [show ((n + k - min n (n + k) : Nat) : Int) = k by omega,
      show (1 : Int) + k - 1 = k by omega]; exact hk
  · simp only [hj3, if_false]; simp

theorem loc_big {σ : List Nat} (hσ : σ ≠ []) (v : Nat → Nat) (M : Nat) (Q : Nat → Prop) [DecidablePred Q] :
    locL n (dl n) σ v M Q = 0 := by
  unfold locL; apply rsum_zero; intro t _
  obtain ⟨a, r, rfl⟩ := List.exists_cons_of_ne_nil hσ
  split <;> rfl

/-! ## Main theorem -/

theorem Y_bal (hn : 4 ≤ n) (hk : (2 : Int) ∣ k) : Bal 2 n k (Y n) (Y n) 2 := by
  have hn0 : 0 < n := by omega
  have sφ : ∀ c, SL (tri (lf G0) (fun _ => 1) (dl n) c) := SL_tri (SL_lf _) (fun _ _ _ _ _ => rfl) (SL_dl n)
  apply bal_win' 2 bt bt bt_lt bt_lt _ sφ 2
  · intro g hg hl hok i hi hf
    obtain ⟨hnd, hmt, hmem, hlen⟩ := fl_props bt bt hg (bt i)
    have hf' : ∀ w ∈ fl bt bt n (bt i) g, w / n ≠ i := fun w hw => hf w (hmem w hw).2
    have hmem' := fun w hw => (hmem w hw).1
    by_cases h3 : i < 3
    · have h0 : bt i = 0 := by simp [bt, h3]
      rw [h0] at hf' hmem' hnd hmt hlen ⊢
      show (2 : Int) ∣ (locL n (lf G0) _ _ _ _ - lf G0 _) * _
      rw [gsym_row bt bt 0 3 G0 hn0 (by omega) (cnt_bt0 n (by omega)) hnd hmt hmem' hf']
      have hl2 := len_fl02 (n := n) bt bt g
      apply Int.dvd_trans _ (Int.dvd_mul_right _ _)
      unfold lf G0
      rcases (by omega : (fl bt bt n 0 g).length = 0 ∨ (fl bt bt n 0 g).length = 1 ∨
        (fl bt bt n 0 g).length = 2) with h | h | h <;> rw [h] <;> decide
    · have h2 : bt i = 2 := by simp [bt, h3]
      rw [h2] at hf' hmem' hnd hmt hlen ⊢
      show (2 : Int) ∣ (locL n (dl n) _ _ _ _ - dl n _) * _
      by_cases he : fl bt bt n 2 g = []
      · rw [he, row_out hn hi (by omega)]; simp [dl]
      · rw [loc_big he]; unfold oth
        simp only [show (2 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 1 by omega, if_false, if_true, tri]
        rw [G0_small hl he]; simp
  · intro g hg hl hok j hj hf
    obtain ⟨hnd, hmt, hmem, hlen⟩ := fl_props bt bt hg (bt j)
    have hf' : ∀ w ∈ fl bt bt n (bt j) g, w % n ≠ j := fun w hw => hf w (hmem w hw).2
    have hmem2 : ∀ w ∈ fl bt bt n (bt j) g, blk bt bt n w = bt j ∧ w < (n + k) * n :=
      fun w hw => ⟨(hmem w hw).1, CM_lt hg (hmem w hw).2⟩
    by_cases h3 : j < 3
    · have h0 : bt j = 0 := by simp [bt, h3]
      rw [h0] at hf' hmem2 hnd hmt hlen ⊢
      show (2 : Int) ∣ (locL n (lf G0) _ _ _ _ - lf G0 _) * _
      rw [gsym_col bt bt 0 3 G0 hn0 (by omega) (cnt_bt0 (n + k) (by omega)) hnd hmt hmem2 hj hf']
      apply Int.dvd_trans _ (Int.dvd_mul_right _ _)
      unfold lf G0
      rcases (by omega : (fl bt bt n 0 g).length = 0 ∨ (fl bt bt n 0 g).length = 1 ∨
        (fl bt bt n 0 g).length = 2) with h | h | h <;> rw [h] <;> decide
    · have h2 : bt j = 2 := by simp [bt, h3]
      rw [h2] at hf' hmem2 hnd hmt hlen ⊢
      show (2 : Int) ∣ (locL n (dl n) _ _ _ _ - dl n _) * _
      by_cases he : fl bt bt n 2 g = []
      · rw [he]; exact Int.dvd_trans (col_out hn hk hj (by omega)) (Int.dvd_mul_right _ _)
      · rw [loc_big he]; unfold oth
        simp only [show (2 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 1 by omega, if_false, if_true, tri]
        rw [G0_small hl he]; simp

theorem Y_eq {g : List Nat} (hl : g.length = 2) : Y n g = T n g := by
  unfold Y T ProdExt.Prod
  by_cases hall : ∀ w ∈ g, w / n < 3 ∧ w % n < 3
  · have hb : ∀ w ∈ g, blk bt bt n w = 0 := fun w hw => (blk_bt w).mpr (hall w hw)
    have hok : okL bt bt n g = true := by
      unfold okL; rw [List.all_eq_true]; intro w hw; simp [hb w hw]
    have f0 : fl bt bt n 0 g = g := List.filter_eq_self.mpr (fun w hw => by simp [hb w hw])
    have f1 : fl bt bt n 1 g = [] := List.filter_eq_nil_iff.mpr (fun w hw => by simp [hb w hw])
    have f2 : fl bt bt n 2 g = [] := List.filter_eq_nil_iff.mpr (fun w hw => by simp [hb w hw])
    rw [if_pos hok, f0, f1, f2, if_pos ⟨hl, hall⟩]; simp [tri, lf, G0, dl, hl]
  · have hT : ¬(g.length = 2 ∧ ∀ w ∈ g, w / n < 3 ∧ w % n < 3) := fun h => hall h.2
    rw [if_neg hT]
    split
    · rename_i hok
      obtain ⟨w, hw, hnot⟩ : ∃ w ∈ g, ¬(w / n < 3 ∧ w % n < 3) := by
        false_or_by_contra; rename_i H; exact hall (fun w hw => Classical.byContradiction (fun h => H ⟨w, hw, h⟩))
      have hlt : blk bt bt n w < 3 := by
        unfold okL at hok; rw [List.all_eq_true] at hok; simpa using hok w hw
      have h2 : blk bt bt n w = 2 := by
        have := blk_bt' (n := n) w; have : blk bt bt n w ≠ 0 := fun h => hnot ((blk_bt w).mp h); omega
      have he : fl bt bt n 2 g ≠ [] := fun h => by
        have : w ∈ fl bt bt n 2 g := (mem_fl ..).mpr ⟨hw, h2⟩
        rw [h] at this; simp at this
      simp only [tri]; rw [G0_small hl he]; simp
    · rfl

/-- **K31 extension part (Lean).** For `n ≥ 4` and `2 ∣ k`, the block indicator `T` has the explicit
level-2 extension `Y` over `ℤ/2`: every free row and column sum of `Y` at a canonical 2-matching `g`
is `≡ T g` mod 2. -/
theorem t_ext (hn : 4 ≤ n) (hk : (2 : Int) ∣ k) : Bal 2 n k (Y n) (T n) 2 :=
  Bal_congr (Y_bal hn hk) (fun g _ hl => by rw [Y_eq hl]; simp)

end Programme.«20261026-1402-proof-complexity».TExt

#print axioms Programme.«20261026-1402-proof-complexity».TExt.t_ext
