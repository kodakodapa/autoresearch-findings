import Programme.«20261026-1402-proof-complexity».ProdExt

/-!
# Local identities on a `3 × 3` block (th's `rect_ext` with `|X| = 1`)

Pigeons `a, a₂, x`, holes `b, b₂, h` (distinct). `r = rect a a₂ b b₂` and
`Yb = x_{ab}x_{a₂b₂} - x_{ab₂}x_{a₂b} + r ⊗ x_{xh}` (as symmetric functions on pairs, `tprod`).
For every block edge `e` and every block pigeon (hole) free in `e`, the block row (column) sum of
`Yb` at `e` equals `r(e)` exactly; block line sums of `r` vanish.
-/

set_option linter.unusedSimpArgs false

namespace Programme.«20261026-1402-proof-complexity».RectBlock

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero var_div var_mod)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt var_decode rsum_pick)
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ExtLin
open Programme.«20261026-1402-proof-complexity».ProdExt

/-- Level-1 function from a weight. -/
def one (w : Nat → Int) : List Nat → Int
  | [v] => w v
  | _ => 0

/-- Level-0 function `1` on the empty list. -/
def emp : List Nat → Int
  | [] => 1
  | _ => 0

def dl (n i j : Nat) (v : Nat) : Int := if v = var n i j then 1 else 0

def Yb (n a a2 x b b2 h : Nat) (l : List Nat) : Int :=
  tprod (dl n a b) (dl n a2 b2) l - tprod (dl n a b2) (dl n a2 b) l + tprod (rect n a a2 b b2) (dl n x h) l

theorem var_eq_iff {n i t i' j : Nat} (ht : t < n) (hj : j < n) : var n i t = var n i' j ↔ i = i' ∧ t = j := by
  constructor
  · intro e
    have h1 := var_div n i t ht; have h2 := var_mod n i t ht
    rw [e, var_div n i' j hj] at h1; rw [e, var_mod n i' j hj] at h2
    exact ⟨h1.symm, h2.symm⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem isMatch_pair {n i t i' j : Nat} (ht : t < n) (hj : j < n) :
    isMatch n [var n i t, var n i' j] = (decide ((i, t) = (i', j)) || (decide (i ≠ i') && decide (t ≠ j))) := by
  unfold isMatch cfl
  simp only [var_div n i t ht, var_mod n i t ht, var_div n i' j hj, var_mod n i' j hj, List.all_cons,
    List.all_nil]
  by_cases h1 : i = i' <;> by_cases h2 : t = j <;> simp [h1, h2, var_eq_iff ht hj, Ne.symm] <;>
    exact fun e => absurd ((var_eq_iff hj hj).mp e).1 h1

theorem isMatch_one (n v : Nat) : isMatch n [v] = true := by
  simp [isMatch, cfl]

theorem rsum3 {M b b2 h : Nat} (hb : b < M) (hb2 : b2 < M) (hh : h < M) (d1 : b ≠ b2) (d2 : b ≠ h)
    (d3 : b2 ≠ h) (Q : Nat → Prop) [DecidablePred Q] (hQ : ∀ t, Q t ↔ t = b ∨ t = b2 ∨ t = h)
    (C : Nat → Prop) [DecidablePred C] (F : Nat → Int) :
    rsum M (fun t => if Q t ∧ C t then F t else 0) =
      (if C b then F b else 0) + (if C b2 then F b2 else 0) + (if C h then F h else 0) := by
  have e : ∀ t < M, (if Q t ∧ C t then F t else 0) =
      (if t = b then (if C t then F t else 0) else 0) + (if t = b2 then (if C t then F t else 0) else 0) +
        (if t = h then (if C t then F t else 0) else 0) := by
    intro t _
    by_cases q1 : t = b
    · subst q1; simp [hQ, d1, d2]
    · by_cases q2 : t = b2
      · subst q2; simp [hQ, d3, Ne.symm d1]
      · by_cases q3 : t = h
        · subst q3; simp [hQ, Ne.symm d2, Ne.symm d3]
        · simp [hQ, q1, q2, q3]
  rw [rsum_congr _ _ _ e, rsum_add, rsum_add, rsum_pick, rsum_pick, rsum_pick]
  simp [hb, hb2, hh]

section
variable {n K a a2 x b b2 h : Nat}

/-- Row identity for `Yb` at a block edge. -/
theorem Yb_row (hb : b < n) (hb2 : b2 < n) (hh : h < n) (p1 : a ≠ a2) (p2 : a ≠ x) (p3 : a2 ≠ x)
    (q1 : b ≠ b2) (q2 : b ≠ h) (q3 : b2 ≠ h) (Q : Nat → Prop) [DecidablePred Q]
    (hQ : ∀ t, Q t ↔ t = b ∨ t = b2 ∨ t = h) {i' j' i : Nat}
    (hi' : i' = a ∨ i' = a2 ∨ i' = x) (hj' : j' = b ∨ j' = b2 ∨ j' = h) (hi : i = a ∨ i = a2 ∨ i = x)
    (hne : i' ≠ i) :
    locL n (Yb n a a2 x b b2 h) [var n i' j'] (var n i) n Q = one (rect n a a2 b b2) [var n i' j'] := by
  unfold locL
  rw [rsum3 hb hb2 hh q1 q2 q3 Q hQ]
  have hj'n : j' < n := by rcases hj' with rfl | rfl | rfl <;> assumption
  simp only [isMatch_pair hb hj'n, isMatch_pair hb2 hj'n, isMatch_pair hh hj'n]
  rcases hi' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl <;> rcases hi with rfl | rfl | rfl <;>
    simp at hne <;>
    simp [Yb, one, tprod, dl, rect, var_eq_iff, hb, hb2, hh, p1, p2, p3, q1, q2, q3, Ne.symm p1,
      Ne.symm p2, Ne.symm p3, Ne.symm q1, Ne.symm q2, Ne.symm q3]

/-- Column identity for `Yb` at a block edge. -/
theorem Yb_col (ha : a < K) (ha2 : a2 < K) (hx : x < K) (hb : b < n) (hb2 : b2 < n) (hh : h < n)
    (p1 : a ≠ a2) (p2 : a ≠ x) (p3 : a2 ≠ x)
    (q1 : b ≠ b2) (q2 : b ≠ h) (q3 : b2 ≠ h) (Q : Nat → Prop) [DecidablePred Q]
    (hQ : ∀ s, Q s ↔ s = a ∨ s = a2 ∨ s = x) {i' j' j : Nat}
    (hi' : i' = a ∨ i' = a2 ∨ i' = x) (hj' : j' = b ∨ j' = b2 ∨ j' = h) (hj : j = b ∨ j = b2 ∨ j = h)
    (hne : j' ≠ j) :
    locL n (Yb n a a2 x b b2 h) [var n i' j'] (fun s => var n s j) K Q = one (rect n a a2 b b2) [var n i' j'] := by
  unfold locL
  rw [rsum3 ha ha2 hx p1 p2 p3 Q hQ]
  have hj'n : j' < n := by rcases hj' with rfl | rfl | rfl <;> assumption
  have hjn : j < n := by rcases hj with rfl | rfl | rfl <;> assumption
  simp only [isMatch_pair hjn hj'n]
  rcases hi' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
    simp at hne <;>
    simp [Yb, one, tprod, dl, rect, var_eq_iff, hb, hb2, hh, p1, p2, p3, q1, q2, q3, Ne.symm p1,
      Ne.symm p2, Ne.symm p3, Ne.symm q1, Ne.symm q2, Ne.symm q3]

theorem r_row (hb : b < n) (hb2 : b2 < n) (hh : h < n) (p1 : a ≠ a2)
    (q1 : b ≠ b2) (q2 : b ≠ h) (q3 : b2 ≠ h) (Q : Nat → Prop) [DecidablePred Q]
    (hQ : ∀ t, Q t ↔ t = b ∨ t = b2 ∨ t = h) (i : Nat) :
    locL n (one (rect n a a2 b b2)) [] (var n i) n Q = 0 := by
  unfold locL
  rw [rsum3 hb hb2 hh q1 q2 q3 Q hQ]
  simp only [isMatch_one, true_and, if_true]
  by_cases e1 : i = a
  · subst e1; simp [one, rect, var_eq_iff, hb, hb2, hh, p1, q1, q2, q3, Ne.symm q1, Ne.symm q2, Ne.symm q3]
  · by_cases e2 : i = a2
    · subst e2; simp [one, rect, var_eq_iff, hb, hb2, hh, e1, Ne.symm p1, q1, q2, q3, Ne.symm q1, Ne.symm q2, Ne.symm q3]
    · simp [one, rect, var_eq_iff, hb, hb2, hh, e1, e2]

theorem r_col (ha : a < K) (ha2 : a2 < K) (hx : x < K) (hj : j < n) (hb : b < n) (hb2 : b2 < n)
    (p1 : a ≠ a2) (p2 : a ≠ x) (p3 : a2 ≠ x) (q1 : b ≠ b2) (Q : Nat → Prop) [DecidablePred Q]
    (hQ : ∀ s, Q s ↔ s = a ∨ s = a2 ∨ s = x) :
    locL n (one (rect n a a2 b b2)) [] (fun s => var n s j) K Q = 0 := by
  unfold locL
  rw [rsum3 ha ha2 hx p1 p2 p3 Q hQ]
  simp only [isMatch_one, true_and, if_true]
  by_cases e1 : j = b
  · subst e1; simp [one, rect, var_eq_iff, hj, hb2, p1, p2, p3, q1, Ne.symm p1, Ne.symm p2, Ne.symm p3, Ne.symm q1]
  · by_cases e2 : j = b2
    · subst e2; simp [one, rect, var_eq_iff, hj, hb, e1, p1, p2, p3, Ne.symm p1, Ne.symm p2, Ne.symm p3, Ne.symm q1]
    · simp [one, rect, var_eq_iff, hj, hb, hb2, e1, e2]

end

end Programme.«20261026-1402-proof-complexity».RectBlock
