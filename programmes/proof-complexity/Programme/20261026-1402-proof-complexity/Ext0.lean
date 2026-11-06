import Programme.«20261026-1402-proof-complexity».ExtLemma

/-!
# EXT at level 0: `p ∣ k` gives `EXT p n k 0`

`EXT p n k 0` (th's `EXT_p(n,k,1)`): for every value `f []` there is `y` on single edges whose
every row sum (pigeon `i < n+k`) and every column sum (hole `j < n`) is `≡ f []` mod `p`.
Witness: `y(x_{ii}) = f []` for `i < n`, `y(x_{i0}) = f []` for the `k` extra pigeons `i ≥ n`,
`0` elsewhere. Rows sum to `f []`; columns `j ≠ 0` sum to `f []`; column `0` sums to
`(k+1) f [] ≡ f []` because `p ∣ k`. With `no_refutation_of_ext` this gives the (known, easy)
fact that `ontoFPHP n k` has no degree-1 `PPCRefutation p` when `p ∣ k`; the point is the
level-0 step of a uniform EXT proof.
-/

namespace Programme.«20261026-1402-proof-complexity».Ext0

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr var_div var_mod)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (rsum_pick var_lt)
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261026-1402-proof-complexity».ExtLemma

theorem canon_single : ∀ (N v : Nat), v < N → canon N [v] = [v] := by
  intro N
  induction N with
  | zero => intro v h; omega
  | succ N ih =>
    intro v h
    unfold canon
    by_cases hv : v = N
    · subst hv
      have : canon v [v] = [] := List.eq_nil_iff_forall_not_mem.mpr
        (fun x hx => by rw [mem_canon] at hx; simp at hx; omega)
      simp [this]
    · have : N ∉ [v] := by simp; omega
      rw [if_neg this]; exact ih v (by omega)

theorem isMatch_single (n v : Nat) : isMatch n [v] = true := by
  simp [isMatch, cfl]

/-- The level-0 witness. -/
def y0 (n : Nat) (a : Int) : List Nat → Int
  | [v] => if v / n = v % n ∨ (n ≤ v / n ∧ v % n = 0) then a else 0
  | _ => 0

theorem term (n k : Nat) (a : Int) (i j : Nat) (hi : i < n + k) (hj : j < n) :
    (if isMatch n (var n i j :: []) then y0 n a (canon ((n + k) * n) (var n i j :: [])) else 0) =
      if i = j ∨ (n ≤ i ∧ j = 0) then a else 0 := by
  rw [isMatch_single, if_pos rfl, canon_single _ _ (var_lt n k i j hi hj)]
  simp only [y0, var_div n i j hj, var_mod n i j hj]

theorem rsum_col0 (a : Int) (m : Nat) (hm : 0 < m) : ∀ k : Nat,
    rsum (m + k) (fun i => if i = 0 ∨ m ≤ i then a else 0) = a + k * a := by
  intro k
  induction k with
  | zero =>
    have : rsum m (fun i => if i = 0 ∨ m ≤ i then a else 0) = rsum m (fun i => if i = 0 then a else 0) :=
      rsum_congr m _ _ (fun i hi => by
        by_cases h : i = 0
        · simp [h]
        · have : ¬ m ≤ i := by omega
          simp [h, this])
    rw [Nat.add_zero, this, rsum_pick, if_pos hm]; simp
  | succ k ih =>
    rw [show m + (k + 1) = (m + k) + 1 by omega]
    simp only [rsum, ih]
    rw [if_pos (Or.inr (by omega))]
    push_cast; rw [Int.add_mul]; omega

/-- **EXT at level 0.** -/
theorem ext0 {p n k : Nat} (hn : 0 < n) (hk : p ∣ k) : EXT p n k 0 := by
  intro f c _
  refine ⟨y0 n (f []), ?_⟩
  intro g hg hgl
  have hg0 : g = [] := List.eq_nil_of_length_eq_zero hgl
  subst hg0
  refine ⟨fun i hi _ => ?_, fun j hj _ => ?_⟩
  · show (p : Int) ∣ rsum n _ - f []
    rw [rsum_congr n _ (fun j => if j = (if i < n then i else 0) then f [] else 0)
      (fun j hj => by
        rw [term n k (f []) i j hi hj]
        by_cases h : i < n
        · simp only [if_pos h]; by_cases e : j = i <;> simp [e] <;> omega
        · simp only [if_neg h]; by_cases e : j = 0 <;> simp [e] <;> omega)]
    rw [rsum_pick, if_pos (by split <;> omega)]; exact ⟨0, by simp⟩
  · show (p : Int) ∣ rsum (n + k) _ - f []
    rw [rsum_congr (n + k) _ (fun i => if i = j ∨ (n ≤ i ∧ j = 0) then f [] else 0)
      (fun i hi => term n k (f []) i j hi hj)]
    by_cases hj0 : j = 0
    · subst hj0
      rw [rsum_congr (n + k) _ (fun i => if i = 0 ∨ n ≤ i then f [] else 0)
        (fun i _ => by simp), rsum_col0 (f []) n hn k]
      obtain ⟨t, rfl⟩ := hk
      exact ⟨t * f [], by push_cast; rw [Int.mul_assoc]; omega⟩
    · rw [rsum_congr (n + k) _ (fun i => if i = j then f [] else 0)
        (fun i _ => by by_cases e : i = j <;> simp [e, hj0])]
      rw [rsum_pick, if_pos (by omega)]; exact ⟨0, by simp⟩

/-- Consequence: `p ∣ k`, `p > 1`, `n > 0` give no degree-1 `PPCRefutation p` of `ontoFPHP n k`. -/
theorem no_deg1 {p n k : Nat} (hp : 1 < p) (hn : 0 < n) (hk : p ∣ k) :
    ¬ PPCRefutation p (ontoFPHP n k) 1 :=
  no_refutation_of_ext hp hn (Nat.le_refl 1) (fun d hd => by
    obtain rfl : d = 0 := by omega
    exact ext0 hn hk)

end Programme.«20261026-1402-proof-complexity».Ext0

#print axioms Programme.«20261026-1402-proof-complexity».Ext0.ext0
#print axioms Programme.«20261026-1402-proof-complexity».Ext0.no_deg1
