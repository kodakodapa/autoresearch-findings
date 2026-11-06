import Programme.«20261025-1627-proof-complexity».OntoMom3
import Programme.«20261025-1627-proof-complexity».Ext4Id

/-!
# Degree-4 design extension for onto-FPHP when `24·n(n-1)⋯(n-6)` is invertible mod `p`

Given a degree-3 design `F` of `ontoFPHP n k` (`p ∣ k`), the extension `Ext4` is the subset-moment
functional (`Work.MomGen.sumW`, subsets of size `≤ 4`) with moments `F(x_S)` for `|S| ≤ 3` and, on a
4-matching, `u · S4` (`Work.Ext4Alg`) built from `c = F(1)`, `y`, `zz`, `tt` (moments of size 1, 2, 3,
set to `0` on conflicts). Non-matchings of size 4 get `0`. Every level-4 pigeon and hole equation holds
by `pig_total` / `hole_total`. With `Work.DesignExt.ext_sound` and the degree-3 extension of
`Work.OntoExt3`: no degree-4 PC refutation; restriction gives all `n ≥ 7` when `gcd(p, 210) = 1`.
-/

namespace Programme.«20261025-1627-proof-complexity».OntoExt4

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr prod2_eval mem_ontoFPHP
  mem_collAx mem_funcAx var_div var_mod prod2_deg mem_pig mem_hole mem_coll mem_func)
open Programme.«20261025-1627-proof-complexity».DesignExt
open Programme.«20261025-1627-proof-complexity».OntoExt2 (SN rsum_dvd rsum_pick rsum_const rsum_cmul rsum_skip var_lt var_decode var_inj
  sumOne_deg_pos not_dvd_one)
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261025-1627-proof-complexity».OntoExt3 (cc yy zz conf zz_symm zz_cp zz_ch F_conf F_zz hR1 hC1 hR2 hC2 perm3 rsum_pick_dvd
  rsum_sub' mono_split)
open Programme.«20261025-1627-proof-complexity».OntoMom3
open Programme.«20261025-1627-proof-complexity».Ext4Alg

variable {p : Nat}

/-! ## Combinatorial helpers -/

theorem tail4 {a b c d x : Nat} (h : [a, b, c, d].Nodup) : x ∈ [b, c, d] ↔ (x ∈ [a, b, c, d] ∧ x ≠ a) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil] at h ⊢
  constructor
  · intro hx; omega
  · intro hx; omega

theorem mem_absorb {x1 x2 x3 y : Nat} (hy : y ∈ [x1, x2, x3]) (x : Nat) :
    x ∈ [x1, x2, x3, y] ↔ x ∈ [x1, x2, x3] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · subst h; exact hy
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

theorem mem_ext3 {x1 x2 x3 y z : Nat} (hy : y ∈ [x1, x2, x3]) : y ∈ [x1, x2, x3, z] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
  rcases hy with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

theorem perm4 (f : Nat → Nat → Nat → Nat → Int) (h01 : ∀ a b c d, f a b c d = f b a c d)
    (h12 : ∀ a b c d, f a b c d = f a c b d) (h23 : ∀ a b c d, f a b c d = f a b d c)
    (x1 x2 x3 x4 s1 s2 s3 s4 : Nat) (hs : [s1, s2, s3, s4].Nodup) (hx : [x1, x2, x3, x4].Nodup)
    (hm : ∀ x, x ∈ [s1, s2, s3, s4] ↔ x ∈ [x1, x2, x3, x4]) : f s1 s2 s3 s4 = f x1 x2 x3 x4 := by
  have key : ∀ y1 y2 y3 y4, [y1, y2, y3, y4].Nodup → (∀ x, x ∈ [y1, y2, y3, y4] ↔ x ∈ [x1, x2, x3, x4]) →
      f y1 y2 y3 y4 = f x1 x2 x3 x4 → s1 = y1 → f s1 s2 s3 s4 = f x1 x2 x3 x4 := by
    intro y1 y2 y3 y4 hy hym hf he
    subst he
    rw [← hf]
    refine perm3 (fun a b c => f s1 a b c) (fun a b c => h12 s1 a b c) (fun a b c => h23 s1 a b c)
      y2 y3 y4 s2 s3 s4 (by simp at hs ⊢; omega) (fun x => ?_)
    rw [tail4 hs, tail4 hy, hm x, hym x]
  have m1 := (hm s1).mp (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at m1
  rcases m1 with h | h | h | h
  · exact key x1 x2 x3 x4 hx (fun _ => Iff.rfl) rfl h
  · exact key x2 x1 x3 x4 (by simp at hx ⊢; omega) (fun x => by simp only [List.mem_cons, List.not_mem_nil, or_false]; constructor <;> intro h <;> rcases h with h | h | h | h <;> simp [h])
      (h01 _ _ _ _) h
  · exact key x3 x1 x2 x4 (by simp at hx ⊢; omega) (fun x => by simp only [List.mem_cons, List.not_mem_nil, or_false]; constructor <;> intro h <;> rcases h with h | h | h | h <;> simp [h])
      ((h01 _ _ _ _).trans (h12 _ _ _ _)) h
  · exact key x4 x1 x2 x3 (by simp at hx ⊢; omega) (fun x => by simp only [List.mem_cons, List.not_mem_nil, or_false]; constructor <;> intro h <;> rcases h with h | h | h | h <;> simp [h])
      ((h01 _ _ _ _).trans ((h12 _ _ _ _).trans (h23 _ _ _ _))) h

theorem nodup4_mem {l : List Nat} (h4 : l.length = 4) : ∃ s1 s2 s3 s4, l = [s1, s2, s3, s4] := by
  match l, h4 with
  | [s1, s2, s3, s4], _ => exact ⟨s1, s2, s3, s4, rfl⟩

theorem small3 {l : List Nat} (hl : l.Nodup) (h3 : l.length ≤ 3) {v w : Nat} (hv : v ∈ l) (hw : w ∈ l)
    (hvw : v ≠ w) : ∃ x, ∀ y, y ∈ l ↔ y ∈ [x, v, w] := by
  match l, h3 with
  | [], _ => simp at hv
  | [a], _ => simp at hv hw; omega
  | [a, b], _ => exact ⟨v, fun y => by simp at hv hw ⊢; constructor <;> intro h <;> omega⟩
  | [a, b, c], _ =>
    simp at hl hv hw
    by_cases ha : a ≠ v ∧ a ≠ w
    · exact ⟨a, fun y => by simp; constructor <;> intro h <;> omega⟩
    by_cases hb : b ≠ v ∧ b ≠ w
    · exact ⟨b, fun y => by simp; constructor <;> intro h <;> omega⟩
    · exact ⟨c, fun y => by simp; constructor <;> intro h <;> omega⟩

theorem rsum_skip3 (m b1 b2 b3 : Nat) (h1 : b1 < m) (h2 : b2 < m) (h3 : b3 < m) (h12 : b1 ≠ b2) (h13 : b1 ≠ b3)
    (h23 : b2 ≠ b3) (G : Nat → Int) :
    rsum m (fun j => if j = b1 ∨ j = b2 ∨ j = b3 then 0 else G j) = rsum m G - G b1 - G b2 - G b3 := by
  have e : rsum m (fun j => if j = b1 ∨ j = b2 ∨ j = b3 then 0 else G j) =
      rsum m (fun j => if j = b3 then 0 else (fun j => if j = b2 then 0 else (fun j => if j = b1 then 0 else G j) j) j) :=
    rsum_congr _ _ _ (fun j _ => by
      by_cases a : j = b1 <;> by_cases b : j = b2 <;> by_cases c : j = b3 <;> simp [a, b, c])
  rw [e, rsum_skip m b3 h3, rsum_skip m b2 h2, rsum_skip m b1 h1]
  simp [Ne.symm h12, Ne.symm h13, Ne.symm h23]

/-! ## The extension functional -/

def isM4 (n x1 x2 x3 x4 : Nat) : Prop :=
  x1 / n ≠ x2 / n ∧ x1 / n ≠ x3 / n ∧ x1 / n ≠ x4 / n ∧ x2 / n ≠ x3 / n ∧ x2 / n ≠ x4 / n ∧ x3 / n ≠ x4 / n ∧
  x1 % n ≠ x2 % n ∧ x1 % n ≠ x3 % n ∧ x1 % n ≠ x4 % n ∧ x2 % n ≠ x3 % n ∧ x2 % n ≠ x4 % n ∧ x3 % n ≠ x4 % n

instance (n x1 x2 x3 x4 : Nat) : Decidable (isM4 n x1 x2 x3 x4) := by unfold isM4; infer_instance

set_option maxHeartbeats 2000000 in
theorem isM4_conf (n s1 s2 s3 s4 v w : Nat) (hv : v ∈ [s1, s2, s3, s4]) (hw : w ∈ [s1, s2, s3, s4])
    (hc : conf n v w) : ¬ isM4 n s1 s2 s3 s4 := by
  intro hM
  unfold conf at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv hw
  rcases hv with rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl <;> unfold isM4 at hM <;> omega

theorem isM4_col (n x1 x2 x3 i j : Nat) (hj : j < n) (h : j = x1 % n ∨ j = x2 % n ∨ j = x3 % n) :
    ¬ isM4 n x1 x2 x3 (var n i j) := by
  intro hM; unfold isM4 at hM; rw [var_mod n _ _ hj] at hM; omega

theorem isM4_col' (n x1 x2 x3 i j : Nat) (hj : j < n)
    (hab : x1 / n ≠ x2 / n ∧ x1 / n ≠ x3 / n ∧ x2 / n ≠ x3 / n ∧ x1 % n ≠ x2 % n ∧ x1 % n ≠ x3 % n ∧ x2 % n ≠ x3 % n)
    (hi1 : ¬ i = x1 / n) (hi2 : ¬ i = x2 / n) (hi3 : ¬ i = x3 / n) (h : ¬ (j = x1 % n ∨ j = x2 % n ∨ j = x3 % n)) :
    isM4 n x1 x2 x3 (var n i j) := by
  unfold isM4; rw [var_div n _ _ hj, var_mod n _ _ hj]; omega

theorem isM4_row (n x1 x2 x3 i j : Nat) (hj : j < n) (h : i = x1 / n ∨ i = x2 / n ∨ i = x3 / n) :
    ¬ isM4 n x1 x2 x3 (var n i j) := by
  intro hM; unfold isM4 at hM; rw [var_div n _ _ hj] at hM; omega

theorem isM4_row' (n x1 x2 x3 i j : Nat) (hj : j < n)
    (hab : x1 / n ≠ x2 / n ∧ x1 / n ≠ x3 / n ∧ x2 / n ≠ x3 / n ∧ x1 % n ≠ x2 % n ∧ x1 % n ≠ x3 % n ∧ x2 % n ≠ x3 % n)
    (hj1 : ¬ j = x1 % n) (hj2 : ¬ j = x2 % n) (hj3 : ¬ j = x3 % n) (h : ¬ (i = x1 / n ∨ i = x2 / n ∨ i = x3 / n)) :
    isM4 n x1 x2 x3 (var n i j) := by
  unfold isM4; rw [var_div n _ _ hj, var_mod n _ _ hj]; omega

section
variable {S : (Nat → Bool) → Prop} (F : Fn p S) (n : Nat) (u : Int)

/-- Level-4 moment of `{x₁, x₂, x₃, x₄}`. -/
def W4 (x1 x2 x3 x4 : Nat) : Int :=
  if isM4 n x1 x2 x3 x4 then
    u * S4 n (cc F) (yy F) (zz F n) (tt F n) (x1 / n) (x2 / n) (x3 / n) (x4 / n) (x1 % n) (x2 % n) (x3 % n) (x4 % n)
  else 0

/-- All moments: `F` up to size 3, `W4` at size 4. -/
def WW4 (T : List Nat) : Int :=
  if T.length ≤ 3 then F.E (fun a => monoEval a T) else
    match T with
    | [x1, x2, x3, x4] => W4 F n u x1 x2 x3 x4
    | _ => 0

theorem W4_01 (x1 x2 x3 x4 : Nat) : W4 F n u x1 x2 x3 x4 = W4 F n u x2 x1 x3 x4 := by
  unfold W4
  by_cases h : isM4 n x1 x2 x3 x4
  · have h' : isM4 n x2 x1 x3 x4 := by unfold isM4 at *; omega
    rw [if_pos h, if_pos h', S4_swap01]
  · have h' : ¬ isM4 n x2 x1 x3 x4 := by unfold isM4 at *; omega
    rw [if_neg h, if_neg h']

theorem W4_12 (x1 x2 x3 x4 : Nat) : W4 F n u x1 x2 x3 x4 = W4 F n u x1 x3 x2 x4 := by
  unfold W4
  by_cases h : isM4 n x1 x2 x3 x4
  · have h' : isM4 n x1 x3 x2 x4 := by unfold isM4 at *; omega
    rw [if_pos h, if_pos h', S4_swap12]
  · have h' : ¬ isM4 n x1 x3 x2 x4 := by unfold isM4 at *; omega
    rw [if_neg h, if_neg h']

theorem W4_23 (x1 x2 x3 x4 : Nat) : W4 F n u x1 x2 x3 x4 = W4 F n u x1 x2 x4 x3 := by
  unfold W4
  by_cases h : isM4 n x1 x2 x3 x4
  · have h' : isM4 n x1 x2 x4 x3 := by unfold isM4 at *; omega
    rw [if_pos h, if_pos h', S4_swap23]
  · have h' : ¬ isM4 n x1 x2 x4 x3 := by unfold isM4 at *; omega
    rw [if_neg h, if_neg h']

end

section
variable {n k : Nat} (F : Fn p (SN ((n + k) * n))) (u : Int)

/-- The extension. -/
def Ext4 : Fn p (SN ((n + k) * n)) := sumWFn p ((n + k) * n) 4 (WW4 F n u)

theorem E_mono (xs : List Nat) (hx : ∀ x ∈ xs, x < (n + k) * n) (hl : xs.length ≤ 4) :
    (Ext4 F u).E (fun a => monoEval a xs) = WW4 F n u (canon ((n + k) * n) xs) :=
  sumW_mono _ 4 _ xs hx (Nat.le_trans (canon_length_le _ xs) hl)

theorem E_low (xs : List Nat) (hx : ∀ x ∈ xs, x < (n + k) * n) (hl : (canon ((n + k) * n) xs).length ≤ 3) :
    (Ext4 F u).E (fun a => monoEval a xs) = F.E (fun a => monoEval a xs) := by
  show sumW _ 4 _ _ = _
  rw [sumW_mono _ 4 _ xs hx (by omega)]
  unfold WW4; rw [if_pos hl]
  congr 1; funext a; exact (monoEval_canon _ a xs hx).symm

theorem E_vanish (xs : List Nat) (x : Nat) (hx : x ∈ xs) (hxN : (n + k) * n ≤ x) :
    (Ext4 F u).E (fun a => monoEval a xs) = (Ext4 F u).E (fun _ => 0) :=
  (Ext4 F u).supp _ _ (fun a ha => monoEval_zero ha xs x hx hxN)

theorem E_extends : Extends 3 (Ext4 F u) F := by
  intro t ht
  by_cases hx : ∀ x ∈ t, x < (n + k) * n
  · rw [E_low F u t hx (Nat.le_trans (canon_length_le _ t) ht), Int.sub_self]; exact ⟨0, by simp⟩
  · have : ∃ x ∈ t, (n + k) * n ≤ x := by
      apply Classical.byContradiction; intro h; apply hx; intro x hxt
      apply Classical.byContradiction; intro h'; exact h ⟨x, hxt, by omega⟩
    obtain ⟨x, hxt, hxN⟩ := this
    rw [E_vanish F u t x hxt hxN, F.supp _ (fun _ => 0) (fun a ha => monoEval_zero ha t x hxt hxN)]
    exact Int.dvd_sub (Ext4 F u).zero F.zero

/-- Moments of size `≤ 3` (as a set) are those of `F`. -/
theorem E_set (xs ys : List Nat) (hx : ∀ x ∈ xs, x < (n + k) * n) (hy : ys.length ≤ 3)
    (hm : ∀ x, x ∈ xs ↔ x ∈ ys) :
    (Ext4 F u).E (fun a => monoEval a xs) = F.E (fun a => monoEval a ys) := by
  have hmem : ∀ x, x ∈ canon ((n + k) * n) xs ↔ x ∈ xs := fun x => by
    rw [mem_canon]; constructor <;> intro h <;> (try exact h.1) <;> exact ⟨h, hx x h⟩
  have hl : (canon ((n + k) * n) xs).length ≤ 3 := by
    have := nodup_len _ ys (canon_nodup _ xs) (fun x h => (hm x).mp ((hmem x).mp h)); omega
  rw [E_low F u xs hx hl]
  congr 1; funext a; exact monoEval_congr a _ _ hm

theorem E_four (x1 x2 x3 x4 : Nat) (hd : [x1, x2, x3, x4].Nodup) (hx : ∀ x ∈ [x1, x2, x3, x4], x < (n + k) * n) :
    (Ext4 F u).E (fun a => monoEval a [x1, x2, x3, x4]) = W4 F n u x1 x2 x3 x4 := by
  rw [E_mono F u _ hx (by simp)]
  have hmem : ∀ x, x ∈ canon ((n + k) * n) [x1, x2, x3, x4] ↔ x ∈ [x1, x2, x3, x4] := fun x => by
    rw [mem_canon]; constructor <;> intro h <;> (try exact h.1) <;> exact ⟨h, hx x h⟩
  have hl1 := canon_length_le ((n + k) * n) [x1, x2, x3, x4]
  have hl2 := nodup_len [x1, x2, x3, x4] _ hd (fun x h => (hmem x).mpr h)
  simp only [List.length_cons, List.length_nil] at hl1 hl2
  obtain ⟨s1, s2, s3, s4, e⟩ := nodup4_mem (l := canon ((n + k) * n) [x1, x2, x3, x4]) (by omega)
  have hs : [s1, s2, s3, s4].Nodup := e ▸ canon_nodup _ _
  rw [e]
  unfold WW4; simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  exact perm4 (W4 F n u) (W4_01 F n u) (W4_12 F n u) (W4_23 F n u) x1 x2 x3 x4 s1 s2 s3 s4 hs hd
    (fun x => by rw [← e]; exact hmem x)

theorem E_rsum (m : Nat) (G : Nat → (Nat → Bool) → Int) (g : (Nat → Bool) → Int) :
    (Ext4 F u).E (fun a => rsum m (fun j => G j a) - g a) = rsum m (fun j => (Ext4 F u).E (G j)) - (Ext4 F u).E g := by
  show sumW ((n + k) * n) 4 (WW4 F n u) _ = rsum m (fun j => sumW ((n + k) * n) 4 (WW4 F n u) (G j)) - sumW ((n + k) * n) 4 (WW4 F n u) g
  have : sumW ((n + k) * n) 4 (WW4 F n u) (fun a => rsum m (fun j => G j a)) =
      rsum m (fun j => sumW ((n + k) * n) 4 (WW4 F n u) (G j)) := by
    induction m with
    | zero =>
      have := sumW_lin ((n + k) * n) 4 (WW4 F n u) (fun _ => 0) (fun _ => 0) 0 0
      simpa [rsum] using this
    | succ m ih =>
      have := sumW_lin ((n + k) * n) 4 (WW4 F n u) (fun a => rsum m (fun j => G j a)) (G m) 1 1
      simp only [Int.one_mul] at this
      simp only [rsum]; rw [this, ih]
  have e : (fun a => rsum m (fun j => G j a) - g a) = fun a => 1 * rsum m (fun j => G j a) + (-1) * g a := by
    funext a; omega
  rw [e, sumW_lin]
  rw [this]; omega

variable (hF : IsDesign (ontoFPHP n k) 3 F)
include hF

/-- `F` vanishes on short monomials with a conflicting pair. -/
theorem F_confL (hn : 0 < n) (xs : List Nat) (hx : ∀ x ∈ xs, x < (n + k) * n)
    (hl : (canon ((n + k) * n) xs).length ≤ 3) (v w : Nat) (hv : v ∈ xs) (hw : w ∈ xs) (hc : conf n v w) :
    (p : Int) ∣ F.E (fun a => monoEval a xs) := by
  have hmem : ∀ x, x ∈ canon ((n + k) * n) xs ↔ x ∈ xs := fun x => by
    rw [mem_canon]; constructor <;> intro h <;> (try exact h.1) <;> exact ⟨h, hx x h⟩
  obtain ⟨x, hxm⟩ := small3 (canon_nodup _ xs) hl ((hmem v).mpr hv) ((hmem w).mpr hw) hc.1
  have e : F.E (fun a => monoEval a xs) = F.E (fun a => monoEval a [x, v, w]) := by
    congr 1; funext a; exact monoEval_congr a _ _ (fun y => by rw [← hmem y]; exact hxm y)
  rw [e]; exact F_conf3 F hF hn x v w hc

theorem E_conf (hn : 0 < n) (xs : List Nat) (hx : ∀ x ∈ xs, x < (n + k) * n) (hl : xs.length ≤ 4)
    (v w : Nat) (hv : v ∈ xs) (hw : w ∈ xs) (hc : conf n v w) :
    (p : Int) ∣ (Ext4 F u).E (fun a => monoEval a xs) := by
  have hmem : ∀ x, x ∈ canon ((n + k) * n) xs ↔ x ∈ xs := fun x => by
    rw [mem_canon]; constructor <;> intro h <;> (try exact h.1) <;> exact ⟨h, hx x h⟩
  by_cases hl3 : (canon ((n + k) * n) xs).length ≤ 3
  · rw [E_low F u xs hx hl3]; exact F_confL F hF hn xs hx hl3 v w hv hw hc
  · rw [E_mono F u xs hx hl]
    have hl4 := Nat.le_trans (canon_length_le ((n + k) * n) xs) hl
    obtain ⟨s1, s2, s3, s4, e⟩ := nodup4_mem (l := canon ((n + k) * n) xs) (by omega)
    rw [e]
    have mv := (hmem v).mpr hv; have mw := (hmem w).mpr hw
    rw [e] at mv mw
    unfold WW4; simp only [List.length_cons, List.length_nil]
    rw [if_neg (by omega)]
    unfold W4
    rw [if_neg (isM4_conf n s1 s2 s3 s4 v w mv mw hc)]
    exact ⟨0, by simp⟩

theorem tt_F (x1 x2 x3 : Nat) (hc : ¬ (conf n x1 x2 ∨ conf n x1 x3 ∨ conf n x2 x3)) :
    F.E (fun a => monoEval a [x1, x2, x3]) = tt F n x1 x2 x3 := by
  unfold tt; rw [if_neg hc]

/-! ## Level-4 equations -/

theorem pig4 (hn : 0 < n) (hu : (p : Int) ∣ u * M4 n - 1) (i : Nat) (hi : i < n + k) (x1 x2 x3 : Nat) :
    (p : Int) ∣ (Ext4 F u).E (fun a => monoEval a [x1, x2, x3] * (sumOne (fun j => var n i j) n).eval a) := by
  let N := (n + k) * n
  by_cases hN : x1 < N ∧ x2 < N ∧ x3 < N
  case neg =>
    have : (Ext4 F u).E (fun a => monoEval a [x1, x2, x3] * (sumOne (fun j => var n i j) n).eval a) =
        (Ext4 F u).E (fun _ => 0) := by
      apply (Ext4 F u).supp; intro a ha
      by_cases h1 : x1 < N
      · by_cases h2 : x2 < N
        · rw [monoEval_zero ha _ x3 (by simp) (by omega), Int.zero_mul]
        · rw [monoEval_zero ha _ x2 (by simp) (by omega), Int.zero_mul]
      · rw [monoEval_zero ha _ x1 (by simp) (by omega), Int.zero_mul]
    rw [this]; exact (Ext4 F u).zero
  obtain ⟨hx1, hx2, hx3⟩ := hN
  have hlowP : ∀ y1 y2 : Nat, (∀ x, x ∈ [x1, x2, x3] ↔ x ∈ [y1, y2]) →
      (p : Int) ∣ (Ext4 F u).E (fun a => monoEval a [x1, x2, x3] * (sumOne (fun j => var n i j) n).eval a) := by
    intro y1 y2 hy
    have e : (fun a => monoEval a [x1, x2, x3] * (sumOne (fun j => var n i j) n).eval a) =
        fun a => monoEval a [y1, y2] * (sumOne (fun j => var n i j) n).eval a := by
      funext a; rw [monoEval_congr a [x1, x2, x3] [y1, y2] hy]
    rw [e]
    exact low_kill (D := 4) hF (E_extends F u) (mem_pig hi) (by have := sumOne_deg (fun j => var n i j) n; simp; omega)
  by_cases h12 : x1 = x2
  · exact hlowP x1 x3 (fun x => by simp; omega)
  by_cases h13 : x1 = x3
  · exact hlowP x1 x2 (fun x => by simp; omega)
  by_cases h23 : x2 = x3
  · exact hlowP x1 x2 (fun x => by simp; omega)
  have hsplit := E_rsum F u n (fun j a => monoEval a [x1, x2, x3, var n i j]) (fun a => monoEval a [x1, x2, x3])
  have e0 : (fun a => monoEval a [x1, x2, x3] * (sumOne (fun j => var n i j) n).eval a) =
      fun a => rsum n (fun j => monoEval a [x1, x2, x3, var n i j]) - monoEval a [x1, x2, x3] := by
    funext a; rw [mono_split]; simp
  rw [e0, hsplit]
  have hvl : ∀ j < n, var n i j < N := fun j hj => var_lt n k i j hi hj
  have hconf : ∀ v w, v ∈ [x1, x2, x3] → w ∈ [x1, x2, x3] → conf n v w →
      (p : Int) ∣ rsum n (fun j => (Ext4 F u).E (fun a => monoEval a [x1, x2, x3, var n i j])) -
        (Ext4 F u).E (fun a => monoEval a [x1, x2, x3]) := by
    intro v w hv hw hc
    apply Int.dvd_sub
    · exact rsum_dvd _ _ _ (fun j hj => E_conf F u hF hn _ (by simp; exact ⟨hx1, hx2, hx3, hvl j hj⟩) (by simp) v w
        (mem_ext3 hv) (mem_ext3 hw) hc)
    · exact E_conf F u hF hn _ (by simp; omega) (by simp) v w hv hw hc
  by_cases hc : conf n x1 x2 ∨ conf n x1 x3 ∨ conf n x2 x3
  · rcases hc with hc | hc | hc
    · exact hconf x1 x2 (by simp) (by simp) hc
    · exact hconf x1 x3 (by simp) (by simp) hc
    · exact hconf x2 x3 (by simp) (by simp) hc
  have ha1 : x1 / n < n + k := (Nat.div_lt_iff_lt_mul hn).mpr hx1
  have ha2 : x2 / n < n + k := (Nat.div_lt_iff_lt_mul hn).mpr hx2
  have ha3 : x3 / n < n + k := (Nat.div_lt_iff_lt_mul hn).mpr hx3
  have hb1 : x1 % n < n := Nat.mod_lt _ hn
  have hb2 : x2 % n < n := Nat.mod_lt _ hn
  have hb3 : x3 % n < n := Nat.mod_lt _ hn
  have hab : x1 / n ≠ x2 / n ∧ x1 / n ≠ x3 / n ∧ x2 / n ≠ x3 / n ∧
      x1 % n ≠ x2 % n ∧ x1 % n ≠ x3 % n ∧ x2 % n ≠ x3 % n := by unfold conf at hc; omega
  have e1 := var_decode n x1; have e2 := var_decode n x2; have e3 := var_decode n x3
  have htrip : (Ext4 F u).E (fun a => monoEval a [x1, x2, x3]) = tt F n x1 x2 x3 := by
    rw [E_set F u _ [x1, x2, x3] (by simp; omega) (by simp) (fun _ => Iff.rfl), tt_F F hF x1 x2 x3 hc]
  -- the new pigeon is the pigeon of some x
  have side : ∀ y : Nat, y ∈ [x1, x2, x3] → y < N → i = y / n →
      (p : Int) ∣ rsum n (fun j => (Ext4 F u).E (fun a => monoEval a [x1, x2, x3, var n i j])) -
        (Ext4 F u).E (fun a => monoEval a [x1, x2, x3]) := by
    intro y hy hyN hiy
    have ey := var_decode n y
    have hby : y % n < n := Nat.mod_lt _ hn
    apply rsum_pick_dvd n (y % n) hby
    intro j hj
    by_cases hjb : j = y % n
    · rw [if_pos hjb]
      have hv : var n i j = y := by rw [hjb, hiy, ey]
      rw [hv, E_set F u [x1, x2, x3, y] [x1, x2, x3] (by simp; omega) (by simp)
        (mem_absorb hy), E_set F u [x1, x2, x3] [x1, x2, x3] (by simp; omega) (by simp)
        (fun _ => Iff.rfl), Int.sub_self]
      exact ⟨0, by simp⟩
    · rw [if_neg hjb, Int.sub_zero]
      refine E_conf F u hF hn _ (by simp; exact ⟨hx1, hx2, hx3, hvl j hj⟩) (by simp) y (var n i j)
        (mem_ext3 hy) (by simp) ⟨?_, Or.inl ?_⟩
      · intro h; apply hjb; rw [h, var_mod n _ _ hj]
      · rw [var_div n _ _ hj, hiy]
  by_cases hi1 : i = x1 / n
  · exact side x1 (by simp) hx1 hi1
  by_cases hi2 : i = x2 / n
  · exact side x2 (by simp) hx2 hi2
  by_cases hi3 : i = x3 / n
  · exact side x3 (by simp) hx3 hi3
  -- main case: a new pigeon
  have hfour : ∀ j < n, (Ext4 F u).E (fun a => monoEval a [x1, x2, x3, var n i j]) =
      if j = x1 % n ∨ j = x2 % n ∨ j = x3 % n then 0 else
        u * S4 n (cc F) (yy F) (zz F n) (tt F n) (x1 / n) (x2 / n) (x3 / n) i (x1 % n) (x2 % n) (x3 % n) j := by
    intro j hj
    have h1 : x1 ≠ var n i j := fun h => hi1 (by rw [h, var_div n _ _ hj])
    have h2 : x2 ≠ var n i j := fun h => hi2 (by rw [h, var_div n _ _ hj])
    have h3 : x3 ≠ var n i j := fun h => hi3 (by rw [h, var_div n _ _ hj])
    have hd : [x1, x2, x3, var n i j].Nodup := by simp [h12, h13, h23, h1, h2, h3, Ne.symm h12, Ne.symm h13, Ne.symm h23]
    rw [E_four F u _ _ _ _ hd (by simp; exact ⟨hx1, hx2, hx3, hvl j hj⟩)]
    unfold W4
    by_cases hj' : j = x1 % n ∨ j = x2 % n ∨ j = x3 % n
    · rw [if_pos hj', if_neg (isM4_col n x1 x2 x3 i j hj hj')]
    · rw [if_neg hj', if_pos (isM4_col' n x1 x2 x3 i j hj hab hi1 hi2 hi3 hj'), var_div n _ _ hj, var_mod n _ _ hj]
  rw [rsum_congr n _ _ hfour, rsum_skip3 n _ _ _ hb1 hb2 hb3 hab.2.2.2.1 hab.2.2.2.2.1 hab.2.2.2.2.2, htrip]
  generalize x1 / n = a1 at *
  generalize x2 / n = a2 at *
  generalize x3 / n = a3 at *
  generalize x1 % n = b1 at *
  generalize x2 % n = b2 at *
  generalize x3 % n = b3 at *
  subst e1 e2 e3
  have hT := pig_total n (cc F) (yy F) (zz F n) (tt F n) (zz_symm F n) (tt_12 F n) (tt_23 F n)
    (fun a a' b hb h => zz_cp F n a a' b hb h) (ttC12 F n) (ttC13 F n) (ttC23 F n) (n + k)
    (hR1 F (Programme.«20261025-1627-proof-complexity».OntoMom3.design2 F hF) hn) (hR2a F hF hn) (hR2 F (Programme.«20261025-1627-proof-complexity».OntoMom3.design2 F hF) hn)
    (hR3a F hF hn) (hR3b F hF hn) (hR3c F hF hn)
    a1 a2 a3 i b1 b2 b3 ha1 ha2 ha3 hi hab.1 hab.2.1 hab.2.2.1 (Ne.symm hi1) (Ne.symm hi2) (Ne.symm hi3)
    hab.2.2.2.1 hab.2.2.2.2.1 hab.2.2.2.2.2 hb1 hb2 hb3
  rw [← rsum_cmul]
  obtain ⟨q, hq⟩ := hu
  have hfin := Int.dvd_add (dvd_cmul u hT) (⟨q * tt F n (var n a1 b1) (var n a2 b2) (var n a3 b3), rfl⟩ :
    (p : Int) ∣ (p : Int) * (q * tt F n (var n a1 b1) (var n a2 b2) (var n a3 b3)))
  refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mp hfin
  refine ⟨0, ?_⟩
  rw [Int.mul_zero]
  have e4 : (p : Int) * (q * tt F n (var n a1 b1) (var n a2 b2) (var n a3 b3)) =
      (u * M4 n - 1) * tt F n (var n a1 b1) (var n a2 b2) (var n a3 b3) := by
    rw [← Int.mul_assoc, ← hq]
  rw [e4]
  grind

theorem hole4 (hn : 0 < n) (hk : (p : Int) ∣ (k : Int)) (hu : (p : Int) ∣ u * M4 n - 1) (j : Nat) (hj : j < n)
    (x1 x2 x3 : Nat) :
    (p : Int) ∣ (Ext4 F u).E (fun a => monoEval a [x1, x2, x3] * (sumOne (fun i => var n i j) (n + k)).eval a) := by
  let N := (n + k) * n
  by_cases hN : x1 < N ∧ x2 < N ∧ x3 < N
  case neg =>
    have : (Ext4 F u).E (fun a => monoEval a [x1, x2, x3] * (sumOne (fun i => var n i j) (n + k)).eval a) =
        (Ext4 F u).E (fun _ => 0) := by
      apply (Ext4 F u).supp; intro a ha
      by_cases h1 : x1 < N
      · by_cases h2 : x2 < N
        · rw [monoEval_zero ha _ x3 (by simp) (by omega), Int.zero_mul]
        · rw [monoEval_zero ha _ x2 (by simp) (by omega), Int.zero_mul]
      · rw [monoEval_zero ha _ x1 (by simp) (by omega), Int.zero_mul]
    rw [this]; exact (Ext4 F u).zero
  obtain ⟨hx1, hx2, hx3⟩ := hN
  have hlowP : ∀ y1 y2 : Nat, (∀ x, x ∈ [x1, x2, x3] ↔ x ∈ [y1, y2]) →
      (p : Int) ∣ (Ext4 F u).E (fun a => monoEval a [x1, x2, x3] * (sumOne (fun i => var n i j) (n + k)).eval a) := by
    intro y1 y2 hy
    have e : (fun a => monoEval a [x1, x2, x3] * (sumOne (fun i => var n i j) (n + k)).eval a) =
        fun a => monoEval a [y1, y2] * (sumOne (fun i => var n i j) (n + k)).eval a := by
      funext a; rw [monoEval_congr a [x1, x2, x3] [y1, y2] hy]
    rw [e]
    exact low_kill (D := 4) hF (E_extends F u) (mem_hole hj)
      (by have := sumOne_deg (fun i => var n i j) (n + k); simp; omega)
  by_cases h12 : x1 = x2
  · exact hlowP x1 x3 (fun x => by simp; omega)
  by_cases h13 : x1 = x3
  · exact hlowP x1 x2 (fun x => by simp; omega)
  by_cases h23 : x2 = x3
  · exact hlowP x1 x2 (fun x => by simp; omega)
  have hsplit := E_rsum F u (n + k) (fun i a => monoEval a [x1, x2, x3, var n i j]) (fun a => monoEval a [x1, x2, x3])
  have e0 : (fun a => monoEval a [x1, x2, x3] * (sumOne (fun i => var n i j) (n + k)).eval a) =
      fun a => rsum (n + k) (fun i => monoEval a [x1, x2, x3, var n i j]) - monoEval a [x1, x2, x3] := by
    funext a; rw [mono_split]; simp
  rw [e0, hsplit]
  have hvl : ∀ i < n + k, var n i j < N := fun i hi => var_lt n k i j hi hj
  have hconf : ∀ v w, v ∈ [x1, x2, x3] → w ∈ [x1, x2, x3] → conf n v w →
      (p : Int) ∣ rsum (n + k) (fun i => (Ext4 F u).E (fun a => monoEval a [x1, x2, x3, var n i j])) -
        (Ext4 F u).E (fun a => monoEval a [x1, x2, x3]) := by
    intro v w hv hw hc
    apply Int.dvd_sub
    · exact rsum_dvd _ _ _ (fun i hi => E_conf F u hF hn _ (by simp; exact ⟨hx1, hx2, hx3, hvl i hi⟩) (by simp) v w
        (mem_ext3 hv) (mem_ext3 hw) hc)
    · exact E_conf F u hF hn _ (by simp; omega) (by simp) v w hv hw hc
  by_cases hc : conf n x1 x2 ∨ conf n x1 x3 ∨ conf n x2 x3
  · rcases hc with hc | hc | hc
    · exact hconf x1 x2 (by simp) (by simp) hc
    · exact hconf x1 x3 (by simp) (by simp) hc
    · exact hconf x2 x3 (by simp) (by simp) hc
  have ha1 : x1 / n < n + k := (Nat.div_lt_iff_lt_mul hn).mpr hx1
  have ha2 : x2 / n < n + k := (Nat.div_lt_iff_lt_mul hn).mpr hx2
  have ha3 : x3 / n < n + k := (Nat.div_lt_iff_lt_mul hn).mpr hx3
  have hb1 : x1 % n < n := Nat.mod_lt _ hn
  have hb2 : x2 % n < n := Nat.mod_lt _ hn
  have hb3 : x3 % n < n := Nat.mod_lt _ hn
  have hab : x1 / n ≠ x2 / n ∧ x1 / n ≠ x3 / n ∧ x2 / n ≠ x3 / n ∧
      x1 % n ≠ x2 % n ∧ x1 % n ≠ x3 % n ∧ x2 % n ≠ x3 % n := by unfold conf at hc; omega
  have e1 := var_decode n x1; have e2 := var_decode n x2; have e3 := var_decode n x3
  have htrip : (Ext4 F u).E (fun a => monoEval a [x1, x2, x3]) = tt F n x1 x2 x3 := by
    rw [E_set F u _ [x1, x2, x3] (by simp; omega) (by simp) (fun _ => Iff.rfl), tt_F F hF x1 x2 x3 hc]
  have side : ∀ y : Nat, y ∈ [x1, x2, x3] → y < N → j = y % n →
      (p : Int) ∣ rsum (n + k) (fun i => (Ext4 F u).E (fun a => monoEval a [x1, x2, x3, var n i j])) -
        (Ext4 F u).E (fun a => monoEval a [x1, x2, x3]) := by
    intro y hy hyN hjy
    have ey := var_decode n y
    have hay : y / n < n + k := (Nat.div_lt_iff_lt_mul hn).mpr hyN
    apply rsum_pick_dvd (n + k) (y / n) hay
    intro i hi
    by_cases hia : i = y / n
    · rw [if_pos hia]
      have hv : var n i j = y := by rw [hia, hjy, ey]
      rw [hv, E_set F u [x1, x2, x3, y] [x1, x2, x3] (by simp; omega) (by simp)
        (mem_absorb hy), E_set F u [x1, x2, x3] [x1, x2, x3] (by simp; omega) (by simp)
        (fun _ => Iff.rfl), Int.sub_self]
      exact ⟨0, by simp⟩
    · rw [if_neg hia, Int.sub_zero]
      refine E_conf F u hF hn _ (by simp; exact ⟨hx1, hx2, hx3, hvl i hi⟩) (by simp) y (var n i j)
        (mem_ext3 hy) (by simp) ⟨?_, Or.inr ?_⟩
      · intro h; apply hia; rw [h, var_div n _ _ hj]
      · rw [var_mod n _ _ hj, hjy]
  by_cases hj1 : j = x1 % n
  · exact side x1 (by simp) hx1 hj1
  by_cases hj2 : j = x2 % n
  · exact side x2 (by simp) hx2 hj2
  by_cases hj3 : j = x3 % n
  · exact side x3 (by simp) hx3 hj3
  have hfour : ∀ i < n + k, (Ext4 F u).E (fun a => monoEval a [x1, x2, x3, var n i j]) =
      if i = x1 / n ∨ i = x2 / n ∨ i = x3 / n then 0 else
        u * S4 n (cc F) (yy F) (zz F n) (tt F n) (x1 / n) (x2 / n) (x3 / n) i (x1 % n) (x2 % n) (x3 % n) j := by
    intro i hi
    have h1 : x1 ≠ var n i j := fun h => hj1 (by rw [h, var_mod n _ _ hj])
    have h2 : x2 ≠ var n i j := fun h => hj2 (by rw [h, var_mod n _ _ hj])
    have h3 : x3 ≠ var n i j := fun h => hj3 (by rw [h, var_mod n _ _ hj])
    have hd : [x1, x2, x3, var n i j].Nodup := by simp [h12, h13, h23, h1, h2, h3, Ne.symm h12, Ne.symm h13, Ne.symm h23]
    rw [E_four F u _ _ _ _ hd (by simp; exact ⟨hx1, hx2, hx3, hvl i hi⟩)]
    unfold W4
    by_cases hi' : i = x1 / n ∨ i = x2 / n ∨ i = x3 / n
    · rw [if_pos hi', if_neg (isM4_row n x1 x2 x3 i j hj hi')]
    · rw [if_neg hi', if_pos (isM4_row' n x1 x2 x3 i j hj hab hj1 hj2 hj3 hi'), var_div n _ _ hj, var_mod n _ _ hj]
  rw [rsum_congr (n + k) _ _ hfour, rsum_skip3 (n + k) _ _ _ ha1 ha2 ha3 hab.1 hab.2.1 hab.2.2.1, htrip]
  generalize x1 / n = a1 at *
  generalize x2 / n = a2 at *
  generalize x3 / n = a3 at *
  generalize x1 % n = b1 at *
  generalize x2 % n = b2 at *
  generalize x3 % n = b3 at *
  subst e1 e2 e3
  have hT := hole_total n (cc F) (yy F) (zz F n) (tt F n) (zz_symm F n) (tt_12 F n) (tt_23 F n)
    (fun a b b' hb hb' h => zz_ch F n a b b' hb hb' h) (ttR12 F n) (ttR13 F n) (ttR23 F n) k hk
    (hC1 F (Programme.«20261025-1627-proof-complexity».OntoMom3.design2 F hF)) (hC2a F hF hn) (hC2 F (Programme.«20261025-1627-proof-complexity».OntoMom3.design2 F hF) hn)
    (hC3a F hF hn) (hC3b F hF hn) (hC3c F hF hn)
    a1 a2 a3 b1 b2 b3 j hab.1 hab.2.1 hab.2.2.1 hab.2.2.2.1 hab.2.2.2.2.1 hab.2.2.2.2.2
    (Ne.symm hj1) (Ne.symm hj2) (Ne.symm hj3) hb1 hb2 hb3 hj
  rw [← rsum_cmul]
  obtain ⟨q, hq⟩ := hu
  have hfin := Int.dvd_add (dvd_cmul u hT) (⟨q * tt F n (var n a1 b1) (var n a2 b2) (var n a3 b3), rfl⟩ :
    (p : Int) ∣ (p : Int) * (q * tt F n (var n a1 b1) (var n a2 b2) (var n a3 b3)))
  refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mp hfin
  refine ⟨0, ?_⟩
  rw [Int.mul_zero]
  have e4 : (p : Int) * (q * tt F n (var n a1 b1) (var n a2 b2) (var n a3 b3)) =
      (u * M4 n - 1) * tt F n (var n a1 b1) (var n a2 b2) (var n a3 b3) := by
    rw [← Int.mul_assoc, ← hq]
  rw [e4]
  grind

end

section
variable {n k : Nat} (F : Fn p (SN ((n + k) * n))) (u : Int) (hF : IsDesign (ontoFPHP n k) 3 F)
include hF

/-- Collision and functional axioms at level 4. -/
theorem prod4 (hn : 0 < n) (x x' v w : Nat) (hv : v < (n + k) * n) (hw : w < (n + k) * n) (hc : conf n v w) :
    (p : Int) ∣ (Ext4 F u).E (fun a => monoEval a [x, x'] * (prod2 v w).eval a) := by
  have e : (fun a => monoEval a [x, x'] * (prod2 v w).eval a) = fun a => monoEval a [x, x', v, w] := by
    funext a; rw [prod2_eval]; simp [monoEval, xv]; grind
  rw [e]
  by_cases hx : x < (n + k) * n
  · by_cases hx' : x' < (n + k) * n
    · exact E_conf F u hF hn _ (by simp; omega) (by simp) v w (by simp) (by simp) hc
    · rw [E_vanish F u _ x' (by simp) (by omega)]; exact (Ext4 F u).zero
  · rw [E_vanish F u _ x (by simp) (by omega)]; exact (Ext4 F u).zero

/-- **Extension.** -/
theorem ext4 (hn : 0 < n) (hk : (p : Int) ∣ (k : Int)) (hu : (p : Int) ∣ u * M4 n - 1) :
    IsDesign (ontoFPHP n k) 4 (Ext4 F u) := by
  intro P hP m hm
  by_cases hlow : m.length + P.deg ≤ 3
  · exact low_kill (D := 4) hF (E_extends F u) hP hlow
  rcases mem_ontoFPHP hP with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩ | hc | hf
  · have h1 := sumOne_deg (fun j => var n i j) n
    match m, hm with
    | [x1, x2, x3], _ => exact pig4 F u hF hn hu i hi x1 x2 x3
    | [], _ => simp at hlow; omega
    | [_], _ => simp at hlow; omega
    | [_, _], _ => simp at hlow; omega
    | _ :: _ :: _ :: _ :: _, hm => have := sumOne_deg_pos (fun j => var n i j) n hn; simp at hm; omega
  · have h1 := sumOne_deg (fun i => var n i j) (n + k)
    match m, hm with
    | [x1, x2, x3], _ => exact hole4 F u hF hn hk hu j hj x1 x2 x3
    | [], _ => simp at hlow; omega
    | [_], _ => simp at hlow; omega
    | [_, _], _ => simp at hlow; omega
    | _ :: _ :: _ :: _ :: _, hm => have := sumOne_deg_pos (fun i => var n i j) (n + k) (by omega); simp at hm; omega
  · obtain ⟨j, i, i', hj, hi, hi', hii, rfl⟩ := mem_collAx.mp hc
    rw [prod2_deg] at hm hlow
    match m, hm with
    | [x, x'], _ =>
      refine prod4 F u hF hn x x' _ _ (var_lt n k i j hi hj) (var_lt n k i' j hi' hj) ⟨fun h => ?_, Or.inr ?_⟩
      · have := (var_inj n _ _ _ _ hj hj h).1; omega
      · rw [var_mod n _ _ hj, var_mod n _ _ hj]
    | [], _ => simp at hlow
    | [_], _ => simp at hlow
    | _ :: _ :: _ :: _, hm => simp at hm
  · obtain ⟨i, j, j', hi, hj, hj', hjj, rfl⟩ := mem_funcAx.mp hf
    rw [prod2_deg] at hm hlow
    match m, hm with
    | [x, x'], _ =>
      refine prod4 F u hF hn x x' _ _ (var_lt n k i j hi hj) (var_lt n k i j' hi hj') ⟨fun h => ?_, Or.inl ?_⟩
      · have := (var_inj n _ _ _ _ hj hj' h).2; omega
      · rw [var_div n _ _ hj, var_div n _ _ hj']
    | [], _ => simp at hlow
    | [_], _ => simp at hlow
    | _ :: _ :: _ :: _, hm => simp at hm

end

/-! ## No degree-4 refutation -/

open Programme.«20261025-1627-proof-complexity».OntoExt2 (momFn mom mom_mono0) in
/-- **No degree-4 refutation.** For `p > 1`, `p ∣ k`, `n > 0`, with `24n(n-1)⋯(n-6)`, `6n(n-1)⋯(n-4)` and
`n(n-1)(n-2)` invertible mod `p`: `onto-FPHP^{n+k}_n` has no degree-4 PC refutation over `Z/p`. -/
theorem ontoFPHP_no_deg4 (n k : Nat) (hp : 1 < p) (hn : 0 < n) (hk : (p : Int) ∣ (k : Int)) (u u3 u2 : Int)
    (hu : (p : Int) ∣ u * M4 n - 1) (hu3 : (p : Int) ∣ u3 * Programme.«20261025-1627-proof-complexity».Ext3Alg.M3 n - 1)
    (hu2 : (p : Int) ∣ u2 * ((n : Int) * ((n : Int) - 1) * ((n : Int) - 2)) - 1) :
    ¬ PPCRefutation p (ontoFPHP n k) 4 := by
  let E0 := momFn p ((n + k) * n) 1 (fun _ => u2 * ((n : Int) - 1) * ((n : Int) - 2)) (fun _ _ => 0)
  have h0 : IsDesign (ontoFPHP n k) 1 E0 := Programme.«20261025-1627-proof-complexity».OntoExt3.base1 n k hn hk u2 hu2
  obtain ⟨E1, hE1, hx1⟩ := Programme.«20261025-1627-proof-complexity».OntoExt2.ext2 n k hn hk u2 hu2 E0 h0
  have hE2 := Programme.«20261025-1627-proof-complexity».OntoExt3.ext3 E1 u3 hE1 hn hk hu3
  have hx2 := Programme.«20261025-1627-proof-complexity».OntoExt3.E_extends E1 u3
  have h1 : ¬ (p : Int) ∣ (Programme.«20261025-1627-proof-complexity».OntoExt3.Ext E1 u3).E (fun _ => 1) := by
    intro h
    have a := hx1 [] (by simp)
    have b := hx2 [] (by simp)
    have e : (fun a => monoEval a ([] : List Nat)) = fun _ => (1 : Int) := by funext a; simp [monoEval]
    rw [e] at a b
    have hE0 : E0.E (fun _ => 1) = 1 := by
      show mom _ 1 _ _ (fun _ => 1) = 1
      rw [← e, mom_mono0]
    rw [hE0] at a
    have := Int.dvd_sub h (Int.dvd_add b a)
    rw [show (Programme.«20261025-1627-proof-complexity».OntoExt3.Ext E1 u3).E (fun _ => 1) -
      ((Programme.«20261025-1627-proof-complexity».OntoExt3.Ext E1 u3).E (fun _ => 1) - E1.E (fun _ => 1) + (E1.E (fun _ => 1) - 1)) = 1 by omega] at this
    exact not_dvd_one hp this
  exact ext_sound (D := 4) (by decide) (fun F hF => ⟨Ext4 F u, ext4 F u hF hn hk hu, E_extends F u⟩) _ hE2 h1

/-- With restriction (K83): for `p > 1` coprime to `210` (`120960 = 24·7!` invertible mod `p`) and `p ∣ k`,
onto-FPHP^{n+k}_n has no PC refutation of degree `≤ 4` over `Z/p`, for every `n ≥ 7`. -/
theorem ontoFPHP_no_deg4_all (n k D : Nat) (hp : 1 < p) (hk : (p : Int) ∣ (k : Int))
    (h120960 : ∃ u : Int, (p : Int) ∣ 120960 * u - 1) (hn : 7 ≤ n) (hD : D ≤ 4) :
    ¬ PPCRefutation p (ontoFPHP n k) D := by
  intro h
  have h4 : PPCRefutation p (ontoFPHP n k) 4 :=
    Programme.«20261025-0459-proof-complexity».OntoPCLower.PPCDerivable.mono hD h
  obtain ⟨u, hu⟩ := h120960
  have base := ontoFPHP_no_deg4 (p := p) 7 k hp (by decide) hk u (8 * u) (576 * u)
    (by have e : u * M4 7 - 1 = 120960 * u - 1 := by unfold M4; push_cast; grind
        rw [e]; exact hu)
    (by have e : 8 * u * Programme.«20261025-1627-proof-complexity».Ext3Alg.M3 7 - 1 = 120960 * u - 1 := by unfold Programme.«20261025-1627-proof-complexity».Ext3Alg.M3; push_cast; grind
        rw [e]; exact hu)
    (by have e : 576 * u * (((7 : Nat) : Int) * (((7 : Nat) : Int) - 1) * (((7 : Nat) : Int) - 2)) - 1 = 120960 * u - 1 := by
          push_cast; grind
        rw [e]; exact hu)
  apply base
  clear h
  obtain ⟨d, rfl⟩ : ∃ d, n = 7 + d := ⟨n - 7, by omega⟩
  clear hn
  induction d with
  | zero => exact h4
  | succ d ih =>
    apply ih
    exact Programme.«20261025-0459-proof-complexity».OntoSubst.ontoFPHP_restrict p (7 + d) k 4
      (by decide) (by omega) (by rwa [show 7 + d + 1 = 7 + (d + 1) by omega])

end Programme.«20261025-1627-proof-complexity».OntoExt4

#print axioms Programme.«20261025-1627-proof-complexity».OntoExt4.ontoFPHP_no_deg4
#print axioms Programme.«20261025-1627-proof-complexity».OntoExt4.ontoFPHP_no_deg4_all
