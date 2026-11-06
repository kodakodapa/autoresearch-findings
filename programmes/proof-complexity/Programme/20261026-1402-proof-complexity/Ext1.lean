import Programme.«20261026-1402-proof-complexity».Ext0

/-!
# EXT at level 1 for odd `p`: no degree-2 PC refutation of onto-FPHP when `p ∣ k`

`EXT p 3 k 1` (th's `EXT_p(3,k,2)`): every `f` on single edges of `ontoFPHP 3 k` whose row and
column sums are all `≡ s` mod `p` has a `y` on 2-matchings with, for every edge `e = (a,b)`, every
free row `i ≠ a` and every free column `j ≠ b`, `∑ y(e,·) ≡ f(e)` along that line.

Explicit operator (non-equivariant: pigeon `0` and hole `2` are special), `t = s(p+1)/2`, so
`2t ≡ s`. For a pair `{(u,c),(v,d)}` of disjoint edges, with `F u c = f(x_{uc})`:
* `c, d ∈ {0,1}`: `F u c + F v d - t` if `u, v ≠ 0`; `F v c + F 0 c - t` if `u = 0`;
* `c = 2`, `d ∈ {0,1}`: `t - F u (1-d)` if `u, v ≠ 0`; `t - F u d` if `v = 0`;
  `t + F v d - F v (1-d) - F 0 (1-d)` if `u = 0`.
It is the closed form of th's rectangle decomposition (K11) at `n = 3` with the constant-`1/2`
2-design on holes `0, 1`. Row conditions are exact identities up to one row sum and `2t ≡ s`;
column conditions use the column sums of `f` and `3 + k ≡ 3` mod `p`.

`no_deg2`: with `Work.Ext0.ext0` and `Work.ExtLemma.no_refutation_of_ext_ge`, for odd `p > 1` and
`p ∣ k`, `ontoFPHP n k` has no degree-2 `PPCRefutation p` for every `n ≥ 3`.
-/

namespace Programme.«20261026-1402-proof-complexity».Ext1

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr var_div var_mod)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (rsum_pick rsum_skip var_lt var_decode)
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261026-1402-proof-complexity».ExtLemma

/-! ## The operator -/

/-- Value on the pair `{(u,c),(v,d)}` with `d ≠ 2`. -/
def Y0 (F : Nat → Nat → Int) (t : Int) (u c v d : Nat) : Int :=
  if c = 2 then
    (if u = 0 then t + F v d - F v (1 - d) - F 0 (1 - d) else if v = 0 then t - F u d else t - F u (1 - d))
  else
    (if u = 0 then F v c + F 0 c - t else if v = 0 then F u d + F 0 d - t else F u c + F v d - t)

/-- Value on the pair `{(u,c),(v,d)}`. -/
def Yf (F : Nat → Nat → Int) (t : Int) (u c v d : Nat) : Int :=
  if d = 2 then Y0 F t v d u c else Y0 F t u c v d

theorem Yf_symm (F : Nat → Nat → Int) (t : Int) (u c v d : Nat) (huv : u ≠ v) (hcd : c ≠ d)
    (hc : c < 3) (hd : d < 3) : Yf F t u c v d = Yf F t v d u c := by
  unfold Yf Y0
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;>
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with rfl | rfl | rfl <;> simp at hcd ⊢ <;>
  by_cases hu : u = 0 <;> by_cases hv : v = 0 <;> simp [hu, hv] <;> omega

/-! ## Arithmetic -/

theorem dvd3 {p A B C E : Int} (h1 : p ∣ A) (h2 : p ∣ B) (h3 : p ∣ C) (c1 c2 c3 : Int)
    (e : E = c1 * A + c2 * B + c3 * C) : p ∣ E := by
  rw [e]
  exact Int.dvd_add (Int.dvd_add (Int.dvd_trans h1 (Int.dvd_mul_left _ _))
    (Int.dvd_trans h2 (Int.dvd_mul_left _ _))) (Int.dvd_trans h3 (Int.dvd_mul_left _ _))

theorem dvd7 {p A1 A2 A3 A4 A5 A6 A7 E : Int} (h1 : p ∣ A1) (h2 : p ∣ A2) (h3 : p ∣ A3) (h4 : p ∣ A4)
    (h5 : p ∣ A5) (h6 : p ∣ A6) (h7 : p ∣ A7) (c1 c2 c3 c4 c5 c6 c7 : Int)
    (e : E = c1 * A1 + c2 * A2 + c3 * A3 + c4 * A4 + c5 * A5 + c6 * A6 + c7 * A7) : p ∣ E := by
  rw [e]
  have m : ∀ {A : Int} (c : Int), p ∣ A → p ∣ c * A := fun {A} c h => Int.dvd_trans h (Int.dvd_mul_left c A)
  exact Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (Int.dvd_add (m c1 h1) (m c2 h2))
    (m c3 h3)) (m c4 h4)) (m c5 h5)) (m c6 h6)) (m c7 h7)

theorem rsum_lin3 (P : Nat) (F : Nat → Nat → Int) (c0 c1 c2 K : Int) :
    rsum P (fun i => c0 * F i 0 + c1 * F i 1 + c2 * F i 2 + K) =
      c0 * rsum P (fun i => F i 0) + c1 * rsum P (fun i => F i 1) + c2 * rsum P (fun i => F i 2) + P * K := by
  induction P with
  | zero => simp [rsum]
  | succ P ih => simp only [rsum, ih]; push_cast; grind

/-- Sum over `i ≠ a`, `a ≠ 0`, of `G`, where `G` agrees with `L` off `{0, a}`. -/
theorem colsum (P a : Nat) (haP : a < P) (ha0 : a ≠ 0) (G L : Nat → Int)
    (hGL : ∀ i < P, i ≠ a → i ≠ 0 → G i = L i) :
    rsum P (fun i => if i = a then 0 else G i) = rsum P L - L a - L 0 + G 0 := by
  have e : rsum P (fun i => if i = a then 0 else G i) =
      rsum P (fun i => if i = a ∨ i = 0 then 0 else L i) + rsum P (fun i => if i = 0 then G 0 else 0) :=
    by
      rw [← rsum_add]
      exact rsum_congr _ _ _ (fun i hi => by
        by_cases h1 : i = a
        · subst h1; simp [ha0]
        · by_cases h2 : i = 0
          · subst h2; simp [show (0 : Nat) ≠ a from fun h => ha0 h.symm]
          · simp [h1, h2, hGL i hi h1 h2])
  rw [e, Programme.«20261025-1627-proof-complexity».OntoExt3.rsum_skip2 P a 0 haP (by omega) ha0, rsum_pick,
    if_pos (by omega)]
  all_goals omega

/-- Sum over `i ≠ 0` of `G`, where `G` agrees with `L` off `0`. -/
theorem colsum0 (P : Nat) (hP : 0 < P) (G L : Nat → Int) (hGL : ∀ i < P, i ≠ 0 → G i = L i) :
    rsum P (fun i => if i = 0 then 0 else G i) = rsum P L - L 0 := by
  rw [← rsum_skip P 0 hP L]
  exact rsum_congr _ _ _ (fun i hi => by by_cases h : i = 0 <;> simp [h, hGL i hi])

/-! ## Line conditions for the operator -/

theorem core_row (p : Int) (F : Nat → Nat → Int) (s t : Int) (ht : p ∣ 2 * t - s) (a i b : Nat)
    (hRa : p ∣ F a 0 + F a 1 + F a 2 - s) (hRi : p ∣ F i 0 + F i 1 + F i 2 - s) (hia : i ≠ a) (hb : b < 3) :
    p ∣ rsum 3 (fun j => if i = a ∨ j = b then 0 else Yf F t i j a b) - F a b := by
  by_cases ha0 : a = 0
  · subst ha0
    have hi0 : i ≠ 0 := hia
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
      simp [rsum, Yf, Y0, hi0] <;>
      first | exact dvd3 hRa hRi ht 0 0 0 (by omega) | exact dvd3 hRa hRi ht (-1) 0 1 (by omega)
  · by_cases hi0 : i = 0
    · subst hi0
      rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
        simp [rsum, Yf, Y0, ha0, hia] <;>
        first | exact dvd3 hRa hRi ht 0 0 0 (by omega) | exact dvd3 hRa hRi ht (-1) 0 1 (by omega)
    · rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
        simp [rsum, Yf, Y0, ha0, hi0, hia] <;>
        first | exact dvd3 hRa hRi ht 0 0 0 (by omega) | exact dvd3 hRa hRi ht (-1) 0 1 (by omega)

theorem core_col (p : Int) (P : Nat) (hP : 0 < P) (F : Nat → Nat → Int) (s t : Int) (ht : p ∣ 2 * t - s)
    (hC : ∀ h < 3, p ∣ rsum P (fun i => F i h) - s) (hPX : ∀ X : Int, p ∣ (P : Int) * X - 3 * X)
    (a b j : Nat) (haP : a < P) (hR0 : p ∣ F 0 0 + F 0 1 + F 0 2 - s) (hRa : p ∣ F a 0 + F a 1 + F a 2 - s)
    (hb : b < 3) (hj : j < 3) (hjb : j ≠ b) :
    p ∣ rsum P (fun i => if i = a ∨ j = b then 0 else Yf F t i j a b) - F a b := by
  rw [rsum_congr P _ (fun i => if i = a then 0 else Yf F t i j a b) (fun i _ => by simp [hjb])]
  have C0 := hC 0 (by omega)
  have C1 := hC 1 (by omega)
  have C2 := hC 2 (by omega)
  by_cases ha0 : a = 0
  · subst ha0
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> simp at hjb
    · -- b = 0, j = 1
      rw [colsum0 P hP _ (fun i => 1 * F i 0 + 0 * F i 1 + 0 * F i 2 + (F 0 0 - t))
        (fun i _ hi => by simp [Yf, Y0] <;> omega), rsum_lin3]
      exact dvd7 C0 C1 C2 hRa hR0 ht (hPX (F 0 0 - t)) 1 0 0 0 0 (-1) 1 (by omega)
    · -- b = 0, j = 2
      rw [colsum0 P hP _ (fun i => (-1) * F i 0 + 0 * F i 1 + 0 * F i 2 + t)
        (fun i _ hi => by simp [Yf, Y0] <;> omega), rsum_lin3]
      exact dvd7 C0 C1 C2 hRa hR0 ht (hPX t) (-1) 0 0 0 0 1 1 (by omega)
    · -- b = 1, j = 0
      rw [colsum0 P hP _ (fun i => 0 * F i 0 + 1 * F i 1 + 0 * F i 2 + (F 0 1 - t))
        (fun i _ hi => by simp [Yf, Y0] <;> omega), rsum_lin3]
      exact dvd7 C0 C1 C2 hRa hR0 ht (hPX (F 0 1 - t)) 0 1 0 0 0 (-1) 1 (by omega)
    · -- b = 1, j = 2
      rw [colsum0 P hP _ (fun i => 0 * F i 0 + (-1) * F i 1 + 0 * F i 2 + t)
        (fun i _ hi => by simp [Yf, Y0] <;> omega), rsum_lin3]
      exact dvd7 C0 C1 C2 hRa hR0 ht (hPX t) 0 (-1) 0 0 0 1 1 (by omega)
    · -- b = 2, j = 0
      rw [colsum0 P hP _ (fun i => 1 * F i 0 + (-1) * F i 1 + 0 * F i 2 + (t - F 0 1))
        (fun i _ hi => by simp [Yf, Y0] <;> omega), rsum_lin3]
      exact dvd7 C0 C1 C2 hRa hR0 ht (hPX (t - F 0 1)) 1 (-1) 0 (-1) 0 1 1 (by omega)
    · -- b = 2, j = 1
      rw [colsum0 P hP _ (fun i => (-1) * F i 0 + 1 * F i 1 + 0 * F i 2 + (t - F 0 0))
        (fun i _ hi => by simp [Yf, Y0] <;> omega), rsum_lin3]
      exact dvd7 C0 C1 C2 hRa hR0 ht (hPX (t - F 0 0)) (-1) 1 0 (-1) 0 1 1 (by omega)
  · rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> simp at hjb
    · -- b = 0, j = 1
      rw [colsum P a haP ha0 _ (fun i => 0 * F i 0 + 1 * F i 1 + 0 * F i 2 + (F a 0 - t))
        (fun i _ h1 h2 => by simp [Yf, Y0, h2, ha0] <;> omega), rsum_lin3]
      simp [Yf, Y0, ha0]
      exact dvd7 C0 C1 C2 hRa hR0 ht (hPX (F a 0 - t)) 0 1 0 0 0 (-1) 1 (by omega)
    · -- b = 0, j = 2
      rw [colsum P a haP ha0 _ (fun i => 0 * F i 0 + (-1) * F i 1 + 0 * F i 2 + t)
        (fun i _ h1 h2 => by simp [Yf, Y0, h2, ha0] <;> omega), rsum_lin3]
      simp [Yf, Y0, ha0]
      exact dvd7 C0 C1 C2 hRa hR0 ht (hPX t) 0 (-1) 0 0 0 1 1 (by omega)
    · -- b = 1, j = 0
      rw [colsum P a haP ha0 _ (fun i => 1 * F i 0 + 0 * F i 1 + 0 * F i 2 + (F a 1 - t))
        (fun i _ h1 h2 => by simp [Yf, Y0, h2, ha0] <;> omega), rsum_lin3]
      simp [Yf, Y0, ha0]
      exact dvd7 C0 C1 C2 hRa hR0 ht (hPX (F a 1 - t)) 1 0 0 0 0 (-1) 1 (by omega)
    · -- b = 1, j = 2
      rw [colsum P a haP ha0 _ (fun i => (-1) * F i 0 + 0 * F i 1 + 0 * F i 2 + t)
        (fun i _ h1 h2 => by simp [Yf, Y0, h2, ha0] <;> omega), rsum_lin3]
      simp [Yf, Y0, ha0]
      exact dvd7 C0 C1 C2 hRa hR0 ht (hPX t) (-1) 0 0 0 0 1 1 (by omega)
    · -- b = 2, j = 0
      rw [colsum P a haP ha0 _ (fun i => 0 * F i 0 + 0 * F i 1 + 0 * F i 2 + (t - F a 1))
        (fun i _ h1 h2 => by simp [Yf, Y0, h2, ha0] <;> omega), rsum_lin3]
      simp [Yf, Y0, ha0]
      exact dvd7 C0 C1 C2 hRa hR0 ht (hPX (t - F a 1)) 0 0 0 (-1) 0 1 1 (by omega)
    · -- b = 2, j = 1
      rw [colsum P a haP ha0 _ (fun i => 0 * F i 0 + 0 * F i 1 + 0 * F i 2 + (t - F a 0))
        (fun i _ h1 h2 => by simp [Yf, Y0, h2, ha0] <;> omega), rsum_lin3]
      simp [Yf, Y0, ha0]
      exact dvd7 C0 C1 C2 hRa hR0 ht (hPX (t - F a 0)) 0 0 0 (-1) 0 1 1 (by omega)

/-! ## The operator in matching coordinates -/

theorem isMatch_pair (n x w : Nat) (hne : x ≠ w) :
    isMatch n [x, w] = true ↔ (x / n ≠ w / n ∧ x % n ≠ w % n) := by
  simp [isMatch, cfl, hne, Ne.symm hne]
  intro h1 h2; exact ⟨fun e => h1 e.symm, fun e => h2 e.symm⟩

theorem canon_pair (N x w : Nat) (hx : x < N) (hw : w < N) (hne : x ≠ w) :
    canon N [x, w] = [x, w] ∨ canon N [x, w] = [w, x] := by
  have hl : (canon N [x, w]).length = 2 := by
    have := canon_len_eq (N := N) (l := [x, w]) (by simp [hne]) (by simp [hx, hw])
    simpa using this
  have hm : ∀ z, z ∈ canon N [x, w] ↔ z = x ∨ z = w := fun z => by
    rw [mem_canon]; simp
    rintro (rfl | rfl) <;> assumption
  have hnd := canon_nodup N [x, w]
  match h : canon N [x, w], hl with
  | [s1, s2], _ =>
    rw [h] at hm hnd
    have h1 := (hm s1).mp (by simp)
    have h2 := (hm s2).mp (by simp)
    have h12 : s1 ≠ s2 := by simp at hnd; exact hnd
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
    · exact absurd rfl h12
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl h12

/-- `F i j = f(x_{ij})` at `n = 3`. -/
def F3 (f : List Nat → Int) (i j : Nat) : Int := f [var 3 i j]

/-- The level-1 witness on canonical 2-lists. -/
def yy (f : List Nat → Int) (t : Int) : List Nat → Int
  | [v, w] => Yf (F3 f) t (v / 3) (v % 3) (w / 3) (w % 3)
  | _ => 0

theorem term (f : List Nat → Int) (t : Int) (k i j w : Nat) (hi : i < 3 + k) (hj : j < 3)
    (hw : w < (3 + k) * 3) :
    (if isMatch 3 (var 3 i j :: [w]) then yy f t (canon ((3 + k) * 3) (var 3 i j :: [w])) else 0) =
      if i = w / 3 ∨ j = w % 3 then 0 else Yf (F3 f) t i j (w / 3) (w % 3) := by
  have hx := var_lt 3 k i j hi hj
  have hdi := var_div 3 i j hj
  have hmj := var_mod 3 i j hj
  by_cases he : var 3 i j = w
  · have hc : canon ((3 + k) * 3) [var 3 i j, w] = [w] := by
      have e1 : canon ((3 + k) * 3) [var 3 i j, w] = canon ((3 + k) * 3) [w] :=
        canon_congr _ _ _ (fun z _ => by simp [he])
      rw [e1, Programme.«20261026-1402-proof-complexity».Ext0.canon_single _ w hw]
    have : i = w / 3 ∨ j = w % 3 := by left; rw [← he, hdi]
    rw [if_pos this, hc]; split <;> rfl
  · by_cases hc : i = w / 3 ∨ j = w % 3
    · rw [if_pos hc]
      have : ¬ isMatch 3 [var 3 i j, w] = true := by
        rw [isMatch_pair 3 _ _ he, hdi, hmj]; omega
      rw [if_neg this]
    · rw [if_neg hc]
      have : isMatch 3 [var 3 i j, w] = true := by
        rw [isMatch_pair 3 _ _ he, hdi, hmj]; omega
      rw [if_pos this]
      have hb : w % 3 < 3 := Nat.mod_lt _ (by omega)
      rcases canon_pair _ _ _ hx hw he with h | h <;> rw [h] <;> simp only [yy, hdi, hmj] <;>
        first | rfl | exact Yf_symm (F3 f) t (w / 3) (w % 3) i j (by omega) (by omega) hb hj

theorem canon_nil (N : Nat) : canon N [] = [] := by
  induction N with
  | zero => rfl
  | succ N ih => simp [canon, ih]

theorem row0 (f : List Nat → Int) (k i : Nat) (hi : i < 3 + k) :
    rowS 3 k f [] i = F3 f i 0 + F3 f i 1 + F3 f i 2 := by
  unfold rowS lineS
  rw [rsum_congr 3 _ (fun j => F3 f i j) (fun j hj => by
    rw [Programme.«20261026-1402-proof-complexity».Ext0.isMatch_single, if_pos rfl, Programme.«20261026-1402-proof-complexity».Ext0.canon_single _ _ (var_lt 3 k i j hi hj)]; rfl)]
  simp [rsum]

theorem col0 (f : List Nat → Int) (k j : Nat) (hj : j < 3) :
    colS 3 k f [] j = rsum (3 + k) (fun i => F3 f i j) := by
  unfold colS lineS
  exact rsum_congr _ _ _ (fun i hi => by
    rw [Programme.«20261026-1402-proof-complexity».Ext0.isMatch_single, if_pos rfl, Programme.«20261026-1402-proof-complexity».Ext0.canon_single _ _ (var_lt 3 k i j hi hj)]; rfl)

/-- **EXT at level 1** for odd `p` and `p ∣ k`, at `n = 3`. -/
theorem ext1 {p k : Nat} (hp : p % 2 = 1) (hk : p ∣ k) : EXT p 3 k 1 := by
  intro f c hbal
  have hb0 := hbal 0 rfl
  have hCM : CM 3 k [] := ⟨canon_nil _, rfl⟩
  have hR : ∀ i < 3 + k, (p : Int) ∣ F3 f i 0 + F3 f i 1 + F3 f i 2 - c [] := fun i hi => by
    have := (hb0 [] hCM rfl).1 i hi (fun v hv => by simp at hv)
    rwa [row0 f k i hi] at this
  have hC : ∀ j < 3, (p : Int) ∣ rsum (3 + k) (fun i => F3 f i j) - c [] := fun j hj => by
    have := (hb0 [] hCM rfl).2 j hj (fun v hv => by simp at hv)
    rwa [col0 f k j hj] at this
  let t : Int := c [] * (((p + 1) / 2 : Nat) : Int)
  have ht : (p : Int) ∣ 2 * t - c [] := by
    have e : 2 * (((p + 1) / 2 : Nat) : Int) = (p : Int) + 1 := by omega
    exact ⟨c [], by
      show 2 * (c [] * (((p + 1) / 2 : Nat) : Int)) - c [] = _
      rw [show 2 * (c [] * (((p + 1) / 2 : Nat) : Int)) = c [] * (2 * (((p + 1) / 2 : Nat) : Int)) by
        rw [← Int.mul_assoc, Int.mul_comm 2 (c []), Int.mul_assoc], e, Int.mul_add, Int.mul_one, Int.mul_comm]
      omega⟩
  have hPX : ∀ X : Int, (p : Int) ∣ ((3 + k : Nat) : Int) * X - 3 * X := fun X => by
    obtain ⟨m, rfl⟩ := hk
    exact ⟨m * X, by push_cast; rw [Int.add_mul, ← Int.mul_assoc]; omega⟩
  refine ⟨yy f t, ?_⟩
  intro g hg hgl
  obtain ⟨w, rfl⟩ : ∃ w, g = [w] := by
    match g, hgl with
    | [w], _ => exact ⟨w, rfl⟩
  have hw : w < (3 + k) * 3 := CM_lt hg (by simp)
  have ha : w / 3 < 3 + k := by
    have := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hw)
    exact this
  have hb : w % 3 < 3 := Nat.mod_lt _ (by omega)
  have hfw : f [w] = F3 f (w / 3) (w % 3) := by
    unfold F3; rw [var_decode]
  rw [hfw]
  refine ⟨fun i hi hpf => ?_, fun j hj hhf => ?_⟩
  · have hia : i ≠ w / 3 := fun e => hpf w (by simp) e.symm
    unfold rowS lineS
    rw [rsum_congr 3 _ _ (fun j hj => term f t k i j w hi hj hw)]
    exact core_row p (F3 f) (c []) t ht (w / 3) i (w % 3) (hR _ ha) (hR i hi) hia hb
  · have hjb : j ≠ w % 3 := fun e => hhf w (by simp) e.symm
    unfold colS lineS
    rw [rsum_congr (3 + k) _ _ (fun i hi => term f t k i j w hi hj hw)]
    exact core_col p (3 + k) (by omega) (F3 f) (c []) t ht hC hPX (w / 3) (w % 3) j ha (hR 0 (by omega))
      (hR _ ha) hb hj hjb

/-- **No degree-2 refutation.** For odd `p > 1` with `p ∣ k`, and every `n ≥ 3`, `ontoFPHP n k` has no
degree-2 `PPCRefutation p`. -/
theorem no_deg2 {p k : Nat} (hp1 : 1 < p) (hp : p % 2 = 1) (hk : p ∣ k) (n : Nat) (hn : 3 ≤ n) :
    ¬ PPCRefutation p (ontoFPHP n k) 2 :=
  no_refutation_of_ext_ge hp1 (by omega) (by omega) (fun d hd => by
    rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl
    · exact Programme.«20261026-1402-proof-complexity».Ext0.ext0 (by omega) hk
    · exact ext1 hp hk) n hn

end Programme.«20261026-1402-proof-complexity».Ext1

#print axioms Programme.«20261026-1402-proof-complexity».Ext1.ext1
#print axioms Programme.«20261026-1402-proof-complexity».Ext1.no_deg2
