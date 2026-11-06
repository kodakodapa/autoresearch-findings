import Programme.«20261026-1402-proof-complexity».Ext1

/-!
# EXT at level 1 over `F_2` when `4 ∣ k`: th's rotational-tournament 2-design (K33)

`EXT 2 3 k 1` for `4 ∣ k`. Write `f = s + G` on single edges, `s = c(∅)`; then `G` has every row
and column sum even (`3 ≡ 1`, `3 + k ≡ 1`). The witness is `Yf G 0 + s · Tour`, where `Yf` is the
char-free part of the odd-`p` operator of `Work.Ext1` (with `t = 0` it needs no division by 2)
and `Tour` is th's rotational tournament on `P = 3 + k` pigeons: the pair `{(u,c),(v,c+1)}` has
value `1` iff `v - u ∈ {1, …, (P-1)/2}` mod `P`. Rows: a tournament orients each pair once. Columns:
out- and in-degrees are `(P-1)/2 = k/2 + 1`, odd iff `4 ∣ k`.

`no_deg2`: for `4 ∣ k` and `n ≥ 3`, `ontoFPHP n k` has no degree-2 `PPCRefutation 2`.
-/

namespace Programme.«20261026-1402-proof-complexity».Ext1F2

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr var_div var_mod)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (rsum_pick rsum_skip var_lt var_decode)
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».Ext1 (Yf core_row core_col isMatch_pair canon_pair F3 row0 col0 canon_nil)

/-! ## The rotational tournament -/

/-- `Tw P a i = 1` iff `i - a ∈ {1, …, P/2}` mod `P` (for `a, i < P`). -/
def Tw (P a i : Nat) : Int := if (a < i ∧ i ≤ a + P / 2) ∨ i + P ≤ a + P / 2 then 1 else 0

/-- The tournament on the pair `{(u,c),(v,d)}`, oriented along the hole cycle `0 → 1 → 2 → 0`. -/
def Tour (P u c v d : Nat) : Int :=
  if d = (c + 1) % 3 then Tw P u v else if c = (d + 1) % 3 then Tw P v u else 0

theorem Tw_self (P a : Nat) (hP : 0 < P) : Tw P a a = 0 := by unfold Tw; simp; omega

theorem Tw_excl (P a i : Nat) (hP : P % 2 = 1) (ha : a < P) (hi : i < P) (hia : i ≠ a) :
    Tw P a i + Tw P i a = 1 := by
  unfold Tw
  by_cases h1 : (a < i ∧ i ≤ a + P / 2) ∨ i + P ≤ a + P / 2 <;>
  by_cases h2 : (i < a ∧ a ≤ i + P / 2) ∨ a + P ≤ i + P / 2 <;> simp only [h1, h2, if_true, if_false] <;>
  omega

theorem Tour_symm (P u c v d : Nat) (hcd : c ≠ d) (hc : c < 3) (hd : d < 3) :
    Tour P u c v d = Tour P v d u c := by
  unfold Tour
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;>
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with rfl | rfl | rfl <;> simp at hcd ⊢

/-! ## Counting -/

theorem cnt (P lo hi : Nat) (h : lo ≤ hi) :
    rsum P (fun i => if lo ≤ i ∧ i < hi then 1 else 0) = ((min hi P - min lo P : Nat) : Int) := by
  induction P with
  | zero => simp [rsum]
  | succ P ih =>
    rw [rsum, ih]
    split <;> omega

theorem rsum_smul (m : Nat) (s : Int) (g : Nat → Int) : rsum m (fun i => s * g i) = s * rsum m g := by
  induction m with
  | zero => simp [rsum]
  | succ m ih => simp only [rsum, ih]; grind

theorem rsum_subc (m : Nat) (s : Int) (g : Nat → Int) : rsum m (fun i => g i - s) = rsum m g - m * s := by
  induction m with
  | zero => simp [rsum]
  | succ m ih => simp only [rsum, ih]; push_cast; grind

theorem rsum_one (m : Nat) : rsum m (fun _ => (1 : Int)) = m := by
  induction m with
  | zero => simp [rsum]
  | succ m ih => simp only [rsum, ih]; push_cast; rfl

theorem out_deg (P a : Nat) (ha : a < P) : rsum P (fun i => Tw P a i) = ((P / 2 : Nat) : Int) := by
  have e : ∀ i, i < P → Tw P a i = (if a + 1 ≤ i ∧ i < a + P / 2 + 1 then 1 else 0) +
      (if 0 ≤ i ∧ i < a + P / 2 + 1 - P then 1 else 0) := fun i hi => by
    unfold Tw
    split <;> split <;> split <;> omega
  rw [rsum_congr P _ _ (fun i hi => e i hi), rsum_add, cnt P _ _ (by omega), cnt P _ _ (by omega)]
  omega

theorem in_deg (P a : Nat) (hP : P % 2 = 1) (ha : a < P) :
    rsum P (fun i => Tw P i a) = ((P / 2 : Nat) : Int) := by
  have e : rsum P (fun i => Tw P a i + Tw P i a) = rsum P (fun i => if i = a then 0 else 1) :=
    rsum_congr P _ _ (fun i hi => by
      by_cases h : i = a
      · subst h; simp [Tw_self P i (by omega)]
      · simp [h, Tw_excl P a i hP ha hi h])
  rw [rsum_add, rsum_skip P a ha, rsum_one, out_deg P a ha] at e
  simp at e
  omega

/-! ## Line sums of the tournament part -/

theorem tour_row (P : Nat) (hP : P % 2 = 1) (s : Int) (a i b : Nat) (ha : a < P) (hi : i < P) (hia : i ≠ a)
    (hb : b < 3) : rsum 3 (fun j => if i = a ∨ j = b then 0 else s * Tour P i j a b) = s := by
  have ex := Tw_excl P a i hP ha hi hia
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
    simp [rsum, Tour, hia] <;> grind

theorem tour_col (P : Nat) (hP : P % 2 = 1) (s : Int) (a b j : Nat) (ha : a < P) (hb : b < 3) (hj : j < 3)
    (hjb : j ≠ b) : rsum P (fun i => if i = a ∨ j = b then 0 else s * Tour P i j a b) = s * ((P / 2 : Nat) : Int) := by
  have hT : (∀ i, Tour P i j a b = Tw P a i) ∨ (∀ i, Tour P i j a b = Tw P i a) := by
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> simp at hjb <;> simp [Tour]
  rcases hT with hT | hT
  · rw [rsum_congr P _ (fun i => s * Tw P a i) (fun i _ => by
        by_cases h : i = a
        · subst h; simp [Tw_self P i (by omega), hT]
        · simp [h, hT, hjb])]
    rw [rsum_smul, out_deg P a ha]
  · rw [rsum_congr P _ (fun i => s * Tw P i a) (fun i _ => by
        by_cases h : i = a
        · subst h; simp [Tw_self P i (by omega), hT]
        · simp [h, hT, hjb])]
    rw [rsum_smul, in_deg P a hP ha]

/-! ## The witness -/

theorem rsum_ite_add (m : Nat) (c : Nat → Prop) [DecidablePred c] (A B : Nat → Int) :
    rsum m (fun j => if c j then 0 else A j + B j) =
      rsum m (fun j => if c j then 0 else A j) + rsum m (fun j => if c j then 0 else B j) := by
  rw [← rsum_add]
  exact rsum_congr _ _ _ (fun j _ => by by_cases h : c j <;> simp [h])

/-- The pair value: `Yf G 0 + s · Tour`. -/
def Z (G : Nat → Nat → Int) (s : Int) (P u c v d : Nat) : Int := Yf G 0 u c v d + s * Tour P u c v d

def yyZ (W : Nat → Nat → Nat → Nat → Int) : List Nat → Int
  | [v, w] => W (v / 3) (v % 3) (w / 3) (w % 3)
  | _ => 0

theorem termZ (W : Nat → Nat → Nat → Nat → Int)
    (hW : ∀ u c v d, u ≠ v → c ≠ d → c < 3 → d < 3 → W u c v d = W v d u c)
    (k i j w : Nat) (hi : i < 3 + k) (hj : j < 3) (hw : w < (3 + k) * 3) :
    (if isMatch 3 (var 3 i j :: [w]) then yyZ W (canon ((3 + k) * 3) (var 3 i j :: [w])) else 0) =
      if i = w / 3 ∨ j = w % 3 then 0 else W i j (w / 3) (w % 3) := by
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
      rcases canon_pair _ _ _ hx hw he with h | h <;> rw [h] <;> simp only [yyZ, hdi, hmj] <;>
        first | rfl | exact hW (w / 3) (w % 3) i j (by omega) (by omega) hb hj

theorem Z_symm (G : Nat → Nat → Int) (s : Int) (P : Nat) :
    ∀ u c v d, u ≠ v → c ≠ d → c < 3 → d < 3 → Z G s P u c v d = Z G s P v d u c := by
  intro u c v d huv hcd hc hd
  unfold Z
  rw [Programme.«20261026-1402-proof-complexity».Ext1.Yf_symm G 0 u c v d huv hcd hc hd, Tour_symm P u c v d hcd hc hd]

/-- **EXT at level 1 over `F_2`** for `4 ∣ k`, at `n = 3`. -/
theorem ext1 {k : Nat} (hk : 4 ∣ k) : EXT 2 3 k 1 := by
  intro f c hbal
  have hb0 := hbal 0 rfl
  have hCM : CM 3 k [] := ⟨canon_nil _, rfl⟩
  have hR : ∀ i < 3 + k, (2 : Int) ∣ F3 f i 0 + F3 f i 1 + F3 f i 2 - c [] := fun i hi => by
    have := (hb0 [] hCM rfl).1 i hi (fun v hv => by simp at hv)
    rwa [row0 f k i hi] at this
  have hC : ∀ j < 3, (2 : Int) ∣ rsum (3 + k) (fun i => F3 f i j) - c [] := fun j hj => by
    have := (hb0 [] hCM rfl).2 j hj (fun v hv => by simp at hv)
    rwa [col0 f k j hj] at this
  obtain ⟨m, rfl⟩ := hk
  let s := c []
  let G : Nat → Nat → Int := fun i j => F3 f i j - s
  have hRG : ∀ i < 3 + 4 * m, (2 : Int) ∣ G i 0 + G i 1 + G i 2 - 0 := fun i hi => by
    obtain ⟨q, hq⟩ := hR i hi
    exact ⟨q - s, by simp only [G]; grind⟩
  have hCG : ∀ h < 3, (2 : Int) ∣ rsum (3 + 4 * m) (fun i => G i h) - 0 := fun h hh => by
    obtain ⟨q, hq⟩ := hC h hh
    refine ⟨q - (1 + 2 * m) * s, ?_⟩
    simp only [G]; rw [rsum_subc]; push_cast; grind
  have hPX : ∀ X : Int, (2 : Int) ∣ ((3 + 4 * m : Nat) : Int) * X - 3 * X := fun X =>
    ⟨2 * m * X, by push_cast; grind⟩
  have ht : (2 : Int) ∣ 2 * 0 - 0 := ⟨0, rfl⟩
  have hP2 : (3 + 4 * m) % 2 = 1 := by omega
  refine ⟨yyZ (Z G s (3 + 4 * m)), ?_⟩
  intro g hg hgl
  obtain ⟨w, rfl⟩ : ∃ w, g = [w] := by
    match g, hgl with
    | [w], _ => exact ⟨w, rfl⟩
  have hw : w < (3 + 4 * m) * 3 := CM_lt hg (by simp)
  have ha : w / 3 < 3 + 4 * m := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hw)
  have hb : w % 3 < 3 := Nat.mod_lt _ (by omega)
  have hfw : f [w] = F3 f (w / 3) (w % 3) := by
    unfold F3; rw [var_decode]
  rw [hfw]
  refine ⟨fun i hi hpf => ?_, fun j hj hhf => ?_⟩
  · have hia : i ≠ w / 3 := fun e => hpf w (by simp) e.symm
    unfold rowS lineS
    rw [rsum_congr 3 _ _ (fun j hj => termZ _ (Z_symm G s _) (4 * m) i j w hi hj hw)]
    simp only [Z]
    rw [rsum_ite_add, tour_row _ hP2 s (w / 3) i (w % 3) ha hi hia hb]
    obtain ⟨q, hq⟩ := core_row 2 G 0 0 ht (w / 3) i (w % 3) (hRG _ ha) (hRG i hi) hia hb
    exact ⟨q, by simp only [G] at hq ⊢; omega⟩
  · have hjb : j ≠ w % 3 := fun e => hhf w (by simp) e.symm
    unfold colS lineS
    rw [rsum_congr (3 + 4 * m) _ _ (fun i hi => termZ _ (Z_symm G s _) (4 * m) i j w hi hj hw)]
    simp only [Z]
    rw [rsum_ite_add, tour_col _ hP2 s (w / 3) (w % 3) j ha hb hj hjb]
    obtain ⟨q, hq⟩ := core_col 2 (3 + 4 * m) (by omega) G 0 0 ht hCG hPX (w / 3) (w % 3) j ha
      (hRG 0 (by omega)) (hRG _ ha) hb hj hjb
    have e2 : ((3 + 4 * m) / 2 : Nat) = 1 + 2 * m := by omega
    rw [e2]
    exact ⟨q + m * s, by simp only [G] at hq ⊢; push_cast; grind⟩

/-- **No degree-2 refutation over `Z/2`.** For `4 ∣ k` and every `n ≥ 3`, `ontoFPHP n k` has no
degree-2 `PPCRefutation 2`. -/
theorem no_deg2 {k : Nat} (hk : 4 ∣ k) (n : Nat) (hn : 3 ≤ n) : ¬ PPCRefutation 2 (ontoFPHP n k) 2 :=
  no_refutation_of_ext_ge (by omega) (by omega) (by omega) (fun d hd => by
    rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl
    · exact Programme.«20261026-1402-proof-complexity».Ext0.ext0 (by omega) (Nat.dvd_trans ⟨2, rfl⟩ hk)
    · exact ext1 hk) n hn

end Programme.«20261026-1402-proof-complexity».Ext1F2

#print axioms Programme.«20261026-1402-proof-complexity».Ext1F2.ext1
#print axioms Programme.«20261026-1402-proof-complexity».Ext1F2.no_deg2
