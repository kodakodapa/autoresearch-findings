import Programme.«20261026-1402-proof-complexity».RectBlock

/-!
# L2: every disjoint rectangle product has a level-2 extension (`n ≥ 7`, `p ∣ k`)

For `f = r ⊗ r'` (`RectProd n k f`: `r = rect a a' b b'`, `r' = rect c c' d d'` on distinct
pigeons and distinct holes) pick fresh pigeons `x, y` and fresh holes `h, h'`. Block 0 is
`{a,a',x} × {b,b',h}`, block 1 is `{c,c',y} × {d,d',h'}`, block 2 is the rest (`n+k-6` pigeons,
`n-6 ≥ 1` holes). In block 2 a weight `μ` has every row and column sum `≡ 1` mod `p` (`mu_exists`,
since `p ∣ k`). Then `Work.ProdExt.bal_prod3` with th's block extensions `Yb` (`Work.RectBlock`)
gives `y` with `Bal p n k y f 2`.
-/

set_option linter.unusedSimpArgs false

namespace Programme.«20261026-1402-proof-complexity».RectExt

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero var_div var_mod)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt var_decode rsum_pick rsum_const)
open Programme.«20261025-1627-proof-complexity».OntoExt3 (rsum_sub')
open Programme.«20261025-1627-proof-complexity».MomGen (nodup_len)
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ExtLin
open Programme.«20261026-1402-proof-complexity».ProdExt
open Programme.«20261026-1402-proof-complexity».RectBlock

/-! ## Membership-invariance and homogeneity -/

theorem len_eq {l l' : List Nat} (hl : l.Nodup) (hl' : l'.Nodup) (hm : ∀ x, x ∈ l ↔ x ∈ l') :
    l.length = l'.length :=
  Nat.le_antisymm (nodup_len l l' hl (fun x h => (hm x).mp h)) (nodup_len l' l hl' (fun x h => (hm x).mpr h))

theorem hom_one (w : Nat → Int) : Hom (one w) 1 := by
  intro l hl; match l, hl with
  | [], _ => rfl
  | [_], h => exact absurd rfl h
  | _ :: _ :: _, _ => rfl

theorem hom_emp : Hom emp 0 := by
  intro l hl; match l, hl with
  | [], h => exact absurd rfl h
  | _ :: _, _ => rfl

theorem hom_tprod (u w : Nat → Int) : Hom (tprod u w) 2 := by
  intro l hl; match l, hl with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], h => exact absurd rfl h
  | _ :: _ :: _ :: _, _ => rfl

theorem SL_of_hom {φ : List Nat → Int} {ℓ : Nat} (hφ : Hom φ ℓ)
    (h : ∀ l l' : List Nat, l.length = ℓ → l.Nodup → l'.Nodup → (∀ x, x ∈ l ↔ x ∈ l') → φ l = φ l') : SL φ := by
  intro l l' hl hl' hm
  by_cases e : l.length = ℓ
  · exact h l l' e hl hl' hm
  · rw [hφ l e, hφ l' (by rw [← len_eq hl hl' hm]; exact e)]

theorem SL_one (w : Nat → Int) : SL (one w) := by
  apply SL_of_hom (hom_one w)
  intro l l' e hl hl' hm
  match l, l', e, len_eq hl hl' hm with
  | [v], [v'], _, _ =>
    have : v' = v := by have := (hm v').mpr (List.mem_singleton_self v'); simpa using this
    rw [this]

theorem SL_emp : SL emp := by
  apply SL_of_hom hom_emp
  intro l l' e hl hl' hm
  match l, l', e, len_eq hl hl' hm with
  | [], [], _, _ => rfl

theorem SL_tprod (u w : Nat → Int) : SL (tprod u w) := by
  apply SL_of_hom (hom_tprod u w)
  intro l l' e hl hl' hm
  match l, l', e, len_eq hl hl' hm with
  | [v1, v2], [w1, w2], _, _ =>
    have m1 := (hm w1).mpr (by simp)
    have m2 := (hm w2).mpr (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at m1 m2
    have n1 : v1 ≠ v2 := by simpa using hl
    have n2 : w1 ≠ w2 := by simpa using hl'
    unfold tprod
    rcases m1 with rfl | rfl <;> rcases m2 with rfl | rfl
    · exact absurd rfl n2
    · rfl
    · exact Int.add_comm _ _
    · exact absurd rfl n2

theorem SL_lin3 {A B C : List Nat → Int} (hA : SL A) (hB : SL B) (hC : SL C) :
    SL (fun l => A l - B l + C l) := by
  intro l l' hl hl' hm; simp only; rw [hA l l' hl hl' hm, hB l l' hl hl' hm, hC l l' hl hl' hm]

theorem SL_Yb (n a a2 x b b2 h : Nat) : SL (Yb n a a2 x b b2 h) :=
  SL_lin3 (SL_tprod _ _) (SL_tprod _ _) (SL_tprod _ _)

theorem hom_Yb (n a a2 x b b2 h : Nat) : Hom (Yb n a a2 x b b2 h) 2 := by
  intro l hl; unfold Yb; rw [hom_tprod _ _ l hl, hom_tprod _ _ l hl, hom_tprod _ _ l hl]; rfl

/-! ## The block-2 weight -/

theorem lsum_map_ite (L : List Nat) (q : Nat) (_F : Nat → Int) (hq : q ∉ L) :
    (L.map (fun j => if j = q then (1 : Int) else 0)).sum = 0 := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    have : a ≠ q := fun e => hq (by rw [← e]; exact List.mem_cons_self)
    rw [if_neg this, ih (fun h => hq (List.mem_cons_of_mem _ h))]; rfl

theorem lsum_congr (L : List Nat) (F G : Nat → Int) (h : ∀ x ∈ L, F x = G x) :
    (L.map F).sum = (L.map G).sum := by
  rw [List.map_congr_left h]

theorem lsum_zero' (L : List Nat) : (L.map (fun _ => (0 : Int))).sum = 0 := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; rfl

theorem lsum_const_one (L : List Nat) : (L.map (fun _ => (1 : Int))).sum = L.length := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; push_cast; omega

/-- Row and column sums `≡ 1` on a rectangle of lists whose lengths agree mod `p`. -/
theorem mu_exists (p : Int) : ∀ (L2 L1 : List Nat), L1.Nodup → L2.Nodup → L2 ≠ [] →
    L2.length ≤ L1.length → p ∣ (L1.length : Int) - L2.length →
    ∃ μ : Nat → Nat → Int, (∀ i ∈ L1, p ∣ (L2.map (μ i)).sum - 1) ∧
      (∀ j ∈ L2, p ∣ (L1.map (fun i => μ i j)).sum - 1)
  | [], _, _, _, h, _, _ => absurd rfl h
  | [q], L1, _, _, _, _, hd => by
    refine ⟨fun _ _ => 1, fun i _ => by simp, fun j hj => ?_⟩
    rw [lsum_const_one]; simpa using hd
  | q :: q2 :: L2, [], _, _, _, hl, _ => by simp at hl
  | q :: q2 :: L2, s :: L1, h1, h2, _, hl, hd => by
    obtain ⟨μ, hr, hc⟩ := mu_exists p (q2 :: L2) L1 (List.nodup_cons.mp h1).2 (List.nodup_cons.mp h2).2
      (by simp) (by simp at hl ⊢; omega) (by simp at hd ⊢; rw [show (L1.length : Int) + 1 - (L2.length + 1 + 1) =
        L1.length - (L2.length + 1) by omega] at hd; exact hd)
    have sL1 : s ∉ L1 := (List.nodup_cons.mp h1).1
    have qL2 : q ∉ q2 :: L2 := (List.nodup_cons.mp h2).1
    refine ⟨fun i j => if i = s then (if j = q then 1 else 0) else if j = q then 0 else μ i j, ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · rw [List.map_cons, List.sum_cons, lsum_congr (q2 :: L2) _ (fun j => if j = q then 1 else 0)
          (fun j _ => by simp), lsum_map_ite _ q (fun _ => 0) qL2]; simp
      · have his : i ≠ s := fun e => sL1 (e ▸ hi)
        simp only [his, if_false]
        rw [List.map_cons, List.sum_cons, if_pos rfl,
          lsum_congr (q2 :: L2) _ (μ i) (fun j hj => by rw [if_neg (fun e : j = q => qL2 (e ▸ hj))])]
        simpa using hr i hi
    · intro j hj
      simp only [List.mem_cons] at hj
      rcases hj with rfl | hj
      · simp only [if_true, List.map_cons, List.sum_cons]
        rw [lsum_congr L1 _ (fun _ => 0) (fun i hi => by rw [if_neg (fun e : i = s => sL1 (e ▸ hi))]),
          lsum_zero']
        simp
      · have hjq : j ≠ q := fun e => qL2 (e ▸ List.mem_cons.mpr hj)
        simp only [hjq, if_false, List.map_cons, List.sum_cons, if_true]
        rw [lsum_congr L1 _ (fun i => μ i j) (fun i hi => by rw [if_neg (fun e : i = s => sL1 (e ▸ hi))])]
        simpa using hc j (List.mem_cons.mpr hj)

theorem rsum_filter (M : Nat) (q : Nat → Prop) [DecidablePred q] (F : Nat → Int) :
    rsum M (fun t => if q t then F t else 0) = (((List.range M).filter (fun t => decide (q t))).map F).sum := by
  induction M with
  | zero => rfl
  | succ M ih =>
    simp only [rsum, ih, List.range_succ, List.filter_append, List.map_append, List.sum_append]
    by_cases h : q M <;> simp [h]

theorem len_filter (M : Nat) (q : Nat → Prop) [DecidablePred q] :
    (((List.range M).filter (fun t => decide (q t))).length : Int) = rsum M (fun t => if q t then 1 else 0) := by
  rw [rsum_filter, lsum_const_one]

theorem fresh (L : List Nat) (N : Nat) (h : L.length < N) : ∃ x, x < N ∧ x ∉ L := by
  apply Classical.byContradiction; intro H
  have hall : ∀ x ∈ List.range N, x ∈ L := fun x hx =>
    Classical.byContradiction fun hn => H ⟨x, List.mem_range.mp hx, hn⟩
  have := nodup_len _ _ List.nodup_range hall
  simp at this; omega

/-! ## Blocks from labels -/

/-- Block of a pigeon (or hole) given block-0 labels `a, a', x` and block-1 labels `c, c', y`. -/
def bpf (a a' x c c' y : Nat) (i : Nat) : Nat :=
  if i = a ∨ i = a' ∨ i = x then 0 else if i = c ∨ i = c' ∨ i = y then 1 else 2

theorem bpf_lt (a a' x c c' y i : Nat) : bpf a a' x c c' y i < 3 := by
  unfold bpf; split
  · omega
  · split <;> omega

theorem bpf0 (a a' x c c' y i : Nat) : bpf a a' x c c' y i = 0 ↔ i = a ∨ i = a' ∨ i = x := by
  unfold bpf; by_cases h : (i = a ∨ i = a' ∨ i = x)
  · rw [if_pos h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]; constructor
    · intro e; split at e <;> omega
    · intro e; exact absurd e h

theorem bpf1 {a a' x c c' y : Nat} (h1 : c ≠ a) (h2 : c ≠ a') (h3 : c ≠ x) (h4 : c' ≠ a) (h5 : c' ≠ a')
    (h6 : c' ≠ x) (h7 : y ≠ a) (h8 : y ≠ a') (h9 : y ≠ x) (i : Nat) :
    bpf a a' x c c' y i = 1 ↔ i = c ∨ i = c' ∨ i = y := by
  unfold bpf
  by_cases h : (i = c ∨ i = c' ∨ i = y)
  · have hn : ¬(i = a ∨ i = a' ∨ i = x) := by rcases h with rfl | rfl | rfl <;> omega
    rw [if_neg hn, if_pos h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · constructor
    · intro e; split at e
      · omega
      · omega
    · intro e; exact absurd e h

theorem bpf2 (a a' x c c' y i : Nat) :
    bpf a a' x c c' y i = 2 ↔ ¬(i = a ∨ i = a' ∨ i = x) ∧ ¬(i = c ∨ i = c' ∨ i = y) := by
  unfold bpf
  by_cases h : i = a ∨ i = a' ∨ i = x <;> by_cases h' : i = c ∨ i = c' ∨ i = y <;> simp [h, h']

theorem ind (t a : Nat) : (if t = a then (1 : Int) else 0) = if t = a then 1 else 0 := rfl

theorem count2 {N a a' x c c' y : Nat} (hP : [a, a', x, c, c', y].Nodup)
    (hl : ∀ i ∈ [a, a', x, c, c', y], i < N) :
    rsum N (fun t => if bpf a a' x c c' y t = 2 then (1 : Int) else 0) = (N : Int) - 6 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hP
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hl
  obtain ⟨⟨d1, d2, d3, d4, d5⟩, ⟨e1, e2, e3, e4⟩, ⟨f1, f2, f3⟩, ⟨g1, g2⟩, g3, -⟩ := hP
  have pt : ∀ t, (if bpf a a' x c c' y t = 2 then (1 : Int) else 0) =
      1 - ((if t = a then 1 else 0) + (if t = a' then 1 else 0) + (if t = x then 1 else 0) +
        (if t = c then 1 else 0) + (if t = c' then 1 else 0) + (if t = y then 1 else 0)) := by
    intro t
    simp only [bpf2]
    by_cases q1 : t = a
    · subst q1; simp [d1, d2, d3, d4, d5]
    by_cases q2 : t = a'
    · subst q2; simp [q1, e1, e2, e3, e4]
    by_cases q3 : t = x
    · subst q3; simp [q1, q2, f1, f2, f3]
    by_cases q4 : t = c
    · subst q4; simp [q1, q2, q3, g1, g2]
    by_cases q5 : t = c'
    · subst q5; simp [q1, q2, q3, q4, g3]
    by_cases q6 : t = y
    · subst q6; simp [q1, q2, q3, q4, q5]
    simp [q1, q2, q3, q4, q5, q6]
  rw [rsum_congr _ _ _ (fun t _ => pt t), rsum_sub', rsum_const, rsum_add, rsum_add, rsum_add, rsum_add,
    rsum_add, rsum_pick, rsum_pick, rsum_pick, rsum_pick, rsum_pick, rsum_pick]
  simp [hl.1, hl.2.1, hl.2.2.1, hl.2.2.2.1, hl.2.2.2.2.1, hl.2.2.2.2.2]

theorem blk_cases (bp bh : Nat → Nat) (hbp : ∀ i, bp i < 3) (n v : Nat) :
    blk bp bh n v = 0 ∨ blk bp bh n v = 1 ∨ blk bp bh n v = 2 ∨ blk bp bh n v = 3 := by
  unfold blk; have := hbp (v / n); split <;> omega

theorem rect_zero {n a a' b b' : Nat} (bp bh : Nat → Nat) {c : Nat} (hb : b < n) (hb' : b' < n)
    (ha : bp a = c) (ha' : bp a' = c) (hhb : bh b = c) (hhb' : bh b' = c) (v : Nat)
    (hv : blk bp bh n v ≠ c) : rect n a a' b b' v = 0 := by
  have k1 : v ≠ var n a b := by rintro rfl; rw [blk_var bp bh hb, ha, hhb] at hv; simp at hv
  have k2 : v ≠ var n a' b' := by rintro rfl; rw [blk_var bp bh hb', ha', hhb'] at hv; simp at hv
  have k3 : v ≠ var n a b' := by rintro rfl; rw [blk_var bp bh hb', ha, hhb'] at hv; simp at hv
  have k4 : v ≠ var n a' b := by rintro rfl; rw [blk_var bp bh hb, ha', hhb] at hv; simp at hv
  simp [rect, k1, k2, k3, k4]

/-- `tprod r r'` agrees with the block product `Prod (r, r', emp)` on pairs. -/
theorem tprod_eq_prod (n : Nat) (bp bh : Nat → Nat) (hbp : ∀ i, bp i < 3) (r r' : Nat → Int)
    (h0 : ∀ v, blk bp bh n v ≠ 0 → r v = 0) (h1 : ∀ v, blk bp bh n v ≠ 1 → r' v = 0) (v w : Nat) :
    tprod r r' [v, w] = ProdExt.Prod bp bh n (tri (one r) (one r') emp) [v, w] := by
  have cv := blk_cases bp bh hbp n v
  have cw := blk_cases bp bh hbp n w
  unfold ProdExt.Prod okL fl
  rcases cv with hv | hv | hv | hv <;> rcases cw with hw | hw | hw | hw <;>
    simp [hv, hw, tri, one, emp, tprod, h0 v, h1 v, h0 w, h1 w] <;> grind

/-- **L2 with labels.** -/
theorem rect_ext_lab {p n k : Nat} (hn : 7 ≤ n) (hk : (p : Int) ∣ k) (a a' x c c' y b b' h d d' h2 : Nat)
    (hP : [a, a', x, c, c', y].Nodup) (hH : [b, b', h, d, d', h2].Nodup)
    (hPl : ∀ i ∈ [a, a', x, c, c', y], i < n + k) (hHl : ∀ j ∈ [b, b', h, d, d', h2], j < n) :
    ∃ Y, Bal p n k Y (tprod (rect n a a' b b') (rect n c c' d d')) 2 := by
  have cP := count2 hP hPl
  have cH := count2 hH hHl
  have hP' := hP; have hH' := hH; have hPl' := hPl; have hHl' := hHl
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hP' hH'
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hPl' hHl'
  obtain ⟨⟨d1, d2, d3, d4, d5⟩, ⟨e1, e2, e3, e4⟩, ⟨f1, f2, f3⟩, ⟨g1, g2⟩, g3, -⟩ := hP'
  obtain ⟨⟨D1, D2, D3, D4, D5⟩, ⟨E1, E2, E3, E4⟩, ⟨F1, F2, F3⟩, ⟨G1, G2⟩, G3, -⟩ := hH'
  obtain ⟨la, la', lx, lc, lc', ly⟩ := hPl'
  obtain ⟨lb, lb', lh, ld, ld', lh2⟩ := hHl'
  have hn0 : 0 < n := by omega
  -- blocks
  let bp := bpf a a' x c c' y
  let bh := bpf b b' h d d' h2
  have bp0 : ∀ i, bp i = 0 ↔ i = a ∨ i = a' ∨ i = x := bpf0 a a' x c c' y
  have bh0 : ∀ j, bh j = 0 ↔ j = b ∨ j = b' ∨ j = h := bpf0 b b' h d d' h2
  have bp1 : ∀ i, bp i = 1 ↔ i = c ∨ i = c' ∨ i = y :=
    bpf1 (Ne.symm d3) (Ne.symm e2) (Ne.symm f1) (Ne.symm d4) (Ne.symm e3) (Ne.symm f2) (Ne.symm d5)
      (Ne.symm e4) (Ne.symm f3)
  have bh1 : ∀ j, bh j = 1 ↔ j = d ∨ j = d' ∨ j = h2 :=
    bpf1 (Ne.symm D3) (Ne.symm E2) (Ne.symm F1) (Ne.symm D4) (Ne.symm E3) (Ne.symm F2) (Ne.symm D5)
      (Ne.symm E4) (Ne.symm F3)
  -- block-2 weight
  let L1 := (List.range (n + k)).filter (fun i => decide (bp i = 2))
  let L2 := (List.range n).filter (fun j => decide (bh j = 2))
  have l1 : (L1.length : Int) = (n + k : Nat) - 6 := by rw [len_filter]; exact cP
  have l2 : (L2.length : Int) = (n : Nat) - 6 := by rw [len_filter]; exact cH
  obtain ⟨μ, hr, hc⟩ := mu_exists (p : Int) L2 L1 ((List.filter_sublist).nodup List.nodup_range)
    ((List.filter_sublist).nodup List.nodup_range)
    (by intro e; have : (L2.length : Int) = 0 := by rw [e]; rfl
        omega)
    (by omega) (by rw [l1, l2]; push_cast; rw [show (n : Int) + k - 6 - (n - 6) = k by omega]; exact hk)
  let M2 := one (fun v => μ (v / n) (v % n))
  -- local facts
  have rM2 : ∀ i < n + k, bp i = 2 → (p : Int) ∣ locL n M2 [] (var n i) n (fun t => bh t = 2) - 1 := by
    intro i hi hb2
    have e : locL n M2 [] (var n i) n (fun t => bh t = 2) = (L2.map (μ i)).sum := by
      unfold locL
      rw [← rsum_filter]
      apply rsum_congr; intro t ht
      simp only [isMatch_one, and_true]
      simp [M2, one, var_div n i t ht, var_mod n i t ht]
    rw [e]
    exact hr i (by simp [L1, hi, hb2])
  have cM2 : ∀ j < n, bh j = 2 → (p : Int) ∣ locL n M2 [] (fun s => var n s j) (n + k) (fun s => bp s = 2) - 1 := by
    intro j hj hb2
    have e : locL n M2 [] (fun s => var n s j) (n + k) (fun s => bp s = 2) = (L1.map (fun i => μ i j)).sum := by
      unfold locL
      rw [← rsum_filter]
      apply rsum_congr; intro t _
      simp only [isMatch_one, and_true]
      simp [M2, one, var_div n t j hj, var_mod n t j hj]
    rw [e]
    exact hc j (by simp [L2, hj, hb2])
  have dz : ∀ {A B : Int}, A = B → (p : Int) ∣ A - B := fun e => by rw [e, Int.sub_self]; exact Int.dvd_zero _
  -- decode a block edge
  have dec : ∀ (e : Nat) (cb : Nat), blk bp bh n e = cb → cb < 3 →
      ∃ i' j', j' < n ∧ e = var n i' j' ∧ bp i' = cb ∧ bh j' = cb := by
    intro e cb he hcb
    refine ⟨e / n, e % n, Nat.mod_lt _ hn0, (var_decode n e).symm, ?_⟩
    unfold blk at he; split at he
    · rename_i hh; exact ⟨he, hh ▸ he⟩
    · omega
  have B := bal_prod3 (n := n) (k := k) p bp bh (bpf_lt a a' x c c' y) (bpf_lt b b' h d d' h2)
    (one (rect n a a' b b')) (Yb n a a' x b b' h) (one (rect n c c' d d')) (Yb n c c' y d d' h2) M2 emp
    (SL_one _) (SL_Yb _ _ _ _ _ _ _) (SL_one _) (SL_Yb _ _ _ _ _ _ _) (SL_one _) SL_emp
    (hom_one _) (hom_Yb _ _ _ _ _ _ _) (hom_one _) (hom_Yb _ _ _ _ _ _ _) (hom_one _) hom_emp rfl
    (fun i _ _ => by rw [r_row lb lb' lh d1 D1 D2 E1 _ bh0]; exact Int.dvd_zero _)
    (fun j hj _ => by rw [r_col la la' lx hj lb lb' d1 d2 e1 D1 _ bp0]; exact Int.dvd_zero _)
    (fun i _ _ => by rw [r_row ld ld' lh2 g1 G1 G2 G3 _ bh1]; exact Int.dvd_zero _)
    (fun j hj _ => by rw [r_col lc lc' ly hj ld ld' g1 g2 g3 G1 _ bp1]; exact Int.dvd_zero _)
    (fun e _ he i _ hi hne => by
      obtain ⟨i', j', hj', rfl, hb1, hb2⟩ := dec e 0 he (by omega)
      rw [var_div n i' j' hj'] at hne
      exact dz (Yb_row lb lb' lh d1 d2 e1 D1 D2 E1 _ bh0 ((bp0 i').mp hb1) ((bh0 j').mp hb2) ((bp0 i).mp hi) hne))
    (fun e _ he j _ hj hne => by
      obtain ⟨i', j', hj', rfl, hb1, hb2⟩ := dec e 0 he (by omega)
      rw [var_mod n i' j' hj'] at hne
      exact dz (Yb_col la la' lx lb lb' lh d1 d2 e1 D1 D2 E1 _ bp0 ((bp0 i').mp hb1) ((bh0 j').mp hb2)
        ((bh0 j).mp hj) hne))
    (fun e _ he i _ hi hne => by
      obtain ⟨i', j', hj', rfl, hb1, hb2⟩ := dec e 1 he (by omega)
      rw [var_div n i' j' hj'] at hne
      exact dz (Yb_row ld ld' lh2 g1 g2 g3 G1 G2 G3 _ bh1 ((bp1 i').mp hb1) ((bh1 j').mp hb2) ((bp1 i).mp hi) hne))
    (fun e _ he j _ hj hne => by
      obtain ⟨i', j', hj', rfl, hb1, hb2⟩ := dec e 1 he (by omega)
      rw [var_mod n i' j' hj'] at hne
      exact dz (Yb_col lc lc' ly ld ld' lh2 g1 g2 g3 G1 G2 G3 _ bp1 ((bp1 i').mp hb1) ((bh1 j').mp hb2)
        ((bh1 j).mp hj) hne))
    rM2 cM2 2
  refine ⟨_, Bal_congr B ?_⟩
  intro g hg hl
  match g, hl with
  | [v, w], _ =>
    apply dz
    exact tprod_eq_prod n bp bh (bpf_lt a a' x c c' y) _ _
      (rect_zero bp bh lb lb' ((bp0 a).mpr (Or.inl rfl)) ((bp0 a').mpr (Or.inr (Or.inl rfl)))
        ((bh0 b).mpr (Or.inl rfl)) ((bh0 b').mpr (Or.inr (Or.inl rfl))))
      (rect_zero bp bh ld ld' ((bp1 c).mpr (Or.inl rfl)) ((bp1 c').mpr (Or.inr (Or.inl rfl)))
        ((bh1 d).mpr (Or.inl rfl)) ((bh1 d').mpr (Or.inr (Or.inl rfl)))) v w

/-- **L2.** For `n ≥ 7` and `p ∣ k`, every product `r ⊗ r'` of `2 × 2` rectangles on disjoint
pigeons and disjoint holes of `ontoFPHP n k` has a level-2 extension: some `Y` on 3-matchings has,
at every canonical 2-matching `g`, every free row and column sum `≡ (r ⊗ r')(g)` mod `p`. -/
theorem rect_ext {p n k : Nat} (hn : 7 ≤ n) (hk : (p : Int) ∣ k) :
    ∀ f, RectProd n k f → ∃ Y, Bal p n k Y f 2 := by
  rintro f ⟨a, a', c, c', b, b', d, d', hP, hH, hPl, hHl, rfl⟩
  obtain ⟨x, hx, hxn⟩ := fresh [a, a', c, c'] (n + k) (by simp; omega)
  obtain ⟨y, hy, hyn⟩ := fresh [a, a', c, c', x] (n + k) (by simp; omega)
  obtain ⟨h, hh, hhn⟩ := fresh [b, b', d, d'] n (by simp; omega)
  obtain ⟨h2, hh2, hh2n⟩ := fresh [b, b', d, d', h] n (by simp; omega)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hP hH hxn hyn hhn hh2n
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hPl hHl
  apply rect_ext_lab hn hk a a' x c c' y b b' h d d' h2
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, by simp⟩ <;>
      intro e <;> subst e <;> simp_all
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, by simp⟩ <;>
      intro e <;> subst e <;> simp_all
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hPl.1, hPl.2.1, hx, hPl.2.2.1, hPl.2.2.2, hy⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hHl.1, hHl.2.1, hh, hHl.2.2.1, hHl.2.2.2, hh2⟩

/-- With S2 (K19, stated in `Work.ExtLin`), every zero-link `f` has a level-2 extension. -/
theorem zero_link_ext {p n k : Nat} (hn : 7 ≤ n) (hk : (p : Int) ∣ k) (hS2 : S2 p n k)
    {f : List Nat → Int} (hf : Bal p n k f (fun _ => 0) 1) : ∃ Y, Bal p n k Y f 2 :=
  ext_zero_link hS2 (rect_ext hn hk) hf

#print axioms rect_ext
#print axioms zero_link_ext

end Programme.«20261026-1402-proof-complexity».RectExt
