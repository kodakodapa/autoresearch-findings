import Programme.«20261027-0607-proof-complexity».SJ
import Programme.«20261026-1402-proof-complexity».Win

/-!
# The flag lemma: links of links agree

If `Bal p n k f c (e + 1)` (at every canonical `(e+1)`-matching, all free row and column sums of
`f` are `≡ c`), then at every canonical `e`-matching `g`, every free row sum of `c` is congruent to
every free column sum of `c` mod `p` (`row_col_gen`; `RowCol.row_col` is the case `g = []`).
Proof: both differ from `c(g + x_{ib})` by the same double sum of `f` over `g + x_{i'b} + x_{ib'}`.
Consequently `c` is balanced one level down against some `c'` (`flag`).
-/

namespace Programme.«20261027-0607-proof-complexity».Flag

open Programme.«20261025-0459-proof-complexity».OntoFPHP (rsum var rsum_comm)
open Programme.«20261025-1627-proof-complexity».MomGen (canon mem_canon canon_congr canon_nodup nodup_len)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt var_inj rsum_skip)
open Programme.«20261025-0459-proof-complexity».OntoSubst (var_div var_mod)
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261027-0607-proof-complexity».LemK (rsum_congr rsum_sub rsum_dvd_congr)
open Programme.«20261027-0607-proof-complexity».SJ (isMatch_cons)

variable {p n k : Nat}

theorem canon_cons_canon (N x : Nat) (l : List Nat) : canon N (x :: canon N l) = canon N (x :: l) :=
  canon_congr N _ _ (fun y hy => by simp [mem_canon, hy])

theorem isMatch_cons_canon (n N x : Nat) (l : List Nat) (hl : ∀ y ∈ l, y < N) :
    isMatch n (x :: canon N l) = isMatch n (x :: l) :=
  isMatch_congr n _ _ (fun y => by simp [mem_canon' hl])

theorem mem_swap (x y z : Nat) (l : List Nat) : z ∈ x :: y :: l ↔ z ∈ y :: x :: l := by
  simp only [List.mem_cons]
  constructor
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

theorem isMatch_swap (n x y : Nat) (l : List Nat) : isMatch n (x :: y :: l) = isMatch n (y :: x :: l) :=
  isMatch_congr n _ _ (fun z => mem_swap x y z l)

theorem canon_swap (N x y : Nat) (l : List Nat) : canon N (x :: y :: l) = canon N (y :: x :: l) :=
  canon_congr N _ _ (fun z _ => mem_swap x y z l)

theorem cfl_var_pig (n i b b' : Nat) (hb : b < n) (hb' : b' < n) (h : b ≠ b') : cfl n (var n i b) (var n i b') = true :=
  pig_cfl b hb b' hb' h

theorem cfl_var_hole (n k b i i' : Nat) (hb : b < n) (hi : i < n + k) (hi' : i' < n + k) (h : i ≠ i') :
    cfl n (var n i b) (var n i' b) = true :=
  hole_cfl (k := k) hb i hi i' hi' h

/-- `canon (x :: g)` of a matching extension is a canonical matching one longer. -/
theorem CM_cons {g : List Nat} (hg : CM n k g) {x : Nat} (hx : x < (n + k) * n) (hxg : x ∉ g)
    (hm : isMatch n (x :: g) = true) :
    CM n k (canon ((n + k) * n) (x :: g)) ∧ (canon ((n + k) * n) (x :: g)).length = g.length + 1 := by
  have hlt : ∀ y ∈ x :: g, y < (n + k) * n := by
    intro y hy; simp at hy; rcases hy with rfl | hy
    · exact hx
    · exact CM_lt hg hy
  refine ⟨⟨canon_idem _, ?_⟩, ?_⟩
  · rw [isMatch_congr n _ (x :: g) (fun y => mem_canon' hlt y)]; exact hm
  · rw [canon_len_eq (List.nodup_cons.mpr ⟨hxg, CM_nodup hg⟩) hlt]; rfl

/-- **Row and column sums of `c` agree** at every canonical `e`-matching. -/
theorem row_col_gen {f c : List Nat → Int} {e : Nat} (hb : Bal p n k f c (e + 1)) {g : List Nat}
    (hg : CM n k g) (hgl : g.length = e) {i : Nat} (hi : i < n + k) (hpi : pfree n g i) {b : Nat}
    (hbn : b < n) (hhb : hfree n g b) : (p : Int) ∣ rowS n k c g i - colS n k c g b := by
  have hN : ∀ a t, a < n + k → t < n → var n a t < ((n + k) * n) := fun a t ha ht => var_lt n k a t ha ht
  have hgN : ∀ y ∈ g, y < ((n + k) * n) := fun y hy => CM_lt hg hy
  let G : Nat → Nat → Int := fun i' b' =>
    if i' = i ∨ b' = b then 0 else
      if isMatch n (var n i' b :: var n i b' :: g) then f (canon ((n + k) * n) (var n i' b :: var n i b' :: g)) else 0
  -- the row side
  have hrow : (p : Int) ∣ rsum n (fun b' => if b' = b then 0 else
      (if isMatch n (var n i b' :: g) then c (canon ((n + k) * n) (var n i b' :: g)) else 0)) -
      rsum n (fun b' => rsum (n + k) (fun i' => G i' b')) := by
    apply rsum_dvd_congr; intro b' hb'
    by_cases e1 : b' = b
    · subst e1; simp only [if_true]
      rw [Programme.«20261027-0607-proof-complexity».LemK.rsum_zero _ _ (fun t _ => by simp [G])]; exact ⟨0, by omega⟩
    · rw [if_neg e1]
      by_cases hm : isMatch n (var n i b' :: g) = true
      · rw [if_pos hm]
        have hxg : var n i b' ∉ g := notin_of_pfree hpi b' hb'
        obtain ⟨hcm, hl⟩ := CM_cons hg (hN i b' hi hb') hxg hm
        have hfree' : hfree n (canon ((n + k) * n) (var n i b' :: g)) b := by
          intro v hv
          have hlt : ∀ y ∈ var n i b' :: g, y < ((n + k) * n) := by
            intro y hy; simp at hy; rcases hy with rfl | hy
            · exact hN i b' hi hb'
            · exact hgN y hy
          rw [mem_canon' hlt] at hv; simp at hv
          rcases hv with rfl | hv
          · rw [var_mod n i b' hb']; exact e1
          · exact hhb v hv
        have hB := (hb _ hcm (by rw [hl, hgl])).2 b hbn hfree'
        refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mpr (Int.dvd_neg.mpr hB)
        rw [show ∀ x y z : Int, x - z - -(y - x) = y - z by intros; omega]
        unfold colS lineS
        apply rsum_dvd_congr; intro i' hi'
        have hlt2 : ∀ y ∈ var n i b' :: g, y < (n + k) * n := by
          intro y hy; simp at hy; rcases hy with rfl | hy
          · exact hN i b' hi hb'
          · exact hgN y hy
        rw [isMatch_cons_canon n ((n + k) * n) _ _ hlt2, canon_cons_canon]
        by_cases e2 : i' = i
        · subst e2
          have : isMatch n (var n i' b :: var n i' b' :: g) = false := by
            cases h : isMatch n (var n i' b :: var n i' b' :: g)
            · rfl
            · rw [isMatch_cons] at h
              have := h.2 (var n i' b') (by simp)
              rw [cfl_var_pig n i' b b' hbn hb' (Ne.symm e1)] at this; cases this
          simp [G, this]
        · simp only [G, e2, e1, or_self, if_false, Int.sub_self]; exact Int.dvd_zero _
      · rw [if_neg hm]
        rw [Programme.«20261027-0607-proof-complexity».LemK.rsum_zero _ _ (fun i' _ => by
          simp only [G]
          split
          · rfl
          · rw [if_neg]; intro h'; apply hm; exact (isMatch_cons n _ _).mp h' |>.1)]
        exact ⟨0, by omega⟩
  -- the column side
  have hcol : (p : Int) ∣ rsum (n + k) (fun i' => if i' = i then 0 else
      (if isMatch n (var n i' b :: g) then c (canon ((n + k) * n) (var n i' b :: g)) else 0)) -
      rsum (n + k) (fun i' => rsum n (fun b' => G i' b')) := by
    apply rsum_dvd_congr; intro i' hi'
    by_cases e1 : i' = i
    · subst e1; simp only [if_true]
      rw [Programme.«20261027-0607-proof-complexity».LemK.rsum_zero _ _ (fun t _ => by simp [G])]; exact ⟨0, by omega⟩
    · rw [if_neg e1]
      by_cases hm : isMatch n (var n i' b :: g) = true
      · rw [if_pos hm]
        have hxg : var n i' b ∉ g := notin_of_hfree hhb i' hbn
        obtain ⟨hcm, hl⟩ := CM_cons hg (hN i' b hi' hbn) hxg hm
        have hpfree' : pfree n (canon ((n + k) * n) (var n i' b :: g)) i := by
          intro v hv
          have hlt : ∀ y ∈ var n i' b :: g, y < ((n + k) * n) := by
            intro y hy; simp at hy; rcases hy with rfl | hy
            · exact hN i' b hi' hbn
            · exact hgN y hy
          rw [mem_canon' hlt] at hv; simp at hv
          rcases hv with rfl | hv
          · rw [var_div n i' b hbn]; exact e1
          · exact hpi v hv
        have hB := (hb _ hcm (by rw [hl, hgl])).1 i hi hpfree'
        refine (Int.dvd_iff_dvd_of_dvd_sub ?_).mpr (Int.dvd_neg.mpr hB)
        rw [show ∀ x y z : Int, x - z - -(y - x) = y - z by intros; omega]
        unfold rowS lineS
        apply rsum_dvd_congr; intro b' hb'
        have hlt2 : ∀ y ∈ var n i' b :: g, y < (n + k) * n := by
          intro y hy; simp at hy; rcases hy with rfl | hy
          · exact hN i' b hi' hbn
          · exact hgN y hy
        rw [isMatch_cons_canon n ((n + k) * n) _ _ hlt2, canon_cons_canon, isMatch_swap, canon_swap]
        by_cases e2 : b' = b
        · subst e2
          have : isMatch n (var n i' b' :: var n i b' :: g) = false := by
            cases h : isMatch n (var n i' b' :: var n i b' :: g)
            · rfl
            · rw [isMatch_cons] at h
              have := h.2 (var n i b') (by simp)
              rw [cfl_var_hole n k b' i' i hbn hi' hi e1] at this; cases this
          simp [G, this]
        · simp only [G, e2, e1, or_self, if_false, Int.sub_self]; exact Int.dvd_zero _
      · rw [if_neg hm]
        rw [Programme.«20261027-0607-proof-complexity».LemK.rsum_zero _ _ (fun b' _ => by
          simp only [G]
          split
          · rfl
          · rw [if_neg]; intro h'; apply hm
            rw [isMatch_swap] at h'
            exact (isMatch_cons n _ _).mp h' |>.1)]
        exact ⟨0, by omega⟩
  -- assemble
  have hm0 : isMatch n (var n i b :: g) = true := by
    rw [isMatch_cons]; refine ⟨hg.2, fun y hy => ?_⟩
    have hy' := hgN y hy
    unfold cfl
    have hyn : y % n < n := Nat.mod_lt _ (by omega)
    rw [var_div n i b hbn, var_mod n i b hbn]
    have h1 : i ≠ y / n := fun e => hpi y hy e.symm
    have h2 : b ≠ y % n := fun e => hhb y hy e.symm
    simp [h1, h2]
  have er : rowS n k c g i = rsum n (fun b' => if b' = b then 0 else
      (if isMatch n (var n i b' :: g) then c (canon ((n + k) * n) (var n i b' :: g)) else 0)) + c (canon ((n + k) * n) (var n i b :: g)) := by
    unfold rowS lineS
    rw [rsum_skip n b hbn]; simp only [hm0, if_true]; omega
  have ec : colS n k c g b = rsum (n + k) (fun i' => if i' = i then 0 else
      (if isMatch n (var n i' b :: g) then c (canon ((n + k) * n) (var n i' b :: g)) else 0)) + c (canon ((n + k) * n) (var n i b :: g)) := by
    unfold colS lineS
    rw [rsum_skip (n + k) i hi]; simp only [hm0, if_true]; omega
  rw [er, ec]
  have := Int.dvd_sub hrow hcol
  rw [rsum_comm (n + k) n G] at this
  rw [show ∀ a b x : Int, a - x - (b - x) = a - b by intros; omega] at this
  rw [show ∀ a b z : Int, a + z - (b + z) = a - b by intros; omega]
  exact this

/-- With a free hole, some pigeon is free. -/
theorem exists_pfree {g : List Nat} (hg : CM n k g) {b : Nat} (hbn : b < n) (hhb : hfree n g b) :
    ∃ i, i < n + k ∧ pfree n g i := by
  apply Classical.byContradiction; intro hno
  have hall : ∀ i < n + k, ∃ v ∈ g, v / n = i := by
    intro i hi; apply Classical.byContradiction; intro h
    exact hno ⟨i, hi, fun v hv e => h ⟨v, hv, e⟩⟩
  have h1 : n + k ≤ g.length := by
    have := nodup_len (List.range (n + k)) (g.map (· / n)) List.nodup_range (fun i hi => by
      obtain ⟨v, hv, e⟩ := hall i (List.mem_range.mp hi); exact List.mem_map.mpr ⟨v, hv, e⟩)
    simpa using this
  have h2 : g.length + 1 ≤ n := by
    have hnd := Programme.«20261026-1402-proof-complexity».Win.nodup_mod (n := n) (CM_nodup hg) hg.2
    have := nodup_len (b :: g.map (· % n)) (List.range n)
      (List.nodup_cons.mpr ⟨fun hm => by obtain ⟨v, hv, e⟩ := List.mem_map.mp hm; exact hhb v hv e, hnd⟩)
      (fun x hx => by
        simp at hx; rcases hx with rfl | ⟨v, _, rfl⟩
        · exact List.mem_range.mpr hbn
        · exact List.mem_range.mpr (Nat.mod_lt _ (by omega)))
    simpa using this
  omega

/-- No free hole: every row sum vanishes. -/
theorem rowS_nohole {c : List Nat → Int} {g : List Nat} {i : Nat} (hpi : pfree n g i)
    (h : ∀ b < n, ¬ hfree n g b) : rowS n k c g i = 0 := by
  unfold rowS lineS
  apply Programme.«20261027-0607-proof-complexity».LemK.rsum_zero; intro b hb
  have : ∃ v ∈ g, v % n = b := by
    apply Classical.byContradiction; intro h'
    exact h b hb (fun v hv e => h' ⟨v, hv, e⟩)
  obtain ⟨v, hv, e⟩ := this
  have hm : isMatch n (var n i b :: g) = false := by
    cases hc : isMatch n (var n i b :: g)
    · rfl
    · rw [isMatch_cons] at hc
      have := hc.2 v hv
      unfold cfl at this
      rw [var_div n i b hb, var_mod n i b hb, e] at this
      have hne : var n i b ≠ v := fun e' => hpi v hv (by rw [← e', var_div n i b hb])
      simp [hne] at this
  rw [hm]; rfl

/-- **Flag lemma.** If `f` is balanced against `c` at level `e + 1`, then `c` is balanced against
some `c'` at level `e`. -/
theorem flag {f c : List Nat → Int} {e : Nat} (hb : Bal p n k f c (e + 1)) : ∃ c', Bal p n k c c' e := by
  classical
  let c' : List Nat → Int := fun g => if h : ∃ b, b < n ∧ hfree n g b then colS n k c g (Classical.choose h) else 0
  refine ⟨c', fun g hg hgl => ⟨fun i hi hpi => ?_, fun b hbn hhb => ?_⟩⟩
  · by_cases h : ∃ b, b < n ∧ hfree n g b
    · have hs := Classical.choose_spec h
      have e1 : c' g = colS n k c g (Classical.choose h) := by simp only [c', dif_pos h]
      rw [e1]; exact row_col_gen hb hg hgl hi hpi hs.1 hs.2
    · have e1 : c' g = 0 := by simp only [c', dif_neg h]
      rw [e1, rowS_nohole hpi (fun b hb hf => h ⟨b, hb, hf⟩)]; exact Int.dvd_zero _
  · have h : ∃ b, b < n ∧ hfree n g b := ⟨b, hbn, hhb⟩
    have hs := Classical.choose_spec h
    have e1 : c' g = colS n k c g (Classical.choose h) := by simp only [c', dif_pos h]
    rw [e1]
    obtain ⟨i, hi, hpi⟩ := exists_pfree hg hbn hhb
    have a1 := row_col_gen hb hg hgl hi hpi hbn hhb
    have a2 := row_col_gen hb hg hgl hi hpi hs.1 hs.2
    have := Int.dvd_sub a2 a1
    rwa [show ∀ x y z : Int, x - z - (x - y) = y - z by intros; omega] at this

end Programme.«20261027-0607-proof-complexity».Flag

#print axioms Programme.«20261027-0607-proof-complexity».Flag.flag
#print axioms Programme.«20261027-0607-proof-complexity».Flag.row_col_gen
