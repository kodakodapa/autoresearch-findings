import Programme.«20261026-1402-proof-complexity».ExtLemma

/-!
# Row and column sums of a link agree at every base matching

`row_col_g` generalises K157 (`RowCol.row_col`, base `[]`) to a canonical matching `g` of any
length `e`: if `Bal p n k f c (e + 1)`, then at `g` every free row sum of `c` is congruent mod `p`
to every free column sum of `c`. Proof: sum `f(g + x_{ij} + x_{i'j'})` over free `j ≠ j'`, free
`i' ≠ i` in both orders.

`link_bal`: if `e < n` (a free hole exists at every `e`-matching), then `Bal p n k f c (e + 1)`
implies `Bal p n k c h e` for an explicit `h`, the row sum of `c` at the first free pigeon. So the
link `c` of a level-`(e+1)` balanced function is itself level-`e` balanced: step (a) of th's route
to `EXT 2 7 8 3` (P27). No hypothesis on `p`, `n`, `k` beyond `e < n`.
-/

namespace Programme.«20261027-1434-proof-complexity».RowColG

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero var_div var_mod)
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261025-1627-proof-complexity».OntoExt2 (rsum_dvd rsum_pick var_lt)
open Programme.«20261025-1627-proof-complexity».OntoExt3 (rsum_sub')
open Programme.«20261026-1402-proof-complexity».ExtLemma

def pfB (n : Nat) (g : List Nat) (i : Nat) : Bool := g.all (fun v => v / n != i)
def hfB (n : Nat) (g : List Nat) (j : Nat) : Bool := g.all (fun v => v % n != j)

theorem pfB_iff {n : Nat} {g : List Nat} {i : Nat} : pfB n g i = true ↔ pfree n g i := by
  simp [pfB, pfree, List.all_eq_true]

theorem hfB_iff {n : Nat} {g : List Nat} {j : Nat} : hfB n g j = true ↔ hfree n g j := by
  simp [hfB, hfree, List.all_eq_true]

theorem pfB_cons (n a : Nat) (g : List Nat) (i : Nat) : pfB n (a :: g) i = ((a / n != i) && pfB n g i) := by
  simp [pfB]

theorem hfB_cons (n a : Nat) (g : List Nat) (j : Nat) : hfB n (a :: g) j = ((a % n != j) && hfB n g j) := by
  simp [hfB]

theorem cfl_self (n v : Nat) : cfl n v v = false := by simp [cfl]

theorem cfl_symm (n v w : Nat) : cfl n v w = cfl n w v := by
  unfold cfl
  cases h1 : (v == w) <;> cases h2 : (w == v) <;> simp_all [bne] <;> grind

theorem cfl_var {n i j w : Nat} (hj : j < n) (hne : var n i j ≠ w) :
    cfl n (var n i j) w = (i == w / n || j == w % n) := by
  unfold cfl; rw [var_div n i j hj, var_mod n i j hj]; simp [hne]

/-- Adding a free edge to a matching. -/
theorem match_cons {n : Nat} {g : List Nat} (hg : isMatch n g = true) {i j : Nat} (hj : j < n)
    (hv : var n i j ∉ g) : isMatch n (var n i j :: g) = (pfB n g i && hfB n g j) := by
  apply Bool.eq_iff_iff.mpr
  rw [isMatch_iff, Bool.and_eq_true, pfB_iff, hfB_iff]
  have hg' := (isMatch_iff n g).mp hg
  have hne : ∀ w ∈ g, var n i j ≠ w := fun w hw e => hv (e ▸ hw)
  constructor
  · intro H
    refine ⟨fun w hw hwi => ?_, fun w hw hwj => ?_⟩
    · have := H _ (List.mem_cons_self ..) w (List.mem_cons_of_mem _ hw)
      rw [cfl_var hj (hne w hw)] at this; simp [hwi] at this
    · have := H _ (List.mem_cons_self ..) w (List.mem_cons_of_mem _ hw)
      rw [cfl_var hj (hne w hw)] at this; simp [hwj] at this
  · intro ⟨hp, hh⟩
    have key : ∀ w ∈ g, cfl n (var n i j) w = false := by
      intro w hw
      rw [cfl_var hj (hne w hw)]
      have h1 := hp w hw; have h2 := hh w hw
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
      exact ⟨fun e => h1 e.symm, fun e => h2 e.symm⟩
    intro a ha b hb
    rcases List.mem_cons.mp ha with rfl | ha <;> rcases List.mem_cons.mp hb with rfl | hb
    · exact cfl_self _ _
    · exact key b hb
    · rw [cfl_symm]; exact key a ha
    · exact hg' a ha b hb

section
variable {n k : Nat}

theorem canon_cons_canon (N a : Nat) (l : List Nat) : canon N (a :: canon N l) = canon N (a :: l) :=
  canon_congr N _ _ (fun x hx => by
    simp only [List.mem_cons]; rw [mem_canon]; constructor
    · rintro (h | ⟨h, -⟩); exact Or.inl h; exact Or.inr h
    · rintro (h | h); exact Or.inl h; exact Or.inr ⟨h, hx⟩)

theorem canon_swap2 (N a b : Nat) (l : List Nat) : canon N (a :: b :: l) = canon N (b :: a :: l) :=
  canon_congr N _ _ (fun x _ => by
    simp only [List.mem_cons]; rw [← or_assoc, ← or_assoc, @or_comm (x = a)])

/-- `g + x_{ij}` for a free pigeon and a free hole is a canonical matching one longer. -/
theorem CM_add {g : List Nat} (hg : CM n k g) {i j : Nat} (hi : i < n + k) (hj : j < n)
    (hp : pfree n g i) (hh : hfree n g j) :
    CM n k (canon ((n + k) * n) (var n i j :: g)) ∧
      (canon ((n + k) * n) (var n i j :: g)).length = g.length + 1 ∧
      var n i j ∉ g ∧ isMatch n (var n i j :: g) = true := by
  have hv : var n i j ∉ g := fun h => hp _ h (var_div n i j hj)
  have hm : isMatch n (var n i j :: g) = true := by
    rw [match_cons hg.2 hj hv, pfB_iff.mpr hp, hfB_iff.mpr hh]; rfl
  have hlt : ∀ x ∈ var n i j :: g, x < (n + k) * n := by
    intro x hx; rcases List.mem_cons.mp hx with rfl | hx
    · exact var_lt n k i j hi hj
    · exact CM_lt hg hx
  have hnd : (var n i j :: g).Nodup := List.nodup_cons.mpr ⟨hv, CM_nodup hg⟩
  refine ⟨⟨canon_idem _, ?_⟩, ?_, hv, hm⟩
  · rw [isMatch_congr n _ _ (mem_canon' hlt)]; exact hm
  · rw [canon_len_eq hnd hlt]; rfl

theorem pfree_add {g : List Nat} {i j i' : Nat} (hj : j < n) (hp : pfree n g i') (hne : i ≠ i')
    (hlt : ∀ x ∈ var n i j :: g, x < (n + k) * n) :
    pfree n (canon ((n + k) * n) (var n i j :: g)) i' := by
  intro v hv
  rw [mem_canon' hlt] at hv
  rcases List.mem_cons.mp hv with rfl | hv
  · rw [var_div n i j hj]; exact hne
  · exact hp v hv

theorem hfree_add {g : List Nat} {i j j' : Nat} (hj : j < n) (hh : hfree n g j') (hne : j ≠ j')
    (hlt : ∀ x ∈ var n i j :: g, x < (n + k) * n) :
    hfree n (canon ((n + k) * n) (var n i j :: g)) j' := by
  intro v hv
  rw [mem_canon' hlt] at hv
  rcases List.mem_cons.mp hv with rfl | hv
  · rw [var_mod n i j hj]; exact hne
  · exact hh v hv

/-- **Row and column sums of the link agree** at every canonical matching `g`. -/
theorem row_col_g {p : Nat} {f c : List Nat → Int} {g : List Nat} (hg : CM n k g)
    (hb : Bal p n k f c (g.length + 1)) {i j' : Nat} (hi : i < n + k) (hj' : j' < n)
    (hpi : pfree n g i) (hhj : hfree n g j') :
    (p : Int) ∣ rowS n k c g i - colS n k c g j' := by
  have hglt : ∀ x ∈ g, x < (n + k) * n := fun x hx => CM_lt hg hx
  have hlt1 : ∀ a b, a < n + k → b < n → ∀ x ∈ var n a b :: g, x < (n + k) * n := by
    intro a b ha hb x hx; rcases List.mem_cons.mp hx with rfl | hx
    · exact var_lt n k a b ha hb
    · exact hglt x hx
  -- the common double sum
  let G : Nat → Nat → Int := fun i' j =>
    if pfB n g i' && hfB n g j && (i' != i) && (j != j') then
      f (canon ((n + k) * n) (var n i' j' :: var n i j :: g)) else 0
  -- membership of edges in `g`
  have hvg : ∀ a b, b < n → hfree n g b → var n a b ∉ g := fun a b hb hh h => hh _ h (var_mod n a b hb)
  -- column side
  have hT : rsum n (fun j => if hfB n g j && (j != j') then colS n k f (canon ((n + k) * n) (var n i j :: g)) j' else 0) =
      rsum n (fun j => rsum (n + k) (fun i' => G i' j)) := by
    apply rsum_congr; intro j hj
    by_cases e : (hfB n g j && (j != j')) = true
    · simp only [e, ite_true, colS, lineS]
      have hhj2 := hfB_iff.mp (Bool.and_eq_true_iff.mp e).1
      have hjj : j ≠ j' := by have := (Bool.and_eq_true_iff.mp e).2; simpa using this
      apply rsum_congr; intro i' hi'
      have hlt2 : ∀ x ∈ var n i' j' :: var n i j :: g, x < (n + k) * n := by
        intro x hx; rcases List.mem_cons.mp hx with rfl | hx
        · exact var_lt n k i' j' hi' hj'
        · exact hlt1 i j hi hj x hx
      rw [isMatch_congr n (var n i' j' :: canon ((n + k) * n) (var n i j :: g)) (var n i' j' :: var n i j :: g)
        (fun x => by simp only [List.mem_cons]; rw [mem_canon' (hlt1 i j hi hj)]; simp),
        canon_cons_canon]
      have hm1 := (CM_add hg hi hj hpi hhj2).2.2.2
      have hnot : var n i' j' ∉ var n i j :: g := by
        intro h; rcases List.mem_cons.mp h with h | h
        · have := congrArg (· % n) h; simp only [var_mod n _ _ hj', var_mod n _ _ hj] at this; exact hjj this.symm
        · exact hvg i' j' hj' hhj h
      rw [match_cons hm1 hj' hnot, pfB_cons, hfB_cons, var_div n i j hj, var_mod n i j hj]
      have h1 : hfB n g j' = true := hfB_iff.mpr hhj
      have h2 : (j != j') = true := by simpa using hjj
      have h3 : hfB n g j = true := hfB_iff.mpr hhj2
      simp only [G, h1, h2, h3, Bool.and_true, Bool.true_and]
      by_cases h4 : (i != i') = true
      · have h5 : (i' != i) = true := by simp at h4 ⊢; omega
        simp [h4, h5]
      · have h5 : (i' != i) = false := by simp at h4 ⊢; omega
        simp at h4; simp [h4, h5]
    · have e' : (hfB n g j && (j != j')) = false := by simpa using e
      simp only [e', Bool.false_eq_true, ite_false]
      symm; apply rsum_zero; intro i' _
      simp only [G]
      have : (pfB n g i' && hfB n g j && (i' != i) && (j != j')) = false := by
        cases h1 : hfB n g j <;> cases h2 : (j != j') <;> simp_all
      simp [this]
  -- row side
  have hT' : rsum (n + k) (fun i' => if pfB n g i' && (i' != i) then rowS n k f (canon ((n + k) * n) (var n i' j' :: g)) i else 0) =
      rsum (n + k) (fun i' => rsum n (fun j => G i' j)) := by
    apply rsum_congr; intro i' hi'
    by_cases e : (pfB n g i' && (i' != i)) = true
    · simp only [e, ite_true, rowS, lineS]
      have hpi2 := pfB_iff.mp (Bool.and_eq_true_iff.mp e).1
      have hii : i' ≠ i := by have := (Bool.and_eq_true_iff.mp e).2; simpa using this
      apply rsum_congr; intro j hj
      rw [isMatch_congr n (var n i j :: canon ((n + k) * n) (var n i' j' :: g)) (var n i j :: var n i' j' :: g)
        (fun x => by simp only [List.mem_cons]; rw [mem_canon' (hlt1 i' j' hi' hj')]; simp),
        canon_cons_canon, canon_swap2]
      have hm1 := (CM_add hg hi' hj' hpi2 hhj).2.2.2
      have hnot : var n i j ∉ var n i' j' :: g := by
        intro h; rcases List.mem_cons.mp h with h | h
        · have := congrArg (· / n) h; simp only [var_div n _ _ hj', var_div n _ _ hj] at this; exact hii this.symm
        · exact hpi _ h (var_div n i j hj)
      rw [match_cons hm1 hj hnot, pfB_cons, hfB_cons, var_div n i' j' hj', var_mod n i' j' hj']
      have h1 : pfB n g i = true := pfB_iff.mpr hpi
      have h2 : (i' != i) = true := by simpa using hii
      have h2' : (i != i') = true := by simp; omega
      have h3 : pfB n g i' = true := pfB_iff.mpr hpi2
      simp only [G, h1, h2, h2', h3, Bool.and_true, Bool.true_and]
      by_cases h4 : (j' != j) = true
      · have h5 : (j != j') = true := by simp at h4 ⊢; omega
        simp [h4, h5]
      · have h5 : (j != j') = false := by simp at h4 ⊢; omega
        simp at h4; simp [h4, h5]
    · have e' : (pfB n g i' && (i' != i)) = false := by simpa using e
      simp only [e', Bool.false_eq_true, ite_false]
      symm; apply rsum_zero; intro j _
      simp only [G]
      have : (pfB n g i' && hfB n g j && (i' != i) && (j != j')) = false := by
        cases h1 : pfB n g i' <;> cases h2 : (i' != i) <;> simp_all
      simp [this]
  have hswap := rsum_comm (n + k) n G
  -- the sums of `c`
  have hrow : rowS n k c g i = rsum n (fun j => if hfB n g j && (j != j') then c (canon ((n + k) * n) (var n i j :: g)) else 0) +
      c (canon ((n + k) * n) (var n i j' :: g)) := by
    have h1 : rowS n k c g i = rsum n (fun j => (if hfB n g j && (j != j') then c (canon ((n + k) * n) (var n i j :: g)) else 0) +
        (if j = j' then c (canon ((n + k) * n) (var n i j :: g)) else 0)) := by
      unfold rowS lineS; apply rsum_congr; intro j hj
      by_cases hh : hfB n g j = true
      · rw [match_cons hg.2 hj (hvg i j hj (hfB_iff.mp hh)), pfB_iff.mpr hpi, hh]
        by_cases e : j = j' <;> simp [e]
      · have hh' : hfB n g j = false := by simpa using hh
        have hjne : j ≠ j' := fun e => by subst e; rw [hfB_iff.mpr hhj] at hh'; exact Bool.noConfusion hh'
        have hm : isMatch n (var n i j :: g) = false := by
          by_cases hin : var n i j ∈ g
          · exact absurd (var_div n i j hj) (hpi _ hin)
          · rw [match_cons hg.2 hj hin, hh']; simp
        simp [hm, hh', hjne]
    rw [h1, rsum_add, rsum_pick n j' (fun j => c (canon ((n + k) * n) (var n i j :: g)))]; simp [hj']
  have hcol : colS n k c g j' = rsum (n + k) (fun i' => if pfB n g i' && (i' != i) then c (canon ((n + k) * n) (var n i' j' :: g)) else 0) +
      c (canon ((n + k) * n) (var n i j' :: g)) := by
    have h1 : colS n k c g j' = rsum (n + k) (fun i' => (if pfB n g i' && (i' != i) then c (canon ((n + k) * n) (var n i' j' :: g)) else 0) +
        (if i' = i then c (canon ((n + k) * n) (var n i' j' :: g)) else 0)) := by
      unfold colS lineS; apply rsum_congr; intro i' hi'
      rw [match_cons hg.2 hj' (hvg i' j' hj' hhj), hfB_iff.mpr hhj, Bool.and_true]
      by_cases hp : pfB n g i' = true
      · by_cases e : i' = i
        · subst e; simp [hp]
        · simp [e, hp]
      · have hp' : pfB n g i' = false := by simpa using hp
        have hine : i' ≠ i := fun e => by subst e; rw [pfB_iff.mpr hpi] at hp'; exact Bool.noConfusion hp'
        simp [hp', hine]
    rw [h1, rsum_add, rsum_pick (n + k) i (fun i' => c (canon ((n + k) * n) (var n i' j' :: g)))]; simp [hi]
  -- congruences from `Bal`
  have dT : (p : Int) ∣ rsum n (fun j => if hfB n g j && (j != j') then colS n k f (canon ((n + k) * n) (var n i j :: g)) j' else 0) -
      rsum n (fun j => if hfB n g j && (j != j') then c (canon ((n + k) * n) (var n i j :: g)) else 0) := by
    rw [← rsum_sub']; apply rsum_dvd; intro j hj
    by_cases e : (hfB n g j && (j != j')) = true
    · simp only [e, ite_true]
      have hhj2 := hfB_iff.mp (Bool.and_eq_true_iff.mp e).1
      have hjj : j ≠ j' := by have := (Bool.and_eq_true_iff.mp e).2; simpa using this
      obtain ⟨hcm, hlen, -, -⟩ := CM_add hg hi hj hpi hhj2
      exact (hb _ hcm hlen).2 j' hj' (hfree_add hj hhj hjj (hlt1 i j hi hj))
    · have e' : (hfB n g j && (j != j')) = false := by simpa using e
      simp [e']
  have dT' : (p : Int) ∣ rsum (n + k) (fun i' => if pfB n g i' && (i' != i) then rowS n k f (canon ((n + k) * n) (var n i' j' :: g)) i else 0) -
      rsum (n + k) (fun i' => if pfB n g i' && (i' != i) then c (canon ((n + k) * n) (var n i' j' :: g)) else 0) := by
    rw [← rsum_sub']; apply rsum_dvd; intro i' hi'
    by_cases e : (pfB n g i' && (i' != i)) = true
    · simp only [e, ite_true]
      have hpi2 := pfB_iff.mp (Bool.and_eq_true_iff.mp e).1
      have hii : i' ≠ i := by have := (Bool.and_eq_true_iff.mp e).2; simpa using this
      obtain ⟨hcm, hlen, -, -⟩ := CM_add hg hi' hj' hpi2 hhj
      exact (hb _ hcm hlen).1 i hi (pfree_add hj' hpi hii (hlt1 i' j' hi' hj'))
    · have e' : (pfB n g i' && (i' != i)) = false := by simpa using e
      simp [e']
  rw [hT] at dT; rw [hT', hswap] at dT'
  have := Int.dvd_sub dT' dT
  rw [hrow, hcol]
  have e : ∀ a b x y : Int, x - b - (x - a) = a + y - (b + y) := by intros; omega
  rw [← e]; exact this

/-- First free pigeon of `g` (or `0`). -/
def fp (n k : Nat) (g : List Nat) : Nat := ((List.range (n + k)).find? (fun i => pfB n g i)).getD 0

/-- Common value of the row sums of `c` at `g`. -/
def lk (n k : Nat) (c : List Nat → Int) (g : List Nat) : Int := rowS n k c g (fp n k g)

theorem exists_free_hole {g : List Nat} (hl : g.length < n) : ∃ j < n, hfree n g j := by
  apply Classical.byContradiction; intro H
  have hall : ∀ j < n, ∃ v ∈ g, v % n = j := by
    intro j hj
    apply Classical.byContradiction; intro h'
    exact H ⟨j, hj, fun v hv e => h' ⟨v, hv, e⟩⟩
  -- every hole is used, so `g` has at least `n` members
  have : n ≤ g.length := by
    have hsub : (List.range n) ⊆ g.map (· % n) := by
      intro j hj; obtain ⟨v, hv, e⟩ := hall j (List.mem_range.mp hj); exact List.mem_map.mpr ⟨v, hv, e⟩
    have := nodup_len _ _ List.nodup_range hsub
    simpa using this
  omega

theorem fp_free {g : List Nat} (hl : g.length < n) : fp n k g < n + k ∧ pfree n g (fp n k g) := by
  -- some pigeon is free, since otherwise `g` has at least `n + k > g.length` members
  have hex : ∃ i < n + k, pfree n g i := by
    apply Classical.byContradiction; intro H
    have hall : ∀ i < n + k, ∃ v ∈ g, v / n = i := by
      intro i hi
      apply Classical.byContradiction; intro h'
      exact H ⟨i, hi, fun v hv e => h' ⟨v, hv, e⟩⟩
    have hsub : (List.range (n + k)) ⊆ g.map (· / n) := by
      intro i hi; obtain ⟨v, hv, e⟩ := hall i (List.mem_range.mp hi); exact List.mem_map.mpr ⟨v, hv, e⟩
    have := nodup_len _ _ List.nodup_range hsub
    simp at this; omega
  obtain ⟨i, hi, hfi⟩ := hex
  have hsome : ((List.range (n + k)).find? (fun i => pfB n g i)).isSome := by
    rw [List.find?_isSome]; exact ⟨i, List.mem_range.mpr hi, pfB_iff.mpr hfi⟩
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hsome
  have h1 := List.mem_of_find?_eq_some ha
  have h2 := List.find?_some ha
  unfold fp; rw [ha]
  exact ⟨List.mem_range.mp h1, pfB_iff.mp h2⟩

/-- **The link of a level-`(e+1)` balanced function is level-`e` balanced.** -/
theorem link_bal {p e : Nat} {f c : List Nat → Int} (he : e < n) (hb : Bal p n k f c (e + 1)) :
    Bal p n k c (lk n k c) e := by
  intro g hg hl
  subst hl
  obtain ⟨hfp, hfpf⟩ := fp_free (k := k) he
  obtain ⟨j0, hj0, hj0f⟩ := exists_free_hole he
  refine ⟨fun i hi hpi => ?_, fun j hj hhj => ?_⟩
  · have h1 := row_col_g hg hb hi hj0 hpi hj0f
    have h2 := row_col_g hg hb hfp hj0 hfpf hj0f
    unfold lk
    have := Int.dvd_sub h1 h2
    rw [show ∀ a b c : Int, a - c - (b - c) = a - b by intros; omega] at this; exact this
  · have h2 := row_col_g hg hb hfp hj hfpf hhj
    unfold lk
    have := Int.dvd_neg.mpr h2
    rw [show ∀ a b : Int, -(a - b) = b - a by intros; omega] at this; exact this

end

end Programme.«20261027-1434-proof-complexity».RowColG

#print axioms Programme.«20261027-1434-proof-complexity».RowColG.row_col_g
#print axioms Programme.«20261027-1434-proof-complexity».RowColG.link_bal
