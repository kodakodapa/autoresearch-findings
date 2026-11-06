import Programme.«20261026-1402-proof-complexity».SymDesign
import Programme.«20261027-1434-proof-complexity».RowColG

namespace Programme.«20261031-1904-proof-complexity».ExtPenultimate
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr)

open Programme.«20261026-1402-proof-complexity».SymDesign
open Programme.«20261027-1434-proof-complexity».RowColG
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt)

/-- The proposed input is supported on the first five pigeons. -/
def f (g : List Nat) : Int := if g.all (fun v => v / 5 < 5) then 1 else 0

theorem no_extension : ¬ ∃ y, Bal 2 5 8 y f 4 := by
  rintro ⟨y, hy⟩
  have h1 : CM 5 8 [18,12,6,0] := by unfold CM; decide
  have h2 : CM 5 8 [29,18,12,6] := by unfold CM; decide
  have a := (hy _ h1 rfl).1 5 (by decide) (by simp [pfree])
  have b := (hy _ h2 rfl).1 0 (by decide) (by simp [pfree])
  have ea : rowS 5 8 y [18,12,6,0] 5 = y [29,18,12,6,0] := by simp +decide [rowS, lineS, rsum, canon]
  have eb : rowS 5 8 y [29,18,12,6] 0 = y [29,18,12,6,0] := by simp +decide [rowS, lineS, rsum, canon]
  have fa : f [18,12,6,0] = 1 := by decide
  have fb : f [29,18,12,6] = 0 := by decide
  rw [ea,fa] at a
  rw [eb,fb] at b
  have h := Int.dvd_sub b a
  have hone : (2 : Int) ∣ 1 := by
    rw [show y [29,18,12,6,0] - 0 - (y [29,18,12,6,0] - 1) = 1 by omega] at h
    exact h
  exact Programme.«20261025-1627-proof-complexity».OntoExt2.not_dvd_one (by decide) hone

def F (n : Nat) (g : List Nat) : Int := if g.all (fun v => v / n < n) then 1 else 0

private theorem F_add {n k : Nat} {g : List Nat} (hg : CM n k g)
    {i j : Nat} (hi : i < n+k) (hj : j < n) :
    F n (canon ((n+k)*n) (var n i j :: g)) =
      if i < n ∧ (∀ v ∈ g, v / n < n) then 1 else 0 := by
  have hlt : ∀ x ∈ var n i j :: g, x < (n+k)*n := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact var_lt n k i j hi hj
    · exact CM_lt hg hx
  have he : (∀ v ∈ canon ((n+k)*n) (var n i j :: g), v / n < n) ↔
      i < n ∧ (∀ v ∈ g, v / n < n) := by
    simp only [mem_canon' hlt, List.forall_mem_cons,
      Programme.«20261025-0459-proof-complexity».OntoSubst.var_div n i j hj]
  simp only [F, List.all_eq_true, decide_eq_true_eq]
  simp only [he]

private theorem row_F {n k : Nat} (hn : 0 < n) {g : List Nat} (hg : CM n k g)
    {i : Nat} (hi : i < n+k) (hf : pfree n g i) :
    rowS n k (F n) g i =
      if i < n ∧ (∀ v ∈ g, v / n < n) then (n : Int) - g.length else 0 := by
  classical
  by_cases h : i < n ∧ (∀ v ∈ g, v / n < n)
  · rw [ite_eq_left h]
    have he : rowS n k (F n) g i = rowS n k (fun _ => 1) g i := by
      unfold rowS lineS
      apply rsum_congr
      intro j hj
      rw [F_add hg hi hj, ite_eq_left h]
    rw [he, rowS_const hn 1 hg hf, Int.mul_one]
  · rw [ite_eq_right h]
    unfold rowS lineS
    apply Programme.«20261025-0459-proof-complexity».OntoSubst.rsum_zero
    intro j hj
    rw [F_add hg hi hj, ite_eq_right h]
    simp

private theorem cutoff (n k : Nat) (a : Nat → Int) :
    rsum (n+k) (fun i => if i < n then a i else 0) = rsum n a := by
  induction k with
  | zero =>
    apply rsum_congr
    intro i hi
    rw [ite_eq_left (by omega)]
  | succ k ih =>
    rw [Nat.add_succ, rsum, ih, ite_eq_right (by omega), Int.add_zero]

private theorem col_F {n k : Nat} (_hn : 0 < n) {g : List Nat} (hg : CM n k g)
    {j : Nat} (hj : j < n) (hf : hfree n g j) :
    colS n k (F n) g j =
      if (∀ v ∈ g, v / n < n) then (n : Int) - g.length else 0 := by
  classical
  have hnot : ∀ i, var n i j ∉ g := fun i h => hf _ h
    (Programme.«20261025-0459-proof-complexity».OntoSubst.var_mod n i j hj)
  have he : colS n k (F n) g j = rsum (n+k) (fun i =>
      if i < n ∧ (∀ v ∈ g, v / n < n) then
        if pfree n g i then 1 else 0 else 0) := by
    unfold colS lineS
    apply rsum_congr
    intro i hi
    rw [F_add hg hi hj, match_cons hg.2 hj (hnot i), hfB_iff.mpr hf, Bool.and_true]
    by_cases hp : pfree n g i
    · rw [pfB_iff.mpr hp]
      simp [hp]
    · have hb : pfB n g i = false := by
        cases he : pfB n g i
        · rfl
        · exact False.elim (hp (pfB_iff.mp he))
      simp [hb, hp]
  rw [he]
  by_cases hs : ∀ v ∈ g, v / n < n
  · rw [ite_eq_left hs]
    have hh : rsum (n+k) (fun i =>
        if i < n ∧ (∀ v ∈ g, v / n < n) then
          if pfree n g i then 1 else 0 else 0) =
        rsum (n+k) (fun i => if i < n then (if pfree n g i then 1 else 0) else 0) := by
      apply rsum_congr
      intro i _
      by_cases hi : i < n
      · rw [ite_eq_left ⟨hi,hs⟩, ite_eq_left hi]
      · rw [ite_eq_right (fun h => hi h.1), ite_eq_right hi]
    rw [hh, cutoff]
    calc
      _ = rsum n (fun t => if ∀ v ∈ g, v / n ≠ t then 1 else 0) := by
        apply rsum_congr
        intro t ht
        by_cases h : pfree n g t
        · have hp : ∀ v ∈ g, v / n ≠ t := h
          rw [ite_eq_left h, ite_eq_left hp]
        · have hp : ¬ (∀ v ∈ g, v / n ≠ t) := h
          rw [ite_eq_right h, ite_eq_right hp]
      _ = _ := count_free (· / n) n g (match_nodup_div hg) hs
  · rw [ite_eq_right hs]
    apply Programme.«20261025-0459-proof-complexity».OntoSubst.rsum_zero
    intro i _
    rw [ite_eq_right (fun h => hs h.2)]

/-- The support indicator has zero link at the penultimate premise level. -/
theorem input_bal {n k : Nat} (hn : 2 ≤ n) :
    Bal 2 n k (F n) (fun _ => 0) (n-2) := by
  classical
  intro g hg hl
  refine ⟨?_, ?_⟩
  · intro i hi hf
    rw [row_F (by omega) hg hi hf, Int.sub_zero]
    split
    · have he : (n : Int) - g.length = 2 := by omega
      rw [he]
      exact Int.dvd_refl _
    · exact ⟨0, by simp⟩
  · intro j hj hf
    rw [col_F (by omega) hg hj hf, Int.sub_zero]
    split
    · have he : (n : Int) - g.length = 2 := by omega
      rw [he]
      exact Int.dvd_refl _
    · exact ⟨0, by simp⟩

theorem not_ext_pilot : ¬ EXT 2 5 8 4 := by
  intro h
  apply no_extension
  apply h f (fun _ => 0)
  intro e he
  have ee : e = 5-2 := by omega
  subst e
  exact input_bal (by decide)

/-- Geometric certificate: two faces of one full matching with opposite input values. -/
def OppositeFaces (n k : Nat) : Prop :=
  ∃ (a b q : List Nat) (i i' : Nat),
    CM n k a ∧ CM n k b ∧ a.length = n-1 ∧ b.length = n-1 ∧
    i < n+k ∧ i' < n+k ∧ pfree n a i ∧ pfree n b i' ∧
    F n a = 1 ∧ F n b = 0 ∧
    (∀ y : List Nat → Int, rowS n k y a i = y q) ∧
    (∀ y : List Nat → Int, rowS n k y b i' = y q)

theorem not_ext_of_faces {n k : Nat} (hn : 2 ≤ n)
    (hw : OppositeFaces n k) : ¬ EXT 2 n k (n-1) := by
  intro h
  obtain ⟨a,b,q,i,i',ha,hb,hal,hbl,hi,hi',hfi,hfi',hfa,hfb,hea,heb⟩ := hw
  obtain ⟨y,hy⟩ := h (F n) (fun _ => 0) (by
    intro e he
    have ee : e = n-2 := by omega
    subst e
    exact input_bal hn)
  have h1 := (hy a ha hal).1 i hi hfi
  have h2 := (hy b hb hbl).1 i' hi' hfi'
  rw [hea y, hfa] at h1
  rw [heb y, hfb] at h2
  have hh := Int.dvd_sub h2 h1
  rw [show y q - 0 - (y q - 1) = 1 by omega] at hh
  exact Programme.«20261025-1627-proof-complexity».OntoExt2.not_dvd_one (by decide) hh

end Programme.«20261031-1904-proof-complexity».ExtPenultimate
#print axioms Programme.«20261031-1904-proof-complexity».ExtPenultimate.no_extension

#print axioms Programme.«20261031-1904-proof-complexity».ExtPenultimate.not_ext_pilot
#print axioms Programme.«20261031-1904-proof-complexity».ExtPenultimate.input_bal

#print axioms Programme.«20261031-1904-proof-complexity».ExtPenultimate.not_ext_of_faces
