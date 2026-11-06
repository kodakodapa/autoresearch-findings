import Programme.«20261027-0607-proof-complexity».Lift78

/-!
# `Bal 2 7 8 T0 T0 e` for `e ≤ 2`, structurally from K167

`Lift78.T0` is K167's design `BDes.B` on `ontoFPHP 4 8` lifted to `ontoFPHP 7 8` by the fixed edges
`12 → 4, 13 → 5, 14 → 6`. Free row and column sums of `T0` at a canonical matching `g` of `ontoFPHP 7 8`
are either the matching sums of `B` at the image `H g` (block rows / columns), a single term equal to
`T0 g` (fixed rows / columns), or zero (when `g` uses an edge outside the lift). So `BDesMain.b_design`
gives `Bal 2 7 8 T0 T0 e` for every `e ≤ 2`, with no kernel enumeration.
-/

namespace Programme.«20261027-0607-proof-complexity».LiftBal

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (rsum_pick)
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261027-0607-proof-complexity».Lift78

abbrev B := Programme.«20261026-1402-proof-complexity».BDes.B

def H (L : List Nat) : List Nat := canon 48 (L.filterMap emb)

theorem rsum_add (a : Nat) (f : Nat → Int) : ∀ b, rsum (a + b) f = rsum a f + rsum b (fun t => f (a + t))
  | 0 => by simp [rsum]
  | b + 1 => by rw [← Nat.add_assoc]; simp only [rsum]; rw [rsum_add a f b]; omega

theorem isMatch_iff (n : Nat) (l : List Nat) :
    isMatch n l = true ↔ ∀ v ∈ l, ∀ w ∈ l, cfl n v w = false := by
  simp [isMatch, List.all_eq_true]

theorem isMatch_congr (n : Nat) {l l' : List Nat} (h : ∀ x, x ∈ l ↔ x ∈ l') :
    isMatch n l = isMatch n l' := by
  apply Bool.eq_iff_iff.2; rw [isMatch_iff, isMatch_iff]; simp only [h]

theorem okV_iff (v : Nat) : okV v = true ↔ (v / 7 < 12 ∧ v % 7 < 4) ∨ (12 ≤ v / 7 ∧ v % 7 + 8 = v / 7) := by
  simp [okV]

theorem mem_fm {L : List Nat} (hL : L.all okV = true) (z : Nat) :
    z ∈ L.filterMap emb ↔ ∃ w ∈ L, w / 7 < 12 ∧ w % 7 < 4 ∧ z = w / 7 * 4 + w % 7 := by
  simp only [List.mem_filterMap, emb]
  constructor
  · rintro ⟨w, hw, he⟩
    have ho := (okV_iff w).1 (List.all_eq_true.1 hL w hw)
    by_cases h : w / 7 < 12
    · simp [h] at he; exact ⟨w, hw, h, by omega, he.symm⟩
    · simp [h] at he
  · rintro ⟨w, hw, h1, _, rfl⟩; exact ⟨w, hw, by simp [h1]⟩

theorem mem_H {L : List Nat} (hL : L.all okV = true) (z : Nat) :
    z ∈ H L ↔ ∃ w ∈ L, w / 7 < 12 ∧ w % 7 < 4 ∧ z = w / 7 * 4 + w % 7 := by
  rw [H, mem_canon, mem_fm hL]
  constructor
  · exact fun h => h.1
  · rintro ⟨w, hw, h1, h2, rfl⟩; exact ⟨⟨w, hw, h1, h2, rfl⟩, by omega⟩

theorem cfl_iff (n v w : Nat) : cfl n v w = false ↔ v = w ∨ (v / n ≠ w / n ∧ v % n ≠ w % n) := by
  simp only [cfl]
  by_cases h : v = w <;> by_cases h1 : v / n = w / n <;> by_cases h2 : v % n = w % n <;> simp [h, h1, h2]

theorem rsum_split (m a b : Nat) (f : Nat → Int) (h : m = a + b) :
    rsum m f = rsum a f + rsum b (fun t => f (a + t)) := by subst h; exact rsum_add a f b

theorem okV_false {v : Nat} (h : ¬((v / 7 < 12 ∧ v % 7 < 4) ∨ (12 ≤ v / 7 ∧ v % 7 + 8 = v / 7))) :
    okV v = false := Bool.eq_false_iff.2 (fun h' => h ((okV_iff v).1 h'))

theorem T0_of_bad {L : List Nat} {w : Nat} (hw : w ∈ L) (h : okV w = false) : T0 L = 0 := by
  have : L.all okV = false := Bool.eq_false_iff.2 (fun ha => by rw [List.all_eq_true.1 ha w hw] at h; cases h)
  simp [T0, this]

/-- On lists inside the lift, being a matching is the same at `n = 7` and for the image at `n = 4`. -/
theorem match_H {L : List Nat} (hL : L.all okV = true) : isMatch 7 L = isMatch 4 (H L) := by
  apply Bool.eq_iff_iff.2
  rw [isMatch_iff, isMatch_iff]
  constructor
  · intro h v' hv' w' hw'
    obtain ⟨v, hv, hv1, hv2, rfl⟩ := (mem_H hL v').1 hv'
    obtain ⟨w, hw, hw1, hw2, rfl⟩ := (mem_H hL w').1 hw'
    have := (cfl_iff 7 v w).1 (h v hv w hw)
    apply (cfl_iff 4 _ _).2; omega
  · intro h v hv w hw
    have ov := (okV_iff v).1 (List.all_eq_true.1 hL v hv)
    have ow := (okV_iff w).1 (List.all_eq_true.1 hL w hw)
    apply (cfl_iff 7 v w).2
    by_cases hb : v / 7 < 12 ∧ w / 7 < 12
    · have := (cfl_iff 4 _ _).1 (h _ ((mem_H hL _).2 ⟨v, hv, hb.1, by omega, rfl⟩)
        _ ((mem_H hL _).2 ⟨w, hw, hb.2, by omega, rfl⟩))
      omega
    · omega

theorem T0_canon {L : List Nat} (hL : ∀ v ∈ L, v < 105) :
    T0 (canon 105 L) = if L.all okV then B (H L) else 0 := by
  have ha : (canon 105 L).all okV = L.all okV := by
    apply Bool.eq_iff_iff.2; simp only [List.all_eq_true, mem_canon' hL]
  have hf : canon 48 ((canon 105 L).filterMap emb) = H L := by
    apply canon_congr; intro z _; simp only [List.mem_filterMap, mem_canon' hL]
  simp only [T0, ha, hf]

theorem H_block {x : Nat} (hx : x / 7 < 12) {L : List Nat} :
    H (x :: L) = canon 48 ((x / 7 * 4 + x % 7) :: H L) := by
  apply canon_congr; intro z hz
  simp only [List.filterMap_cons, emb, hx, ite_true, List.mem_cons, H, mem_canon]
  constructor
  · rintro (h | h); exact Or.inl h; exact Or.inr ⟨h, hz⟩
  · rintro (h | h); exact Or.inl h; exact Or.inr h.1

theorem H_fixed {x : Nat} (hx : ¬ x / 7 < 12) (L : List Nat) : H (x :: L) = H L := by
  simp [H, emb, hx]

theorem var_div {i j : Nat} (hj : j < 7) : var 7 i j / 7 = i ∧ var 7 i j % 7 = j := by
  unfold var; omega

section
variable {g : List Nat} (hg : CM 7 8 g)
include hg

theorem g_lt : ∀ v ∈ g, v < 105 := by
  intro v hv; have := hg.1 ▸ hv; exact ((mem_canon _ _ _).1 this).2

theorem T0_g : T0 g = if g.all okV then B (H g) else 0 := by
  have := T0_canon (g_lt hg); rw [show canon 105 g = g from hg.1] at this; exact this

/-- A term of a line sum at a block edge `x` equals the term of the `n = 4` line sum at its image. -/
theorem term_block (hok : g.all okV = true) {x : Nat} (hx : x < 105) (h1 : x / 7 < 12) (h2 : x % 7 < 4) :
    (if isMatch 7 (x :: g) then T0 (canon ((7 + 8) * 7) (x :: g)) else 0) =
      (if isMatch 4 ((x / 7 * 4 + x % 7) :: H g) then B (canon ((4 + 8) * 4) ((x / 7 * 4 + x % 7) :: H g)) else 0) := by
  have hxg : (x :: g).all okV = true := by
    simp only [List.all_cons, hok, Bool.and_true]; exact (okV_iff x).2 (Or.inl ⟨h1, h2⟩)
  have hlt : ∀ v ∈ x :: g, v < 105 := by
    intro v hv; cases List.mem_cons.1 hv with
    | inl h => exact h ▸ hx
    | inr h => exact g_lt hg v h
  have hH : ∀ z ∈ (x / 7 * 4 + x % 7) :: H g, z < 48 := by
    intro z hz; cases List.mem_cons.1 hz with
    | inl h => omega
    | inr h => exact ((mem_canon _ _ _).1 h).2
  have hm : isMatch 4 ((x / 7 * 4 + x % 7) :: H g) = isMatch 7 (x :: g) := by
    rw [match_H hxg, H_block h1]
    exact isMatch_congr 4 (fun z => (mem_canon' hH z).symm)
  rw [show (7 + 8) * 7 = 105 from rfl, show (4 + 8) * 4 = 48 from rfl, hm, T0_canon hlt, hxg, H_block h1]
  simp

/-- At a fixed edge `x` whose pigeon and hole are free in `g`, the term is `T0 g`. -/
theorem term_fixed (hok : g.all okV = true) {x : Nat} (hx : x < 105) (h1 : 12 ≤ x / 7) (h2 : x % 7 + 8 = x / 7)
    (hp : pfree 7 g (x / 7)) :
    (if isMatch 7 (x :: g) then T0 (canon ((7 + 8) * 7) (x :: g)) else 0) = T0 g := by
  have hxg : (x :: g).all okV = true := by
    simp only [List.all_cons, hok, Bool.and_true]; exact (okV_iff x).2 (Or.inr ⟨h1, h2⟩)
  have hlt : ∀ v ∈ x :: g, v < 105 := by
    intro v hv; cases List.mem_cons.1 hv with
    | inl h => exact h ▸ hx
    | inr h => exact g_lt hg v h
  have hxw : ∀ w ∈ g, w / 7 ≠ x / 7 ∧ w % 7 ≠ x % 7 := by
    intro w hw
    have ow := (okV_iff w).1 (List.all_eq_true.1 hok w hw)
    have := hp w hw; omega
  have hm : isMatch 7 (x :: g) = true := by
    rw [isMatch_iff]
    have hgm := (isMatch_iff 7 g).1 hg.2
    intro v hv w hw
    rcases List.mem_cons.1 hv with hv | hv <;> rcases List.mem_cons.1 hw with hw | hw
    · rw [hv, hw]; exact (cfl_iff 7 _ _).2 (Or.inl rfl)
    · have := hxw w hw; rw [hv]; exact (cfl_iff 7 _ _).2 (Or.inr ⟨fun e => this.1 e.symm, fun e => this.2 e.symm⟩)
    · have := hxw v hv; rw [hw]; exact (cfl_iff 7 _ _).2 (Or.inr this)
    · exact hgm v hv w hw
  rw [show (7 + 8) * 7 = 105 from rfl, hm, T0_canon hlt, hxg, T0_g hg, hok, H_fixed (by omega)]
  simp

/-- A term at an edge outside the lift is zero. -/
theorem term_out {x : Nat} (hx105 : x < 105) (hx : okV x = false) :
    (if isMatch 7 (x :: g) then T0 (canon ((7 + 8) * 7) (x :: g)) else 0) = 0 := by
  rw [T0_of_bad ((mem_canon _ _ _).2 ⟨List.mem_cons_self .., hx105⟩) hx]; simp

theorem term_bad (hok : g.all okV = false) (x : Nat) :
    (if isMatch 7 (x :: g) then T0 (canon ((7 + 8) * 7) (x :: g)) else 0) = 0 := by
  obtain ⟨w, hw, hb⟩ : ∃ w ∈ g, okV w = false := by
    have := hok; simp only [List.all_eq_false] at this
    obtain ⟨w, hw, hb⟩ := this; exact ⟨w, hw, by simpa using hb⟩
  rw [T0_of_bad ((mem_canon _ _ _).2 ⟨List.mem_cons_of_mem _ hw, g_lt hg w hw⟩) hb]; simp

end

theorem pfree_H {g : List Nat} (hok : g.all okV = true) {i : Nat} (hp : pfree 7 g i) : pfree 4 (H g) i := by
  intro w' hw'
  obtain ⟨w, hw, h1, h2, rfl⟩ := (mem_H hok w').1 hw'
  have := hp w hw; omega

theorem hfree_H {g : List Nat} (hok : g.all okV = true) {j : Nat} (hp : hfree 7 g j) : hfree 4 (H g) j := by
  intro w' hw'
  obtain ⟨w, hw, h1, h2, rfl⟩ := (mem_H hok w').1 hw'
  have := hp w hw; omega

theorem CM_H {g : List Nat} (hg : CM 7 8 g) (hok : g.all okV = true) : CM 4 8 (H g) :=
  ⟨canon_idem _, by rw [← match_H hok]; exact hg.2⟩

theorem len_H (g : List Nat) : (H g).length ≤ g.length :=
  Nat.le_trans (canon_length_le _ _) (List.length_filterMap_le _ _)

/-- **`Bal 2 7 8 T0 T0 e` for every `e ≤ 2`**, from `BDesMain.b_design`. -/
theorem bal2 : ∀ e ≤ 2, Bal 2 7 8 T0 T0 e := by
  intro e he g hg hl
  have hB := Programme.«20261026-1402-proof-complexity».BDesMain.b_design.2
  by_cases hok : g.all okV = true
  · have hb := hB (H g).length (by have := len_H g; omega) (H g) (CM_H hg hok) rfl
    rw [T0_g hg, hok, if_pos rfl]
    refine ⟨fun i hi hp => ?_, fun j hj hp => ?_⟩
    · by_cases hi12 : i < 12
      · have hrow := hb.1 i (by omega) (pfree_H hok hp)
        suffices heq : rowS 7 8 T0 g i = rowS 4 8 B (H g) i by rw [heq]; exact hrow
        simp only [rowS, lineS]
        rw [rsum_split 7 4 3 _ rfl]
        rw [rsum_zero 3 _ (fun t ht => term_out hg (by unfold var; omega) (okV_false (by unfold var; omega)))]
        rw [Int.add_zero]
        apply rsum_congr; intro t ht
        have hA : var 7 i t / 7 * 4 + var 7 i t % 7 = var 4 i t := by unfold var; omega
        have := term_block hg hok (x := var 7 i t) (by unfold var; omega) (by unfold var; omega)
          (by unfold var; omega)
        rw [hA] at this; exact this
      · have hT : ∀ t < 7, (if isMatch 7 (var 7 i t :: g) then T0 (canon ((7 + 8) * 7) (var 7 i t :: g)) else 0)
            = if t = i - 8 then B (H g) else 0 := by
          intro t ht
          by_cases hti : t = i - 8
          · have hpf : pfree 7 g (var 7 i t / 7) := by
              have : var 7 i t / 7 = i := by unfold var; omega
              rw [this]; exact hp
            rw [if_pos hti, term_fixed hg hok (by unfold var; omega) (by unfold var; omega)
              (by unfold var; omega) hpf, T0_g hg, hok, if_pos rfl]
          · rw [if_neg hti]; exact term_out hg (by unfold var; omega) (okV_false (by unfold var; omega))
        have : rowS 7 8 T0 g i = B (H g) := by
          simp only [rowS, lineS]; rw [rsum_congr 7 _ _ hT, rsum_pick, if_pos (by omega)]
        rw [this]; simp
    · by_cases hj4 : j < 4
      · have hcol := hb.2 j hj4 (hfree_H hok hp)
        suffices heq : colS 7 8 T0 g j = colS 4 8 B (H g) j by rw [heq]; exact hcol
        simp only [colS, lineS]
        rw [rsum_split (7 + 8) (4 + 8) 3 _ rfl]
        rw [rsum_zero 3 _ (fun t ht => by have hv := var_div (i := 4 + 8 + t) (by omega : j < 7); exact term_out hg (by omega) (okV_false (by omega)))]
        rw [Int.add_zero]
        apply rsum_congr; intro t ht
        have hA : var 7 t j / 7 * 4 + var 7 t j % 7 = var 4 t j := by unfold var; omega
        have := term_block hg hok (x := var 7 t j) (by unfold var; omega) (by unfold var; omega)
          (by unfold var; omega)
        rw [hA] at this; exact this
      · have hT : ∀ t < 7 + 8, (if isMatch 7 (var 7 t j :: g) then T0 (canon ((7 + 8) * 7) (var 7 t j :: g)) else 0)
            = if t = j + 8 then B (H g) else 0 := by
          intro t ht
          by_cases htj : t = j + 8
          · have hpf : pfree 7 g (var 7 t j / 7) := by
              intro w hw
              have ow := (okV_iff w).1 (List.all_eq_true.1 hok w hw)
              have := hp w hw; unfold var; omega
            rw [if_pos htj, term_fixed hg hok (by unfold var; omega) (by unfold var; omega)
              (by unfold var; omega) hpf, T0_g hg, hok, if_pos rfl]
          · rw [if_neg htj]; exact term_out hg (by unfold var; omega) (okV_false (by unfold var; omega))
        have : colS 7 8 T0 g j = B (H g) := by
          simp only [colS, lineS]; rw [rsum_congr (7 + 8) _ _ hT, rsum_pick, if_pos (by omega)]
        rw [this]; simp
  · have hok' : g.all okV = false := by simpa using hok
    rw [T0_g hg, hok', if_neg (by simp)]
    refine ⟨fun i _ _ => ?_, fun j _ _ => ?_⟩
    · simp only [rowS, lineS]; rw [rsum_zero _ _ (fun t _ => term_bad hg hok' _)]; simp
    · simp only [colS, lineS]; rw [rsum_zero _ _ (fun t _ => term_bad hg hok' _)]; simp

end Programme.«20261027-0607-proof-complexity».LiftBal

#print axioms Programme.«20261027-0607-proof-complexity».LiftBal.bal2
