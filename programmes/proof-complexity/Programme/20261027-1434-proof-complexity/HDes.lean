import Programme.«20261026-1402-proof-complexity».Win
import Programme.«20261026-1402-proof-complexity».BDesMain
import Programme.«20261026-1402-proof-complexity».Relabel

/-!
# th's degree-3 design `H` on `ontoFPHP 7 8` over `Z/2`

Blocks: pigeons `< 12` with holes `< 4` (block 0) and pigeons `12, 13, 14` with holes `4, 5, 6`
(block 1). On block 0, `H` is K35's design `B` of `ontoFPHP 4 8` (library `BDes.B`, K167) read
through `ρ(7i + j) = 4i + j`; on block 1 it is the indicator of the diagonal `(12,4), (13,5), (14,6)`;
cross edges give `0`. `h_design`: `H [] = 1` and `Bal 2 7 8 H H e` for `e ≤ 2`, by `Win.bal_win`:
block 0's local windows are B's (`BDesMain.b_design`) after reindexing, block 1's are checked by hand.
-/

namespace Programme.«20261027-1434-proof-complexity».HDes

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero var_div var_mod)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (rsum_pick)
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ProdExt
open Programme.«20261026-1402-proof-complexity».Win

def bp (i : Nat) : Nat := if i < 12 then 0 else 1
def bh (j : Nat) : Nat := if j < 4 then 0 else 1
def rho (v : Nat) : Nat := (v / 7) * 4 + v % 7
def B7 (l : List Nat) : Int := Programme.«20261026-1402-proof-complexity».BDes.B (canon 48 (l.map rho))
def Dg (l : List Nat) : Int := if l.all (fun v => v / 7 == v % 7 + 8) then 1 else 0
def H : List Nat → Int := Prod bp bh 7 (tri B7 Dg (fun _ => 1))

theorem bp_lt (i : Nat) : bp i < 3 := by unfold bp; split <;> omega
theorem bh_lt (j : Nat) : bh j < 3 := by unfold bh; split <;> omega

/-! ## Block 0: reindexing to `ontoFPHP 4 8` -/

/-- An edge of block 0. -/
def In0 (v : Nat) : Prop := v / 7 < 12 ∧ v % 7 < 4

theorem rho_div {v : Nat} (h : In0 v) : rho v / 4 = v / 7 := by unfold rho In0 at *; omega
theorem rho_mod {v : Nat} (h : In0 v) : rho v % 4 = v % 7 := by unfold rho In0 at *; omega
theorem rho_lt {v : Nat} (h : In0 v) : rho v < 48 := by unfold rho In0 at *; omega
theorem rho_inj {v w : Nat} (hv : In0 v) (hw : In0 w) (e : rho v = rho w) : v = w := by
  unfold rho In0 at *; omega
theorem rho_var {i t : Nat} (ht : t < 4) : rho (var 7 i t) = var 4 i t := by
  unfold rho var; omega

theorem cfl_rho {v w : Nat} (hv : In0 v) (hw : In0 w) : cfl 4 (rho v) (rho w) = cfl 7 v w := by
  have h1 := rho_div hv; have h2 := rho_div hw; have h3 := rho_mod hv; have h4 := rho_mod hw
  have h5 : rho v = rho w ↔ v = w := ⟨rho_inj hv hw, fun e => e ▸ rfl⟩
  unfold cfl; rw [h1, h2, h3, h4]
  congr 1
  by_cases e : v = w
  · subst e; simp
  · have : rho v ≠ rho w := fun h => e (h5.mp h)
    rw [bne_iff_ne.mpr this, bne_iff_ne.mpr e]

theorem isMatch_rho {l : List Nat} (hl : ∀ v ∈ l, In0 v) : isMatch 4 (l.map rho) = isMatch 7 l := by
  apply Bool.eq_iff_iff.mpr
  rw [isMatch_iff, isMatch_iff]
  constructor
  · intro H v hv w hw
    rw [← cfl_rho (hl v hv) (hl w hw)]
    exact H _ (List.mem_map_of_mem hv) _ (List.mem_map_of_mem hw)
  · intro H v' hv' w' hw'
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hv'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hw'
    rw [cfl_rho (hl v hv) (hl w hw)]; exact H v hv w hw

theorem mem_red {σ : List Nat} (hσ : ∀ v ∈ σ, In0 v) (x : Nat) :
    x ∈ canon 48 (σ.map rho) ↔ x ∈ σ.map rho := by
  rw [mem_canon]; constructor
  · exact fun h => h.1
  · intro h; refine ⟨h, ?_⟩
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h; exact rho_lt (hσ v hv)

/-- Membership-invariance of `B7`. -/
theorem SL_B7 : SL B7 := by
  intro l l' _ _ hm; unfold B7
  congr 1; apply canon_congr; intro x _
  simp only [List.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact ⟨v, (hm v).mp hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩; exact ⟨v, (hm v).mpr hv, rfl⟩

theorem SL_Dg : SL Dg := by
  intro l l' _ _ hm; unfold Dg
  have : l.all (fun v => v / 7 == v % 7 + 8) = l'.all (fun v => v / 7 == v % 7 + 8) := by
    apply Bool.eq_iff_iff.mpr; simp only [List.all_eq_true]
    exact ⟨fun H x hx => H x ((hm x).mpr hx), fun H x hx => H x ((hm x).mp hx)⟩
  rw [this]

theorem rsum_tail (M a : Nat) (F : Nat → Int) (h : ∀ t, a ≤ t → t < a + M → F t = 0) :
    rsum (a + M) F = rsum a F := by
  induction M with
  | zero => rfl
  | succ M ih =>
    show rsum (a + M) F + F (a + M) = rsum a F
    rw [ih (fun t h1 h2 => h t h1 (by omega)), h (a + M) (by omega) (by omega)]; simp

theorem rsum_tail' (N a : Nat) (F : Nat → Int) (hN : a ≤ N) (h : ∀ t, a ≤ t → t < N → F t = 0) :
    rsum N F = rsum a F := by
  obtain ⟨M, rfl⟩ : ∃ M, N = a + M := ⟨N - a, by omega⟩
  exact rsum_tail M a F (fun t h1 h2 => h t h1 h2)

/-- Row of block 0. -/
theorem row0 {σ : List Nat} (hσ : ∀ v ∈ σ, In0 v) {i : Nat} (hi : i < 12) :
    locL 7 B7 σ (var 7 i) 7 (fun t => bh t = 0) =
      rowS 4 8 Programme.«20261026-1402-proof-complexity».BDes.B (canon 48 (σ.map rho)) i := by
  unfold locL rowS lineS
  rw [rsum_tail' 7 4 _ (by omega) (fun t h1 _ => by
    have : bh t = 1 := by unfold bh; split <;> omega
    simp [this])]
  apply rsum_congr; intro t ht
  have hb : bh t = 0 := by unfold bh; simp [ht]
  have hin : ∀ v ∈ var 7 i t :: σ, In0 v := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · unfold In0 var; omega
    · exact hσ v hv
  simp only [hb, true_and]
  rw [ ← isMatch_rho hin, List.map_cons, rho_var ht]
  have hc : ∀ L : List Nat, (∀ x, x ∈ L ↔ x ∈ var 4 i t :: σ.map rho) →
      canon 48 L = canon 48 (var 4 i t :: canon 48 (σ.map rho)) := by
    intro L hL; apply canon_congr; intro x _
    rw [hL, List.mem_cons, List.mem_cons, mem_red hσ]
  rw [isMatch_congr 4 (var 4 i t :: σ.map rho) (var 4 i t :: canon 48 (σ.map rho))
    (fun x => by rw [List.mem_cons, List.mem_cons, mem_red hσ])]
  unfold B7
  rw [List.map_cons, rho_var ht, hc _ (fun x => Iff.rfl)]

/-- Column of block 0. -/
theorem col0 {σ : List Nat} (hσ : ∀ v ∈ σ, In0 v) {j : Nat} (hj : j < 4) :
    locL 7 B7 σ (fun s => var 7 s j) 15 (fun s => bp s = 0) =
      colS 4 8 Programme.«20261026-1402-proof-complexity».BDes.B (canon 48 (σ.map rho)) j := by
  unfold locL colS lineS
  rw [rsum_tail' 15 12 _ (by omega) (fun t h1 _ => by
    have : bp t = 1 := by unfold bp; split <;> omega
    simp [this])]
  apply rsum_congr; intro s hs
  have hb : bp s = 0 := by unfold bp; simp [hs]
  have hin : ∀ v ∈ var 7 s j :: σ, In0 v := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · unfold In0 var; omega
    · exact hσ v hv
  simp only [hb, true_and]
  rw [← isMatch_rho hin, List.map_cons, rho_var hj]
  have hc : ∀ L : List Nat, (∀ x, x ∈ L ↔ x ∈ var 4 s j :: σ.map rho) →
      canon 48 L = canon 48 (var 4 s j :: canon 48 (σ.map rho)) := by
    intro L hL; apply canon_congr; intro x _
    rw [hL, List.mem_cons, List.mem_cons, mem_red hσ]
  rw [isMatch_congr 4 (var 4 s j :: σ.map rho) (var 4 s j :: canon 48 (σ.map rho))
    (fun x => by rw [List.mem_cons, List.mem_cons, mem_red hσ])]
  unfold B7
  rw [List.map_cons, rho_var hj, hc _ (fun x => Iff.rfl)]

/-- The reduced local matching is a canonical matching of `ontoFPHP 4 8`. -/
theorem red_CM {σ : List Nat} (hσ : ∀ v ∈ σ, In0 v) (hm : isMatch 7 σ = true) :
    CM 4 8 (canon 48 (σ.map rho)) := by
  refine ⟨canon_idem _, ?_⟩
  rw [isMatch_congr 4 _ (σ.map rho) (mem_red hσ), isMatch_rho hσ, hm]

theorem red_len {σ : List Nat} (hσ : ∀ v ∈ σ, In0 v) (hn : σ.Nodup) :
    (canon 48 (σ.map rho)).length = σ.length := by
  rw [canon_len_eq _ (fun x hx => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx; exact rho_lt (hσ v hv)), List.length_map]
  exact Programme.«20261026-1402-proof-complexity».Relabel.nodup_map_on rho hn
    (fun x hx y hy e => rho_inj (hσ x hx) (hσ y hy) e)

theorem red_pfree {σ : List Nat} (hσ : ∀ v ∈ σ, In0 v) {i : Nat} (hf : ∀ w ∈ σ, w / 7 ≠ i) :
    pfree 4 (canon 48 (σ.map rho)) i := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ((mem_red hσ x).mp hx)
  rw [rho_div (hσ v hv)]; exact hf v hv

theorem red_hfree {σ : List Nat} (hσ : ∀ v ∈ σ, In0 v) {j : Nat} (hf : ∀ w ∈ σ, w % 7 ≠ j) :
    hfree 4 (canon 48 (σ.map rho)) j := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ((mem_red hσ x).mp hx)
  rw [rho_mod (hσ v hv)]; exact hf v hv

/-! ## Block 1: the diagonal `(12,4), (13,5), (14,6)` -/

def In1 (v : Nat) : Prop := 12 ≤ v / 7 ∧ v / 7 < 15 ∧ 4 ≤ v % 7

theorem Dg_cons (v : Nat) (l : List Nat) :
    Dg (v :: l) = if v / 7 = v % 7 + 8 then Dg l else 0 := by
  unfold Dg; by_cases h : v / 7 = v % 7 + 8 <;> simp [h]

theorem Dg_diag {σ : List Nat} (h : Dg σ ≠ 0) : ∀ w ∈ σ, w / 7 = w % 7 + 8 := by
  unfold Dg at h; split at h
  · rename_i hd; simp only [List.all_eq_true, beq_iff_eq] at hd; exact hd
  · exact absurd rfl h

theorem row1 {σ : List Nat} (hm : isMatch 7 σ = true) {i : Nat} (hi1 : 12 ≤ i) (hi2 : i < 15)
    (hf : ∀ w ∈ σ, w / 7 ≠ i) : locL 7 Dg σ (var 7 i) 7 (fun t => bh t = 1) = Dg σ := by
  unfold locL
  have key : ∀ t < 7, (if bh t = 1 ∧ isMatch 7 (var 7 i t :: σ) = true then Dg (var 7 i t :: σ) else 0) =
      (if t = i - 8 then Dg σ else 0) := by
    intro t ht
    rw [Dg_cons, var_div 7 i t ht, var_mod 7 i t ht]
    by_cases h : t = i - 8
    · have hb : bh t = 1 := by unfold bh; split <;> omega
      rw [if_pos (show i = t + 8 by omega), if_pos h]
      by_cases hd : Dg σ = 0
      · rw [hd]; simp
      · have hmt : isMatch 7 (var 7 i t :: σ) = true := (match_row hm ht hf).mpr (fun w hw e => by
          have := Dg_diag hd w hw; have := hf w hw; omega)
        simp [hb, hmt]
    · rw [if_neg (show ¬ i = t + 8 by omega), if_neg h]; simp
  rw [rsum_congr _ _ _ key, rsum_pick, if_pos (by omega)]

theorem col1 {σ : List Nat} (hm : isMatch 7 σ = true) {j : Nat} (hj1 : 4 ≤ j) (hj2 : j < 7)
    (hf : ∀ w ∈ σ, w % 7 ≠ j) :
    locL 7 Dg σ (fun s => var 7 s j) 15 (fun s => bp s = 1) = Dg σ := by
  unfold locL
  have key : ∀ s < 15, (if bp s = 1 ∧ isMatch 7 (var 7 s j :: σ) = true then Dg (var 7 s j :: σ) else 0) =
      (if s = j + 8 then Dg σ else 0) := by
    intro s hs
    rw [Dg_cons, var_div 7 s j hj2, var_mod 7 s j hj2]
    by_cases h : s = j + 8
    · have hb : bp s = 1 := by unfold bp; split <;> omega
      rw [if_pos h]
      by_cases hd : Dg σ = 0
      · rw [hd]; simp
      · have hmt : isMatch 7 (var 7 s j :: σ) = true := (match_col hm hj2 hf).mpr (fun w hw e => by
          have := Dg_diag hd w hw; have := hf w hw; omega)
        simp [hb, hmt]
    · rw [if_neg h]; simp
  rw [rsum_congr _ _ _ key, rsum_pick, if_pos (by omega)]

/-! ## Assembly -/

theorem in0_of {v : Nat} (h : blk bp bh 7 v = 0) : In0 v := by
  have := blk_eq h (by omega); unfold bp bh at this; unfold In0
  obtain ⟨h1, h2⟩ := this
  split at h1 <;> split at h2 <;> omega

theorem in1_of {v : Nat} (h : blk bp bh 7 v = 1) (hv : v < 105) : In1 v := by
  have := blk_eq h (by omega); unfold bp bh at this; unfold In1
  obtain ⟨h1, h2⟩ := this
  split at h1 <;> split at h2 <;> omega

theorem SL_phi : ∀ c, SL (tri B7 Dg (fun _ => 1) c) :=
  SL_tri SL_B7 SL_Dg (fun _ _ _ _ _ => rfl)

/-- **th's design `H` at `(7,8)`**: `H [] = 1` and `Bal 2 7 8 H H e` for every `e ≤ 2`. -/
theorem h_design : H [] = 1 ∧ ∀ e ≤ 2, Bal 2 7 8 H H e := by
  refine ⟨by decide, fun e he => ?_⟩
  apply bal_win 2 bp bh bp_lt bh_lt _ SL_phi e
  · intro g hg hl _ i hi hf
    obtain ⟨hnd, hmt, hmem, hlen⟩ := fl_props (n := 7) (k := 8) bp bh hg (bp i)
    have hf' : ∀ w ∈ fl bp bh 7 (bp i) g, w / 7 ≠ i := fun w hw => hf w (hmem w hw).2
    by_cases hi12 : i < 12
    · have hb : bp i = 0 := by unfold bp; simp [hi12]
      rw [hb] at hf' hmem hnd hmt hlen ⊢
      have hσ : ∀ v ∈ fl bp bh 7 0 g, In0 v := fun v hv => in0_of (hmem v hv).1
      show (2 : Int) ∣ locL 7 B7 _ (var 7 i) 7 (fun t => bh t = 0) - B7 _
      rw [row0 hσ hi12]
      exact ((Programme.«20261026-1402-proof-complexity».BDesMain.b_design.2 _ (by omega))
        _ (red_CM hσ hmt) (red_len hσ hnd)).1 i (by omega) (red_pfree hσ hf')
    · have hb : bp i = 1 := by unfold bp; simp [hi12]
      rw [hb] at hf' hmem hnd hmt hlen ⊢
      show (2 : Int) ∣ locL 7 Dg _ (var 7 i) 7 (fun t => bh t = 1) - Dg _
      rw [row1 hmt (by omega) hi hf', Int.sub_self]; exact Int.dvd_zero _
  · intro g hg hl _ j hj hf
    obtain ⟨hnd, hmt, hmem, hlen⟩ := fl_props (n := 7) (k := 8) bp bh hg (bh j)
    have hf' : ∀ w ∈ fl bp bh 7 (bh j) g, w % 7 ≠ j := fun w hw => hf w (hmem w hw).2
    by_cases hj4 : j < 4
    · have hb : bh j = 0 := by unfold bh; simp [hj4]
      rw [hb] at hf' hmem hnd hmt hlen ⊢
      have hσ : ∀ v ∈ fl bp bh 7 0 g, In0 v := fun v hv => in0_of (hmem v hv).1
      show (2 : Int) ∣ locL 7 B7 _ (fun s => var 7 s j) (7 + 8) (fun s => bp s = 0) - B7 _
      rw [show (7 + 8 : Nat) = 15 from rfl, col0 hσ hj4]
      exact ((Programme.«20261026-1402-proof-complexity».BDesMain.b_design.2 _ (by omega))
        _ (red_CM hσ hmt) (red_len hσ hnd)).2 j hj4 (red_hfree hσ hf')
    · have hb : bh j = 1 := by unfold bh; simp [hj4]
      rw [hb] at hf' hmem hnd hmt hlen ⊢
      show (2 : Int) ∣ locL 7 Dg _ (fun s => var 7 s j) (7 + 8) (fun s => bp s = 1) - Dg _
      rw [show (7 + 8 : Nat) = 15 from rfl, col1 hmt (by omega) hj hf', Int.sub_self]
      exact Int.dvd_zero _

end Programme.«20261027-1434-proof-complexity».HDes

#print axioms Programme.«20261027-1434-proof-complexity».HDes.h_design
