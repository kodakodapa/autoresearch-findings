import Programme.«20261027-1434-proof-complexity».ProdM
import Programme.«20261026-1402-proof-complexity».TExt

/-!
# Length-only blocks of an `m`-block product

A block function `lf G` (value `G |l|`) is locally balanced in block `c` of `ProdM` at local
matchings of length `s ≤ L` as soon as `(Q - s) G(s+1) ≡ G s` and `(P - s) G(s+1) ≡ G s` mod `p`,
where `P`, `Q` count the pigeons and holes of block `c`. This is the `m`-block form of the library
`TExt.gsym_row` / `gsym_col`. Examples over `Z/2`: a `2 × 2` rectangle tower is `lf [s ≥ 1]`, the
`3 × 3` tower of `T` is `lf [s ≥ 2]`, a `1 × 1` pin is `lf 1`, and a `9 × 1` block `lf 1` (`L = 0`).
-/

namespace Programme.«20261027-1434-proof-complexity».LocLf

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr)
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ProdExt (SL locL)
open Programme.«20261026-1402-proof-complexity».Win (match_row match_col count_freeQ nodup_mod nodup_div)
open Programme.«20261026-1402-proof-complexity».SymDesign (rsum_mulc)
open Programme.«20261026-1402-proof-complexity».TExt (lf SL_lf)
open Programme.«20261027-1434-proof-complexity».ProdM

variable {n k : Nat}

theorem blkM_eq {m : Nat} {bp bh : Nat → Nat} {w c : Nat} (h : blkM m bp bh n w = c) (hc : c < m) :
    bp (w / n) = c ∧ bh (w % n) = c := by
  unfold blkM at h; split at h
  · rename_i e; exact ⟨h, e.1 ▸ h⟩
  · omega

theorem lf_row (m : Nat) (bp bh : Nat → Nat) (c Q : Nat) (G : Nat → Int) (hn : 0 < n) (hc : c < m)
    (hQ : rsum n (fun t => if bh t = c then 1 else 0) = (Q : Int))
    {σ : List Nat} (hσ : σ.Nodup) (hσm : isMatch n σ = true) (hσb : ∀ w ∈ σ, blkM m bp bh n w = c)
    {i : Nat} (hf : ∀ w ∈ σ, w / n ≠ i) :
    locL n (lf G) σ (var n i) n (fun t => bh t = c) = ((Q : Int) - σ.length) * G (σ.length + 1) := by
  have e : ∀ t < n, (if bh t = c ∧ isMatch n (var n i t :: σ) = true then lf G (var n i t :: σ) else 0) =
      (if bh t = c ∧ ∀ w ∈ σ, w % n ≠ t then 1 else 0) * G (σ.length + 1) := by
    intro t ht
    have key := match_row hσm ht hf
    by_cases h2 : ∀ w ∈ σ, w % n ≠ t
    · have h3 := key.mpr h2; by_cases h1 : bh t = c
      · rw [if_pos ⟨h1, h3⟩, if_pos ⟨h1, h2⟩]; simp [lf]
      · rw [if_neg (fun h => h1 h.1), if_neg (fun h => h1 h.1)]; simp
    · have h3 : isMatch n (var n i t :: σ) = false := by
        cases h : isMatch n (var n i t :: σ)
        · rfl
        · exact absurd (key.mp h) h2
      rw [if_neg (fun h => by rw [h3] at h; exact absurd h.2 (by simp)), if_neg (fun h => h2 h.2)]; simp
  unfold locL
  rw [rsum_congr _ _ _ e, rsum_mulc, count_freeQ (fun t => bh t = c) (· % n) n σ (nodup_mod hσ hσm)
    (fun w hw => ⟨Nat.mod_lt _ hn, (blkM_eq (hσb w hw) hc).2⟩), hQ]

theorem lf_col (m : Nat) (bp bh : Nat → Nat) (c P : Nat) (G : Nat → Int) (hn : 0 < n) (hc : c < m)
    (hP : rsum (n + k) (fun s => if bp s = c then 1 else 0) = (P : Int))
    {σ : List Nat} (hσ : σ.Nodup) (hσm : isMatch n σ = true)
    (hσb : ∀ w ∈ σ, w < (n + k) * n ∧ blkM m bp bh n w = c)
    {j : Nat} (hj : j < n) (hf : ∀ w ∈ σ, w % n ≠ j) :
    locL n (lf G) σ (fun s => var n s j) (n + k) (fun s => bp s = c) =
      ((P : Int) - σ.length) * G (σ.length + 1) := by
  have e : ∀ t < n + k, (if bp t = c ∧ isMatch n (var n t j :: σ) = true then lf G (var n t j :: σ) else 0) =
      (if bp t = c ∧ ∀ w ∈ σ, w / n ≠ t then 1 else 0) * G (σ.length + 1) := by
    intro t _
    have key := match_col (s := t) hσm hj hf
    by_cases h2 : ∀ w ∈ σ, w / n ≠ t
    · have h3 := key.mpr h2; by_cases h1 : bp t = c
      · rw [if_pos ⟨h1, h3⟩, if_pos ⟨h1, h2⟩]; simp [lf]
      · rw [if_neg (fun h => h1 h.1), if_neg (fun h => h1 h.1)]; simp
    · have h3 : isMatch n (var n t j :: σ) = false := by
        cases h : isMatch n (var n t j :: σ)
        · rfl
        · exact absurd (key.mp h) h2
      rw [if_neg (fun h => by rw [h3] at h; exact absurd h.2 (by simp)), if_neg (fun h => h2 h.2)]; simp
  unfold locL
  rw [rsum_congr _ _ _ e, rsum_mulc, count_freeQ (fun t => bp t = c) (· / n) (n + k) σ (nodup_div hσ hσm)
    (fun w hw => ⟨(Nat.div_lt_iff_lt_mul hn).mpr (hσb w hw).1, (blkM_eq (hσb w hw).2 hc).1⟩), hP]

theorem rsum_ind_pos (q : Nat → Prop) [DecidablePred q] {i : Nat} (hq : q i) :
    ∀ M, i < M → 1 ≤ rsum M (fun t => if q t then (1 : Int) else 0)
  | 0, h => absurd h (by omega)
  | M + 1, h => by
    have h0 : ∀ M, 0 ≤ rsum M (fun t => if q t then (1 : Int) else 0) := by
      intro M; induction M with
      | zero => simp [rsum]
      | succ M ih => simp only [rsum]; split <;> omega
    simp only [rsum]
    by_cases e : i = M
    · subst e; rw [if_pos hq]; have := h0 i; omega
    · have := rsum_ind_pos q hq M (by omega); split <;> omega

/-- **Length-only blocks are locally balanced** under the two counting congruences: at a local
matching of size `s` the row condition is needed only when a block pigeon is free (`s < P`), the
column condition only when a block hole is free (`s < Q`). -/
theorem lf_locbal (p m : Nat) (bp bh : Nat → Nat) (c P Q L : Nat) (G : Nat → Int) (hn : 0 < n) (hc : c < m)
    (hQ : rsum n (fun t => if bh t = c then 1 else 0) = (Q : Int))
    (hP : rsum (n + k) (fun s => if bp s = c then 1 else 0) = (P : Int))
    (hG : ∀ s ≤ L, (s < P → (p : Int) ∣ ((Q : Int) - s) * G (s + 1) - G s) ∧
      (s < Q → (p : Int) ∣ ((P : Int) - s) * G (s + 1) - G s)) :
    LocBal p m bp bh n k (lf G) c L := by
  intro g' hnd hm hb hl
  refine ⟨fun i hi hbi hf => ?_, fun j hj hbj hf => ?_⟩
  · rw [lf_row m bp bh c Q G hn hc hQ hnd hm (fun w hw => (hb w hw).2) hf]
    have hc' := count_freeQ (fun t => bp t = c) (· / n) (n + k) g' (nodup_div hnd hm)
      (fun w hw => ⟨(Nat.div_lt_iff_lt_mul hn).mpr (hb w hw).1, (blkM_eq (hb w hw).2 hc).1⟩)
    have h1 := rsum_ind_pos (fun t => bp t = c ∧ ∀ v ∈ g', v / n ≠ t) (i := i) ⟨hbi, hf⟩ (n + k) hi
    rw [hc', hP] at h1
    exact (hG _ hl).1 (by omega)
  · rw [lf_col m bp bh c P G hn hc hP hnd hm hb hj hf]
    have hc' := count_freeQ (fun t => bh t = c) (· % n) n g' (nodup_mod hnd hm)
      (fun w hw => ⟨Nat.mod_lt _ hn, (blkM_eq (hb w hw).2 hc).2⟩)
    have h1 := rsum_ind_pos (fun t => bh t = c ∧ ∀ v ∈ g', v % n ≠ t) (i := j) ⟨hbj, hf⟩ n hj
    rw [hc', hQ] at h1
    exact (hG _ hl).2 (by omega)

end Programme.«20261027-1434-proof-complexity».LocLf
