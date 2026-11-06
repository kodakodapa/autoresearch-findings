import Programme.«20261027-0607-proof-complexity».Blocks

/-!
# Type-`j` windows

Blocks `c < J` are given by pigeon pairs `A c` and hole pairs `Bq c`; block `J` is the rest. Blocks
`c < j` are `2 × 2` rectangle blocks carrying the rectangle window `Aw` (levels `0, r, det`); blocks
`j ≤ c < J` are `1 × 1` blocks (`A c`, `Bq c` degenerate pairs) carrying the constant `1`; the rest
block (`m` holes, pigeons `≡ m` mod `p`) carries the symmetric design `cvf m D`.

- `win_bal`: for every `e < D + j`, `Bal p n k W W e`. Rest lines at a matching in which every
  rectangle block is occupied see at most `e - j < D` rest edges (`Blocks.cnt_filter`); otherwise an
  empty rectangle block makes the other factors vanish (`Aw [] = 0`).
- `win_val`: on canonical `j`-matchings, `W = cv m D 0 · RP n j P Q` when `A c = P c`, `Bq c = Q c`
  for `c < j` (`Blocks.jp_prod`).
-/

namespace Programme.«20261027-0607-proof-complexity».WinJ

open Programme.«20261025-0459-proof-complexity».OntoFPHP (rsum var)
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero var_div var_mod)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt var_decode var_inj)
open Programme.«20261025-1627-proof-complexity».MomGen (canon)
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ExtLin (rect tprod)
open Programme.«20261026-1402-proof-complexity».ProdExt (SL locL len_one)
open Programme.«20261026-1402-proof-complexity».SymDesign (cv)
open Programme.«20261026-1402-proof-complexity».Win (Aw cvf SL_Aw SL_cvf)
open Programme.«20261026-1402-proof-complexity».RectBlock (one)
open Programme.«20261027-0607-proof-complexity».LemK (rprod rprod_congr rprod_zero ls ls_congr dl)
open Programme.«20261027-0607-proof-complexity».SJ (jp RP)
open Programme.«20261027-0607-proof-complexity».BProd
open Programme.«20261027-0607-proof-complexity».LocWin
open Programme.«20261027-0607-proof-complexity».Blocks

/-- Local factors. -/
def phi (n j J m D : Nat) (A Bq : Nat → Nat × Nat) (c : Nat) : List Nat → Int :=
  if c < j then Aw n (A c).1 (A c).2 (Bq c).1 (Bq c).2 else if c < J then (fun _ => 1) else cvf m D

/-- The window. -/
def Wn (n j J m D : Nat) (A Bq : Nat → Nat × Nat) : List Nat → Int :=
  PB (J + 1) (bpA J A) (bpA J Bq) n (phi n j J m D A Bq)

/-- Hypotheses on the block data. -/
structure Good (p n k j J m : Nat) (A Bq : Nat → Nat × Nat) : Prop where
  hJ : j ≤ J
  hA : ∀ c < J, (A c).1 < n + k ∧ (A c).2 < n + k
  hB : ∀ c < J, (Bq c).1 < n ∧ (Bq c).2 < n
  dA : DisjA J A
  dB : DisjA J Bq
  rA : ∀ c < j, (A c).1 ≠ (A c).2
  rB : ∀ c < j, (Bq c).1 ≠ (Bq c).2
  uA : ∀ c, j ≤ c → c < J → (A c).1 = (A c).2
  uB : ∀ c, j ≤ c → c < J → (Bq c).1 = (Bq c).2
  cH : rsum n (fun t => if bpA J Bq t = J then 1 else 0) = (m : Int)
  cP : (p : Int) ∣ rsum (n + k) (fun s => if bpA J A s = J then 1 else 0) - m

theorem SL_phi (n j J m D : Nat) (A Bq : Nat → Nat × Nat) (c : Nat) : SL (phi n j J m D A Bq c) := by
  unfold phi; split
  · exact SL_Aw _ _ _ _ _
  · split
    · exact fun _ _ _ _ _ => rfl
    · exact SL_cvf _ _

theorem Aw_nil (n a a' b b' : Nat) : Aw n a a' b b' [] = 0 := by simp [Aw, one, tprod]

theorem Aw_one (n a a' b b' v : Nat) : Aw n a a' b b' [v] = rect n a a' b b' v := by simp [Aw, one, tprod]

theorem blkB_eq {B : Nat} {bp bh : Nat → Nat} {n w c : Nat} (h : blkB B bp bh n w = c) (hc : c < B) :
    bp (w / n) = c ∧ bh (w % n) = c := by
  unfold blkB at h; split at h
  · rename_i e; exact ⟨h, e ▸ h⟩
  · omega

theorem flB_props (B : Nat) (bp bh : Nat → Nat) {n k : Nat} {g : List Nat} (hg : CM n k g) {c : Nat} (hc : c < B) :
    (flB B bp bh n c g).Nodup ∧ isMatch n (flB B bp bh n c g) = true ∧
      ∀ w ∈ flB B bp bh n c g, (bp (w / n) = c ∧ bh (w % n) = c) ∧ w ∈ g := by
  refine ⟨flB_nodup B bp bh n c (CM_nodup hg), ?_, fun w hw => ?_⟩
  · rw [isMatch_iff]; intro v hv w hw
    exact (isMatch_iff n g).mp hg.2 v ((mem_flB ..).mp hv).1 w ((mem_flB ..).mp hw).1
  · have := (mem_flB ..).mp hw; exact ⟨blkB_eq this.2 hc, this.1⟩

theorem dvd_of_eq {p : Int} {a b : Int} (h : a = b) : p ∣ a - b := by rw [h, Int.sub_self]; exact Int.dvd_zero _

/-- If every rectangle block is occupied, the rest block holds at most `|g| - j` edges. -/
theorem rest_small {J j : Nat} (hJ : j ≤ J) (bp bh : Nat → Nat) {n : Nat} (g : List Nat)
    (hne : ∀ s < j, flB (J + 1) bp bh n s g ≠ []) :
    (flB (J + 1) bp bh n J g).length + j ≤ g.length := by
  have h := cnt_filter (blkB (J + 1) bp bh n) (J + 1) g
  have e : ∀ c, ((g.filter (fun v => blkB (J + 1) bp bh n v == c)).length : Int) = (flB (J + 1) bp bh n c g).length :=
    fun c => rfl
  rw [rsum_congr _ _ _ (fun c _ => e c)] at h
  have h1 := rsum_ge_card (fun c => ((flB (J + 1) bp bh n c g).length : Int)) j (fun c hc => by
    have := hne c hc
    have : (flB (J + 1) bp bh n c g).length ≠ 0 := fun h0 => this (List.eq_nil_of_length_eq_zero h0)
    omega)
  have h2 := rsum_nonneg_le (fun c => ((flB (J + 1) bp bh n c g).length : Int)) (fun c => by simp) J j hJ
  simp only [rsum] at h
  omega

section Bal
variable {p n k j J m D : Nat} {A Bq : Nat → Nat × Nat}

theorem othB_zero (G : Good p n k j J m A Bq) {g : List Nat} {b : Nat} (hb : b = J) {s : Nat} (hs : s < j)
    (he : flB (J + 1) (bpA J A) (bpA J Bq) n s g = []) :
    othB (J + 1) (bpA J A) (bpA J Bq) n (phi n j J m D A Bq) b g = 0 := by
  have := G.hJ
  apply rprod_zero _ _ s (by omega)
  rw [if_neg (by omega), he]; simp only [phi, if_pos hs]; exact Aw_nil _ _ _ _ _

theorem win_bal (G : Good p n k j J m A Bq) (hn : 0 < n) (e : Nat) (he : e < D + j) :
    Bal p n k (Wn n j J m D A Bq) (Wn n j J m D A Bq) e := by
  have hJ := G.hJ
  apply bal_winB p (J + 1) (bpA J A) (bpA J Bq) (fun i => by have := bpA_le J A i; omega)
    (fun i => by have := bpA_le J Bq i; omega) _ (SL_phi n j J m D A Bq) e
  · intro g hg hl _ i hi hf
    have hcle := bpA_le J A i
    obtain ⟨hnd, hmt, hmem⟩ := flB_props (J + 1) (bpA J A) (bpA J Bq) hg (c := bpA J A i) (by omega)
    have hf' : ∀ w ∈ flB (J + 1) (bpA J A) (bpA J Bq) n (bpA J A i) g, w / n ≠ i :=
      fun w hw => hf w (hmem w hw).2
    have hmem' := fun w hw => (hmem w hw).1
    by_cases h1 : bpA J A i < j
    · right; simp only [phi, if_pos h1]
      have hc : bpA J A i < J := by omega
      exact dvd_of_eq (rect_row (G.hB _ hc).1 (G.hB _ hc).2 (G.rA _ h1) (G.rB _ h1) (bpA_iff G.dA hc)
        (bpA_iff G.dB hc) hnd hmt hmem' rfl hf')
    by_cases h2 : bpA J A i < J
    · right; simp only [phi, if_neg h1, if_pos h2]
      have uA := G.uA _ (by omega) h2; have uB := G.uB _ (by omega) h2
      rw [unit_row (x := (A (bpA J A i)).1) (h := (Bq (bpA J A i)).1) (G.hB _ h2).1
        (fun i' => by rw [bpA_iff G.dA h2, ← uA, or_self])
        (fun j' => by rw [bpA_iff G.dB h2, ← uB, or_self]) hmem' rfl hf']
      exact dvd_of_eq rfl
    have hc : bpA J A i = J := by omega
    by_cases hemp : ∃ s < j, flB (J + 1) (bpA J A) (bpA J Bq) n s g = []
    · obtain ⟨s, hs, he'⟩ := hemp; left; exact othB_zero G hc hs he'
    · right
      have hne : ∀ s < j, flB (J + 1) (bpA J A) (bpA J Bq) n s g ≠ [] := fun s hs h => hemp ⟨s, hs, h⟩
      have hsm := rest_small hJ (bpA J A) (bpA J Bq) g hne
      simp only [phi, if_neg h1, if_neg h2]
      rw [hc]
      obtain ⟨hnd2, hmt2, hmem2⟩ := flB_props (J + 1) (bpA J A) (bpA J Bq) hg (c := J) (by omega)
      exact sym_rowD p m D hn G.cH hnd2 hmt2 (fun w hw => (hmem2 w hw).1) (by omega) (fun w hw => hf w (hmem2 w hw).2)
  · intro g hg hl _ y hy hf
    have hcle := bpA_le J Bq y
    obtain ⟨hnd, hmt, hmem⟩ := flB_props (J + 1) (bpA J A) (bpA J Bq) hg (c := bpA J Bq y) (by omega)
    have hf' : ∀ w ∈ flB (J + 1) (bpA J A) (bpA J Bq) n (bpA J Bq y) g, w % n ≠ y :=
      fun w hw => hf w (hmem w hw).2
    have hmem' := fun w hw => (hmem w hw).1
    by_cases h1 : bpA J Bq y < j
    · right; simp only [phi, if_pos h1]
      have hc : bpA J Bq y < J := by omega
      exact dvd_of_eq (rect_col (G.hA _ hc).1 (G.hA _ hc).2 (G.hB _ hc).1 (G.hB _ hc).2 (G.rA _ h1) (G.rB _ h1)
        (bpA_iff G.dA hc) (bpA_iff G.dB hc) hnd hmt hmem' rfl hf')
    by_cases h2 : bpA J Bq y < J
    · right; simp only [phi, if_neg h1, if_pos h2]
      have uA := G.uA _ (by omega) h2; have uB := G.uB _ (by omega) h2
      rw [unit_col (x := (A (bpA J Bq y)).1) (h := (Bq (bpA J Bq y)).1) (G.hA _ h2).1
        (fun i' => by rw [bpA_iff G.dA h2, ← uA, or_self])
        (fun j' => by rw [bpA_iff G.dB h2, ← uB, or_self]) hmem' rfl hf']
      exact dvd_of_eq rfl
    have hc : bpA J Bq y = J := by omega
    by_cases hemp : ∃ s < j, flB (J + 1) (bpA J A) (bpA J Bq) n s g = []
    · obtain ⟨s, hs, he'⟩ := hemp; left; exact othB_zero G hc hs he'
    · right
      have hne : ∀ s < j, flB (J + 1) (bpA J A) (bpA J Bq) n s g ≠ [] := fun s hs h => hemp ⟨s, hs, h⟩
      have hsm := rest_small hJ (bpA J A) (bpA J Bq) g hne
      simp only [phi, if_neg h1, if_neg h2]
      rw [hc]
      obtain ⟨hnd2, hmt2, hmem2⟩ := flB_props (J + 1) (bpA J A) (bpA J Bq) hg (c := J) (by omega)
      exact sym_colD p m D hn G.cP hnd2 hmt2 (fun w hw => ⟨(hmem2 w hw).1, CM_lt hg (hmem2 w hw).2⟩)
        (by omega) hy (fun w hw => hf w (hmem2 w hw).2)

end Bal

/-! ## Values on `j`-matchings -/

theorem dl_ne {q : Nat × Nat} {y : Nat} (h : dl q y ≠ 0) : y = q.1 ∨ y = q.2 := by
  unfold dl at h
  by_cases h1 : y = q.1
  · exact Or.inl h1
  · by_cases h2 : y = q.2
    · exact Or.inr h2
    · simp [h1, h2] at h

theorem dl_disj {q q' : Nat × Nat} (h : q.1 ≠ q'.1 ∧ q.1 ≠ q'.2 ∧ q.2 ≠ q'.1 ∧ q.2 ≠ q'.2) (y : Nat) :
    dl q y * dl q' y = 0 := by
  by_cases h1 : dl q y = 0
  · rw [h1, Int.zero_mul]
  by_cases h2 : dl q' y = 0
  · rw [h2, Int.mul_zero]
  have := dl_ne h1; have := dl_ne h2; omega

theorem ite_and1 (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P ∧ Q then (1 : Int) else 0) = (if P then 1 else 0) * (if Q then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem rect_dl {n a a' b b' : Nat} (hb : b < n) (hb' : b' < n) (v : Nat) :
    rect n a a' b b' v = dl (a, a') (v / n) * dl (b, b') (v % n) := by
  have hn : 0 < n := by omega
  have hvm : v % n < n := Nat.mod_lt _ hn
  have key : ∀ i t, t < n → (v = var n i t ↔ v / n = i ∧ v % n = t) := by
    intro i t ht
    constructor
    · intro h; subst h; rw [var_div n i t ht, var_mod n i t ht]; exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩; rw [← h1, ← h2]; exact (var_decode n v).symm
  unfold rect dl
  simp only [key a b hb, key a' b' hb', key a b' hb', key a' b hb, ite_and1]
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]; omega

section Val
variable {p n k j J m D : Nat} {A Bq P Q : Nat → Nat × Nat}

theorem win_val (G : Good p n k j J m A Bq) (hAP : ∀ c < j, A c = P c) (hBQ : ∀ c < j, Bq c = Q c)
    {g : List Nat} (hg : CM n k g) (hl : g.length = j) :
    Wn n j J m D A Bq g = cv m D 0 * RP n j P Q g := by
  have hJ := G.hJ
  let r : Nat → Nat → Int := fun s v => dl (P s) (v / n) * dl (Q s) (v % n)
  have hdis : ∀ s < j, ∀ s' < j, s ≠ s' → ∀ x, r s x * r s' x = 0 := by
    intro s hs s' hs' hne x
    have dA := G.dA s (by omega) s' (by omega) hne; have dB := G.dB s (by omega) s' (by omega) hne
    rw [hAP s hs, hAP s' hs'] at dA; rw [hBQ s hs, hBQ s' hs'] at dB
    have e : r s x * r s' x = (dl (P s) (x / n) * dl (P s') (x / n)) * (dl (Q s) (x % n) * dl (Q s') (x % n)) := by
      simp only [r]; simp only [Int.mul_assoc, Int.mul_left_comm]
    rw [e, dl_disj dA, Int.zero_mul]
  have hRP : RP n j P Q g = rprod j (fun s => ls g (r s)) := jp_prod j r g (CM_nodup hg) hl hdis
  -- `r s` vanishes off block `s`
  have hsupp : ∀ s < j, ∀ x, r s x ≠ 0 → blkB (J + 1) (bpA J A) (bpA J Bq) n x = s := by
    intro s hs x hx
    have h1 : dl (P s) (x / n) ≠ 0 := fun h => hx (by simp only [r]; rw [h, Int.zero_mul])
    have h2 : dl (Q s) (x % n) ≠ 0 := fun h => hx (by simp only [r]; rw [h, Int.mul_zero])
    have e1 := (bpA_iff G.dA (by omega : s < J) (x / n)).mpr (by rw [hAP s hs]; exact dl_ne h1)
    have e2 := (bpA_iff G.dB (by omega : s < J) (x % n)).mpr (by rw [hBQ s hs]; exact dl_ne h2)
    unfold blkB; rw [e1, e2]; simp
  have hls : ∀ s < j, ls g (r s) = ls (flB (J + 1) (bpA J A) (bpA J Bq) n s g) (r s) := by
    intro s hs
    apply ls_filter; intro x _ hq
    exact Classical.byContradiction fun hx => by
      have := hsupp s hs x hx; simp [this] at hq
  rw [hRP]
  by_cases hemp : ∃ s < j, flB (J + 1) (bpA J A) (bpA J Bq) n s g = []
  · obtain ⟨s, hs, he⟩ := hemp
    have h0 : rprod j (fun s => ls g (r s)) = 0 := rprod_zero _ _ s hs (by rw [hls s hs, he]; rfl)
    rw [h0, Int.mul_zero]
    unfold Wn PB; split
    · apply rprod_zero _ _ s (by omega)
      rw [he]; simp only [phi, if_pos hs]; exact Aw_nil _ _ _ _ _
    · rfl
  · have hne : ∀ s < j, flB (J + 1) (bpA J A) (bpA J Bq) n s g ≠ [] := fun s hs h => hemp ⟨s, hs, h⟩
    have hc := cnt_filter (blkB (J + 1) (bpA J A) (bpA J Bq) n) j g
    have e : ∀ c, ((g.filter (fun v => blkB (J + 1) (bpA J A) (bpA J Bq) n v == c)).length : Int) =
        (flB (J + 1) (bpA J A) (bpA J Bq) n c g).length := fun c => rfl
    rw [rsum_congr _ _ _ (fun c _ => e c)] at hc
    have hge : ∀ c < j, 1 ≤ ((flB (J + 1) (bpA J A) (bpA J Bq) n c g).length : Int) := by
      intro c hc'
      have := hne c hc'
      have : (flB (J + 1) (bpA J A) (bpA J Bq) n c g).length ≠ 0 := fun h0 => this (List.eq_nil_of_length_eq_zero h0)
      omega
    have h1 := rsum_ge_card _ j hge
    have hcross : (g.filter (fun v => decide (j ≤ blkB (J + 1) (bpA J A) (bpA J Bq) n v))).length = 0 := by omega
    have hone := rsum_eq_card _ j hge (by omega)
    have hin : ∀ x ∈ g, blkB (J + 1) (bpA J A) (bpA J Bq) n x < j := by
      intro x hx
      exact Classical.byContradiction fun h => by
        have : x ∈ g.filter (fun v => decide (j ≤ blkB (J + 1) (bpA J A) (bpA J Bq) n v)) := by
          simp [hx]; omega
        rw [List.eq_nil_of_length_eq_zero hcross] at this; simp at this
    have hok : okB (J + 1) (bpA J A) (bpA J Bq) n g = true := by
      unfold okB; simp only [List.all_eq_true, decide_eq_true_eq]; intro x hx; have := hin x hx; omega
    have hemp' : ∀ c, j ≤ c → flB (J + 1) (bpA J A) (bpA J Bq) n c g = [] := by
      intro c hc'
      apply List.eq_nil_iff_forall_not_mem.mpr; intro x hx
      have := (mem_flB ..).mp hx; have := hin x this.1; omega
    unfold Wn PB; rw [if_pos hok]
    simp only [rprod]
    rw [rprod_one_tail _ j J hJ (fun c hc1 hc2 => by
      simp only [phi, if_neg (show ¬ c < j by omega), if_pos hc2])]
    rw [hemp' J hJ]
    simp only [phi, if_neg (show ¬ J < j by omega), Nat.lt_irrefl, if_false]
    rw [show cvf m D [] = cv m D 0 from rfl, Int.mul_comm]
    congr 1
    apply rprod_congr; intro s hs
    obtain ⟨v, hv⟩ := len_one (by have := hone s hs; omega : (flB (J + 1) (bpA J A) (bpA J Bq) n s g).length = 1)
    rw [hls s hs, hv, if_pos hs, Aw_one]
    simp only [Programme.«20261027-0607-proof-complexity».LemK.ls_cons, Programme.«20261027-0607-proof-complexity».LemK.ls_nil, Int.add_zero, r]
    have hb := G.hB s (by omega)
    rw [rect_dl hb.1 hb.2, ← hAP s hs, ← hBQ s hs]

end Val

end Programme.«20261027-0607-proof-complexity».WinJ
