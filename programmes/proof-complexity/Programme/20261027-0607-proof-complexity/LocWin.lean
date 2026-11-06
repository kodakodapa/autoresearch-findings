import Programme.«20261027-0607-proof-complexity».BProd

/-!
# Local windows on a block `c` of a `B`-block partition

The block is given by `bp i = c` (pigeons) and `bh j = c` (holes). Local identities
`locL φ σ (line) = φ σ` (mod `p`) at a matching `σ` inside the block, for a free line of the block:
- `rect_row`, `rect_col`: the rectangle window `Win.Aw` (levels `0, r, det`) on a `2 × 2` block
  (from the library lemmas `Win.blk0_row`, `Win.blk0_col` via a relabelling of blocks);
- `unit_row`, `unit_col`: the constant `1` on a `1 × 1` block;
- `sym_rowD`, `sym_colD`: the symmetric design `cvf m D` of degree `D` (block with `m` holes and
  `≡ m` mod `p` pigeons) at `σ` with `|σ| < D` (generalises `Win.sym_row`, `Win.sym_col`, `D = 3`).
-/

namespace Programme.«20261027-0607-proof-complexity».LocWin

open Programme.«20261025-0459-proof-complexity».OntoFPHP (rsum var)
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero var_div var_mod)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt var_decode rsum_pick rsum_const)
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ProdExt (SL locL blk)
open Programme.«20261026-1402-proof-complexity».SymDesign (cv cv_step rsum_mulc)
open Programme.«20261026-1402-proof-complexity».Win (Aw cvf blk0_row blk0_col rsum1 match_row match_col
  nodup_mod nodup_div count_freeQ)
open Programme.«20261026-1402-proof-complexity».RectBlock (isMatch_one)

variable {n k : Nat}

theorem locL_iff (φ : List Nat → Int) (σ : List Nat) (v : Nat → Nat) (M : Nat) (Q Q' : Nat → Prop)
    [DecidablePred Q] [DecidablePred Q'] (h : ∀ t, Q t ↔ Q' t) :
    locL n φ σ v M Q = locL n φ σ v M Q' := by
  unfold locL; apply rsum_congr; intro t _
  by_cases hq : Q t
  · have := (h t).mp hq; simp [hq, this]
  · have : ¬ Q' t := fun h' => hq ((h t).mpr h'); simp [hq, this]

/-- Relabelled block indicator. -/
def ind (bp : Nat → Nat) (c : Nat) (i : Nat) : Nat := if bp i = c then 0 else 1

theorem ind0 (bp : Nat → Nat) (c i : Nat) : ind bp c i = 0 ↔ bp i = c := by
  unfold ind; split <;> simp_all

section Rect
variable {a a' b b' c : Nat} {bp bh : Nat → Nat}

theorem rect_row (hb : b < n) (hb' : b' < n) (p1 : a ≠ a') (q1 : b ≠ b')
    (hP : ∀ i, bp i = c ↔ i = a ∨ i = a') (hH : ∀ j, bh j = c ↔ j = b ∨ j = b')
    {σ : List Nat} (hσ : σ.Nodup) (hσm : isMatch n σ = true) (hσb : ∀ w ∈ σ, bp (w / n) = c ∧ bh (w % n) = c)
    {i : Nat} (hi : bp i = c) (hf : ∀ w ∈ σ, w / n ≠ i) :
    locL n (Aw n a a' b b') σ (var n i) n (fun t => bh t = c) = Aw n a a' b b' σ := by
  rw [locL_iff _ _ _ _ _ (fun t => ind bh c t = 0) (fun t => (ind0 bh c t).symm)]
  exact blk0_row hb hb' p1 q1 (bp := ind bp c) (bh := ind bh c)
    (fun i => by rw [ind0]; exact hP i) (fun j => by rw [ind0]; exact hH j) hσ hσm
    (fun w hw => by
      unfold blk; have h1 := (ind0 bp c (w / n)).mpr (hσb w hw).1
      have h2 := (ind0 bh c (w % n)).mpr (hσb w hw).2; rw [h1, h2]; simp)
    ((ind0 bp c i).mpr hi) hf _ (Or.inl rfl)

theorem rect_col (ha : a < n + k) (ha' : a' < n + k) (hb : b < n) (hb' : b' < n) (p1 : a ≠ a') (q1 : b ≠ b')
    (hP : ∀ i, bp i = c ↔ i = a ∨ i = a') (hH : ∀ j, bh j = c ↔ j = b ∨ j = b')
    {σ : List Nat} (hσ : σ.Nodup) (hσm : isMatch n σ = true) (hσb : ∀ w ∈ σ, bp (w / n) = c ∧ bh (w % n) = c)
    {j : Nat} (hj : bh j = c) (hf : ∀ w ∈ σ, w % n ≠ j) :
    locL n (Aw n a a' b b') σ (fun s => var n s j) (n + k) (fun s => bp s = c) = Aw n a a' b b' σ := by
  rw [locL_iff _ _ _ _ _ (fun t => ind bp c t = 0) (fun t => (ind0 bp c t).symm)]
  exact blk0_col ha ha' hb hb' p1 q1 (bp := ind bp c) (bh := ind bh c)
    (fun i => by rw [ind0]; exact hP i) (fun j => by rw [ind0]; exact hH j) hσ hσm
    (fun w hw => by
      unfold blk; have h1 := (ind0 bp c (w / n)).mpr (hσb w hw).1
      have h2 := (ind0 bh c (w % n)).mpr (hσb w hw).2; rw [h1, h2]; simp)
    ((ind0 bh c j).mpr hj) hf _ (Or.inl rfl)

end Rect

section Unit
variable {x h c : Nat} {bp bh : Nat → Nat}

theorem unit_row (hh : h < n) (hx : ∀ i, bp i = c ↔ i = x) (hhq : ∀ j, bh j = c ↔ j = h)
    {σ : List Nat} (hσb : ∀ w ∈ σ, bp (w / n) = c ∧ bh (w % n) = c) {i : Nat}
    (hi : bp i = c) (hf : ∀ w ∈ σ, w / n ≠ i) :
    locL n (fun _ => (1 : Int)) σ (var n i) n (fun t => bh t = c) = 1 := by
  have hσ : σ = [] := List.eq_nil_iff_forall_not_mem.mpr (fun w hw =>
    hf w hw (by rw [(hx _).mp (hσb w hw).1, (hx i).mp hi]))
  subst hσ; unfold locL
  rw [rsum1 hh _ hhq]; simp [isMatch_one]

theorem unit_col (hxl : x < n + k) (hx : ∀ i, bp i = c ↔ i = x) (hhq : ∀ j, bh j = c ↔ j = h)
    {σ : List Nat} (hσb : ∀ w ∈ σ, bp (w / n) = c ∧ bh (w % n) = c) {j : Nat}
    (hj : bh j = c) (hf : ∀ w ∈ σ, w % n ≠ j) :
    locL n (fun _ => (1 : Int)) σ (fun s => var n s j) (n + k) (fun s => bp s = c) = 1 := by
  have hσ : σ = [] := List.eq_nil_iff_forall_not_mem.mpr (fun w hw =>
    hf w hw (by rw [(hhq _).mp (hσb w hw).2, (hhq j).mp hj]))
  subst hσ; unfold locL
  rw [rsum1 hxl _ hx]; simp [isMatch_one]

end Unit

section Sym
variable {c : Nat} {bp bh : Nat → Nat}

theorem sym_rowD (p : Nat) (m D : Nat) (hn : 0 < n)
    (hm : rsum n (fun t => if bh t = c then 1 else 0) = (m : Int))
    {σ : List Nat} (hσ : σ.Nodup) (hσm : isMatch n σ = true) (hσb : ∀ w ∈ σ, bp (w / n) = c ∧ bh (w % n) = c)
    (hlen : σ.length < D) {i : Nat} (hf : ∀ w ∈ σ, w / n ≠ i) :
    (p : Int) ∣ locL n (cvf m D) σ (var n i) n (fun t => bh t = c) - cvf m D σ := by
  have e : ∀ t < n, (if bh t = c ∧ isMatch n (var n i t :: σ) = true then cvf m D (var n i t :: σ) else 0) =
      (if bh t = c ∧ ∀ w ∈ σ, w % n ≠ t then 1 else 0) * cv m D (σ.length + 1) := by
    intro t ht
    have key := match_row hσm ht hf
    by_cases h2 : ∀ w ∈ σ, w % n ≠ t
    · have h3 := key.mpr h2; by_cases h1 : bh t = c
      · rw [if_pos ⟨h1, h3⟩, if_pos ⟨h1, h2⟩]; simp [cvf]
      · rw [if_neg (fun h => h1 h.1), if_neg (fun h => h1 h.1)]; simp
    · have h3 : isMatch n (var n i t :: σ) = false := by
        cases h : isMatch n (var n i t :: σ)
        · rfl
        · exact absurd (key.mp h) h2
      rw [if_neg (fun h => by rw [h3] at h; exact absurd h.2 (by simp)), if_neg (fun h => h2 h.2)]; simp
  unfold locL
  rw [rsum_congr _ _ _ e, rsum_mulc, count_freeQ (fun t => bh t = c) (· % n) n σ (nodup_mod hσ hσm)
    (fun w hw => ⟨Nat.mod_lt _ hn, (hσb w hw).2⟩),
    hm, cvf, cv_step m D σ.length hlen]
  simp

theorem sym_colD (p : Nat) (m D : Nat) (hn : 0 < n)
    (hPm : (p : Int) ∣ rsum (n + k) (fun s => if bp s = c then 1 else 0) - m)
    {σ : List Nat} (hσ : σ.Nodup) (hσm : isMatch n σ = true)
    (hσb : ∀ w ∈ σ, (bp (w / n) = c ∧ bh (w % n) = c) ∧ w < (n + k) * n)
    (hlen : σ.length < D) {j : Nat} (hj : j < n) (hf : ∀ w ∈ σ, w % n ≠ j) :
    (p : Int) ∣ locL n (cvf m D) σ (fun s => var n s j) (n + k) (fun s => bp s = c) - cvf m D σ := by
  have e : ∀ t < n + k, (if bp t = c ∧ isMatch n (var n t j :: σ) = true then cvf m D (var n t j :: σ) else 0) =
      (if bp t = c ∧ ∀ w ∈ σ, w / n ≠ t then 1 else 0) * cv m D (σ.length + 1) := by
    intro t _
    have key := match_col (s := t) hσm hj hf
    by_cases h2 : ∀ w ∈ σ, w / n ≠ t
    · have h3 := key.mpr h2; by_cases h1 : bp t = c
      · rw [if_pos ⟨h1, h3⟩, if_pos ⟨h1, h2⟩]; simp [cvf]
      · rw [if_neg (fun h => h1 h.1), if_neg (fun h => h1 h.1)]; simp
    · have h3 : isMatch n (var n t j :: σ) = false := by
        cases h : isMatch n (var n t j :: σ)
        · rfl
        · exact absurd (key.mp h) h2
      rw [if_neg (fun h => by rw [h3] at h; exact absurd h.2 (by simp)), if_neg (fun h => h2 h.2)]; simp
  unfold locL
  rw [rsum_congr _ _ _ e, rsum_mulc, count_freeQ (fun t => bp t = c) (· / n) (n + k) σ (nodup_div hσ hσm)
    (fun w hw => ⟨(Nat.div_lt_iff_lt_mul hn).mpr (hσb w hw).2, (hσb w hw).1.1⟩),
    cvf, cv_step m D σ.length hlen]
  generalize rsum (n + k) (fun s => if bp s = c then 1 else 0) = P2 at hPm ⊢
  have : (P2 - σ.length) * cv m D (σ.length + 1) - ((m : Int) - σ.length) * cv m D (σ.length + 1) =
      (P2 - m) * cv m D (σ.length + 1) := by rw [← Int.sub_mul]; congr 1; omega
  rw [this]; exact Int.dvd_trans hPm (Int.dvd_mul_right _ _)

end Sym

end Programme.«20261027-0607-proof-complexity».LocWin
