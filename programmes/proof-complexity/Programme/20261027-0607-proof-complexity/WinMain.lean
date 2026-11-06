import Programme.«20261027-0607-proof-complexity».WinJ

/-!
# Windows for arbitrary rectangle data

`window`: for `p ∣ k`, `j ≤ d`, `2d + 1 ≤ n` and valid pigeon pairs `P`, hole pairs `Q` (`j` pairs
each, all points distinct), there is a `W` with `Bal p n k W W e` for every `e ≤ d` and
`W = (d-j+1)! · RP n j P Q` on canonical `j`-matchings. Blocks: the `j` rectangles, `n - j - d - 1`
fresh `1 × 1` blocks, and a rest block with `d - j + 1` holes carrying the symmetric design of
degree `d - j + 1` (value `(d-j+1)!` at `∅`).
-/

namespace Programme.«20261027-0607-proof-complexity».WinMain

open Programme.«20261025-0459-proof-complexity».OntoFPHP (rsum var rsum_add)
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (rsum_const)
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».SymDesign (cv ff)
open Programme.«20261027-0607-proof-complexity».LemK (VP)
open Programme.«20261027-0607-proof-complexity».SJ (RP allT fact)
open Programme.«20261027-0607-proof-complexity».Blocks
open Programme.«20261027-0607-proof-complexity».WinJ

def AA (j : Nat) (P : Nat → Nat × Nat) (X : Nat → Nat) (c : Nat) : Nat × Nat :=
  if c < j then P c else (X (c - j), X (c - j))

def pts (j : Nat) (P : Nat → Nat × Nat) : List Nat := (List.range j).flatMap (fun s => [(P s).1, (P s).2])

theorem mem_pts {j : Nat} {P : Nat → Nat × Nat} {x : Nat} : x ∈ pts j P ↔ ∃ s < j, x = (P s).1 ∨ x = (P s).2 := by
  unfold pts; simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]

theorem len_pts (j : Nat) (P : Nat → Nat × Nat) : (pts j P).length = 2 * j := by
  induction j with
  | zero => rfl
  | succ j ih => unfold pts at *; rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp; omega

theorem rsum21 (j : Nat) : ∀ T, rsum (j + T) (fun c => if c < j then (2 : Int) else 1) = 2 * j + T
  | 0 => by
    rw [Nat.add_zero, rsum_congr j _ (fun _ => 2) (fun c hc => by simp [hc]), rsum_const]; push_cast; omega
  | T + 1 => by
    rw [show j + (T + 1) = (j + T) + 1 by omega]; simp only [rsum]
    rw [rsum21 j T, if_neg (by omega)]; push_cast; omega

theorem disj_AA {j T M : Nat} {P : Nat → Nat × Nat} {X : Nat → Nat} (hP : VP M allT j P)
    (hX : ∀ t < T, X t < M ∧ X t ∉ pts j P) (hXi : ∀ t < T, ∀ t' < T, X t = X t' → t = t') :
    DisjA (j + T) (AA j P X) := by
  intro c hc c' hc' hne
  unfold AA
  by_cases h1 : c < j <;> by_cases h2 : c' < j <;> simp only [h1, h2, if_true, if_false]
  · have a := hP.2 c h1 c' h2 hne; have b := hP.2 c' h2 c h1 (Ne.symm hne)
    exact ⟨a.1, a.2.1, fun e => b.2.1 e.symm, a.2.2⟩
  · have := (hX (c' - j) (by omega)).2
    have m1 : (P c).1 ∈ pts j P := mem_pts.mpr ⟨c, h1, Or.inl rfl⟩
    have m2 : (P c).2 ∈ pts j P := mem_pts.mpr ⟨c, h1, Or.inr rfl⟩
    exact ⟨fun e => this (e ▸ m1), fun e => this (e ▸ m1), fun e => this (e ▸ m2), fun e => this (e ▸ m2)⟩
  · have := (hX (c - j) (by omega)).2
    have m1 : (P c').1 ∈ pts j P := mem_pts.mpr ⟨c', h2, Or.inl rfl⟩
    have m2 : (P c').2 ∈ pts j P := mem_pts.mpr ⟨c', h2, Or.inr rfl⟩
    exact ⟨fun e => this (e ▸ m1), fun e => this (e ▸ m2), fun e => this (e ▸ m1), fun e => this (e ▸ m2)⟩
  · have : X (c - j) ≠ X (c' - j) := fun e => hne (by have := hXi _ (by omega) _ (by omega) e; omega)
    exact ⟨this, this, this, this⟩

theorem cnt_AA {j T : Nat} {P : Nat → Nat × Nat} {X : Nat → Nat} (hP : ∀ s < j, (P s).1 ≠ (P s).2) :
    rsum (j + T) (fun c => if (AA j P X c).1 = (AA j P X c).2 then (1 : Int) else 2) = 2 * j + T := by
  rw [rsum_congr _ _ (fun c => if c < j then (2 : Int) else 1), rsum21]
  intro c _; unfold AA; by_cases h : c < j <;> simp [h, hP c]

theorem good_of {p n k j T : Nat} (hk : (p : Int) ∣ k) (hT : 2 * j + T ≤ n)
    {P Q : Nat → Nat × Nat} (hP : VP (n + k) allT j P) (hQ : VP n allT j Q) {X H : Nat → Nat}
    (hX : ∀ t < T, X t < n + k ∧ X t ∉ pts j P) (hXi : ∀ t < T, ∀ t' < T, X t = X t' → t = t')
    (hH : ∀ t < T, H t < n ∧ H t ∉ pts j Q) (hHi : ∀ t < T, ∀ t' < T, H t = H t' → t = t') :
    Good p n k j (j + T) (n - 2 * j - T) (AA j P X) (AA j Q H) := by
  have bA : ∀ c < j + T, (AA j P X c).1 < n + k ∧ (AA j P X c).2 < n + k := by
    intro c hc; unfold AA; by_cases h : c < j
    · simp only [h, if_true]; have := hP.1 c h; exact ⟨this.1, this.2.2.1⟩
    · simp only [h, if_false]; have := (hX (c - j) (by omega)).1; exact ⟨this, this⟩
  have bB : ∀ c < j + T, (AA j Q H c).1 < n ∧ (AA j Q H c).2 < n := by
    intro c hc; unfold AA; by_cases h : c < j
    · simp only [h, if_true]; have := hQ.1 c h; exact ⟨this.1, this.2.2.1⟩
    · simp only [h, if_false]; have := (hH (c - j) (by omega)).1; exact ⟨this, this⟩
  have rP : ∀ s < j, (P s).1 ≠ (P s).2 := fun s hs => (hP.1 s hs).2.2.2.2
  have rQ : ∀ s < j, (Q s).1 ≠ (Q s).2 := fun s hs => (hQ.1 s hs).2.2.2.2
  have dA := disj_AA hP hX hXi
  have dB := disj_AA hQ hH hHi
  refine ⟨by omega, bA, bB, dA, dB, fun c hc => ?_, fun c hc => ?_, fun c h1 _ => ?_, fun c h1 _ => ?_, ?_, ?_⟩
  · unfold AA; simp only [hc, if_true]; exact rP c hc
  · unfold AA; simp only [hc, if_true]; exact rQ c hc
  · unfold AA; simp [show ¬ c < j by omega]
  · unfold AA; simp [show ¬ c < j by omega]
  · rw [cnt_rest dB bB, cnt_AA rQ]; omega
  · rw [cnt_rest dA bA, cnt_AA rP]
    rw [show ((n + k : Nat) : Int) - (2 * j + T) - ((n - 2 * j - T : Nat) : Int) = k by omega]; exact hk

theorem ff_fact : ∀ m : Nat, ff (m : Int) m = (fact m : Int)
  | 0 => rfl
  | m + 1 => by
    simp only [ff, fact]
    rw [show ((m + 1 : Nat) : Int) - 1 = (m : Int) by omega, ff_fact m]; push_cast; rfl

/-- **Windows for rectangle data.** -/
theorem window {p n k d j : Nat} (hk : (p : Int) ∣ k) (hn : 2 * d + 1 ≤ n) (hj : j ≤ d)
    {P Q : Nat → Nat × Nat} (hP : VP (n + k) allT j P) (hQ : VP n allT j Q) :
    ∃ W : List Nat → Int, (∀ e ≤ d, Bal p n k W W e) ∧
      ∀ g, CM n k g → g.length = j → W g = (fact (d - j + 1) : Int) * RP n j P Q g := by
  let T := n - j - d - 1
  obtain ⟨X, hX, hXi⟩ := fresh_fn (pts j P) (n + k) T (by rw [len_pts]; omega)
  obtain ⟨H, hH, hHi⟩ := fresh_fn (pts j Q) n T (by rw [len_pts]; omega)
  have G := good_of (p := p) hk (by omega) hP hQ hX hXi hH hHi
  refine ⟨Wn n j (j + T) (n - 2 * j - T) (d - j + 1) (AA j P X) (AA j Q H), fun e he => ?_, fun g hg hl => ?_⟩
  · exact win_bal G (by omega) e (by omega)
  · rw [win_val (P := P) (Q := Q) G (fun c hc => by simp [AA, hc]) (fun c hc => by simp [AA, hc]) hg hl]
    congr 1
    unfold cv
    rw [show n - 2 * j - T = d - j + 1 by omega]
    rw [Nat.sub_zero, show ((d - j + 1 : Nat) : Int) - ((0 : Nat) : Int) = ((d - j + 1 : Nat) : Int) by omega]
    exact ff_fact _

end Programme.«20261027-0607-proof-complexity».WinMain
