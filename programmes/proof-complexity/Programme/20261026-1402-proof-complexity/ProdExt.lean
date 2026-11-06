import Programme.«20261026-1402-proof-complexity».ExtLin

/-!
# Block products and `Bal` (generic part of L2)

Pigeons and holes are split into three blocks by `bp`, `bh` (values `< 3`). An edge `v` lies in
block `blk v` (`3` for a cross edge). `Prod φ l` is `∏_c φ c (l ∩ block c)` if `l` has no cross
edge and `0` otherwise. Since an edge from a block-`b` pigeon to a hole outside block `b` is a
cross edge, the row (column) sum of `Prod φ` at a matching `g` factors as the local row (column)
sum of `φ b` at `g ∩ block b` times the other factors (`line_Prod`).

`bal_prod3`: with level-1 functions `R0`, `R1`, level-2 functions `Y0`, `Y1` (local extensions of
`R0`, `R1` in blocks 0, 1), a level-1 function `M2` with local line sums `≡ 1` in block 2 and the
level-0 function `emp`,
`Bal (Prod(R0,R1,M2) + Prod(Y0,R1,emp) + Prod(R0,Y1,emp)) (Prod(R0,R1,emp)) e` for every `e`.
-/

namespace Programme.«20261026-1402-proof-complexity».ProdExt

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero var_div var_mod)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt var_decode)
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ExtLin

variable {n k : Nat}

/-- Membership-invariant functions on duplicate-free lists. -/
def SL (φ : List Nat → Int) : Prop :=
  ∀ l l' : List Nat, l.Nodup → l'.Nodup → (∀ x, x ∈ l ↔ x ∈ l') → φ l = φ l'

/-- `φ` vanishes off lists of length `ℓ`. -/
def Hom (φ : List Nat → Int) (ℓ : Nat) : Prop := ∀ l : List Nat, l.length ≠ ℓ → φ l = 0

section Blocks

variable (bp bh : Nat → Nat) (n : Nat)

def blk (v : Nat) : Nat := if bp (v / n) = bh (v % n) then bp (v / n) else 3

def fl (c : Nat) (l : List Nat) : List Nat := l.filter (fun v => blk bp bh n v == c)

def okL (l : List Nat) : Bool := l.all (fun v => decide (blk bp bh n v < 3))

def Prod (φ : Nat → List Nat → Int) (l : List Nat) : Int :=
  if okL bp bh n l then φ 0 (fl bp bh n 0 l) * φ 1 (fl bp bh n 1 l) * φ 2 (fl bp bh n 2 l) else 0

def oth (φ : Nat → List Nat → Int) (b : Nat) (g : List Nat) : Int :=
  (if b = 0 then 1 else φ 0 (fl bp bh n 0 g)) * (if b = 1 then 1 else φ 1 (fl bp bh n 1 g)) *
    (if b = 2 then 1 else φ 2 (fl bp bh n 2 g))

end Blocks

theorem fl_nodup (bp bh : Nat → Nat) (n c : Nat) {l : List Nat} (h : l.Nodup) : (fl bp bh n c l).Nodup :=
  (List.filter_sublist).nodup h

theorem mem_fl (bp bh : Nat → Nat) (n c : Nat) (l : List Nat) (x : Nat) :
    x ∈ fl bp bh n c l ↔ x ∈ l ∧ blk bp bh n x = c := by
  simp [fl]

theorem SL_Prod (bp bh : Nat → Nat) (n : Nat) (φ : Nat → List Nat → Int) (hφ : ∀ c, SL (φ c)) :
    SL (Prod bp bh n φ) := by
  intro l l' hl hl' hm
  have hok : okL bp bh n l = okL bp bh n l' := by
    unfold okL
    cases h1 : l.all (fun v => decide (blk bp bh n v < 3)) <;>
    cases h2 : l'.all (fun v => decide (blk bp bh n v < 3)) <;> try rfl
    · simp only [List.all_eq_true, List.all_eq_false, decide_eq_true_eq] at h1 h2
      obtain ⟨x, hx, hx'⟩ := h1; exact absurd (h2 x ((hm x).mp hx)) hx'
    · simp only [List.all_eq_true, List.all_eq_false, decide_eq_true_eq] at h1 h2
      obtain ⟨x, hx, hx'⟩ := h2; exact absurd (h1 x ((hm x).mpr hx)) hx'
  have e : ∀ c, φ c (fl bp bh n c l) = φ c (fl bp bh n c l') := fun c =>
    hφ c _ _ (fl_nodup bp bh n c hl) (fl_nodup bp bh n c hl') (fun x => by
      rw [mem_fl, mem_fl, hm x])
  unfold Prod; rw [hok, e 0, e 1, e 2]

theorem blk_var (bp bh : Nat → Nat) {i j : Nat} (hj : j < n) :
    blk bp bh n (var n i j) = if bp i = bh j then bp i else 3 := by
  unfold blk; rw [var_div n i j hj, var_mod n i j hj]

/-- A matching stays a matching after adding an edge of block `b` iff it does inside block `b`. -/
theorem match_fl (bp bh : Nat → Nat) {g : List Nat} {w : Nat} {b : Nat} (hb : b < 3)
    (hg : isMatch n g = true) (hok : okL bp bh n g = true) (hw : blk bp bh n w = b) :
    isMatch n (w :: g) = isMatch n (w :: fl bp bh n b g) := by
  have sub : ∀ x, x ∈ w :: fl bp bh n b g → x ∈ w :: g := by
    intro x hx; simp only [List.mem_cons, mem_fl] at hx ⊢
    rcases hx with h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  cases h1 : isMatch n (w :: g) <;> cases h2 : isMatch n (w :: fl bp bh n b g) <;> try rfl
  · -- right true, left false
    exfalso
    obtain ⟨u, hu, v, hv, hc⟩ := not_match h1
    rw [isMatch_iff] at h2
    have hg' := (isMatch_iff n g).mp hg
    have hok' : ∀ x ∈ g, blk bp bh n x < 3 := by
      intro x hx; unfold okL at hok; simp only [List.all_eq_true, decide_eq_true_eq] at hok
      exact hok x hx
    -- cross pair w, x with blk x ≠ b
    have cross : ∀ x ∈ g, blk bp bh n x ≠ b → cfl n w x = false := by
      intro x hx hxb
      have hx3 := hok' x hx
      unfold blk at hw hx3 hxb
      unfold cfl
      have hb3 : b < 3 := hb
      by_cases e1 : bp (w / n) = bh (w % n) <;> by_cases e2 : bp (x / n) = bh (x % n) <;>
        simp only [e1, e2, if_true, if_false] at hw hx3 hxb <;> try omega
      have q1 : w / n ≠ x / n := fun h => hxb (by rw [← e2, ← h, e1]; exact hw)
      have q2 : w % n ≠ x % n := fun h => hxb (by rw [← h]; exact hw)
      simp [q1, q2]
    simp only [List.mem_cons] at hu hv
    have hm : w ∈ w :: fl bp bh n b g := List.mem_cons_self
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · rw [hu, hv] at hc; exact absurd (h2 w hm w hm) (by simp [hc])
    · rw [hu] at hc
      by_cases hvb : blk bp bh n v = b
      · have := h2 w hm v (List.mem_cons_of_mem _ ((mem_fl ..).mpr ⟨hv, hvb⟩))
        simp [hc] at this
      · have := cross v hv hvb; simp [hc] at this
    · rw [hv] at hc
      by_cases hub : blk bp bh n u = b
      · have := h2 u (List.mem_cons_of_mem _ ((mem_fl ..).mpr ⟨hu, hub⟩)) w hm
        simp [hc] at this
      · have := cross u hu hub; rw [cfl_symm] at this; simp [hc] at this
    · have := hg' u hu v hv; simp [hc] at this
  · exfalso
    rw [isMatch_iff] at h1
    obtain ⟨u, hu, v, hv, hc⟩ := not_match h2
    have := h1 u (sub u hu) v (sub v hv); simp [hc] at this

theorem rsum_mulr (M : Nat) (f : Nat → Int) (c : Int) : rsum M (fun j => f j * c) = rsum M f * c := by
  induction M with
  | zero => simp [rsum]
  | succ M ih => simp only [rsum]; rw [ih, Int.add_mul]

/-- **Factorisation of line sums of a block product.** `v t` (`t < M`) are edges not in `g`;
`Q t` says `v t` lies in block `b`, otherwise it is a cross edge. -/
theorem line_Prod (bp bh : Nat → Nat) (φ : Nat → List Nat → Int) (hφ : ∀ c, SL (φ c))
    {g : List Nat} (hg : CM n k g) (v : Nat → Nat) (M b : Nat) (hb : b < 3) (Q : Nat → Prop)
    [DecidablePred Q] (hv : ∀ t < M, v t < (n + k) * n ∧ v t ∉ g)
    (hQ : ∀ t < M, blk bp bh n (v t) = if Q t then b else 3) :
    lineS n k (Prod bp bh n φ) g v M =
      if okL bp bh n g then
        rsum M (fun t => if Q t ∧ isMatch n (v t :: fl bp bh n b g) = true then
          φ b (v t :: fl bp bh n b g) else 0) * oth bp bh n φ b g
      else 0 := by
  unfold lineS
  have hcan : ∀ t < M, Prod bp bh n φ (canon ((n + k) * n) (v t :: g)) = Prod bp bh n φ (v t :: g) := by
    intro t ht
    obtain ⟨h1, h2⟩ := hv t ht
    apply SL_Prod bp bh n φ hφ _ _ (canon_nodup _ _) (List.nodup_cons.mpr ⟨h2, CM_nodup hg⟩)
    intro x; rw [mem_canon]; simp only [List.mem_cons]
    constructor
    · exact fun h => h.1
    · intro h; refine ⟨h, ?_⟩; rcases h with rfl | h
      · exact h1
      · exact CM_lt hg h
  rw [rsum_congr _ _ _ (fun t ht => by rw [hcan t ht])]
  split
  · rename_i hok
    rw [← rsum_mulr]
    apply rsum_congr; intro t ht
    have hq := hQ t ht
    by_cases hqt : Q t
    · simp only [hqt, if_true] at hq
      rw [match_fl bp bh hb hg.2 hok hq]
      simp only [hqt, true_and]
      split
      · unfold Prod oth
        have hok' : okL bp bh n (v t :: g) = true := by
          unfold okL at hok ⊢; simp only [List.all_cons, hok, Bool.and_true, decide_eq_true_eq]; omega
        rw [if_pos hok']
        have e : ∀ c, fl bp bh n c (v t :: g) = if b = c then v t :: fl bp bh n c g else fl bp bh n c g := by
          intro c; unfold fl; simp only [List.filter_cons, hq]; by_cases h : b = c <;> simp [h]
        rw [e 0, e 1, e 2]
        rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;> simp <;> grind
      · simp
    · simp only [hqt, if_false] at hq
      simp only [hqt, false_and, if_false, Int.zero_mul]
      unfold Prod
      have : okL bp bh n (v t :: g) = false := by
        unfold okL; simp [hq]
      simp [this]
  · rename_i hok
    apply rsum_zero; intro t ht
    unfold Prod
    have : okL bp bh n (v t :: g) = false := by
      unfold okL at hok ⊢; simp only [List.all_cons, Bool.and_eq_false_iff]; right; simpa using hok
    simp [this]


/-! ## Local line sums and the three-block theorem -/

/-- Local line sum of `φ` at `g'` along `v`, restricted to the `t` with `Q t`. -/
def locL (n : Nat) (φ : List Nat → Int) (g' : List Nat) (v : Nat → Nat) (M : Nat) (Q : Nat → Prop)
    [DecidablePred Q] : Int :=
  rsum M (fun t => if Q t ∧ isMatch n (v t :: g') = true then φ (v t :: g') else 0)

theorem locL_hom {φ : List Nat → Int} {ℓ : Nat} (h : Hom φ ℓ) (g' : List Nat) (v : Nat → Nat) (M : Nat)
    (Q : Nat → Prop) [DecidablePred Q] (hl : g'.length + 1 ≠ ℓ) : locL n φ g' v M Q = 0 := by
  apply rsum_zero; intro t _; split
  · exact h _ (by simpa using hl)
  · rfl

/-- Three-factor table. -/
def tri (A B C : List Nat → Int) : Nat → List Nat → Int
  | 0 => A
  | 1 => B
  | _ => C

theorem SL_tri {A B C : List Nat → Int} (hA : SL A) (hB : SL B) (hC : SL C) : ∀ c, SL (tri A B C c)
  | 0 => hA
  | 1 => hB
  | _ + 2 => hC

theorem dvd_lin3 {p A B C X Y Z E : Int} (h1 : p ∣ A) (h2 : p ∣ B) (h3 : p ∣ C)
    (e : E = A * X + B * Y + C * Z) : p ∣ E := by
  rw [e]
  have m : ∀ {A : Int} (X : Int), p ∣ A → p ∣ A * X := fun X h => Int.dvd_trans h (Int.dvd_mul_right _ X)
  exact Int.dvd_add (Int.dvd_add (m _ h1) (m _ h2)) (m _ h3)

/-- The case analysis on the block of the line, abstract in the local line-sum operator `L`. -/
theorem core (p : Int) (b : Nat) (hb : b < 3) (R0 Y0 R1 Y1 M2 E : List Nat → Int)
    (L : (List Nat → Int) → List Nat → Int) (G : Nat → List Nat)
    (h0 : b = 0 → p ∣ L R0 (G 0) ∧ p ∣ L Y0 (G 0) - R0 (G 0))
    (h1 : b = 1 → p ∣ L R1 (G 1) ∧ p ∣ L Y1 (G 1) - R1 (G 1))
    (h2 : b = 2 → p ∣ L M2 (G 2) - E (G 2) ∧ L E (G 2) = 0) :
    let o := fun (φ : Nat → List Nat → Int) =>
      (if b = 0 then 1 else φ 0 (G 0)) * (if b = 1 then 1 else φ 1 (G 1)) * (if b = 2 then 1 else φ 2 (G 2))
    p ∣ L (tri R0 R1 M2 b) (G b) * o (tri R0 R1 M2) + L (tri Y0 R1 E b) (G b) * o (tri Y0 R1 E) +
        L (tri R0 Y1 E b) (G b) * o (tri R0 Y1 E) - R0 (G 0) * R1 (G 1) * E (G 2) := by
  intro o
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl
  · obtain ⟨a1, a2⟩ := h0 rfl
    simp only [o, tri, if_true]
    exact dvd_lin3 a1 a2 a1 (X := R1 (G 1) * M2 (G 2)) (Y := R1 (G 1) * E (G 2)) (Z := Y1 (G 1) * E (G 2))
      (by simp; grind)
  · obtain ⟨a1, a2⟩ := h1 rfl
    simp only [o, tri, if_true]
    exact dvd_lin3 a1 a1 a2 (X := R0 (G 0) * M2 (G 2)) (Y := Y0 (G 0) * E (G 2)) (Z := R0 (G 0) * E (G 2))
      (by simp; grind)
  · obtain ⟨a1, a2⟩ := h2 rfl
    simp only [o, tri, if_true]
    rw [a2]
    exact dvd_lin3 a1 (Int.dvd_zero p) (Int.dvd_zero p) (X := R0 (G 0) * R1 (G 1)) (Y := 0) (Z := 0)
      (by simp; grind)

theorem len_one {l : List Nat} (h : l.length = 1) : ∃ e, l = [e] := by
  match l, h with
  | [e], _ => exact ⟨e, rfl⟩

/-- **Three-block extension.** -/
theorem bal_prod3 (p : Nat) (bp bh : Nat → Nat) (hbp : ∀ i, bp i < 3) (hbh : ∀ j, bh j < 3)
    (R0 Y0 R1 Y1 M2 E : List Nat → Int)
    (sR0 : SL R0) (sY0 : SL Y0) (sR1 : SL R1) (sY1 : SL Y1) (sM2 : SL M2) (sE : SL E)
    (oR0 : Hom R0 1) (oY0 : Hom Y0 2) (oR1 : Hom R1 1) (oY1 : Hom Y1 2) (oM2 : Hom M2 1) (oE : Hom E 0)
    (hE : E [] = 1)
    (rR0 : ∀ i < n + k, bp i = 0 → (p : Int) ∣ locL n R0 [] (var n i) n (fun t => bh t = 0))
    (cR0 : ∀ j < n, bh j = 0 → (p : Int) ∣ locL n R0 [] (fun s => var n s j) (n + k) (fun s => bp s = 0))
    (rR1 : ∀ i < n + k, bp i = 1 → (p : Int) ∣ locL n R1 [] (var n i) n (fun t => bh t = 1))
    (cR1 : ∀ j < n, bh j = 1 → (p : Int) ∣ locL n R1 [] (fun s => var n s j) (n + k) (fun s => bp s = 1))
    (rY0 : ∀ e < (n + k) * n, blk bp bh n e = 0 → ∀ i < n + k, bp i = 0 → e / n ≠ i →
      (p : Int) ∣ locL n Y0 [e] (var n i) n (fun t => bh t = 0) - R0 [e])
    (cY0 : ∀ e < (n + k) * n, blk bp bh n e = 0 → ∀ j < n, bh j = 0 → e % n ≠ j →
      (p : Int) ∣ locL n Y0 [e] (fun s => var n s j) (n + k) (fun s => bp s = 0) - R0 [e])
    (rY1 : ∀ e < (n + k) * n, blk bp bh n e = 1 → ∀ i < n + k, bp i = 1 → e / n ≠ i →
      (p : Int) ∣ locL n Y1 [e] (var n i) n (fun t => bh t = 1) - R1 [e])
    (cY1 : ∀ e < (n + k) * n, blk bp bh n e = 1 → ∀ j < n, bh j = 1 → e % n ≠ j →
      (p : Int) ∣ locL n Y1 [e] (fun s => var n s j) (n + k) (fun s => bp s = 1) - R1 [e])
    (rM2 : ∀ i < n + k, bp i = 2 → (p : Int) ∣ locL n M2 [] (var n i) n (fun t => bh t = 2) - 1)
    (cM2 : ∀ j < n, bh j = 2 → (p : Int) ∣ locL n M2 [] (fun s => var n s j) (n + k) (fun s => bp s = 2) - 1)
    (e : Nat) :
    Bal p n k (fun g => Prod bp bh n (tri R0 R1 M2) g + Prod bp bh n (tri Y0 R1 E) g +
      Prod bp bh n (tri R0 Y1 E) g) (Prod bp bh n (tri R0 R1 E)) e := by
  intro g hg _
  have hφ1 := SL_tri sR0 sR1 sM2
  have hφ2 := SL_tri sY0 sR1 sE
  have hφ3 := SL_tri sR0 sY1 sE
  have hlen : ∀ c, ∀ x ∈ fl bp bh n c g, x ∈ g ∧ blk bp bh n x = c := fun c x hx => (mem_fl ..).mp hx
  -- generic line: v, M, Q, b
  have line : ∀ (v : Nat → Nat) (M b : Nat) (Q : Nat → Prop) [DecidablePred Q], b < 3 →
      (∀ t < M, v t < (n + k) * n ∧ v t ∉ g) → (∀ t < M, blk bp bh n (v t) = if Q t then b else 3) →
      (b = 0 → (p : Int) ∣ locL n R0 (fl bp bh n 0 g) v M Q ∧
        (p : Int) ∣ locL n Y0 (fl bp bh n 0 g) v M Q - R0 (fl bp bh n 0 g)) →
      (b = 1 → (p : Int) ∣ locL n R1 (fl bp bh n 1 g) v M Q ∧
        (p : Int) ∣ locL n Y1 (fl bp bh n 1 g) v M Q - R1 (fl bp bh n 1 g)) →
      (b = 2 → (p : Int) ∣ locL n M2 (fl bp bh n 2 g) v M Q - E (fl bp bh n 2 g) ∧
        locL n E (fl bp bh n 2 g) v M Q = 0) →
      (p : Int) ∣ lineS n k (fun g => Prod bp bh n (tri R0 R1 M2) g + Prod bp bh n (tri Y0 R1 E) g +
        Prod bp bh n (tri R0 Y1 E) g) g v M - Prod bp bh n (tri R0 R1 E) g := by
    intro v M b Q _ hb hv hQ h0 h1 h2
    rw [lineS_add, lineS_add, line_Prod bp bh _ hφ1 hg v M b hb Q hv hQ,
      line_Prod bp bh _ hφ2 hg v M b hb Q hv hQ, line_Prod bp bh _ hφ3 hg v M b hb Q hv hQ]
    unfold Prod
    split
    · have := core p b hb R0 Y0 R1 Y1 M2 E (fun φ G => locL n φ G v M Q) (fun c => fl bp bh n c g)
        h0 h1 h2
      simp only at this
      unfold oth; unfold locL at this
      rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;> simpa [tri] using this
    · simp
  -- strong local facts
  have sA : ∀ (R : List Nat → Int), Hom R 1 → ∀ (c : Nat) (v : Nat → Nat) (M : Nat) (Q : Nat → Prop)
      [DecidablePred Q], (p : Int) ∣ locL n R [] v M Q → (p : Int) ∣ locL n R (fl bp bh n c g) v M Q := by
    intro R hR c v M Q _ h
    by_cases h0 : (fl bp bh n c g).length = 0
    · rw [List.length_eq_zero_iff.mp h0]; exact h
    · rw [locL_hom hR _ v M Q (by omega)]; exact Int.dvd_zero _
  have sB : ∀ (R Y : List Nat → Int), Hom R 1 → Hom Y 2 → ∀ (c : Nat) (v : Nat → Nat) (M : Nat)
      (Q : Nat → Prop) [DecidablePred Q],
      (∀ x, x ∈ g → blk bp bh n x = c → (p : Int) ∣ locL n Y [x] v M Q - R [x]) →
      (p : Int) ∣ locL n Y (fl bp bh n c g) v M Q - R (fl bp bh n c g) := by
    intro R Y hR hY c v M Q _ h
    by_cases h1 : (fl bp bh n c g).length = 1
    · obtain ⟨x, hx⟩ := len_one h1
      have := hlen c x (by rw [hx]; exact List.mem_singleton_self x)
      rw [hx]; exact h x this.1 this.2
    · rw [locL_hom hY _ v M Q (by omega), hR _ h1]; exact Int.dvd_zero _
  have sC : ∀ (v : Nat → Nat) (M : Nat) (Q : Nat → Prop) [DecidablePred Q],
      (p : Int) ∣ locL n M2 [] v M Q - 1 →
      (p : Int) ∣ locL n M2 (fl bp bh n 2 g) v M Q - E (fl bp bh n 2 g) ∧ locL n E (fl bp bh n 2 g) v M Q = 0 := by
    intro v M Q _ h
    refine ⟨?_, locL_hom oE _ v M Q (by omega)⟩
    by_cases h0 : (fl bp bh n 2 g).length = 0
    · rw [List.length_eq_zero_iff.mp h0, hE]; exact h
    · rw [locL_hom oM2 _ v M Q (by omega), oE _ h0]; exact Int.dvd_zero _
  refine ⟨fun i hi hf => ?_, fun j hj hf => ?_⟩
  · unfold rowS
    have hb := hbp i
    apply line (var n i) n (bp i) (fun t => bh t = bp i) hb
      (fun t ht => ⟨var_lt n k i t hi ht, notin_of_pfree hf t ht⟩)
      (fun t ht => by rw [blk_var bp bh ht]; by_cases h : bp i = bh t <;> simp [h, eq_comm])
    · intro h0; rw [h0]
      exact ⟨sA R0 oR0 0 _ _ _ (rR0 i hi h0), sB R0 Y0 oR0 oY0 0 _ _ _ (fun x hx hb0 =>
        rY0 x (CM_lt hg hx) hb0 i hi h0 (fun e => hf x hx e))⟩
    · intro h0; rw [h0]
      exact ⟨sA R1 oR1 1 _ _ _ (rR1 i hi h0), sB R1 Y1 oR1 oY1 1 _ _ _ (fun x hx hb0 =>
        rY1 x (CM_lt hg hx) hb0 i hi h0 (fun e => hf x hx e))⟩
    · intro h0; rw [h0]; exact sC _ _ _ (rM2 i hi h0)
  · unfold colS
    have hb := hbh j
    apply line (fun s => var n s j) (n + k) (bh j) (fun s => bp s = bh j) hb
      (fun t ht => ⟨var_lt n k t j ht hj, notin_of_hfree hf t hj⟩)
      (fun t ht => by rw [blk_var bp bh hj]; by_cases h : bp t = bh j <;> simp [h])
    · intro h0; rw [h0]
      exact ⟨sA R0 oR0 0 _ _ _ (cR0 j hj h0), sB R0 Y0 oR0 oY0 0 _ _ _ (fun x hx hb0 =>
        cY0 x (CM_lt hg hx) hb0 j hj h0 (fun e => hf x hx e))⟩
    · intro h0; rw [h0]
      exact ⟨sA R1 oR1 1 _ _ _ (cR1 j hj h0), sB R1 Y1 oR1 oY1 1 _ _ _ (fun x hx hb0 =>
        cY1 x (CM_lt hg hx) hb0 j hj h0 (fun e => hf x hx e))⟩
    · intro h0; rw [h0]; exact sC _ _ _ (cM2 j hj h0)

end Programme.«20261026-1402-proof-complexity».ProdExt
