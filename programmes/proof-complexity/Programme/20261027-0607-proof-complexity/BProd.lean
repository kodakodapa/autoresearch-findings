import Programme.«20261027-0607-proof-complexity».Flag

/-!
# Block products with `B` blocks

Pigeons and holes are split into blocks `0, …, B-1` by `bp`, `bh` (values `< B`). An edge `v` lies
in block `blkB v` (`B` for a cross edge). `PB φ l = ∏_{c<B} φ c (l ∩ block c)` if `l` has no cross
edge, `0` otherwise. As for three blocks (`ProdExt.line_Prod`), the row (column) sum of `PB φ`
at a matching `g` factors as the local line sum in the block of the line times the other factors
(`line_PB`). `bal_winB`: `PB φ` is a window at level `e` (`Bal (PB φ) (PB φ) e`) as soon as, for
every free line, either the local window identity holds in its block, or some other factor
vanishes at `g`.
-/

namespace Programme.«20261027-0607-proof-complexity».BProd

open Programme.«20261025-0459-proof-complexity».OntoFPHP (rsum var)
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero var_div var_mod)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt var_decode)
open Programme.«20261025-1627-proof-complexity».MomGen (canon mem_canon canon_nodup)
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ProdExt (SL locL rsum_mulr)
open Programme.«20261027-0607-proof-complexity».LemK (rprod rprod_congr rprod_zero)

section Blocks

variable (B : Nat) (bp bh : Nat → Nat) (n : Nat)

def blkB (v : Nat) : Nat := if bp (v / n) = bh (v % n) then bp (v / n) else B

def flB (c : Nat) (l : List Nat) : List Nat := l.filter (fun v => blkB B bp bh n v == c)

def okB (l : List Nat) : Bool := l.all (fun v => decide (blkB B bp bh n v < B))

def PB (φ : Nat → List Nat → Int) (l : List Nat) : Int :=
  if okB B bp bh n l then rprod B (fun c => φ c (flB B bp bh n c l)) else 0

def othB (φ : Nat → List Nat → Int) (b : Nat) (g : List Nat) : Int :=
  rprod B (fun c => if c = b then 1 else φ c (flB B bp bh n c g))

end Blocks

theorem rprod_split (f : Nat → Int) : ∀ (B b : Nat), b < B →
    rprod B f = f b * rprod B (fun c => if c = b then 1 else f c)
  | 0, _, h => absurd h (by omega)
  | B + 1, b, h => by
    simp only [rprod]
    by_cases hb : b = B
    · subst hb
      rw [rprod_congr b (fun c => if c = b then 1 else f c) f (fun s hs => by rw [if_neg (by omega)])]
      simp [Int.mul_comm]
    · rw [rprod_split f B b (by omega), if_neg (Ne.symm hb)]
      simp only [Int.mul_assoc]

theorem flB_nodup (B : Nat) (bp bh : Nat → Nat) (n c : Nat) {l : List Nat} (h : l.Nodup) :
    (flB B bp bh n c l).Nodup :=
  (List.filter_sublist).nodup h

theorem mem_flB (B : Nat) (bp bh : Nat → Nat) (n c : Nat) (l : List Nat) (x : Nat) :
    x ∈ flB B bp bh n c l ↔ x ∈ l ∧ blkB B bp bh n x = c := by
  simp [flB]

theorem SL_PB (B : Nat) (bp bh : Nat → Nat) (n : Nat) (φ : Nat → List Nat → Int) (hφ : ∀ c, SL (φ c)) :
    SL (PB B bp bh n φ) := by
  intro l l' hl hl' hm
  have hok : okB B bp bh n l = okB B bp bh n l' := by
    unfold okB
    cases h1 : l.all (fun v => decide (blkB B bp bh n v < B)) <;>
    cases h2 : l'.all (fun v => decide (blkB B bp bh n v < B)) <;> try rfl
    · simp only [List.all_eq_true, List.all_eq_false, decide_eq_true_eq] at h1 h2
      obtain ⟨x, hx, hx'⟩ := h1; exact absurd (h2 x ((hm x).mp hx)) hx'
    · simp only [List.all_eq_true, List.all_eq_false, decide_eq_true_eq] at h1 h2
      obtain ⟨x, hx, hx'⟩ := h2; exact absurd (h1 x ((hm x).mpr hx)) hx'
  have e : ∀ c, φ c (flB B bp bh n c l) = φ c (flB B bp bh n c l') := fun c =>
    hφ c _ _ (flB_nodup B bp bh n c hl) (flB_nodup B bp bh n c hl') (fun x => by
      rw [mem_flB, mem_flB, hm x])
  unfold PB; rw [hok, rprod_congr B _ _ (fun c _ => e c)]

theorem blkB_var (B : Nat) (bp bh : Nat → Nat) {n i j : Nat} (hj : j < n) :
    blkB B bp bh n (var n i j) = if bp i = bh j then bp i else B := by
  unfold blkB; rw [var_div n i j hj, var_mod n i j hj]

/-- A matching stays a matching after adding an edge of block `b` iff it does inside block `b`. -/
theorem match_flB (B : Nat) (bp bh : Nat → Nat) {n : Nat} {g : List Nat} {w : Nat} {b : Nat} (hb : b < B)
    (hg : isMatch n g = true) (hok : okB B bp bh n g = true) (hw : blkB B bp bh n w = b) :
    isMatch n (w :: g) = isMatch n (w :: flB B bp bh n b g) := by
  have sub : ∀ x, x ∈ w :: flB B bp bh n b g → x ∈ w :: g := by
    intro x hx; simp only [List.mem_cons, mem_flB] at hx ⊢
    rcases hx with h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  cases h1 : isMatch n (w :: g) <;> cases h2 : isMatch n (w :: flB B bp bh n b g) <;> try rfl
  · exfalso
    obtain ⟨u, hu, v, hv, hc⟩ := not_match h1
    rw [isMatch_iff] at h2
    have hg' := (isMatch_iff n g).mp hg
    have hok' : ∀ x ∈ g, blkB B bp bh n x < B := by
      intro x hx; unfold okB at hok; simp only [List.all_eq_true, decide_eq_true_eq] at hok
      exact hok x hx
    have cross : ∀ x ∈ g, blkB B bp bh n x ≠ b → cfl n w x = false := by
      intro x hx hxb
      have hx3 := hok' x hx
      unfold blkB at hw hx3 hxb
      unfold cfl
      by_cases e1 : bp (w / n) = bh (w % n) <;> by_cases e2 : bp (x / n) = bh (x % n) <;>
        simp only [e1, e2, if_true, if_false] at hw hx3 hxb <;> try omega
      have q1 : w / n ≠ x / n := fun h => hxb (by rw [← e2, ← h, e1]; exact hw)
      have q2 : w % n ≠ x % n := fun h => hxb (by rw [← h]; exact hw)
      simp [q1, q2]
    simp only [List.mem_cons] at hu hv
    have hm : w ∈ w :: flB B bp bh n b g := List.mem_cons_self
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · rw [hu, hv] at hc; exact absurd (h2 w hm w hm) (by simp [hc])
    · rw [hu] at hc
      by_cases hvb : blkB B bp bh n v = b
      · have := h2 w hm v (List.mem_cons_of_mem _ ((mem_flB ..).mpr ⟨hv, hvb⟩))
        simp [hc] at this
      · have := cross v hv hvb; simp [hc] at this
    · rw [hv] at hc
      by_cases hub : blkB B bp bh n u = b
      · have := h2 u (List.mem_cons_of_mem _ ((mem_flB ..).mpr ⟨hu, hub⟩)) w hm
        simp [hc] at this
      · have := cross u hu hub; rw [cfl_symm] at this; simp [hc] at this
    · have := hg' u hu v hv; simp [hc] at this
  · exfalso
    rw [isMatch_iff] at h1
    obtain ⟨u, hu, v, hv, hc⟩ := not_match h2
    have := h1 u (sub u hu) v (sub v hv); simp [hc] at this

theorem PB_fac (B : Nat) (bp bh : Nat → Nat) (n : Nat) (φ : Nat → List Nat → Int) (g : List Nat)
    {b : Nat} (hb : b < B) :
    PB B bp bh n φ g = if okB B bp bh n g then φ b (flB B bp bh n b g) * othB B bp bh n φ b g else 0 := by
  unfold PB othB; split
  · rw [rprod_split _ B b hb]
  · rfl

/-- **Factorisation of line sums of a block product.** -/
theorem line_PB (B : Nat) (bp bh : Nat → Nat) (φ : Nat → List Nat → Int) (hφ : ∀ c, SL (φ c))
    {n k : Nat} {g : List Nat} (hg : CM n k g) (v : Nat → Nat) (M b : Nat) (hb : b < B) (Q : Nat → Prop)
    [DecidablePred Q] (hv : ∀ t < M, v t < (n + k) * n ∧ v t ∉ g)
    (hQ : ∀ t < M, blkB B bp bh n (v t) = if Q t then b else B) :
    lineS n k (PB B bp bh n φ) g v M =
      if okB B bp bh n g then
        locL n (φ b) (flB B bp bh n b g) v M Q * othB B bp bh n φ b g
      else 0 := by
  unfold lineS locL
  have hcan : ∀ t < M, PB B bp bh n φ (canon ((n + k) * n) (v t :: g)) = PB B bp bh n φ (v t :: g) := by
    intro t ht
    obtain ⟨h1, h2⟩ := hv t ht
    apply SL_PB B bp bh n φ hφ _ _ (canon_nodup _ _) (List.nodup_cons.mpr ⟨h2, CM_nodup hg⟩)
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
      rw [match_flB B bp bh hb hg.2 hok hq]
      simp only [hqt, true_and]
      split
      · have hok' : okB B bp bh n (v t :: g) = true := by
          unfold okB at hok ⊢; simp only [List.all_cons, hok, Bool.and_true, decide_eq_true_eq]; omega
        rw [PB_fac B bp bh n φ _ hb, if_pos hok']
        have e : ∀ c, flB B bp bh n c (v t :: g) = if b = c then v t :: flB B bp bh n c g else flB B bp bh n c g := by
          intro c; unfold flB; simp only [List.filter_cons, hq]; by_cases h : b = c <;> simp [h]
        rw [e b, if_pos rfl]
        congr 1
        unfold othB; apply rprod_congr; intro c _
        by_cases hc : c = b
        · simp [hc]
        · rw [if_neg hc, if_neg hc, e c, if_neg (Ne.symm hc)]
      · simp
    · simp only [hqt, if_false] at hq
      simp only [hqt, false_and, if_false, Int.zero_mul]
      unfold PB
      have : okB B bp bh n (v t :: g) = false := by
        unfold okB; simp [hq]
      simp [this]
  · rename_i hok
    apply rsum_zero; intro t ht
    unfold PB
    have : okB B bp bh n (v t :: g) = false := by
      unfold okB at hok ⊢; simp only [List.all_cons, Bool.and_eq_false_iff]; right; simpa using hok
    simp [this]

/-- **Window products with `B` blocks.** For every free line of a canonical `e`-matching `g` with no
cross edge: either some other factor vanishes at `g` (`othB = 0`), or the factor of the line's block
satisfies the local window identity. Then `PB φ` is a window at level `e`. -/
theorem bal_winB (p B : Nat) (bp bh : Nat → Nat) (hbp : ∀ i, bp i < B) (hbh : ∀ j, bh j < B)
    (φ : Nat → List Nat → Int) (hφ : ∀ c, SL (φ c)) {n k : Nat} (e : Nat)
    (hr : ∀ g, CM n k g → g.length = e → okB B bp bh n g = true → ∀ i < n + k, pfree n g i →
      othB B bp bh n φ (bp i) g = 0 ∨
      (p : Int) ∣ locL n (φ (bp i)) (flB B bp bh n (bp i) g) (var n i) n (fun t => bh t = bp i) -
        φ (bp i) (flB B bp bh n (bp i) g))
    (hc : ∀ g, CM n k g → g.length = e → okB B bp bh n g = true → ∀ j < n, hfree n g j →
      othB B bp bh n φ (bh j) g = 0 ∨
      (p : Int) ∣ locL n (φ (bh j)) (flB B bp bh n (bh j) g) (fun s => var n s j) (n + k)
        (fun s => bp s = bh j) - φ (bh j) (flB B bp bh n (bh j) g)) :
    Bal p n k (PB B bp bh n φ) (PB B bp bh n φ) e := by
  intro g hg hl
  refine ⟨fun i hi hf => ?_, fun j hj hf => ?_⟩
  · unfold rowS
    rw [line_PB B bp bh φ hφ hg (var n i) n (bp i) (hbp i) (fun t => bh t = bp i)
      (fun t ht => ⟨var_lt n k i t hi ht, notin_of_pfree hf t ht⟩)
      (fun t ht => by rw [blkB_var B bp bh ht]; by_cases h : bp i = bh t <;> simp [h, eq_comm]),
      PB_fac B bp bh n φ g (hbp i)]
    split
    · rename_i hok
      rcases hr g hg hl hok i hi hf with h0 | h1
      · rw [h0]; simp
      · rw [← Int.sub_mul]; exact Int.dvd_trans h1 (Int.dvd_mul_right _ _)
    · simp
  · unfold colS
    rw [line_PB B bp bh φ hφ hg (fun s => var n s j) (n + k) (bh j) (hbh j) (fun s => bp s = bh j)
      (fun t ht => ⟨var_lt n k t j ht hj, notin_of_hfree hf t hj⟩)
      (fun t ht => by rw [blkB_var B bp bh hj]; by_cases h : bp t = bh j <;> simp [h]),
      PB_fac B bp bh n φ g (hbh j)]
    split
    · rename_i hok
      rcases hc g hg hl hok j hj hf with h0 | h1
      · rw [h0]; simp
      · rw [← Int.sub_mul]; exact Int.dvd_trans h1 (Int.dvd_mul_right _ _)
    · simp

end Programme.«20261027-0607-proof-complexity».BProd
