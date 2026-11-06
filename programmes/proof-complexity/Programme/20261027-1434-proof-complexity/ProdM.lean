import Programme.«20261026-1402-proof-complexity».ProdExt

/-!
# Products of `m` locally self-balanced blocks are self-balanced

Pigeons and holes are split into `m` blocks by `bp`, `bh` (every pigeon and hole in a block).
An edge lies in block `blkM v` (`m` for a cross edge). `ProdM φ l = ∏_{c<m} φ c (l ∩ block c)` if
`l` has no cross edge, `0` otherwise. This is th's product tower (P27): if `φ c` is a block
function whose local line sums at every local matching `g'` are `≡ φ c g'` (a local tower
`φ^{(0)}, φ^{(1)}, …` merged into one function graded by length), then `ProdM φ` is balanced
against itself, `Bal p n k (ProdM φ) (ProdM φ) e`. Read at levels `e` and `e + 1`, this says the
level-`(e+1)` part of the product extends its level-`e` part.

Truncation: block `c` need only be balanced at local matchings of length `≤ Eb c`, provided it
vanishes below length `s c` and `e ≤ Eb b + ∑_{c ≠ b} s c` for every block `b`. Then a local
matching longer than `Eb b` forces another factor below its `s c`, so both sides vanish.

`bal_prodM` generalises the library `ProdExt.bal_prod3` (three fixed blocks, levels 1 and 2).
-/

namespace Programme.«20261027-1434-proof-complexity».ProdM

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero var_div var_mod)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt)
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ProdExt (SL locL rsum_mulr)

/-! ## Finite products and sums -/

def prodR : Nat → (Nat → Int) → Int
  | 0, _ => 1
  | c + 1, F => prodR c F * F c

def natSum : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | c + 1, F => natSum c F + F c

theorem prodR_congr : ∀ (M : Nat) (F G : Nat → Int), (∀ c < M, F c = G c) → prodR M F = prodR M G
  | 0, _, _, _ => rfl
  | M + 1, F, G, h => by
    simp only [prodR]; rw [prodR_congr M F G (fun c hc => h c (by omega)), h M (by omega)]

theorem prodR_split : ∀ (M : Nat) (F : Nat → Int) (b : Nat), b < M →
    prodR M F = F b * prodR M (fun c => if c = b then 1 else F c)
  | 0, _, _, h => absurd h (by omega)
  | M + 1, F, b, h => by
    simp only [prodR]
    by_cases e : b = M
    · subst e
      rw [prodR_congr b (fun c => if c = b then 1 else F c) F (fun c hc => by simp [show c ≠ b by omega])]
      simp [Int.mul_comm]
    · rw [prodR_split M F b (by omega)]
      simp only [show M ≠ b from fun h => e h.symm, ite_false]
      rw [Int.mul_assoc]

theorem prodR_zero : ∀ (M : Nat) (F : Nat → Int) (c : Nat), c < M → F c = 0 → prodR M F = 0
  | 0, _, _, h, _ => absurd h (by omega)
  | M + 1, F, c, h, hz => by
    simp only [prodR]
    by_cases e : c = M
    · subst e; rw [hz, Int.mul_zero]
    · rw [prodR_zero M F c (by omega) hz, Int.zero_mul]

theorem natSum_split : ∀ (M : Nat) (F : Nat → Nat) (b : Nat), b < M →
    natSum M F = F b + natSum M (fun c => if c = b then 0 else F c)
  | 0, _, _, h => absurd h (by omega)
  | M + 1, F, b, h => by
    simp only [natSum]
    by_cases e : b = M
    · subst e
      have : natSum b (fun c => if c = b then 0 else F c) = natSum b F := by
        clear h
        have : ∀ M', M' ≤ b → natSum M' (fun c => if c = b then 0 else F c) = natSum M' F := by
          intro M' hM'
          induction M' with
          | zero => rfl
          | succ M' ih => simp only [natSum]; rw [ih (by omega)]; simp [show M' ≠ b by omega]
        exact this b (Nat.le_refl _)
      rw [this]; simp; omega
    · rw [natSum_split M F b (by omega)]
      simp only [show M ≠ b from fun h => e h.symm, ite_false]
      omega

theorem natSum_le : ∀ (M : Nat) (F G : Nat → Nat), (∀ c < M, F c ≤ G c) → natSum M F ≤ natSum M G
  | 0, _, _, _ => Nat.le_refl _
  | M + 1, F, G, h => by
    simp only [natSum]; have := natSum_le M F G (fun c hc => h c (by omega)); have := h M (by omega); omega

theorem natSum_add : ∀ (M : Nat) (F G : Nat → Nat), natSum M (fun c => F c + G c) = natSum M F + natSum M G
  | 0, _, _ => rfl
  | M + 1, F, G => by simp only [natSum]; rw [natSum_add M F G]; omega

theorem natSum_pick : ∀ (M x : Nat), x < M → natSum M (fun c => if x = c then 1 else 0) = 1
  | 0, _, h => absurd h (by omega)
  | M + 1, x, h => by
    simp only [natSum]
    by_cases e : x = M
    · subst e
      have : ∀ M', M' ≤ x → natSum M' (fun c => if x = c then 1 else 0) = 0 := by
        intro M' hM'
        induction M' with
        | zero => rfl
        | succ M' ih => simp only [natSum]; rw [ih (by omega)]; simp [show x ≠ M' by omega]
      rw [this x (Nat.le_refl _)]; simp
    · rw [natSum_pick M x (by omega)]; simp [e]

theorem natSum_zero : ∀ (M : Nat), natSum M (fun _ => 0) = 0
  | 0 => rfl
  | M + 1 => by simp only [natSum]; rw [natSum_zero M]

/-! ## Blocks -/

section Blocks

variable (m : Nat) (bp bh : Nat → Nat) (n : Nat)

def blkM (v : Nat) : Nat := if bp (v / n) = bh (v % n) ∧ bp (v / n) < m then bp (v / n) else m

def flM (c : Nat) (l : List Nat) : List Nat := l.filter (fun v => blkM m bp bh n v == c)

def okM (l : List Nat) : Bool := l.all (fun v => decide (blkM m bp bh n v < m))

def ProdM (φ : Nat → List Nat → Int) (l : List Nat) : Int :=
  if okM m bp bh n l then prodR m (fun c => φ c (flM m bp bh n c l)) else 0

def othM (φ : Nat → List Nat → Int) (b : Nat) (g : List Nat) : Int :=
  prodR m (fun c => if c = b then 1 else φ c (flM m bp bh n c g))

end Blocks

variable {m : Nat} {bp bh : Nat → Nat} {n k : Nat}

theorem mem_flM (m : Nat) (bp bh : Nat → Nat) (n c : Nat) (l : List Nat) (x : Nat) :
    x ∈ flM m bp bh n c l ↔ x ∈ l ∧ blkM m bp bh n x = c := by
  simp [flM]

theorem flM_nodup (c : Nat) {l : List Nat} (h : l.Nodup) : (flM m bp bh n c l).Nodup :=
  (List.filter_sublist).nodup h

theorem blkM_le (v : Nat) : blkM m bp bh n v ≤ m := by
  unfold blkM; split
  · next h => omega
  · omega

theorem SL_ProdM (φ : Nat → List Nat → Int) (hφ : ∀ c, SL (φ c)) : SL (ProdM m bp bh n φ) := by
  intro l l' hl hl' hm
  have hok : okM m bp bh n l = okM m bp bh n l' := by
    unfold okM
    cases h1 : l.all (fun v => decide (blkM m bp bh n v < m)) <;>
    cases h2 : l'.all (fun v => decide (blkM m bp bh n v < m)) <;> try rfl
    · simp only [List.all_eq_true, List.all_eq_false, decide_eq_true_eq] at h1 h2
      obtain ⟨x, hx, hx'⟩ := h1; exact absurd (h2 x ((hm x).mp hx)) hx'
    · simp only [List.all_eq_true, List.all_eq_false, decide_eq_true_eq] at h1 h2
      obtain ⟨x, hx, hx'⟩ := h2; exact absurd (h1 x ((hm x).mpr hx)) hx'
  have e : ∀ c, φ c (flM m bp bh n c l) = φ c (flM m bp bh n c l') := fun c =>
    hφ c _ _ (flM_nodup c hl) (flM_nodup c hl') (fun x => by rw [mem_flM, mem_flM, hm x])
  unfold ProdM; rw [hok, prodR_congr m _ _ (fun c _ => e c)]

theorem cfl_symm (n v w : Nat) : cfl n v w = cfl n w v := by
  unfold cfl
  cases h1 : (v == w) <;> cases h2 : (w == v) <;> simp_all [bne] <;> grind

/-- A matching stays a matching after adding an edge of block `b` iff it does inside block `b`. -/
theorem match_flM {g : List Nat} {w : Nat} {b : Nat} (hb : b < m)
    (hg : isMatch n g = true) (hok : okM m bp bh n g = true) (hw : blkM m bp bh n w = b) :
    isMatch n (w :: g) = isMatch n (w :: flM m bp bh n b g) := by
  have sub : ∀ x, x ∈ w :: flM m bp bh n b g → x ∈ w :: g := by
    intro x hx; simp only [List.mem_cons, mem_flM] at hx ⊢
    rcases hx with h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  cases h1 : isMatch n (w :: g) <;> cases h2 : isMatch n (w :: flM m bp bh n b g) <;> try rfl
  · exfalso
    obtain ⟨u, hu, v, hv, hc⟩ := not_match h1
    rw [isMatch_iff] at h2
    have hg' := (isMatch_iff n g).mp hg
    have hok' : ∀ x ∈ g, blkM m bp bh n x < m := by
      intro x hx; unfold okM at hok; simp only [List.all_eq_true, decide_eq_true_eq] at hok
      exact hok x hx
    have cross : ∀ x ∈ g, blkM m bp bh n x ≠ b → cfl n w x = false := by
      intro x hx hxb
      have hx3 := hok' x hx
      have hwe : bp (w / n) = b ∧ bh (w % n) = b := by
        unfold blkM at hw; split at hw
        · next h => exact ⟨hw, by rw [← h.1]; exact hw⟩
        · omega
      have hxe : bp (x / n) = blkM m bp bh n x ∧ bh (x % n) = blkM m bp bh n x := by
        unfold blkM at hx3 ⊢; split
        · next h => exact ⟨rfl, h.1.symm⟩
        · next h => rw [ite_cond_eq_false _ _ (eq_false h)] at hx3; omega
      have q1 : w / n ≠ x / n := fun h => hxb (by rw [← hxe.1, ← h, hwe.1])
      have q2 : w % n ≠ x % n := fun h => hxb (by rw [← hxe.2, ← h, hwe.2])
      unfold cfl; simp [q1, q2]
    simp only [List.mem_cons] at hu hv
    have hm : w ∈ w :: flM m bp bh n b g := List.mem_cons_self
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · rw [hu, hv] at hc; exact absurd (h2 w hm w hm) (by simp [hc])
    · rw [hu] at hc
      by_cases hvb : blkM m bp bh n v = b
      · have := h2 w hm v (List.mem_cons_of_mem _ ((mem_flM ..).mpr ⟨hv, hvb⟩))
        simp [hc] at this
      · have := cross v hv hvb; simp [hc] at this
    · rw [hv] at hc
      by_cases hub : blkM m bp bh n u = b
      · have := h2 u (List.mem_cons_of_mem _ ((mem_flM ..).mpr ⟨hu, hub⟩)) w hm
        simp [hc] at this
      · have := cross u hu hub; rw [cfl_symm] at this; simp [hc] at this
    · have := hg' u hu v hv; simp [hc] at this
  · exfalso
    rw [isMatch_iff] at h1
    obtain ⟨u, hu, v, hv, hc⟩ := not_match h2
    have := h1 u (sub u hu) v (sub v hv); simp [hc] at this

/-- **Factorisation of line sums of an `m`-block product.** -/
theorem line_ProdM (φ : Nat → List Nat → Int) (hφ : ∀ c, SL (φ c))
    {g : List Nat} (hg : CM n k g) (v : Nat → Nat) (M b : Nat) (hb : b < m) (Q : Nat → Prop)
    [DecidablePred Q] (hv : ∀ t < M, v t < (n + k) * n ∧ v t ∉ g)
    (hQ : ∀ t < M, blkM m bp bh n (v t) = if Q t then b else m) :
    lineS n k (ProdM m bp bh n φ) g v M =
      if okM m bp bh n g then locL n (φ b) (flM m bp bh n b g) v M Q * othM m bp bh n φ b g else 0 := by
  unfold lineS
  have hcan : ∀ t < M, ProdM m bp bh n φ (canon ((n + k) * n) (v t :: g)) = ProdM m bp bh n φ (v t :: g) := by
    intro t ht
    obtain ⟨h1, h2⟩ := hv t ht
    apply SL_ProdM φ hφ _ _ (canon_nodup _ _) (List.nodup_cons.mpr ⟨h2, CM_nodup hg⟩)
    intro x; rw [mem_canon]; simp only [List.mem_cons]
    constructor
    · exact fun h => h.1
    · intro h; refine ⟨h, ?_⟩; rcases h with rfl | h
      · exact h1
      · exact CM_lt hg h
  rw [rsum_congr _ _ _ (fun t ht => by rw [hcan t ht])]
  split
  · rename_i hok
    unfold locL
    rw [← rsum_mulr]
    apply rsum_congr; intro t ht
    have hq := hQ t ht
    by_cases hqt : Q t
    · simp only [hqt, ite_true] at hq
      rw [match_flM hb hg.2 hok hq]
      simp only [hqt, true_and]
      split
      · unfold ProdM othM
        have hok' : okM m bp bh n (v t :: g) = true := by
          unfold okM at hok ⊢; simp only [List.all_cons, hok, Bool.and_true, decide_eq_true_eq]; omega
        rw [if_pos hok']
        have e : ∀ c, flM m bp bh n c (v t :: g) = if b = c then v t :: flM m bp bh n c g else flM m bp bh n c g := by
          intro c; unfold flM; simp only [List.filter_cons, hq]; by_cases h : b = c <;> simp [h]
        rw [prodR_congr m _ _ (fun c _ => by rw [e c]), prodR_split m _ b hb]
        simp only [ite_true]
        congr 1
        apply prodR_congr; intro c _
        by_cases h : c = b
        · simp [h]
        · simp [h, show b ≠ c from fun e => h e.symm]
      · simp
    · simp only [hqt, ite_false] at hq
      simp only [hqt, false_and, ite_false, Int.zero_mul]
      unfold ProdM
      have : okM m bp bh n (v t :: g) = false := by
        unfold okM; simp [hq]
      simp [this]
  · rename_i hok
    apply rsum_zero; intro t ht
    unfold ProdM
    have : okM m bp bh n (v t :: g) = false := by
      unfold okM at hok ⊢; simp only [List.all_cons, Bool.and_eq_false_iff]; right; simpa using hok
    simp [this]

/-! ## Counting block lengths -/

theorem len_sum : ∀ l : List Nat, okM m bp bh n l = true →
    l.length = natSum m (fun c => (flM m bp bh n c l).length)
  | [], _ => by simp [flM]; exact (natSum_zero m).symm
  | v :: l, h => by
    unfold okM at h; simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := len_sum l (by unfold okM; exact h.2)
    have e : ∀ c, (flM m bp bh n c (v :: l)).length =
        (if blkM m bp bh n v = c then 1 else 0) + (flM m bp bh n c l).length := by
      intro c; unfold flM; simp only [List.filter_cons]
      by_cases hc : blkM m bp bh n v = c <;> simp [hc]; omega
    rw [show natSum m (fun c => (flM m bp bh n c (v :: l)).length) =
      natSum m (fun c => (if blkM m bp bh n v = c then 1 else 0) + (flM m bp bh n c l).length) from by
        congr 1; funext c; exact e c]
    rw [natSum_add, natSum_pick m _ h.1, ← ih]; simp; omega

/-! ## The product theorem -/

/-- Block `c` is locally self-balanced at local matchings of length `≤ L`. -/
def LocBal (p : Nat) (m : Nat) (bp bh : Nat → Nat) (n k : Nat) (φc : List Nat → Int) (c L : Nat) : Prop :=
  ∀ g' : List Nat, g'.Nodup → isMatch n g' = true → (∀ v ∈ g', v < (n + k) * n ∧ blkM m bp bh n v = c) →
    g'.length ≤ L →
    (∀ i < n + k, bp i = c → (∀ v ∈ g', v / n ≠ i) →
      (p : Int) ∣ locL n φc g' (var n i) n (fun t => bh t = c) - φc g') ∧
    (∀ j < n, bh j = c → (∀ v ∈ g', v % n ≠ j) →
      (p : Int) ∣ locL n φc g' (fun s => var n s j) (n + k) (fun s => bp s = c) - φc g')

theorem isMatch_sub {g g' : List Nat} (hg : isMatch n g = true) (h : ∀ x ∈ g', x ∈ g) : isMatch n g' = true := by
  rw [isMatch_iff] at hg ⊢; exact fun v hv w hw => hg v (h v hv) w (h w hw)

/-- **Products of locally self-balanced blocks are self-balanced.** -/
theorem bal_prodM (p : Nat) (hbp : ∀ i < n + k, bp i < m) (hbh : ∀ j < n, bh j < m)
    (φ : Nat → List Nat → Int) (hφ : ∀ c, SL (φ c)) (s Eb : Nat → Nat)
    (hs : ∀ c < m, ∀ l : List Nat, l.length < s c → φ c l = 0)
    (hloc : ∀ c < m, LocBal p m bp bh n k (φ c) c (Eb c)) (e : Nat)
    (he : ∀ b < m, e ≤ Eb b + natSum m (fun c => if c = b then 0 else s c)) :
    Bal p n k (ProdM m bp bh n φ) (ProdM m bp bh n φ) e := by
  intro g hg hl
  -- the key congruence for a line in block `b`
  have key : ∀ b < m, okM m bp bh n g = true → ∀ X : Int,
      ((flM m bp bh n b g).length ≤ Eb b → (p : Int) ∣ X - φ b (flM m bp bh n b g)) →
      (p : Int) ∣ X * othM m bp bh n φ b g - ProdM m bp bh n φ g := by
    intro b hb hok X hX
    have hP : ProdM m bp bh n φ g = φ b (flM m bp bh n b g) * othM m bp bh n φ b g := by
      unfold ProdM othM; rw [if_pos hok, prodR_split m _ b hb]
    rw [hP, ← Int.sub_mul]
    by_cases hL : (flM m bp bh n b g).length ≤ Eb b
    · exact Int.dvd_trans (hX hL) (Int.dvd_mul_right _ _)
    · -- another block is below its `s`
      have hz : othM m bp bh n φ b g = 0 := by
        have hex : ∃ c < m, c ≠ b ∧ (flM m bp bh n c g).length < s c := by
          apply Classical.byContradiction; intro H
          have hge : ∀ c < m, (fun c => if c = b then 0 else s c) c ≤
              (fun c => if c = b then 0 else (flM m bp bh n c g).length) c := by
            intro c hc
            by_cases hcb : c = b
            · simp [hcb]
            · simp only [hcb, ite_false]
              apply Classical.byContradiction; intro h'
              exact H ⟨c, hc, hcb, by omega⟩
          have h1 := natSum_le m _ _ hge
          have h2 := len_sum g hok
          rw [natSum_split m _ b hb] at h2
          have h3 := he b hb
          omega
        obtain ⟨c, hc, hcb, hcs⟩ := hex
        exact prodR_zero m _ c hc (by simp [hcb, hs c hc _ hcs])
      rw [hz, Int.mul_zero]; exact Int.dvd_zero _
  -- local facts about `g ∩ block b`
  have gloc : ∀ b, (flM m bp bh n b g).Nodup ∧ isMatch n (flM m bp bh n b g) = true ∧
      (∀ v ∈ flM m bp bh n b g, v < (n + k) * n ∧ blkM m bp bh n v = b) := by
    intro b
    refine ⟨flM_nodup b (CM_nodup hg), isMatch_sub hg.2 (fun x hx => ((mem_flM ..).mp hx).1), ?_⟩
    intro v hv; obtain ⟨h1, h2⟩ := (mem_flM ..).mp hv; exact ⟨CM_lt hg h1, h2⟩
  have hP0 : okM m bp bh n g = false → ProdM m bp bh n φ g = 0 := by
    intro h; unfold ProdM; simp [h]
  refine ⟨fun i hi hpi => ?_, fun j hj hhj => ?_⟩
  · have hb := hbp i hi
    have hline := line_ProdM (m := m) (bp := bp) (bh := bh) (k := k) φ hφ hg (var n i) n (bp i) hb (fun t => bh t = bp i)
      (fun t ht => ⟨var_lt n k i t hi ht, fun hm => hpi _ hm (var_div n i t ht)⟩)
      (fun t ht => by
        unfold blkM; rw [var_div n i t ht, var_mod n i t ht]
        by_cases h : bh t = bp i
        · simp [h, hb]
        · simp [h, show ¬ bp i = bh t from fun e => h e.symm])
    unfold rowS; rw [hline]
    split
    · next hok =>
      apply key _ hb hok
      intro hL
      obtain ⟨h1, h2, h3⟩ := gloc (bp i)
      exact (hloc _ hb _ h1 h2 h3 hL).1 i hi rfl (fun v hv => hpi v ((mem_flM ..).mp hv).1)
    · next hok =>
      rw [hP0 (by simpa using hok)]; exact Int.dvd_zero _
  · have hb := hbh j hj
    have hline := line_ProdM (m := m) (bp := bp) (bh := bh) (k := k) φ hφ hg (fun s => var n s j) (n + k) (bh j) hb (fun s => bp s = bh j)
      (fun t ht => ⟨var_lt n k t j ht hj, fun hm => hhj _ hm (var_mod n t j hj)⟩)
      (fun t ht => by
        unfold blkM; rw [var_div n t j hj, var_mod n t j hj]
        by_cases h : bp t = bh j
        · simp [h, hb]
        · simp [h])
    unfold colS; rw [hline]
    split
    · next hok =>
      apply key _ hb hok
      intro hL
      obtain ⟨h1, h2, h3⟩ := gloc (bh j)
      exact (hloc _ hb _ h1 h2 h3 hL).2 j hj rfl (fun v hv => hhj v ((mem_flM ..).mp hv).1)
    · next hok =>
      rw [hP0 (by simpa using hok)]; exact Int.dvd_zero _

end Programme.«20261027-1434-proof-complexity».ProdM

#print axioms Programme.«20261027-1434-proof-complexity».ProdM.bal_prodM
