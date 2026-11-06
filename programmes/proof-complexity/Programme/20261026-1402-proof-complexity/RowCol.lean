import Programme.«20261025-1627-proof-complexity».OntoExt3

/-!
# Step 0 of L3 (K28): row and column sums of the target `c` agree mod `p`

If `f` is balanced against `c` at level 1 (`Bal p n k f c 1`: at every edge `x_{ij}`, every free
row and column sum of the link of `f` is `≡ c [x_{ij}]`), then every row sum of `c` is congruent
to every column sum of `c` mod `p`: `rowS c [] i ≡ colS c [] j'`. Proof: sum `f({x_{ij}, x_{i'j'}})`
over `j ≠ j'`, `i' ≠ i` in both orders. No hypothesis on `p`, `n`, `k`.

The definitions `cfl`, `isMatch`, `pfree`, `hfree`, `CM`, `lineS`, `rowS`, `colS`, `Bal` are
verbatim copies of pr's `Work.ExtLemma` (no peer imports this run, owner P66/P67); they are
definitionally equal to pr's, so the theorem transfers by `exact`.
-/

namespace Programme.«20261026-1402-proof-complexity».RowCol

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr rsum_zero var_div var_mod)
open Programme.«20261025-1627-proof-complexity».MomGen
open Programme.«20261025-1627-proof-complexity».OntoExt2 (rsum_dvd rsum_pick)
open Programme.«20261025-1627-proof-complexity».OntoExt3 (rsum_sub')

def cfl (n v w : Nat) : Bool := v != w && (v / n == w / n || v % n == w % n)
def isMatch (n : Nat) (l : List Nat) : Bool := l.all fun v => l.all fun w => !cfl n v w
def pfree (n : Nat) (g : List Nat) (i : Nat) : Prop := ∀ v ∈ g, v / n ≠ i
def hfree (n : Nat) (g : List Nat) (j : Nat) : Prop := ∀ v ∈ g, v % n ≠ j
def CM (n k : Nat) (g : List Nat) : Prop := canon ((n + k) * n) g = g ∧ isMatch n g = true
def lineS (n k : Nat) (f : List Nat → Int) (g : List Nat) (v : Nat → Nat) (M : Nat) : Int :=
  rsum M (fun t => if isMatch n (v t :: g) then f (canon ((n + k) * n) (v t :: g)) else 0)
def rowS (n k : Nat) (f : List Nat → Int) (g : List Nat) (i : Nat) : Int := lineS n k f g (fun j => var n i j) n
def colS (n k : Nat) (f : List Nat → Int) (g : List Nat) (j : Nat) : Int :=
  lineS n k f g (fun i => var n i j) (n + k)
def Bal (p n k : Nat) (f c : List Nat → Int) (e : Nat) : Prop :=
  ∀ g, CM n k g → g.length = e →
    (∀ i < n + k, pfree n g i → (p : Int) ∣ rowS n k f g i - c g) ∧
    (∀ j < n, hfree n g j → (p : Int) ∣ colS n k f g j - c g)

theorem canon_ge : ∀ (M : Nat) (xs : List Nat), (∀ x ∈ xs, M ≤ x) → canon M xs = [] := by
  intro M
  induction M with
  | zero => intro xs _; rfl
  | succ M ih =>
    intro xs h
    unfold canon
    have : M ∉ xs := fun hm => by have := h M hm; omega
    simp only [this, ite_false]
    exact ih xs (fun x hx => by have := h x hx; omega)

theorem canon_one : ∀ (M v : Nat), v < M → canon M [v] = [v] := by
  intro M
  induction M with
  | zero => intro v h; omega
  | succ M ih =>
    intro v h
    unfold canon
    by_cases hv : v = M
    · subst hv; simp only [List.mem_singleton, ite_true]
      rw [canon_ge]; intro x hx; simp at hx; omega
    · have : M ∉ [v] := by simp; omega
      simp only [this, ite_false]; exact ih v (by omega)

theorem isMatch_one (n v : Nat) : isMatch n [v] = true := by
  simp [isMatch, cfl]

theorem isMatch_two (n v w : Nat) :
    isMatch n [v, w] = (!cfl n v w) := by
  have h1 : cfl n v v = false := by simp [cfl]
  have h2 : cfl n w w = false := by simp [cfl]
  have h3 : cfl n w v = cfl n v w := by
    unfold cfl
    cases h1 : (v == w) <;> cases h2 : (w == v) <;> simp_all [bne] <;> grind
  simp [isMatch, h1, h2, h3]

theorem cfl_symm' (n v w : Nat) : cfl n v w = cfl n w v := by
  unfold cfl
  cases h1 : (v == w) <;> cases h2 : (w == v) <;> simp_all [bne] <;> grind

theorem canon_swap (N v w : Nat) : canon N [v, w] = canon N [w, v] :=
  canon_congr N _ _ (fun x _ => by simp; omega)

/-- **Step 0 of L3.** `Bal p n k f c 1` forces all row sums and column sums of `c` (on single
edges) to be congruent mod `p`. -/
theorem row_col {p n k : Nat} {f c : List Nat → Int} (hb : Bal p n k f c 1)
    {i j' : Nat} (hi : i < n + k) (hj' : j' < n) :
    (p : Int) ∣ rowS n k c [] i - colS n k c [] j' := by
  have hn : 0 < n := by omega
  have hN : ∀ a b, a < n + k → b < n → var n a b < (n + k) * n := by
    intro a b ha hb; unfold var
    have : a * n + b < a * n + n := by omega
    have : a * n + n ≤ (n + k) * n := by
      rw [show a * n + n = (a + 1) * n by rw [Nat.succ_mul]]; exact Nat.mul_le_mul_right n ha
    omega
  have hcm : ∀ a b, a < n + k → b < n → CM n k [var n a b] := fun a b ha hb =>
    ⟨canon_one _ _ (hN a b ha hb), isMatch_one n _⟩
  -- the common double sum
  let G : Nat → Nat → Int := fun i' j =>
    if i' = i ∨ j = j' then 0 else f (canon ((n + k) * n) [var n i' j', var n i j])
  have hinj : ∀ a b a' b', b < n → b' < n → var n a b = var n a' b' → a = a' ∧ b = b' := by
    intro a b a' b' hb hb' h
    have h1 : var n a b / n = var n a' b' / n := by rw [h]
    have h2 : var n a b % n = var n a' b' % n := by rw [h]
    rw [var_div n a b hb, var_div n a' b' hb'] at h1
    rw [var_mod n a b hb, var_mod n a' b' hb'] at h2
    exact ⟨h1, h2⟩
  have hcf : ∀ i' < n + k, ∀ j < n, ¬(i' = i ∧ j = j') →
      cfl n (var n i' j') (var n i j) = (i' == i || j' == j) := by
    intro i' _ j hj hne
    have hv : var n i' j' ≠ var n i j := fun h => hne (by
      have := hinj _ _ _ _ hj' hj h; omega)
    unfold cfl
    rw [var_div n i' j' hj', var_div n i j hj, var_mod n i' j' hj', var_mod n i j hj]
    simp [hv]
  -- column side: T = ∑_j [j ≠ j'] colS f [x_ij] j'
  have hT : rsum n (fun j => if j = j' then 0 else colS n k f [var n i j] j') =
      rsum n (fun j => rsum (n + k) (fun i' => G i' j)) := by
    apply rsum_congr; intro j hj
    by_cases e : j = j'
    · subst e; simp only [ite_true]
      symm; apply rsum_zero; intro t _; simp [G]
    · simp only [e, if_false, colS, lineS]
      apply rsum_congr; intro i' hi'
      rw [isMatch_two, hcf i' hi' j hj (by omega)]
      by_cases e2 : i' = i
      · simp [G, e2]
      · have : (j' == j) = false := by simp; omega
        simp [G, e, e2, this]
  -- row side: T' = ∑_{i'} [i' ≠ i] rowS f [x_{i'j'}] i
  have hT' : rsum (n + k) (fun i' => if i' = i then 0 else rowS n k f [var n i' j'] i) =
      rsum (n + k) (fun i' => rsum n (fun j => G i' j)) := by
    apply rsum_congr; intro i' hi'
    by_cases e : i' = i
    · subst e; simp only [ite_true]
      symm; apply rsum_zero; intro t _; simp [G]
    · simp only [e, if_false, rowS, lineS]
      apply rsum_congr; intro j hj
      rw [isMatch_two, cfl_symm', hcf i' hi' j hj (by omega), canon_swap]
      by_cases e2 : j = j'
      · subst e2; simp [G]
      · have : (j' == j) = false := by simp; omega
        simp [G, e, e2, this]
  have hswap := rsum_comm (n + k) n G
  -- the sums of c
  have hrow : rowS n k c [] i = rsum n (fun j => if j = j' then 0 else c [var n i j]) + c [var n i j'] := by
    have h1 : rowS n k c [] i = rsum n (fun j => (if j = j' then 0 else c [var n i j]) +
        (if j = j' then c [var n i j] else 0)) := by
      unfold rowS lineS; apply rsum_congr; intro j hj
      rw [isMatch_one, canon_one _ _ (hN i j hi hj)]; by_cases e : j = j' <;> simp [e]
    rw [h1, rsum_add, rsum_pick n j' (fun j => c [var n i j])]; simp [hj']
  have hcol : colS n k c [] j' = rsum (n + k) (fun i' => if i' = i then 0 else c [var n i' j']) +
      c [var n i j'] := by
    have h1 : colS n k c [] j' = rsum (n + k) (fun i' => (if i' = i then 0 else c [var n i' j']) +
        (if i' = i then c [var n i' j'] else 0)) := by
      unfold colS lineS; apply rsum_congr; intro i' hi'
      rw [isMatch_one, canon_one _ _ (hN i' j' hi' hj')]; by_cases e : i' = i <;> simp [e]
    rw [h1, rsum_add, rsum_pick (n + k) i (fun i' => c [var n i' j'])]; simp [hi]
  -- congruences from `Bal`
  have dT : (p : Int) ∣ rsum n (fun j => if j = j' then 0 else colS n k f [var n i j] j') -
      rsum n (fun j => if j = j' then 0 else c [var n i j]) := by
    rw [← rsum_sub']; apply rsum_dvd; intro j hj
    by_cases e : j = j'
    · simp [e]
    · simp only [e, ite_false]
      refine (hb _ (hcm i j hi hj) rfl).2 j' hj' ?_
      intro v hv; simp at hv; subst hv; rw [var_mod n i j hj]; exact e
  have dT' : (p : Int) ∣ rsum (n + k) (fun i' => if i' = i then 0 else rowS n k f [var n i' j'] i) -
      rsum (n + k) (fun i' => if i' = i then 0 else c [var n i' j']) := by
    rw [← rsum_sub']; apply rsum_dvd; intro i' hi'
    by_cases e : i' = i
    · simp [e]
    · simp only [e, ite_false]
      refine (hb _ (hcm i' j' hi' hj') rfl).1 i hi ?_
      intro v hv; simp at hv; subst hv; rw [var_div n i' j' hj']; exact e
  rw [hT] at dT; rw [hT', hswap] at dT'
  have := Int.dvd_sub dT' dT
  rw [hrow, hcol]
  have e : ∀ a b x y : Int, x - b - (x - a) = a + y - (b + y) := by intros; omega
  rw [← e]; exact this

#print axioms Programme.«20261026-1402-proof-complexity».RowCol.row_col

end Programme.«20261026-1402-proof-complexity».RowCol
