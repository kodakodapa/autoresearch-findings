import Programme.«20261024-1633-proof-complexity».PCTseitin

/-!
# Onto functional pigeonhole principle: polynomial encoding and polynomial calculus

`ontoFPHP n k`: `n + k` pigeons `i`, `n` holes `j`, variable `x_{ij} = i * n + j`. Axioms (as
polynomials over `Z`, read mod `p` on the Boolean cube, so `x² = x` is built in):
* pigeon `i`: `∑_j x_{ij} - 1`;  hole (onto) `j`: `∑_i x_{ij} - 1`;
* collision `x_{ij} x_{i'j}` (`i < i'`);  functional `x_{ij} x_{ij'}` (`j < j'`).
This is the Beame–Riis style encoding (linear pigeon/onto axioms), not the CNF: the library's
clause-based `PCRefutation` asks every used axiom clause to have width `≤ D`, so with the CNF the
pigeon clauses alone would force degree `≥ n`.

`PPCDerivable p A D`: polynomial calculus over `Z/p` from a list `A` of polynomial axioms of degree
`≤ D`, the same rules as `PCTseitin.PCDerivable` (linear combination, multiplication by a variable
of a line of cube-degree `≤ D - 1`, congruence mod `p` on the cube).

Warm-up `ontoFPHP_deg1`: if `k` is invertible mod `p`, there is a degree-1 refutation
(`∑_i pigeon_i - ∑_j hole_j = -k`). So the interesting case is `p ∣ k`.
-/

namespace Programme.«20261025-0459-proof-complexity».OntoFPHP

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin

/-- `∑_{i<m} f i`. -/
def rsum : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | m + 1, f => rsum m f + f m

/-- Lines of a degree-`D` polynomial calculus derivation over `Z/p` from polynomial axioms `A`. -/
inductive PPCDerivable (p : Nat) (A : List (Poly Nat)) (D : Nat) : ((Nat → Bool) → Int) → Prop
  | ax (P : Poly Nat) : P ∈ A → P.deg ≤ D → PPCDerivable p A D (fun a => P.eval a)
  | lin (f g : (Nat → Bool) → Int) (u v : Int) : PPCDerivable p A D f → PPCDerivable p A D g →
      PPCDerivable p A D (fun a => u * f a + v * g a)
  | mul (x : Nat) (g : (Nat → Bool) → Int) (d : Nat) : PPCDerivable p A D g → CubeDeg p g d →
      d + 1 ≤ D → PPCDerivable p A D (fun a => xv x a * g a)
  | congr (f g : (Nat → Bool) → Int) : PPCDerivable p A D g → (∀ a, (p : Int) ∣ f a - g a) →
      PPCDerivable p A D f

/-- A degree-`D` refutation: the line `1` is derivable. -/
def PPCRefutation (p : Nat) (A : List (Poly Nat)) (D : Nat) : Prop :=
  PPCDerivable p A D (fun _ => 1)

/-- Terms `x_{v 0} + … + x_{v (m-1)}`. -/
def linTerms (v : Nat → Nat) : Nat → List (Int × List Nat)
  | 0 => []
  | m + 1 => linTerms v m ++ [(1, [v m])]

/-- `∑_{t<m} x_{v t} - 1`. -/
def sumOne (v : Nat → Nat) (m : Nat) : Poly Nat := ⟨(-1, []) :: linTerms v m⟩

/-- `x_u x_w`. -/
def prod2 (u w : Nat) : Poly Nat := ⟨[(1, [u, w])]⟩

/-- Variable of pigeon `i`, hole `j`. -/
def var (n i j : Nat) : Nat := i * n + j

def pigeonAx (n k : Nat) : List (Poly Nat) :=
  (List.range (n + k)).map fun i => sumOne (fun j => var n i j) n
def holeAx (n k : Nat) : List (Poly Nat) :=
  (List.range n).map fun j => sumOne (fun i => var n i j) (n + k)
def collAx (n k : Nat) : List (Poly Nat) :=
  (List.range n).flatMap fun j => (List.range (n + k)).flatMap fun i =>
    (List.range (n + k)).filterMap fun i' => if i < i' then some (prod2 (var n i j) (var n i' j)) else none
def funcAx (n k : Nat) : List (Poly Nat) :=
  (List.range (n + k)).flatMap fun i => (List.range n).flatMap fun j =>
    (List.range n).filterMap fun j' => if j < j' then some (prod2 (var n i j) (var n i j')) else none

/-- The onto functional pigeonhole principle `onto-FPHP^{n+k}_n`, polynomial encoding. -/
def ontoFPHP (n k : Nat) : List (Poly Nat) := pigeonAx n k ++ holeAx n k ++ collAx n k ++ funcAx n k

/-- Soundness: at a Boolean point where every axiom vanishes mod `p`, every line vanishes mod `p`
(so `1` is underivable for `p > 1` when the axioms have a common Boolean zero). -/
theorem PPCDerivable.sound {p D : Nat} {A : List (Poly Nat)} (a : Nat → Bool)
    (ha : ∀ P ∈ A, (p : Int) ∣ P.eval a) {g : (Nat → Bool) → Int} (h : PPCDerivable p A D g) :
    (p : Int) ∣ g a := by
  induction h with
  | ax P hP _ => exact ha P hP
  | lin f g u v _ _ ihf ihg => exact Int.dvd_add (dvd_mul_of u ihf) (dvd_mul_of v ihg)
  | mul x g d _ _ _ ih => exact dvd_mul_of _ ih
  | congr f g _ hfg ih => have := Int.dvd_add (hfg a) ih; simpa using this

/-! ## Evaluation and degree of the linear axioms -/

theorem linTerms_eval (v : Nat → Nat) (a : Nat → Bool) (m : Nat) :
    ((linTerms v m).map fun t => t.1 * monoEval a t.2).sum = rsum m (fun t => xv (v t) a) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [linTerms, List.map_append, List.sum_append, ih]
    simp only [rsum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, monoEval, xv]
    cases a (v m) <;> simp

theorem sumOne_eval (v : Nat → Nat) (m : Nat) (a : Nat → Bool) :
    (sumOne v m).eval a = rsum m (fun t => xv (v t) a) - 1 := by
  simp only [sumOne, Poly.eval, List.map_cons, List.sum_cons]
  rw [linTerms_eval]
  simp [monoEval]; omega

theorem foldr_max_le (l : List Nat) (D : Nat) (h : ∀ x ∈ l, x ≤ D) : l.foldr max 0 ≤ D := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldr_cons]
    exact Nat.max_le.mpr ⟨h x (by simp), ih fun y hy => h y (by simp [hy])⟩

theorem linTerms_len (v : Nat → Nat) (m : Nat) : ∀ t ∈ linTerms v m, t.2.length = 1 := by
  induction m with
  | zero => simp [linTerms]
  | succ m ih =>
    intro t ht
    simp only [linTerms, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | ht
    · exact ih t ht
    · subst ht; rfl

theorem sumOne_deg (v : Nat → Nat) (m : Nat) : (sumOne v m).deg ≤ 1 := by
  apply foldr_max_le
  intro x hx
  simp only [sumOne, List.map_cons, List.mem_cons, List.mem_map] at hx
  rcases hx with hx | ⟨t, ht, rfl⟩
  · simp at hx; omega
  · rw [linTerms_len v m t ht]; exact Nat.le_refl 1

/-! ## Sums -/

theorem rsum_add (m : Nat) (f g : Nat → Int) :
    rsum m (fun t => f t + g t) = rsum m f + rsum m g := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [rsum, ih]; omega

theorem rsum_comm (m n : Nat) (g : Nat → Nat → Int) :
    rsum m (fun i => rsum n (fun j => g i j)) = rsum n (fun j => rsum m (fun i => g i j)) := by
  induction m with
  | zero =>
    simp only [rsum]
    induction n with
    | zero => rfl
    | succ n ih => simp only [rsum, ← ih]; omega
  | succ m ih => simp only [rsum, ih]; rw [← rsum_add]

theorem rsum_sub_one (m : Nat) (f : Nat → Int) :
    rsum m (fun t => f t - 1) = rsum m f - m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [rsum, ih]; omega

/-- A sum of derivable lines, started from a derivable line `z`, is derivable. -/
theorem der_rsum {p D : Nat} {A : List (Poly Nat)} (F : Nat → (Nat → Bool) → Int) (z : (Nat → Bool) → Int)
    (hz : PPCDerivable p A D z) :
    ∀ m, (∀ i < m, PPCDerivable p A D (F i)) →
      PPCDerivable p A D (fun a => z a + rsum m (fun i => F i a))
  | 0, _ => PPCDerivable.congr _ _ hz (fun a => ⟨0, by simp [rsum]⟩)
  | m + 1, h => by
    have ih := der_rsum F z hz m (fun i hi => h i (by omega))
    have := PPCDerivable.lin _ _ 1 1 ih (h m (by omega))
    exact PPCDerivable.congr _ _ this (fun a => ⟨0, by simp only [rsum]; omega⟩)

/-! ## The degree-1 refutation when `k` is invertible mod `p` -/

/-- If `0 < k` and `k` is invertible mod `p` (e.g. `p` prime, `p ∤ k`), `onto-FPHP^{n+k}_n` has
a degree-1 polynomial calculus refutation over `Z/p`. -/
theorem ontoFPHP_deg1 (p n k : Nat) (hk0 : 0 < k) (hk : ∃ u : Int, (p : Int) ∣ u * k - 1) :
    PPCRefutation p (ontoFPHP n k) 1 := by
  obtain ⟨u, hu⟩ := hk
  have hpig : ∀ i < n + k, PPCDerivable p (ontoFPHP n k) 1
      (fun a => rsum n (fun j => xv (var n i j) a) - 1) := by
    intro i hi
    have hm : sumOne (fun j => var n i j) n ∈ ontoFPHP n k := by
      simp only [ontoFPHP, pigeonAx, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl (Or.inl ⟨i, hi, rfl⟩))
    have := PPCDerivable.ax (p := p) (D := 1) _ hm (sumOne_deg _ _)
    exact PPCDerivable.congr _ _ this (fun a => by rw [sumOne_eval]; simp)
  have hhole : ∀ j < n, PPCDerivable p (ontoFPHP n k) 1
      (fun a => rsum (n + k) (fun i => xv (var n i j) a) - 1) := by
    intro j hj
    have hm : sumOne (fun i => var n i j) (n + k) ∈ ontoFPHP n k := by
      simp only [ontoFPHP, holeAx, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl (Or.inr ⟨j, hj, rfl⟩))
    have := PPCDerivable.ax (p := p) (D := 1) _ hm (sumOne_deg _ _)
    exact PPCDerivable.congr _ _ this (fun a => by rw [sumOne_eval]; simp)
  have hzero : PPCDerivable p (ontoFPHP n k) 1 (fun _ => 0) :=
    PPCDerivable.congr _ _ (PPCDerivable.lin _ _ 0 0 (hpig 0 (by omega)) (hpig 0 (by omega)))
      (fun a => by simp)
  have hP := der_rsum _ _ hzero (n + k) hpig
  have hH := der_rsum _ _ hzero n hhole
  have hL := PPCDerivable.lin _ _ (-u) u hP hH
  refine PPCDerivable.congr _ _ hL (fun a => ?_)
  -- the line is `-u * (∑ pigeons - ∑ holes) = u * k`
  have e1 := rsum_sub_one (n + k) (fun i => rsum n (fun j => xv (var n i j) a))
  have e2 := rsum_sub_one n (fun j => rsum (n + k) (fun i => xv (var n i j) a))
  have e3 := rsum_comm (n + k) n (fun i j => xv (var n i j) a)
  rw [Int.zero_add, Int.zero_add, e1, e2, e3]
  generalize (rsum n fun j => rsum (n + k) fun i => xv (var n i j) a) = S
  have h : (1 : Int) - (-u * (S - ((n + k : Nat) : Int)) + u * (S - (n : Int))) = -(u * k - 1) := by
    rw [Int.natCast_add]; simp only [Int.mul_sub, Int.mul_add, Int.neg_mul]; omega
  rw [h]; exact Int.dvd_neg.mpr hu

end Programme.«20261025-0459-proof-complexity».OntoFPHP

#print axioms Programme.«20261025-0459-proof-complexity».OntoFPHP.ontoFPHP_deg1
#print axioms Programme.«20261025-0459-proof-complexity».OntoFPHP.PPCDerivable.sound
