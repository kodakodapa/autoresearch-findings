import Programme.«20261025-0459-proof-complexity».OntoSubst

/-!
# No degree-1 refutation of onto-FPHP when `p ∣ k`

Converse of `Work.OntoFPHP.ontoFPHP_deg1`. A degree-`D` derivation only uses axioms of degree
`≤ D` (`sound_deg`): if a Boolean point zeroes those mod `p`, no line is `1`. At `D = 1` only the
pigeon and hole axioms count, and the point "pigeon `i < n` to hole `i`, pigeons `n .. n+k-1` to
hole `0`" satisfies every pigeon axiom, every hole axiom `j > 0`, and hole `0` up to `k ≡ 0`.
-/

namespace Programme.«20261025-0459-proof-complexity».OntoDeg1Lower

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261025-0459-proof-complexity».OntoFPHP Programme.«20261025-0459-proof-complexity».OntoSubst

/-- Soundness restricted to the axioms of degree `≤ D`. -/
theorem sound_deg {p D : Nat} {A : List (Poly Nat)} (a : Nat → Bool)
    (ha : ∀ P ∈ A, P.deg ≤ D → (p : Int) ∣ P.eval a) {g : (Nat → Bool) → Int}
    (h : PPCDerivable p A D g) : (p : Int) ∣ g a := by
  induction h with
  | ax P hP hd => exact ha P hP hd
  | lin f g u v _ _ ihf ihg => exact Int.dvd_add (dvd_mul_of u ihf) (dvd_mul_of v ihg)
  | mul x g d _ _ _ ih => exact dvd_mul_of _ ih
  | congr f g _ hfg ih => have := Int.dvd_add (hfg a) ih; simpa using this

/-- The point: pigeon `i < n` sits in hole `i`, every pigeon `i ≥ n` in hole `0`. -/
def pt (n : Nat) (v : Nat) : Bool :=
  decide ((v / n < n ∧ v % n = v / n) ∨ (n ≤ v / n ∧ v % n = 0))

theorem pt_var (n i j : Nat) (hj : j < n) :
    xv (var n i j) (pt n) = if (i < n ∧ j = i) ∨ (n ≤ i ∧ j = 0) then 1 else 0 := by
  unfold xv pt
  rw [var_div n i j hj, var_mod n i j hj]
  by_cases h : (i < n ∧ j = i) ∨ (n ≤ i ∧ j = 0) <;> simp [h]

theorem rsum_one_at (m c : Nat) (f : Nat → Int) (hc : c < m) (h1 : f c = 1)
    (h0 : ∀ t < m, t ≠ c → f t = 0) : rsum m f = 1 := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [rsum]
    by_cases hcm : c = m
    · subst hcm
      rw [rsum_zero c f (fun t ht => h0 t (by omega) (by omega)), h1]; rfl
    · rw [ih (by omega) (fun t ht hne => h0 t (by omega) hne), h0 m (by omega) (fun e => hcm e.symm)]
      rfl

theorem rsum_split (n k : Nat) (f : Nat → Int) :
    rsum (n + k) f = rsum n f + rsum k (fun t => f (n + t)) := by
  induction k with
  | zero => simp [rsum]
  | succ k ih =>
    show rsum (n + k) f + f (n + k) = _
    rw [ih]; simp only [rsum]; omega

theorem rsum_const_one (k : Nat) : rsum k (fun _ => (1 : Int)) = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rsum, ih]; omega

/-- For `p > 1`, `p ∣ k` and `n ≥ 1`, `onto-FPHP^{n+k}_n` has no degree-1 polynomial calculus
refutation over `Z/p`. -/
theorem ontoFPHP_no_deg1 (p n k : Nat) (hp : 1 < p) (hn : 1 ≤ n) (hk : (p : Int) ∣ k) :
    ¬ PPCRefutation p (ontoFPHP n k) 1 := by
  intro h
  have key := sound_deg (pt n) (fun P hP hd => ?_) h
  · obtain ⟨c, hc⟩ := key
    have : (p : Int) * c = 1 := hc.symm
    have hp' : (1 : Int) < p := by omega
    rcases Int.lt_or_le 0 c with hc0 | hc0
    · have : (p : Int) * c ≥ p * 1 := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega
    · have : (p : Int) * c ≤ p * 0 := Int.mul_le_mul_of_nonneg_left hc0 (by omega)
      omega
  rcases mem_ontoFPHP hP with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩ | hc | hf
  · -- pigeon `i`: exactly one hole
    rw [sumOne_eval]
    have : rsum n (fun j => xv (var n i j) (pt n)) = 1 := by
      by_cases hin : i < n
      · refine rsum_one_at n i _ hin ?_ ?_
        · rw [pt_var n i i hin]; simp [hin]
        · intro t ht hne; rw [pt_var n i t ht]; simp; omega
      · refine rsum_one_at n 0 _ (by omega) ?_ ?_
        · rw [pt_var n i 0 (by omega)]; simp; omega
        · intro t ht hne; rw [pt_var n i t ht]; simp; omega
    rw [this]; exact ⟨0, by simp⟩
  · -- hole `j`
    rw [sumOne_eval, rsum_split]
    have h1 : rsum n (fun i => xv (var n i j) (pt n)) = 1 := by
      refine rsum_one_at n j _ hj ?_ ?_
      · rw [pt_var n j j hj]; simp [hj]
      · intro t ht hne; rw [pt_var n t j hj]; simp; omega
    rw [h1]
    by_cases hj0 : j = 0
    · subst hj0
      have h2 : rsum k (fun t => xv (var n (n + t) 0) (pt n)) = k := by
        rw [← rsum_const_one k]
        exact rsum_congr k _ _ (fun t _ => by rw [pt_var n (n + t) 0 hj]; simp)
      rw [h2]; have e : (1 : Int) + k - 1 = k := by omega
      rw [e]; exact hk
    · have h2 : rsum k (fun t => xv (var n (n + t) j) (pt n)) = 0 :=
        rsum_zero k _ (fun t _ => by rw [pt_var n (n + t) j hj]; simp; omega)
      rw [h2]; exact ⟨0, by simp⟩
  · obtain ⟨_, _, _, _, _, _, _, rfl⟩ := mem_collAx.mp hc
    rw [prod2_deg] at hd; omega
  · obtain ⟨_, _, _, _, _, _, _, rfl⟩ := mem_funcAx.mp hf
    rw [prod2_deg] at hd; omega

end Programme.«20261025-0459-proof-complexity».OntoDeg1Lower

#print axioms Programme.«20261025-0459-proof-complexity».OntoDeg1Lower.ontoFPHP_no_deg1
