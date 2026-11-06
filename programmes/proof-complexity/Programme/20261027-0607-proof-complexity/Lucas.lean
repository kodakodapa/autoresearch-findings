import Programme.«20261027-0607-proof-complexity».Peel
import Programme.«20261025-0459-proof-complexity».OntoLucas
import Programme.«20261025-0459-proof-complexity».OntoPCLower

/-!
# Exact PC degree `p` for onto-FPHP over `F_p` when `p ∥ k`

`bin (n + p c) p - bin n p ≡ c` mod `p` for prime `p` (`telescope`, from `p ∣ bin p r` for
`0 < r < p` via the absorption identity and Euclid's lemma). With `OntoLucas.ontoFPHP_upper` at
`t = p` and `Peel.pc_degree_ge_p`: for prime `p`, `p ∤ c`, `n ≥ 2p - 3`, `ontoFPHP n (p c)` has a
degree-`D` `PPCRefutation p` iff `D ≥ p`.
-/

namespace Programme.«20261027-0607-proof-complexity».Lucas

open Programme.«20261025-0459-proof-complexity».OntoFPHP (ontoFPHP PPCRefutation)
open Programme.«20261025-0459-proof-complexity».OntoLucas (bin bin_zero ontoFPHP_upper)
open Programme.«20261027-0607-proof-complexity».Peel (IsPrime bezout pc_degree_ge_p)

theorem bin_succ (n t : Nat) : bin (n + 1) (t + 1) = bin n t + bin n (t + 1) := rfl

theorem bin_gt : ∀ n t, n < t → bin n t = 0
  | 0, 0, h => absurd h (by omega)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (by omega)
  | n + 1, t + 1, h => by rw [bin_succ, bin_gt n t (by omega), bin_gt n (t + 1) (by omega)]

theorem bin_self : ∀ n, bin n n = 1
  | 0 => rfl
  | n + 1 => by rw [bin_succ, bin_self n, bin_gt n (n + 1) (by omega)]

theorem bin_one : ∀ n, bin n 1 = n
  | 0 => rfl
  | n + 1 => by rw [bin_succ, bin_zero, bin_one n]; omega

/-- Absorption: `(r+1) C(m+1, r+1) = (m+1) C(m, r)`. -/
theorem absorb : ∀ m r, (r + 1) * bin (m + 1) (r + 1) = (m + 1) * bin m r
  | 0, 0 => rfl
  | 0, r + 1 => by rw [bin_gt 1 (r + 2) (by omega), bin_gt 0 (r + 1) (by omega)]; simp
  | m + 1, 0 => by rw [bin_one, bin_zero]; omega
  | m + 1, r + 1 => by
    have h1 := absorb m (r + 1)
    have h2 := absorb m r
    have h3 : bin (m + 1) (r + 1) = bin m r + bin m (r + 1) := rfl
    rw [bin_succ (m + 1) (r + 1)]
    generalize bin (m + 1) (r + 1) = X at *
    generalize bin (m + 1) (r + 1 + 1) = Y at *
    generalize bin m r = A at *
    generalize bin m (r + 1) = Bv at *
    subst h3
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one] at *
    omega

theorem euclid {p a b : Nat} (hp : IsPrime p) (h : p ∣ a * b) (ha : ¬ p ∣ a) : p ∣ b := by
  have hg : Nat.gcd a p = 1 := by
    rcases hp.2 _ (Nat.gcd_dvd_right a p) with h' | h'
    · exact h'
    · exact absurd (h' ▸ Nat.gcd_dvd_left a p) ha
  obtain ⟨x, y, hxy⟩ := bezout a p
  rw [hg] at hxy
  have hI : (p : Int) ∣ ((a * b : Nat) : Int) := Int.natCast_dvd_natCast.mpr h
  have : (b : Int) = x * ((a * b : Nat) : Int) + (y * b) * (p : Int) := by
    push_cast at hxy ⊢
    have e1 : (x * a + y * p) * (b : Int) = b := by rw [hxy]; simp
    have e2 : (x * a + y * p) * (b : Int) = x * (a * b) + y * b * p := by
      rw [Int.add_mul, Int.mul_assoc x, Int.mul_right_comm y]
    omega
  have : (p : Int) ∣ (b : Int) := by
    rw [this]; exact Int.dvd_add (Int.dvd_mul_of_dvd_right hI) (Int.dvd_mul_left _ _)
  exact Int.natCast_dvd_natCast.mp this

theorem dvd_bin {p r : Nat} (hp : IsPrime p) (h0 : 0 < r) (hr : r < p) : p ∣ bin p r := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.1; omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have := absorb m s
  have hd : m + 1 ∣ (s + 1) * bin (m + 1) (s + 1) := by rw [this]; exact Nat.dvd_mul_right _ _
  exact euclid hp hd (fun h => by have := Nat.le_of_dvd (by omega) h; omega)

theorem shift {p : Nat} (hp : IsPrime p) : ∀ m r, r < p → (p : Int) ∣ (bin (m + p) r : Int) - bin m r
  | 0, 0, _ => by rw [bin_zero, bin_zero]; simp
  | 0, r + 1, hr => by
    rw [Nat.zero_add, bin_gt 0 (r + 1) (by omega)]
    simpa using Int.natCast_dvd_natCast.mpr (dvd_bin hp (by omega) hr)
  | m + 1, 0, _ => by rw [bin_zero, bin_zero]; simp
  | m + 1, r + 1, hr => by
    rw [show m + 1 + p = (m + p) + 1 by omega, bin_succ, bin_succ]
    have h1 := shift hp m r (by omega); have h2 := shift hp m (r + 1) hr
    have := Int.dvd_add h1 h2
    push_cast
    rw [show ∀ a b c d : Int, a + b - (c + d) = a - c + (b - d) by intros; omega]; exact this

theorem shiftp {p : Nat} (hp : IsPrime p) : ∀ m, (p : Int) ∣ (bin (m + p) p : Int) - bin m p - 1
  | 0 => by rw [Nat.zero_add, bin_self, bin_gt 0 p (by have := hp.1; omega)]; simp
  | m + 1 => by
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.1; omega⟩
    have h1 := shiftp hp m
    have h2 := shift hp m q (by omega)
    rw [hq] at h1 h2 ⊢
    rw [show m + 1 + (q + 1) = (m + (q + 1)) + 1 by omega, bin_succ, bin_succ]
    have := Int.dvd_add h1 h2
    push_cast
    rw [show ∀ a b c d : Int, a + b - (c + d) - 1 = b - d - 1 + (a - c) by intros; omega]
    exact this

theorem telescope {p : Nat} (hp : IsPrime p) (n : Nat) : ∀ c, (p : Int) ∣ (bin (n + p * c) p : Int) - bin n p - c
  | 0 => by simp
  | c + 1 => by
    have h1 := telescope hp n c
    have h2 := shiftp hp (n + p * c)
    rw [show n + p * (c + 1) = n + p * c + p by rw [Nat.mul_succ]; omega]
    have := Int.dvd_add h1 h2
    push_cast
    rw [show ∀ a b c d : Int, a - b - (c + 1) = (d - b - c) + (a - d - 1) by intros; omega]
    exact this

theorem unit_c {p c : Nat} (hp : IsPrime p) (hc : ¬ p ∣ c) (n : Nat) :
    ∃ u : Int, (p : Int) ∣ u * ((bin (n + p * c) p : Int) - bin n p) - 1 := by
  have hg : Nat.gcd c p = 1 := by
    rcases hp.2 _ (Nat.gcd_dvd_right c p) with h' | h'
    · exact h'
    · exact absurd (h' ▸ Nat.gcd_dvd_left c p) hc
  obtain ⟨x, y, hxy⟩ := bezout c p
  rw [hg] at hxy
  refine ⟨x, ?_⟩
  have h1 := Int.dvd_trans (telescope hp n c) (Int.dvd_mul_left x _)
  have : x * ((bin (n + p * c) p : Int) - bin n p) - 1 =
      x * ((bin (n + p * c) p : Int) - bin n p - c) + (-y) * (p : Int) := by
    rw [Int.mul_sub x _ (c : Int)]
    have : x * (c : Int) = 1 - y * p := by push_cast at hxy; omega
    rw [this, Int.neg_mul]; omega
  rw [this]; exact Int.dvd_add h1 (Int.dvd_mul_left _ _)

/-- **Exact PC degree `p`.** For prime `p`, `p ∤ c` and `n ≥ 2p - 3`: `ontoFPHP n (p c)` has a
degree-`D` `PPCRefutation p` iff `p ≤ D`. -/
theorem pc_degree_exact {p c : Nat} (hp : IsPrime p) (hc : ¬ p ∣ c) (n : Nat) (hn : 2 * p - 3 ≤ n) (D : Nat) :
    PPCRefutation p (ontoFPHP n (p * c)) D ↔ p ≤ D := by
  have hp2 := hp.1
  constructor
  · intro h
    apply Classical.byContradiction; intro hD
    exact pc_degree_ge_p hp ⟨c, rfl⟩ n hn
      (Programme.«20261025-0459-proof-complexity».OntoPCLower.PPCDerivable.mono (by omega) h)
  · intro hD
    exact Programme.«20261025-0459-proof-complexity».OntoPCLower.PPCDerivable.mono hD
      (ontoFPHP_upper p n (p * c) p hp2 (by omega) (unit_c hp hc n))

theorem unit_of_ndvd {q k : Nat} (hq : IsPrime q) (hk : ¬ q ∣ k) : ∃ u : Int, (q : Int) ∣ u * k - 1 := by
  have hg : Nat.gcd k q = 1 := by
    rcases hq.2 _ (Nat.gcd_dvd_right k q) with h' | h'
    · exact h'
    · exact absurd (h' ▸ Nat.gcd_dvd_left k q) hk
  obtain ⟨x, y, hxy⟩ := bezout k q
  rw [hg] at hxy
  exact ⟨x, ⟨-y, by rw [Int.mul_neg, Int.mul_comm (q : Int) y]; push_cast at hxy; omega⟩⟩

/-- **Separation across characteristics.** For primes `p`, `q`, `p ∤ c`, `q ∤ p c` and `n ≥ 2p - 3`:
over `Z/p` the PC degree of `ontoFPHP n (p c)` is exactly `p`, over `Z/q` it has a degree-1 refutation
(library `OntoFPHP.ontoFPHP_deg1`). -/
theorem separation {p q c : Nat} (hp : IsPrime p) (hq : IsPrime q) (hc : ¬ p ∣ c) (hqk : ¬ q ∣ p * c)
    (n : Nat) (hn : 2 * p - 3 ≤ n) :
    (∀ D, PPCRefutation p (ontoFPHP n (p * c)) D ↔ p ≤ D) ∧ PPCRefutation q (ontoFPHP n (p * c)) 1 := by
  refine ⟨pc_degree_exact hp hc n hn, ?_⟩
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · exact absurd (h ▸ Nat.dvd_zero p) hc
    · exact h
  exact Programme.«20261025-0459-proof-complexity».OntoFPHP.ontoFPHP_deg1 q n (p * c)
    (Nat.mul_pos (by have := hp.1; omega) hc0) (unit_of_ndvd hq hqk)

end Programme.«20261027-0607-proof-complexity».Lucas

#print axioms Programme.«20261027-0607-proof-complexity».Lucas.pc_degree_exact
#print axioms Programme.«20261027-0607-proof-complexity».Lucas.separation
