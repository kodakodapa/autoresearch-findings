import Programme.«20261027-0607-proof-complexity».CRT
import Programme.«20261027-0607-proof-complexity».Lucas

/-!
# Onto-FPHP over composite moduli

* `composite_lower`: over `Z/m`, if a prime `q` divides both `m` and `k`, then for `n ≥ 2q - 3`
  there is no degree-`(q-1)` refutation of `ontoFPHP n k` (reduce mod `q`, th's K14).
* `two_primes_exact`: for distinct primes `p, q` with `p, q ∤ c` and `n ≥ 2p-3, 2q-3`, the PC degree
  of `ontoFPHP n (p*q*c)` over `Z/(pq)` is exactly `max p q` (CRT plus th's K13 at both primes).
-/

namespace Programme.«20261027-0607-proof-complexity».CRTOnto

open Programme.«20261025-0459-proof-complexity».OntoFPHP (ontoFPHP PPCRefutation)
open Programme.«20261027-0607-proof-complexity».Peel (IsPrime pc_degree_ge_p)
open Programme.«20261027-0607-proof-complexity».Lucas (pc_degree_exact unit_of_ndvd euclid)

theorem composite_lower {m q k : Nat} (hq : IsPrime q) (hqm : q ∣ m) (hqk : q ∣ k) (n : Nat)
    (hn : 2 * q - 3 ≤ n) : ¬ PPCRefutation m (ontoFPHP n k) (q - 1) :=
  fun h => pc_degree_ge_p hq hqk n hn (Programme.«20261027-0607-proof-complexity».CRT.refutation_down hqm h)

theorem not_dvd_prime {p q : Nat} (hp : IsPrime p) (hq : IsPrime q) (hpq : p ≠ q) : ¬ q ∣ p := by
  intro h
  rcases hp.2 q h with h1 | h1
  · have := hq.1; omega
  · exact hpq h1.symm

theorem two_primes_exact {p q c : Nat} (hp : IsPrime p) (hq : IsPrime q) (hpq : p ≠ q)
    (hpc : ¬ p ∣ c) (hqc : ¬ q ∣ c) (n : Nat) (hnp : 2 * p - 3 ≤ n) (hnq : 2 * q - 3 ≤ n) (D : Nat) :
    PPCRefutation (p * q) (ontoFPHP n (p * q * c)) D ↔ p ≤ D ∧ q ≤ D := by
  have hcop : ∃ x y : Int, x * p + y * q = 1 := by
    obtain ⟨u, t, ht⟩ := unit_of_ndvd hq (not_dvd_prime hp hq hpq)
    exact ⟨u, -t, by rw [Int.neg_mul, Int.mul_comm t]; omega⟩
  rw [Programme.«20261027-0607-proof-complexity».CRT.crt _ hcop]
  have hP : ¬ p ∣ q * c := fun h => hpc (euclid hp h (not_dvd_prime hq hp (Ne.symm hpq)))
  have hQ : ¬ q ∣ p * c := fun h => hqc (euclid hq h (not_dvd_prime hp hq hpq))
  have e1 : p * q * c = p * (q * c) := Nat.mul_assoc p q c
  have e2 : p * q * c = q * (p * c) := by rw [Nat.mul_comm p q, Nat.mul_assoc]
  constructor
  · rintro ⟨h1, h2⟩
    rw [e1] at h1; rw [e2] at h2
    exact ⟨(pc_degree_exact hp hP n hnp D).1 h1, (pc_degree_exact hq hQ n hnq D).1 h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [e1]; exact (pc_degree_exact hp hP n hnp D).2 h1
    · rw [e2]; exact (pc_degree_exact hq hQ n hnq D).2 h2

end Programme.«20261027-0607-proof-complexity».CRTOnto

#print axioms Programme.«20261027-0607-proof-complexity».CRTOnto.composite_lower
#print axioms Programme.«20261027-0607-proof-complexity».CRTOnto.two_primes_exact
