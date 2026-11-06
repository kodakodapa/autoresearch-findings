import Programme.«20261027-0607-proof-complexity».Lucas

/-! Arithmetic component of the direct syzygy / NoDrop chain.
This file does not assume a syzygy spanning statement. -/
namespace Programme.«20261104-1627-proof-complexity».DirectND
open Programme.«20261025-0459-proof-complexity».OntoLucas (bin bin_zero)
open Programme.«20261027-0607-proof-complexity».Lucas (bin_succ)

/-- Pascal induction transports vanishing of the initial binomial row to a
shift congruence. No primality assumption is needed. -/
theorem bin_shift_of_initial (p q : Nat)
    (initial : ∀ t, t < q → (p : Int) ∣ (bin q t : Int) - bin 0 t) :
    ∀ n t, t < q → (p : Int) ∣ (bin (n + q) t : Int) - bin n t
  | 0, t, ht => by simpa using initial t ht
  | n + 1, 0, _ => by simp [bin_zero]
  | n + 1, t + 1, ht => by
    rw [show n + 1 + q = (n + q) + 1 by omega, bin_succ, bin_succ]
    have h := Int.dvd_add
      (bin_shift_of_initial p q initial n t (by omega))
      (bin_shift_of_initial p q initial n (t + 1) ht)
    push_cast
    have he : ∀ a b c d : Int, a + b - (c + d) = a - c + (b - d) := by intros; omega
    rw [he]; exact h

/-- Iterating a binomial-row period. -/
theorem bin_shift_mul (p q : Nat)
    (initial : ∀ t, t < q → (p : Int) ∣ (bin q t : Int) - bin 0 t)
    (n t : Nat) (ht : t < q) :
    ∀ c, (p : Int) ∣ (bin (n + q * c) t : Int) - bin n t
  | 0 => by simp
  | c + 1 => by
    have h := Int.dvd_add (bin_shift_mul p q initial n t ht c)
      (bin_shift_of_initial p q initial (n + q * c) t ht)
    rw [Nat.mul_succ]
    rw [show n + (q * c + q) = n + q * c + q by omega]
    have he : ∀ a b c : Int, a - b = c - b + (a - c) := by intros; omega
    rw [he _ _ (bin (n + q * c) t)]; exact h

/-- The finite initial congruences needed for the concrete F3 target. -/
theorem initial_three_nine :
    ∀ t, t < 9 → (3 : Int) ∣ (bin 9 t : Int) - bin 0 t := by
  intro t ht
  have : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨
      t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 := by omega
  rcases this with h | h | h | h | h | h | h | h | h <;> subst t <;> decide

/-- Lemma 3 specialised to the owner target, with the base-matching bound
stated explicitly. This holds for every anchor and every board size. -/
theorem lucas_three_nine {n k s t : Nat} (hk : 9 ∣ k)
    (hs : s ≤ n) (ht : t < 9) :
    (3 : Int) ∣ (bin (n + k - s) t : Int) - bin (n - s) t := by
  obtain ⟨c, rfl⟩ := hk
  rw [show n + 9 * c - s = (n - s) + 9 * c by omega]
  exact bin_shift_mul 3 9 initial_three_nine (n - s) t ht c

end Programme.«20261104-1627-proof-complexity».DirectND
#print axioms Programme.«20261104-1627-proof-complexity».DirectND.bin_shift_of_initial
#print axioms Programme.«20261104-1627-proof-complexity».DirectND.bin_shift_mul
#print axioms Programme.«20261104-1627-proof-complexity».DirectND.initial_three_nine
#print axioms Programme.«20261104-1627-proof-complexity».DirectND.lucas_three_nine
