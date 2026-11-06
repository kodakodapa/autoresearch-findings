import Programme.«20261102-0806-proof-complexity».P11Reachability
import Programme.«20261102-0806-proof-complexity».P11Swap

namespace Programme.«20261102-0806-proof-complexity».P11Digits
open Programme.«20261102-0806-proof-complexity».P11Reachability Programme.«20261102-0806-proof-complexity».P11Swap

theorem digit_encode (a b c : Nat) (ha : a < 11) (hb : b < 11) :
    digit (a + 11*b + 121*c) 0 = a ∧
    digit (a + 11*b + 121*c) 1 = b ∧
    digit (a + 11*b + 121*c) 2 = c := by
  simp [digit]
  omega

/-- The strict capacity test prevents a carry in either ten-hole digit. -/
theorem bump_decode (x j : Nat) (hj : j < 3)
    (h : digit x 0 + digit x 1 + digit x 2 < 10) (t : Nat) (ht : t < 3) :
    digit (x + 11^j) t = digit x t + if t = j then 1 else 0 := by
  have decomp : x = x % 11 + 11 * (x / 11 % 11) + 121 * (x / 121) := by
    have := Nat.mod_add_div x 11
    have := Nat.mod_add_div (x / 11) 11
    have hd : x / 11 / 11 = x / 121 := by rw [Nat.div_div_eq_div_mul]
    omega
  simp only [digit] at h ⊢
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  have ht' : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  rcases hj' with rfl | rfl | rfl <;>
    rcases ht' with rfl | rfl | rfl <;> simp only [Nat.pow_zero, Nat.pow_one, show (11:Nat)^2 = 121 from rfl, Nat.reduceEqDiff, ite_true, ite_false] at * <;> omega

#print axioms digit_encode
#print axioms bump_decode
end Programme.«20261102-0806-proof-complexity».P11Digits
