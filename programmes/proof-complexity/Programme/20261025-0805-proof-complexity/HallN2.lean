/-! Concrete instance of K19's arithmetic: at `n = 2^550`, `ℓ = 4` the bound forces `s > n^2`.
Pure arithmetic: the hypothesis is `hall_cp_explicit`'s conclusion at these values. -/

namespace Programme.«20261025-0805-proof-complexity».HallN2

set_option exponentiation.threshold 2000

/-- The constant `Y` of `hall_cp_explicit` at `ℓ = 4`, `n = 2^550` (`log₂ n = 550`). -/
def Y4 : Nat := (3 * 4) ^ (3 * 4) * ((4 + 1) * (550 + 1) * 2 ^ 4 * (2 * 4 + 1) ^ (2 * 4)) ^ (3 * 4)

theorem key : 2 ^ (4 * 4 + 5) * (2 ^ 550) ^ 2 * (2 * 2 ^ 550 + 7) * 4 * Y4 ^ 2 < (2 ^ 550 - 4) ^ (4 + 1) :=
  Nat.le_of_ble_eq_true rfl

theorem n2 (s : Nat)
    (h : (2 ^ 550 - 4) ^ (4 + 1) ≤ 2 ^ (4 * 4 + 5) * s * (2 * 2 ^ 550 + 7) * 4 * Y4 ^ 2) :
    (2 ^ 550) ^ 2 < s := by
  refine Nat.lt_of_not_le fun hs => Nat.lt_irrefl _ (Nat.lt_of_le_of_lt h (Nat.lt_of_le_of_lt ?_ key))
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
    (Nat.mul_le_mul_left _ hs)))

end Programme.«20261025-0805-proof-complexity».HallN2

#print axioms Programme.«20261025-0805-proof-complexity».HallN2.n2
