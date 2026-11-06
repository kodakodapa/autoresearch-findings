import Programme.«20261025-0805-proof-complexity».HallCPX
import Programme.«20261025-0805-proof-complexity».HallN2

/-! K19 at `n = 2^550`, `ℓ = 4`: every DAG-like CP refutation of `Hall (2^550)` has more than `n^2` lines. -/

namespace Programme.«20261025-0805-proof-complexity».HallN2X

set_option exponentiation.threshold 2000

theorem hall_n2 (Rf : Programme.«20261025-0459b-proof-complexity».CPDag.DRefutation (Programme.«20261025-0459b-proof-complexity».Hall.Hall (2 ^ 550))) : (2 ^ 550) ^ 2 < Rf.size := by
  have h := Programme.«20261025-0805-proof-complexity».HallCPX.hall_cp_explicit (2 ^ 550) 4 (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) Rf
  have hl : (2 ^ 550 : Nat).log2 = 550 := Nat.log2_two_pow
  rw [hl] at h
  exact Programme.«20261025-0805-proof-complexity».HallN2.n2 _ h

end Programme.«20261025-0805-proof-complexity».HallN2X

#print axioms Programme.«20261025-0805-proof-complexity».HallN2X.hall_n2
