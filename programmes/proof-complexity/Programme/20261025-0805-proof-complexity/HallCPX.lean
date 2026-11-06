import Programme.«20261025-0805-proof-complexity».HallCP
import Programme.«20261025-0805-proof-complexity».HallCor

/-! Explicit corollary of K17: `hall_cp` at `p = (ℓ+1)(log₂ n+1)(2^ℓ-1)` fed to `hall_cor`. -/

namespace Programme.«20261025-0805-proof-complexity».HallCPX

theorem hall_cp_explicit (n ℓ : Nat) (hℓ : 1 ≤ ℓ) (hℓn : ℓ < n)
    (Rf : Programme.«20261025-0459b-proof-complexity».CPDag.DRefutation (Programme.«20261025-0459b-proof-complexity».Hall.Hall n)) :
    (n - ℓ) ^ (ℓ + 1) ≤ 2 ^ (4 * ℓ + 5) * Rf.size * (2 * n + 7) * ℓ *
      ((3 * ℓ) ^ (3 * ℓ) * ((ℓ + 1) * (n.log2 + 1) * 2 ^ ℓ * (2 * ℓ + 1) ^ (2 * ℓ)) ^ (3 * ℓ)) ^ 2 := by
  have h2 : 2 ^ 1 ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by decide) hℓ
  rw [Nat.pow_one] at h2
  have hp : 1 ≤ (ℓ + 1) * (n.log2 + 1) * (2 ^ ℓ - 1) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  exact Programme.«20261025-0805-proof-complexity».HallCor.hall_cor n ℓ Rf.size hℓ hℓn (Programme.«20261025-0805-proof-complexity».HallCP.hall_cp n _ ℓ hp hℓ hℓn Rf)

end Programme.«20261025-0805-proof-complexity».HallCPX

#print axioms Programme.«20261025-0805-proof-complexity».HallCPX.hall_cp_explicit
