import Programme.«20261024-1633-proof-complexity».Ts3Upper
import Programme.«20261024-1633-proof-complexity».NSFamilies

/-!
# `F_3` vs `Z/p` (`3 ∤ p`, e.g. `F_2`): Nullstellensatz degree separations for mod-3 Tseitin

The other direction of the Buss–Grigoriev–Impagliazzo–Pitassi separation, on the library graphs
(charge `1` at vertex `0`):
* `hc3_sep`: on the cube-connected cycles `CC k` (`k ≥ 2`, degree `3`), `Ts3` has a degree-`12`
  Nullstellensatz refutation over `F_3` and none of degree `< ⌊⌊2^k/3⌋/(k+1)⌋` over `Z/p`, `3 ∤ p`.
* `hq3_sep`: on the hypercube `Q k` (`k ≥ 3`), degree `4k` over `F_3` and none of degree `< 2^k/3`
  over `Z/p`, `3 ∤ p`.
-/

namespace Programme.«20261024-1633-proof-complexity».Ts3Separation

open Programme.«20261024-1633-proof-complexity».NS Programme.«20261024-1633-proof-complexity».Ts3 Programme.«20261024-1633-proof-complexity».Ts3Upper Programme.«20261024-1110-proof-complexity».Haken
open Programme.«20261024-1110-proof-complexity».Tseitin
open Programme.«20261024-1110-proof-complexity».Hypercube
open Programme.«20261024-1110-proof-complexity».CCC

theorem hc3_sep (k : Nat) (hk : 2 ≤ k) :
    Nonempty (NSRefutation 3 (Ts3 (2 ^ k * k) (CC k) chg) 12) ∧
    ∀ p D : Nat, p % 3 ≠ 0 → 1 < p → D < 2 ^ k / 3 / (k + 1) →
      NSRefutation p (Ts3 (2 ^ k * k) (CC k) chg) D → False := by
  refine ⟨ts3_ns_upper (CC_ends k hk) 3
    (by rw [chg_sum _ (Nat.mul_pos (Nat.two_pow_pos k) (by omega))]; decide)
    (fun v _ => by rw [inc_len]; exact CC_deg k (by omega) v) (Nat.le_refl 3),
    fun p D hp hp1 hD π => ?_⟩
  exact ts3_ns_lower (by have := Nat.mul_le_mul (three_le k hk) hk; omega)
    (CC_ends k hk) (hconn' k (by omega)) (hexp' k (by omega)) p hp hp1 hD π

theorem hq3_sep (k : Nat) (hk : 3 ≤ k) :
    Nonempty (NSRefutation 3 (Ts3 (2 ^ k) (Q k) chg) (4 * k)) ∧
    ∀ p D : Nat, p % 3 ≠ 0 → 1 < p → D < 2 ^ k / 3 →
      NSRefutation p (Ts3 (2 ^ k) (Q k) chg) D → False := by
  have hE : ∀ p ∈ Q k, p.1 < 2 ^ k ∧ p.2 < 2 ^ k ∧ p.1 ≠ p.2 := fun p hp =>
    ⟨Nat.lt_trans (Q_ends k p hp).1 (Q_ends k p hp).2, (Q_ends k p hp).2,
      Nat.ne_of_lt (Q_ends k p hp).1⟩
  refine ⟨ts3_ns_upper hE k (by rw [chg_sum _ (Nat.one_le_two_pow)]; decide)
    (fun v _ => by rw [inc_len]; exact deg_le k v) hk, fun p D hp hp1 hD π => ?_⟩
  exact ts3_ns_lower (three_le k (by omega)) hE (hconn k) (hexp k) p hp hp1 hD π

end Programme.«20261024-1633-proof-complexity».Ts3Separation

#print axioms Programme.«20261024-1633-proof-complexity».Ts3Separation.hc3_sep
#print axioms Programme.«20261024-1633-proof-complexity».Ts3Separation.hq3_sep
