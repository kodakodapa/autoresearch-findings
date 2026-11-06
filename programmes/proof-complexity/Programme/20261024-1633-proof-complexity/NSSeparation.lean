import Programme.«20261024-1633-proof-complexity».NSTseitin
import Programme.«20261024-1633-proof-complexity».NSFamilies

/-!
# `F_2` vs odd characteristic: Nullstellensatz degree separations for the library Tseitin families

* `hq_sep`: the hypercube Tseitin formula `HQ k` (`k ≥ 2`, `2^k` vertices) has a degree-`k`
  Nullstellensatz refutation over `F_2`, and none of degree `< 2^k/3` over `Z/p` for any odd `p > 1`.
* `hc_sep`: the cube-connected-cycles Tseitin formula `HC k` (`k ≥ 2`, `k 2^k` vertices, degree 3)
  has a degree-`3` refutation over `F_2`, and none of degree `< ⌊⌊2^k/3⌋/(k+1)⌋` over `Z/p`, `p` odd.
Both lower bounds are instances of `Work.NSTseitin.tseitin_ns_lower` (Grigoriev's design).
-/

namespace Programme.«20261024-1633-proof-complexity».NSSeparation

open Programme.«20261024-1633-proof-complexity».NS Programme.«20261024-1633-proof-complexity».NSTseitin Programme.«20261024-1110-proof-complexity».Haken
open Programme.«20261024-1110-proof-complexity».Tseitin
open Programme.«20261024-1110-proof-complexity».Hypercube
open Programme.«20261024-1110-proof-complexity».CCC

theorem hq_sep (k : Nat) (hk : 2 ≤ k) :
    Nonempty (NSRefutation 2 (HQ k) k) ∧
    ∀ p D : Nat, p % 2 = 1 → 1 < p → D < 2 ^ k / 3 → NSRefutation p (HQ k) D → False := by
  refine ⟨Programme.«20261024-1633-proof-complexity».NSFamilies.hq_ns2 k, fun p D hp hp1 hD π => ?_⟩
  exact tseitin_ns_lower (three_le k hk)
    (fun p hp => ⟨Nat.lt_trans (Q_ends k p hp).1 (Q_ends k p hp).2, (Q_ends k p hp).2,
      Nat.ne_of_lt (Q_ends k p hp).1⟩)
    (hconn k) (hexp k) p hp hp1 hD π

theorem hc_sep (k : Nat) (hk : 2 ≤ k) :
    Nonempty (NSRefutation 2 (HC k) 3) ∧
    ∀ p D : Nat, p % 2 = 1 → 1 < p → D < 2 ^ k / 3 / (k + 1) → NSRefutation p (HC k) D → False := by
  refine ⟨Programme.«20261024-1633-proof-complexity».NSFamilies.hc_ns2 k hk, fun p D hp hp1 hD π => ?_⟩
  exact tseitin_ns_lower (by have := Nat.mul_le_mul (three_le k hk) hk; omega)
    (CC_ends k hk) (hconn' k (by omega)) (hexp' k (by omega)) p hp hp1 hD π

end Programme.«20261024-1633-proof-complexity».NSSeparation

#print axioms Programme.«20261024-1633-proof-complexity».NSSeparation.hq_sep
#print axioms Programme.«20261024-1633-proof-complexity».NSSeparation.hc_sep
