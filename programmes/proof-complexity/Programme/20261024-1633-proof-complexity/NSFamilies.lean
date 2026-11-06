import Programme.«20261024-1633-proof-complexity».NS
import Programme.«20261024-1110-proof-complexity».CCC

/-!
# Degree-bounded `F_2` Nullstellensatz refutations of the library's Tseitin families

* `hq_ns2`: the hypercube Tseitin formula `HQ k` has a degree-`k` NS refutation over `F_2`.
* `hc_ns2`: the cube-connected-cycles Tseitin formula `HC k` (`k ≥ 2`) has a degree-`3` NS
  refutation over `F_2`.
* `hc_separation`: for `k ≥ 11`, `HC k` has a degree-`3` NS refutation over `F_2`, and every
  resolution refutation (`Refutation`, weakening allowed) has the exponential size bound of
  `CCC.hc_main`: constant NS degree over `F_2` against exponential resolution size, both proved
  for the same CNF.
-/

namespace Programme.«20261024-1633-proof-complexity».NSFamilies

open Programme.«20261024-1633-proof-complexity».NS Programme.«20261024-1110-proof-complexity».Haken
open Programme.«20261024-1110-proof-complexity».Tseitin
open Programme.«20261024-1110-proof-complexity».Hypercube
open Programme.«20261024-1110-proof-complexity».CCC

theorem hq_ns2 (k : Nat) : Nonempty (NSRefutation 2 (HQ k) k) :=
  tseitin_ns2 (2 ^ k) (Q k) chg k
    (fun p hp => ⟨Nat.lt_trans (Q_ends k p hp).1 (Q_ends k p hp).2, (Q_ends k p hp).2,
      Nat.ne_of_lt (Q_ends k p hp).1⟩)
    (by rw [chg_sum _ (Nat.one_le_two_pow)])
    (fun v _ => by rw [inc_len]; exact deg_le k v)

theorem hc_ns2 (k : Nat) (hk : 2 ≤ k) : Nonempty (NSRefutation 2 (HC k) 3) :=
  tseitin_ns2 (2 ^ k * k) (CC k) chg 3 (CC_ends k hk)
    (by rw [chg_sum _ (Nat.mul_pos (Nat.two_pow_pos k) (by omega))])
    (fun v _ => by rw [inc_len]; exact CC_deg k (by omega) v)

/-- For `k ≥ 11`: a degree-3 `F_2` Nullstellensatz refutation of `HC k` exists, and every
resolution refutation of `HC k` with `L` clauses has `(3k2^k)^B ≤ L (3k2^k - B)^B`,
`B = ⌊2^k/(8(k+1))⌋`. -/
theorem hc_separation (k : Nat) (hk : 11 ≤ k) :
    Nonempty (NSRefutation 2 (HC k) 3) ∧
    ∀ π : Refutation (HC k),
      (3 * k * 2 ^ k) ^ (2 ^ k / (8 * (k + 1))) ≤
        π.steps.length * (3 * k * 2 ^ k - 2 ^ k / (8 * (k + 1))) ^ (2 ^ k / (8 * (k + 1))) :=
  ⟨hc_ns2 k (by omega), (hc_main k (by omega)).2.2 hk⟩

end Programme.«20261024-1633-proof-complexity».NSFamilies

#print axioms Programme.«20261024-1633-proof-complexity».NSFamilies.hq_ns2
#print axioms Programme.«20261024-1633-proof-complexity».NSFamilies.hc_ns2
#print axioms Programme.«20261024-1633-proof-complexity».NSFamilies.hc_separation
