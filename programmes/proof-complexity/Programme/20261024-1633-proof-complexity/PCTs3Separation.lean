import Programme.«20261024-1633-proof-complexity».PCTs3
import Programme.«20261024-1633-proof-complexity».PCSeparation
import Programme.«20261024-1633-proof-complexity».Ts3Separation

/-!
# `F_3` vs `Z/p` (`3 ∤ p`, e.g. `F_2`): polynomial calculus degree separations for mod-3 Tseitin

PC versions of `Work.Ts3Separation` (charge `1` at vertex `0`):
* `hc3_pc_sep`: on the cube-connected cycles `CC k` (`k ≥ 2`), `Ts3` has a degree-`12` PC
  refutation over `F_3` and none of degree `D` with `2D < ⌊⌊2^k/3⌋/(k+1)⌋` over `Z/p`, `3 ∤ p`.
* `hq3_pc_sep`: on the hypercube `Q k` (`k ≥ 3`), degree `4k` over `F_3`, none with `2D < 2^k/3`.
-/

namespace Programme.«20261024-1633-proof-complexity».PCTs3Separation

open Programme.«20261024-1633-proof-complexity».NS Programme.«20261024-1633-proof-complexity».Ts3 Programme.«20261024-1633-proof-complexity».PCTseitin Programme.«20261024-1633-proof-complexity».PCTs3 Programme.«20261024-1633-proof-complexity».PCSeparation Programme.«20261024-1633-proof-complexity».Ts3Separation
open Programme.«20261024-1110-proof-complexity».Haken
open Programme.«20261024-1110-proof-complexity».Tseitin
open Programme.«20261024-1110-proof-complexity».Hypercube
open Programme.«20261024-1110-proof-complexity».CCC

theorem hc3_pc_sep (k : Nat) (hk : 2 ≤ k) :
    PCRefutation 3 (Ts3 (2 ^ k * k) (CC k) chg) 12 ∧
    ∀ p D : Nat, p % 3 ≠ 0 → 1 < p → 2 * D < 2 ^ k / 3 / (k + 1) →
      PCRefutation p (Ts3 (2 ^ k * k) (CC k) chg) D → False := by
  obtain ⟨π⟩ := (hc3_sep k hk).1
  refine ⟨ns_to_pc 3 (by decide) π, fun p D hp hp1 hD π' => ?_⟩
  exact ts3_pc_lower (by have := Nat.mul_le_mul (three_le k hk) hk; omega)
    (CC_ends k hk) (hconn' k (by omega)) (hexp' k (by omega)) p hp hp1 hD π'

theorem hq3_pc_sep (k : Nat) (hk : 3 ≤ k) :
    PCRefutation 3 (Ts3 (2 ^ k) (Q k) chg) (4 * k) ∧
    ∀ p D : Nat, p % 3 ≠ 0 → 1 < p → 2 * D < 2 ^ k / 3 →
      PCRefutation p (Ts3 (2 ^ k) (Q k) chg) D → False := by
  have hE : ∀ p ∈ Q k, p.1 < 2 ^ k ∧ p.2 < 2 ^ k ∧ p.1 ≠ p.2 := fun p hp =>
    ⟨Nat.lt_trans (Q_ends k p hp).1 (Q_ends k p hp).2, (Q_ends k p hp).2,
      Nat.ne_of_lt (Q_ends k p hp).1⟩
  obtain ⟨π⟩ := (hq3_sep k hk).1
  refine ⟨ns_to_pc 3 (by decide) π, fun p D hp hp1 hD π' => ?_⟩
  exact ts3_pc_lower (three_le k (by omega)) hE (hconn k) (hexp k) p hp hp1 hD π'

end Programme.«20261024-1633-proof-complexity».PCTs3Separation

#print axioms Programme.«20261024-1633-proof-complexity».PCTs3Separation.hc3_pc_sep
#print axioms Programme.«20261024-1633-proof-complexity».PCTs3Separation.hq3_pc_sep
