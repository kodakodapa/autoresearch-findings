import Programme.«20261025-1627-proof-complexity».NoDrop
import Programme.«20261025-1627-proof-complexity».OntoNS
import Programme.«20261025-1627-proof-complexity».OntoQ7

/-!
# `Hard 2 3 4` from the two finite facts at `(n,k) = (7,8)`

The base case of the owner's Step 1 rests on two finite statements about `ontoFPHP 7 8` over `Z/2`,
both measured (not yet Lean-checked):
* `NoDrop 2 (ontoFPHP 7 8) 4` (no degree drop at level 4; exact elimination, board K21 / th),
* `¬ NSRefutation 2 (ontoFPHP 7 8) 4` (th's invariant design, board K5).

`hard234_of`: together they give no degree-4 PC refutation of `ontoFPHP n 8` over `Z/2` for every
`n ≥ 7` (`pc_ns`, then restriction `ontoFPHP_restrict`), i.e. `Hard 2 3 4`; with `Hard` monotone in
`l` this gives `Hard 2 l 4` for every `l ≥ 3`.
-/

namespace Programme.«20261025-1627-proof-complexity».Hard234

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoFPHP

/-- Restriction iterated: a refutation at `n ≥ m` gives one at `m`. -/
theorem down {p m k D : Nat} (hD : 1 ≤ D) (hmk : 0 < m + k) :
    ∀ n, m ≤ n → PPCRefutation p (ontoFPHP n k) D → PPCRefutation p (ontoFPHP m k) D := by
  intro n hn
  induction hn with
  | refl => exact id
  | @step n hmn ih =>
    intro h
    exact ih (Programme.«20261025-0459-proof-complexity».OntoSubst.ontoFPHP_restrict p n k D hD
      (by have : m ≤ n := hmn; omega) h)

/-- Conditional Step 1: the two finite facts at `(7,8)` give, for every `n ≥ 7`, no degree-4 PC
refutation of onto-FPHP^{n+8}_n over `Z/2`; hence `Hard 2 l 4` for every `l ≥ 3`. -/
theorem hard234_of (hND : Programme.«20261025-1627-proof-complexity».NoDrop.NoDrop 2 (ontoFPHP 7 8) 4)
    (hNS : ¬ Programme.«20261025-1627-proof-complexity».OntoNS.NSRefutation 2 (ontoFPHP 7 8) 4) :
    (∀ n, 7 ≤ n → ¬ PPCRefutation 2 (ontoFPHP n 8) 4) ∧
    (∀ l, 3 ≤ l → Programme.«20261025-1627-proof-complexity».OntoQ7.Hard 2 l 4) := by
  have h7 : ∀ n, 7 ≤ n → ¬ PPCRefutation 2 (ontoFPHP n 8) 4 :=
    fun n hn h => hNS (Programme.«20261025-1627-proof-complexity».NoDrop.pc_ns hND (down (by decide) (by decide) n hn h))
  refine ⟨h7, fun l hl => ?_⟩
  have h3 : Programme.«20261025-1627-proof-complexity».OntoQ7.Hard 2 3 4 := ⟨7, fun n hn => by simpa using h7 n hn⟩
  exact Programme.«20261025-1627-proof-complexity».OntoQ7.hard_mono_l (by decide) (by decide) hl h3

end Programme.«20261025-1627-proof-complexity».Hard234

#print axioms Programme.«20261025-1627-proof-complexity».Hard234.hard234_of
