import Programme.«20261026-1402-proof-complexity».Ext0
import Programme.«20261025-1627-proof-complexity».OntoQ7

/-!
# Second route to degree 4 for `k = 8` over `Z/2`, conditional on the owner's EXT computation

Owner note P118: th's `EXT_2(7,8,d+1)` was computed for `d+1 = 1..4` (excess 0 in all 15 isotypic
components under the free `C15 × C7` action). In library coordinates that is
`ExtLemma.EXT 2 7 8 d` for `d = 0..3`; `d = 0` is proved (`Ext0.ext0`). This file states, as a
conditional theorem, what the remaining three computed levels give through the EXT criterion
(`ExtLemma.no_refutation_of_ext_ge`), independently of the `NoDrop` route (`Split.hard234_on`).
The hypotheses are computed facts, not proved here.
-/

namespace Programme.«20261027-0607-proof-complexity».Ext784

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261025-1627-proof-complexity».OntoQ7

theorem hard_of_ext784 (h1 : EXT 2 7 8 1) (h2 : EXT 2 7 8 2) (h3 : EXT 2 7 8 3) :
    (∀ n, 7 ≤ n → ¬ PPCRefutation 2 (ontoFPHP n 8) 4) ∧ (∀ l, 3 ≤ l → Hard 2 l 4) := by
  have base : ∀ n, 7 ≤ n → ¬ PPCRefutation 2 (ontoFPHP n 8) 4 := by
    intro n hn
    refine no_refutation_of_ext_ge (by decide) (by decide) (by decide) ?_ n hn
    intro d hd
    match d, hd with
    | 0, _ => exact Programme.«20261026-1402-proof-complexity».Ext0.ext0 (by decide) (by decide)
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3
  refine ⟨base, fun l hl => hard_mono_l (by decide) (by decide) hl ⟨7, ?_⟩⟩
  intro n hn
  exact base n hn

end Programme.«20261027-0607-proof-complexity».Ext784

#print axioms Programme.«20261027-0607-proof-complexity».Ext784.hard_of_ext784
