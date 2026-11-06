import Programme.«20261027-0607-proof-complexity».Ext784
import Programme.«20261027-0607-proof-complexity».Lift78

/-!
# Degree 4 for `k = 8` over `Z/2` from two computed EXT levels

`Work.Ext784.hard_of_ext784` assumed `EXT 2 7 8 d` for `d = 1, 2, 3`. Level `1` is now proved
(`Work.Lift78.ext1`), so only the owner's computed levels `d = 2, 3` (th's `EXT_2(7,8,3)`,
`EXT_2(7,8,4)`) remain as hypotheses.
-/

namespace Programme.«20261027-0607-proof-complexity».Ext784b

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261025-1627-proof-complexity».OntoQ7

theorem hard_of_ext23 (h2 : EXT 2 7 8 2) (h3 : EXT 2 7 8 3) :
    (∀ n, 7 ≤ n → ¬ PPCRefutation 2 (ontoFPHP n 8) 4) ∧ (∀ l, 3 ≤ l → Hard 2 l 4) :=
  Programme.«20261027-0607-proof-complexity».Ext784.hard_of_ext784 Programme.«20261027-0607-proof-complexity».Lift78.ext1 h2 h3

end Programme.«20261027-0607-proof-complexity».Ext784b

#print axioms Programme.«20261027-0607-proof-complexity».Ext784b.hard_of_ext23
