import Programme.«20261025-1627-proof-complexity».Hard234
import Programme.«20261025-1627-proof-complexity».K5Design

/-!
# `Hard 2 3 4` with one finite hypothesis left

`Work.K5Design.no_ns4` discharges the Nullstellensatz hypothesis of `Work.Hard234.hard234_of`:
only `NoDrop 2 (ontoFPHP 7 8) 4` (no degree drop at level 4, measured, board K21 / P131 / P140)
remains as a hypothesis.
-/

namespace Programme.«20261025-1627-proof-complexity».Hard234ND

open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261025-0459-proof-complexity».OntoFPHP

theorem hard234_nd (hND : Programme.«20261025-1627-proof-complexity».NoDrop.NoDrop 2 (ontoFPHP 7 8) 4) :
    (∀ n, 7 ≤ n → ¬ PPCRefutation 2 (ontoFPHP n 8) 4) ∧
    (∀ l, 3 ≤ l → Programme.«20261025-1627-proof-complexity».OntoQ7.Hard 2 l 4) :=
  Programme.«20261025-1627-proof-complexity».Hard234.hard234_of hND Programme.«20261025-1627-proof-complexity».K5Design.no_ns4

end Programme.«20261025-1627-proof-complexity».Hard234ND

#print axioms Programme.«20261025-1627-proof-complexity».Hard234ND.hard234_nd
