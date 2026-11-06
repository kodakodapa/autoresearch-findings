import Programme.«20261026-1037-proof-complexity».Split

/-! Refiles of the programme's `Split` theorems (owner P29, item 2): each theorem restates the
library theorem by its own type and proves it by the library name. -/

namespace Programme.«20261026-1402-proof-complexity».RefileSplit

open Programme.«20261026-1037-proof-complexity»

theorem noDrop_of_on : type_of% @Split.noDrop_of_on := @Split.noDrop_of_on
theorem hard234_on : type_of% @Split.hard234_on := @Split.hard234_on

example : type_of% @noDrop_of_on = type_of% @Split.noDrop_of_on := rfl
example : type_of% @hard234_on = type_of% @Split.hard234_on := rfl

end Programme.«20261026-1402-proof-complexity».RefileSplit

#print axioms Programme.«20261026-1402-proof-complexity».RefileSplit.noDrop_of_on
#print axioms Programme.«20261026-1402-proof-complexity».RefileSplit.hard234_on
