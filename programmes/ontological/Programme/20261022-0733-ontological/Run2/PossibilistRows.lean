import Programme.«20261022-0733-ontological».Run2.Principal
import Programme.«20261022-0733-ontological».Run2.GexTwo
import Programme.«20261022-0733-ontological».Run2.TwoNeedsAx2a
import Programme.«20261022-0733-ontological».Run2.Monotheism

/-! # Closed possibilist rows of K32, K33, K34, K37, K38

The possibilist reading of `TwoClosed.Model` is `act := fun _ _ => True` (all guards trivial).
The positive theorems of K32 (`mc_of_two`), K33 (`mono`), K34 (`gex_2a4`), K37 (`uf_of_2a4two`),
K38 (`princ_of_2a4two`, `mc_of_princ_2b`) hold for an arbitrary `act`, hence in that reading.
Every minimality witness used for them already has universal actuality (`poss_witnesses`),
so each minimality result holds verbatim in the closed possibilist regime. -/

namespace Programme.«20261022-0733-ontological».Run2.PossibilistRows

open Programme.«20261022-0733-ontological».Run2 Programme.«20261022-0733-ontological».Run2.TwoClosed

def Possibilist {W D : Type} (M : Model W D) : Prop := ∀ x w, M.act x w

theorem poss_witnesses :
    Possibilist Minimal.noAx2a ∧ Possibilist TwoNeedsAx2a.anti ∧ Possibilist RigidExit.rx ∧
    Possibilist FM.fm ∧ Possibilist TwoNeedsAx2a.tm ∧ Possibilist Monotheism.tg :=
  ⟨fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial,
   fun _ _ => trivial, fun _ _ => trivial⟩

/-- K34 and K37/K38 in the possibilist regime, stated with the hypothesis made explicit. -/
theorem poss_rows {W D : Type} [Nonempty D] (M : Model W D) (_hp : Possibilist M)
    (C : Closed M) (h2a : Ax2a M) (h4 : Ax4 M) (hT : Ax1GenTwo M) :
    (∀ w, ExG M w) ∧ (∀ w, Ultrafilter.UF M w) ∧ (∀ w, Principal.Princ M w) :=
  ⟨GexTwo.gex_2a4 C h2a h4 hT, Ultrafilter.uf_of_2a4two C h2a h4 hT,
   Principal.princ_of_2a4two C h2a h4 hT⟩

end Programme.«20261022-0733-ontological».Run2.PossibilistRows

#print axioms Programme.«20261022-0733-ontological».Run2.PossibilistRows.poss_witnesses
#print axioms Programme.«20261022-0733-ontological».Run2.PossibilistRows.poss_rows
