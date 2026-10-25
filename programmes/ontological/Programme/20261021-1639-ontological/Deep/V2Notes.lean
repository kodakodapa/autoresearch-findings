import Programme.«20261021-1639-ontological».Deep.ScottNotes
import Programme.«20261021-1639-ontological».Theorist.V2Deep

/-! Parameterized restricted Notes-operator adapter for th's P303 higher-type bridge.
This is object-language closure, not a Henkin model of HOL with a world type.
The Boolean chooses uniform entity guards; higher quantifiers are unguarded. -/
namespace Programme.«20261021-1639-ontological».Deep.V2Notes
open Henkin ScottNotes
open Programme.«20261021-1639-ontological».Theorist.ScottBridge Programme.«20261021-1639-ontological».Theorist.ScottDeep
open Programme.«20261021-1639-ontological».Theorist.SymmetricModels Programme.«20261021-1639-ontological».Theorist.HenkinScott
open Programme.«20261021-1639-ontological».Theorist.V2Deep
variable {W : Type} (m : Henkin.Model OntConst W)

theorem notes_profile {gm : GModel W (m.frame.D .entity)} (hp : Presents m gm)
    (a : Bool) (ρ : Assignment m.frame []) :
    (valid m ρ (tAx1Gen a) ↔ Programme.«20261021-1639-ontological».Theorist.HenkinVariant2.Ax1Gen gm a (admH m)) ∧
    (valid m ρ tAx2a ↔ Programme.«20261021-1639-ontological».Theorist.HenkinVariant2.Ax2a gm) ∧
    (valid m ρ tT ↔ ∀ c, gm.admP c → ∀ w, (∀ v, gm.rel w v → c v) → c w) ∧
    (valid m ρ (tNecEx a) ↔ ∀ w v, gm.rel w v → ∃ x, guard gm a x v ∧ GH gm x v) := by
  simp only [valid, NotesHenkin.validity_bridge]
  exact ⟨bridge_Ax1Gen hp a ρ, bridge_Ax2a hp ρ, bridge_T hp ρ,
    bridge_NecEx hp a ρ⟩

theorem canonical_closure (a : Bool) (ρ : Assignment m.frame []) :
    Programme.«20261021-1639-ontological».Theorist.HenkinVariant2.CloV2 (canon m) a (admH m) :=
  cloV2_of_presents (canon_presents m) a ρ

/-- A compositional transport, with no extra frame or closure-interface assumptions. -/
theorem notes_consequences (a : Bool) (ρ : Assignment m.frame [])
    (h1 : valid m ρ (tAx1Gen a)) (h2 : valid m ρ tAx2a) :
    valid m ρ tT ∧ valid m ρ (tNecEx a) ∧
      (valid m ρ tA4 → valid m ρ tMC) := by
  simp only [valid, NotesHenkin.validity_bridge] at *
  exact ⟨(deep_v2 a ρ h1 h2).1, (deep_v2 a ρ h1 h2).2,
    fun h4 => deep_v2_mc a ρ h1 h2 h4⟩

#print axioms notes_profile
#print axioms canonical_closure
#print axioms notes_consequences
end Programme.«20261021-1639-ontological».Deep.V2Notes
