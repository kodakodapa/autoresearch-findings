import Programme.«20261021-1639-ontological».Deep.NotesHenkin
import Programme.«20261021-1639-ontological».Theorist.ScottDeep

/-! Operator adapter for th's ScottBridge (P285), using K46.
The Boolean selects uniform actualist/possibilist guards, not mixed Anderson guards. -/
namespace Programme.«20261021-1639-ontological».Deep.ScottNotes
open Henkin NotesHenkin NotesParameterized
open Programme.«20261021-1639-ontological».Theorist.ScottBridge Programme.«20261021-1639-ontological».Theorist.ScottDeep
open Programme.«20261021-1639-ontological».Theorist.HenkinScott Programme.«20261021-1639-ontological».Theorist.SymmetricModels
variable {W : Type} (m : Henkin.Model OntConst W)
def valid (ρ : Assignment m.frame []) (t : Term OntConst [] .prop) : Prop :=
  Mvalid (m.frame.truth (NotesHenkin.toNotes m.frame m.interp t ρ))
theorem notes_profile {gm : GModel W (m.frame.D .entity)} (hp : Presents m gm)
    (a : Bool) (ρ : Assignment m.frame []) :
    (valid m ρ tA1a ↔ A1a gm) ∧ (valid m ρ tA1b ↔ A1b gm) ∧
    (valid m ρ (tA2 a) ↔ A2 gm a) ∧ (valid m ρ tA3 ↔ A3 gm) ∧
    (valid m ρ tA4 ↔ A4 gm) ∧ (valid m ρ (tA5 a) ↔ A5 gm a) ∧
    (valid m ρ tMC ↔ MCadm gm) := by
  simp only [valid, validity_bridge]
  exact profile hp a ρ

theorem canonical_notes_profile (a : Bool) (ρ : Assignment m.frame []) :
    (valid m ρ tA1a ↔ A1a (canon m)) ∧ (valid m ρ tA1b ↔ A1b (canon m)) ∧
    (valid m ρ (tA2 a) ↔ A2 (canon m) a) ∧ (valid m ρ tA3 ↔ A3 (canon m)) ∧
    (valid m ρ tA4 ↔ A4 (canon m)) ∧ (valid m ρ (tA5 a) ↔ A5 (canon m) a) ∧
    (valid m ρ tMC ↔ MCadm (canon m)) :=
  notes_profile m (canon_presents m) a ρ
#print axioms notes_profile
#print axioms canonical_notes_profile
end Programme.«20261021-1639-ontological».Deep.ScottNotes
