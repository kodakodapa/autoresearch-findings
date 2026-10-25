import Programme.«20261021-1639-ontological».Deep.V2Notes

/-! Ax1/Ax4 terms and bridge proofs extracted unchanged from th P348.
Only the imports/namespace and Notes adapter are local. Uniform guards only. -/
namespace Programme.«20261021-1639-ontological».Deep.V2FullNotes
open Programme.«20261021-1639-ontological».Deep Programme.«20261021-1639-ontological».Deep.Henkin Programme.«20261021-1639-ontological».Theorist.HenkinScott
open Programme.«20261021-1639-ontological».Theorist.SymmetricModels Programme.«20261021-1639-ontological».Theorist.ScottBridge
open Programme.«20261021-1639-ontological».Theorist.ScottDeep Programme.«20261021-1639-ontological».Theorist.V2Deep
open Programme.«20261021-1639-ontological».Theorist

variable {W : Type} {m : Henkin.Model OntConst W} {gm : GModel W (m.frame.D .entity)}

def tAx1 : T [] .prop :=
  .all (a := Property) (.all (a := Property) (.imp (pos v1) (.imp (pos v0)
    (pos (.lam (conj (.app v2 v0) (.app v1 v0)))))))
def tAx4 (a : Bool) : T [] .prop := tA2 a

theorem bridge_Ax1 (hp : Presents m gm) (ρ : Assignment m.frame []) :
    DeepValid m ρ tAx1 ↔ HenkinVariant2.Ax1 gm := by
  rw [deepValid_iff]
  simp only [tAx1, sem_all, sem_imp, sem_conj, sem_pos hp, img_lam, sem_app, tr_v0, tr_v1, tr_v2]
  constructor
  · intro h p q w hpa hqa hpw hqw
    obtain ⟨P, rfl⟩ := (hp.2.1 p).2 hpa
    obtain ⟨Q, rfl⟩ := (hp.2.1 q).2 hqa
    exact h w P Q hpw hqw
  · intro h w P Q hpw hqw
    exact h _ _ w ((hp.2.1 _).1 ⟨P, rfl⟩) ((hp.2.1 _).1 ⟨Q, rfl⟩) hpw hqw

theorem bridge_Ax4 (hp : Presents m gm) (a : Bool) (ρ : Assignment m.frame []) :
    DeepValid m ρ (tAx4 a) ↔ HenkinVariant2.Ax4 gm a := bridge_A2 hp a ρ


theorem notes_profile (hp : Presents m gm) (a : Bool) (ρ : Assignment m.frame []) :
    (ScottNotes.valid m ρ tAx1 ↔ HenkinVariant2.Ax1 gm) ∧
    (ScottNotes.valid m ρ (tAx4 a) ↔ HenkinVariant2.Ax4 gm a) := by
  simp only [ScottNotes.valid, NotesHenkin.validity_bridge]
  exact ⟨bridge_Ax1 hp ρ, bridge_Ax4 hp a ρ⟩

theorem canonical_notes_profile (a : Bool) (ρ : Assignment m.frame []) :
    (ScottNotes.valid m ρ tAx1 ↔ HenkinVariant2.Ax1 (canon m)) ∧
    (ScottNotes.valid m ρ (tAx4 a) ↔ HenkinVariant2.Ax4 (canon m) a) :=
  notes_profile (canon_presents m) a ρ

#print axioms bridge_Ax1
#print axioms bridge_Ax4
#print axioms notes_profile
#print axioms canonical_notes_profile
end Programme.«20261021-1639-ontological».Deep.V2FullNotes
