import Programme.«20261021-1639-ontological».Deep.V2FullNotes

/-! Mixed Anderson guards: inclusion/essence use all entities, while necessary
existence uses actual entities. The two choices are independent syntax parameters.
Reuses the compositional lemmas of th's ScottBridge; no atlas consequence asserted. -/
namespace Programme.«20261021-1639-ontological».Deep.MixedNotes
open Henkin ScottNotes
open Programme.«20261021-1639-ontological».Theorist.ScottBridge Programme.«20261021-1639-ontological».Theorist.ScottDeep
open Programme.«20261021-1639-ontological».Theorist.SymmetricModels Programme.«20261021-1639-ontological».Theorist.HenkinScott
open Programme.«20261021-1639-ontological».Theorist.V2Deep
open Programme.«20261021-1639-ontological».Theorist
variable {W : Type} {m : Henkin.Model OntConst W}
variable {gm : GModel W (m.frame.D .entity)}

def tNEMixed (ess ex : Bool) : T [] Property :=
  .lam (.all (.imp (tEss ess) (.box (tExA ex))))
def tA5Mixed (ess ex : Bool) : T [] .prop := pos (tNEMixed ess ex)
def NEMixed (gm : GModel W E) (ess ex : Bool) (x : E) (w : W) : Prop :=
  ∀ p, gm.adm p → EssH gm ess p x w →
    ∀ v, gm.rel w v → ∃ y, guard gm ex y v ∧ p y v

theorem uniform_term (a : Bool) : tNEMixed a a = tNE a := rfl
theorem uniform_image (gm : GModel W E) (a : Bool) : NEMixed gm a a = NEH gm a := rfl

theorem img_NEMixed (hp : Presents m gm) (ess ex : Bool) (ρ : Assignment m.frame []) :
    (fun x => m.frame.truth (m.frame.app (Henkin.translate m.frame m.interp (tNEMixed ess ex) ρ) x)) =
      NEMixed gm ess ex := by
  rw [tNEMixed, img_lam]
  funext x w
  simp only [sem_all, sem_imp, sem_box, sem_Ess hp, sem_ExA hp]
  apply propext
  constructor
  · intro h p ha hess v hv
    obtain ⟨P, rfl⟩ := (hp.2.1 p).2 ha
    exact h P hess v ((hp.2.2.1 w v).2 hv)
  · intro h P hess v hv
    exact h _ ((hp.2.1 _).1 ⟨P, rfl⟩) hess v ((hp.2.2.1 w v).1 hv)

theorem bridge_A5Mixed (hp : Presents m gm) (ess ex : Bool) (ρ : Assignment m.frame []) :
    DeepValid m ρ (tA5Mixed ess ex) ↔ ∀ w, gm.positive (NEMixed gm ess ex) w := by
  rw [deepValid_iff]
  simp only [tA5Mixed, sem_pos hp, img_NEMixed hp]

theorem mixed_admitted (hp : Presents m gm) (ess ex : Bool) (ρ : Assignment m.frame []) :
    gm.adm (NEMixed gm ess ex) := by
  apply (hp.2.1 _).1
  exact ⟨Henkin.translate m.frame m.interp (tNEMixed ess ex) ρ, img_NEMixed hp ess ex ρ⟩

/-- Scott Anderson: possibilist A2 and essence, actualist NE and conclusion. -/
theorem scott_profile (hp : Presents m gm) (ρ : Assignment m.frame []) :
    (valid m ρ tA1a ↔ A1a gm) ∧ (valid m ρ tA1b ↔ A1b gm) ∧
    (valid m ρ (tA2 false) ↔ A2 gm false) ∧ (valid m ρ tA3 ↔ A3 gm) ∧
    (valid m ρ tA4 ↔ A4 gm) ∧
    (valid m ρ (tA5Mixed false true) ↔ ∀ w, gm.positive (NEMixed gm false true) w) ∧
    (valid m ρ (tNecEx true) ↔ ∀ w v, gm.rel w v → ∃ x, guard gm true x v ∧ GH gm x v) ∧
    (valid m ρ tMC ↔ MCadm gm) := by
  simp only [valid, NotesHenkin.validity_bridge]
  exact ⟨bridge_A1a hp ρ, bridge_A1b hp ρ, bridge_A2 hp false ρ, bridge_A3 hp ρ,
    bridge_A4 hp ρ, bridge_A5Mixed hp false true ρ, bridge_NecEx hp true ρ, bridge_MC hp ρ⟩

/-- Variant 2 Anderson: all-entity Ax1Gen/Ax4, mixed Ax3. -/
theorem v2_profile (hp : Presents m gm) (ρ : Assignment m.frame []) :
    (valid m ρ V2FullNotes.tAx1 ↔ HenkinVariant2.Ax1 gm) ∧
    (valid m ρ (tAx1Gen false) ↔ HenkinVariant2.Ax1Gen gm false (admH m)) ∧
    (valid m ρ tAx2a ↔ HenkinVariant2.Ax2a gm) ∧
    (valid m ρ tA4 ↔ A4 gm) ∧
    (valid m ρ (tA5Mixed false true) ↔ ∀ w, gm.positive (NEMixed gm false true) w) ∧
    (valid m ρ (V2FullNotes.tAx4 false) ↔ HenkinVariant2.Ax4 gm false) := by
  simp only [valid, NotesHenkin.validity_bridge]
  exact ⟨V2FullNotes.bridge_Ax1 hp ρ, bridge_Ax1Gen hp false ρ, bridge_Ax2a hp ρ,
    bridge_A4 hp ρ, bridge_A5Mixed hp false true ρ, V2FullNotes.bridge_Ax4 hp false ρ⟩

#print axioms img_NEMixed
#print axioms bridge_A5Mixed
#print axioms mixed_admitted
#print axioms scott_profile
#print axioms v2_profile
end Programme.«20261021-1639-ontological».Deep.MixedNotes
