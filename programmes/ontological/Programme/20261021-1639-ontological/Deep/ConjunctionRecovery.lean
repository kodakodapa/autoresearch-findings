import Programme.«20261021-1639-ontological».Theorist.V2Deep

/-! Recovery of unrestricted world-dependent conjunction from admitted modal collapse.
No frame identity or world-name assumption is used. -/
namespace Programme.«20261021-1639-ontological».Deep.ConjunctionRecovery
open Programme.«20261021-1639-ontological».Deep Programme.«20261021-1639-ontological».Deep.Henkin Programme.«20261021-1639-ontological».Theorist.HenkinScott
open Programme.«20261021-1639-ontological».Theorist.SymmetricModels Programme.«20261021-1639-ontological».Theorist.ScottBridge
open Programme.«20261021-1639-ontological».Theorist.ScottDeep Programme.«20261021-1639-ontological».Theorist.V2Deep

variable {W : Type} {m : Henkin.Model OntConst W}
  {gm : GModel W (m.frame.D .entity)}

theorem recover (hp : Presents m gm) (a : Bool) (ρ : Assignment m.frame [])
    (hmc : MCadm gm) (hG : A3 gm) (h4 : Programme.«20261021-1639-ontological».Theorist.HenkinVariant2.Ax4 gm a) :
    Programme.«20261021-1639-ontological».Theorist.HenkinVariant2.Ax1Gen gm a (admH m) := by
  intro s p w hs hpa hpos hconj
  obtain ⟨S, hS⟩ := hs
  have hgadm := (cloV2_of_presents hp a ρ).god
  apply h4 (GH gm) p w hgadm hpa (hG w)
  intro v hv y hy hgy
  apply (hconj v hv y hy).2
  intro q hqa hsqv
  obtain ⟨Q, rfl⟩ := (adm_iff hp q).1 hqa
  have hneg : gm.admP (fun u => ¬ s (img m Q) u) := by
    apply (hp.1 _).1
    refine ⟨Henkin.translate m.frame m.interp
      (neg (.app v1 v0) : T [Property, HP] .prop) (push (push ρ S) Q), ?_⟩
    funext u
    apply propext
    change sem m (push (push ρ S) Q) (neg (.app v1 v0)) u ↔ _
    simp only [sem_neg, sem_app, tr_v0, tr_v1]
    exact not_congr (hS Q u).symm
  have hsqw : s (img m Q) w := Classical.byContradiction fun hn =>
    hmc _ hneg w hn v hv hsqv
  have hP : gm.admP (gm.positive (img m Q)) := by
    apply (hp.1 _).1
    refine ⟨m.frame.app (m.interp OntConst.positive) Q, ?_⟩
    funext u
    exact propext (hp.2.2.2.2 Q u)
  exact hgy _ hqa (hmc _ hP w (hpos _ hqa hsqw) v hv)

theorem recover_deep (hp : Presents m gm) (a : Bool) (ρ : Assignment m.frame [])
    (hmc : DeepValid m ρ tMC) (hG : A3 gm) (h4 : Programme.«20261021-1639-ontological».Theorist.HenkinVariant2.Ax4 gm a) :
    DeepValid m ρ (tAx1Gen a) :=
  (bridge_Ax1Gen hp a ρ).2 (recover hp a ρ ((bridge_MC hp ρ).1 hmc) hG h4)

#print axioms recover
#print axioms recover_deep
end Programme.«20261021-1639-ontological».Deep.ConjunctionRecovery
