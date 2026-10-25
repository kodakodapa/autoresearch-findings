import Programme.«20261021-1639-ontological».Deep.NotesHenkin
import Programme.«20261021-1639-ontological».Deep.HenkinCollapseCore

namespace Programme.«20261021-1639-ontological».Deep.Henkin

def singletonAssignment (x : h.D a) : Assignment h [a]
  | _, .here => x
  | _, .there v => nomatch v

def propertyTruth (h : Frame W) (p : h.D (.arr .entity .prop)) : h.D .entity → W → Prop :=
  fun x => h.truth (h.app p x)

theorem constant_lift (m : Model C W) (p : m.frame.D .prop) :
    ∃ f : m.frame.D (.arr .entity .prop), propertyTruth m.frame f = fun _ => m.frame.truth p := by
  let t : Term C [.prop] (.arr .entity .prop) := .lam (.var (.there .here))
  obtain ⟨f, hf⟩ := m.closed (singletonAssignment p) t
  refine ⟨f, ?_⟩
  funext x
  have he := denotes_clause hf x
  change m.frame.app f x = p at he
  exact congrArg m.frame.truth he

theorem bottom_admitted (m : Model C W) :
    ∃ p : m.frame.D .prop, m.frame.truth p = fun _ => False := by
  let ρ : Assignment m.frame [] := fun v => nomatch v
  obtain ⟨p, hp⟩ := m.closed ρ (.falsum : Term C [] .prop)
  exact ⟨p, denotes_clause hp⟩

theorem top_admitted (m : Model C W) :
    ∃ p : m.frame.D .prop, m.frame.truth p = fun _ => True := by
  obtain ⟨q, _⟩ := bottom_admitted m
  let ρ : Assignment m.frame [.prop] := singletonAssignment q
  let t : Term C [.prop] .prop := .equal (.var .here) (.var .here)
  refine ⟨translate m.frame m.interp t ρ, ?_⟩
  rw [truth_equal]
  funext w
  exact propext ⟨fun _ => True.intro, fun _ => rfl⟩

/-- Set-valued presentation of exactly the admitted truth images. The actual and
positive maps are parameters; no closure of arbitrary external maps is asserted. -/
def toGModel (m : Model C W) (actual : m.frame.D .entity → W → Prop)
    (positive : (m.frame.D .entity → W → Prop) → W → Prop) :
    Programme.«20261021-1639-ontological».Theorist.HenkinCollapse.GModel W (m.frame.D .entity) where
  rel := m.frame.rel
  actual := actual
  positive := positive
  adm := fun f => ∃ p, propertyTruth m.frame p = f
  admP := fun p => ∃ q, m.frame.truth q = p

theorem toGModel_closed (m : Model C W) (actual : m.frame.D .entity → W → Prop)
    (positive : (m.frame.D .entity → W → Prop) → W → Prop) :
    Programme.«20261021-1639-ontological».Theorist.HenkinCollapse.Closed (toGModel m actual positive) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := top_admitted m
    obtain ⟨f, hf⟩ := constant_lift m p
    exact ⟨f, by rw [hf, hp]⟩
  · obtain ⟨p, hp⟩ := bottom_admitted m
    obtain ⟨f, hf⟩ := constant_lift m p
    exact ⟨f, by rw [hf, hp]⟩
  · rintro p ⟨q, rfl⟩
    exact constant_lift m q

/-- Instantiates th's collapse argument with definable-term closure, with no
full-intension or world-separation assumption. -/
theorem admitted_mc_of_filter (m : Model C W)
    (actual : m.frame.D .entity → W → Prop)
    (positive : (m.frame.D .entity → W → Prop) → W → Prop) (a : Bool)
    (hU : Programme.«20261021-1639-ontological».Theorist.HenkinCollapse.HasU (toGModel m actual positive))
    (h0 : Programme.«20261021-1639-ontological».Theorist.HenkinCollapse.NoEmpty (toGModel m actual positive))
    (hup : Programme.«20261021-1639-ontological».Theorist.HenkinCollapse.UpCW (toGModel m actual positive) a)
    (h4 : Programme.«20261021-1639-ontological».Theorist.HenkinCollapse.A4 (toGModel m actual positive)) :
    ∀ p : m.frame.D .prop, ∀ w, m.frame.truth p w →
      ∀ v, m.frame.rel w v → m.frame.truth p v := by
  intro p
  exact Programme.«20261021-1639-ontological».Theorist.HenkinCollapse.mc_of_cw_A4 _ a
    (toGModel_closed m actual positive) hU h0 hup h4 _ ⟨p, rfl⟩

#print axioms constant_lift
#print axioms toGModel_closed
#print axioms admitted_mc_of_filter
end Programme.«20261021-1639-ontological».Deep.Henkin
