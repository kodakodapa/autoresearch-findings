import Programme.«20261021-1639-ontological».Atlas.Scott

namespace Programme.«20261021-1639-ontological».Atlas.Scott
open Programme.«20261021-1639-ontological».Countermodels.Tests Programme.«20261021-1639-ontological».Countermodels.Scott
variable {W E : Type}

def TFrame (R : W → W → Prop) (t : W → W) : Prop :=
  (∀ w, R w (t w)) ∧ (∀ w v, R (t w) v ↔ v = t w) ∧
  (∀ w v, R w v → t v = t w)

theorem scott_principal (m : Model W E) (a : Bool) (h : Axioms m a) (w : W) :
    ∃ y v, m.rel w v ∧ guard m a y v ∧ G m y v ∧
      ∀ p, m.positive p w ↔ p y v := by
  classical
  obtain ⟨v, hv, y, hy, hg⟩ := poss_of_A1a_A2_A3 m a
    (fun p w hp => (h.A1 p w).mpr hp) h.A2 h.A3 w
  refine ⟨y, v, hv, hy, hg, ?_⟩
  intro p
  constructor
  · intro hp; exact hg p (h.A4 p w hp v hv)
  · intro hp
    apply Classical.byContradiction
    intro hn
    exact hg _ (h.A4 _ w ((h.A1 p w).mp hn) v hv) hp

theorem scott_has_tframe (m : Model W E) (a : Bool) (h : Axioms m a) :
    ∃ t, TFrame m.rel t := by
  classical
  let y := fun w => (scott_principal m a h w).choose
  let t := fun w => (scott_principal m a h w).choose_spec.choose
  have spec := fun w => (scott_principal m a h w).choose_spec.choose_spec
  have ht : ∀ w, m.rel w (t w) := fun w => (spec w).1
  have hg : ∀ w, G m (y w) (t w) := fun w => (spec w).2.2.1
  have hp : ∀ w p, m.positive p w ↔ p (y w) (t w) := fun w => (spec w).2.2.2
  have stable : ∀ w v, m.rel w v → t v = t w := by
    intro w v hv
    exact ((hp v (fun _ u => u = t w)).mp
      (h.A4 _ w ((hp w _).mpr rfl) v hv))
  refine ⟨t, ht, ?_, stable⟩
  intro w v
  constructor
  · intro hv
    have hn := hg w (NE m a) (h.A5 (t w))
    exact (hn _ (singleton_essence m a (y w) (t w)) v hv).choose_spec.2.2
  · intro hv
    subst v
    have he := stable w (t w) (ht w)
    simpa only [he] using ht (t w)

def principalModel (R : W → W → Prop) (t : W → W) (x : E) : Model W E :=
  ⟨R, fun _ _ => True, fun p w => p x (t w)⟩

theorem principalModel_axioms (R : W → W → Prop) (t : W → W) (x : E)
    (ht : TFrame R t) (a : Bool) : Axioms (principalModel R t x) a := by
  have idem : ∀ w, t (t w) = t w := fun w => ht.2.2 w (t w) (ht.1 w)
  constructor
  · intro p w; rfl
  · intro p q w hp hi
    exact hi (t w) (ht.1 w) x (fun _ => trivial) hp
  · intro w p hp
    change p x (t (t w)) at hp
    simpa only [idem w] using hp
  · intro p w hp v hv
    change p x (t w) at hp
    change p x (t v)
    simpa only [ht.2.2 w v hv] using hp
  · intro w p hp v hv
    have he : v = t w := (ht.2.1 w v).mp hv
    subst v
    exact ⟨x, (fun _ => trivial), hp.1⟩

theorem scott_frame_iff [Nonempty E] (R : W → W → Prop) (a : Bool) :
    (∃ act : E → W → Prop, ∃ pos, Axioms (Model.mk R act pos) a) ↔
      ∃ t, TFrame R t := by
  constructor
  · rintro ⟨act, pos, h⟩
    exact scott_has_tframe _ a h
  · rintro ⟨t, ht⟩
    classical
    exact ⟨_, _, principalModel_axioms R t (Classical.choice inferInstance) ht a⟩

theorem scott_MC_iff (m : Model W E) :
    MC m ↔ ∀ w v, m.rel w v → w = v := by
  constructor
  · intro h w v hv
    exact (h (fun u => u = w) w rfl v hv).symm
  · intro h p w hp v hv
    exact h w v hv ▸ hp

theorem scott_T3_iff (m : Model W E) (a : Bool) (h : Axioms m a) :
    T3 m a ↔ ∀ w v, m.rel w v → ∀ u, m.rel w u → v = u := by
  classical
  constructor
  · intro ht w v hv u hu
    obtain ⟨y, _, hy⟩ := ht w v hv
    obtain ⟨z, _, hz⟩ := ht w u hu
    let p : E → W → Prop := fun _ s => s = v
    by_cases hp : m.positive p w
    · exact (hz p (h.A4 p w hp u hu)).symm
    · exact (hy _ (h.A4 _ w ((h.A1 p w).mp hp) v hv) rfl).elim
  · intro hs w v hv
    obtain ⟨y, u, hu, ha, hg, _⟩ := scott_principal m a h w
    have he := hs w u hu v hv
    exact he ▸ ⟨y, ha, hg⟩

#print axioms scott_principal
#print axioms scott_has_tframe
#print axioms principalModel_axioms
#print axioms scott_frame_iff
#print axioms scott_MC_iff
#print axioms scott_T3_iff
end Programme.«20261021-1639-ontological».Atlas.Scott
