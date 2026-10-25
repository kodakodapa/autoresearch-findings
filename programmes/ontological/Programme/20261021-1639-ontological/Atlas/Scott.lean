import Programme.«20261021-1639-ontological».Countermodels.Scott

namespace Programme.«20261021-1639-ontological».Atlas.Scott
open Programme.«20261021-1639-ontological».Countermodels.Tests Programme.«20261021-1639-ontological».Countermodels.Scott
variable {W E : Type} (m : Model W E) (a : Bool)

def A1a : Prop := ∀ p w, m.positive (fun x v => ¬ p x v) w → ¬ m.positive p w
def A1b : Prop := ∀ p w, ¬ m.positive p w → m.positive (fun x v => ¬ p x v) w
def A2 : Prop := ∀ p q w, m.positive p w →
  (∀ v, m.rel w v → ∀ y, guard m a y v → p y v → q y v) → m.positive q w

theorem mono_of_A1b (h : A1b m) :
    ∀ w x y, G m x w → G m y w → x = y := by
  classical
  intro w x y hx hy
  let p : E → W → Prop := fun z _ => x = z
  by_cases hp : m.positive p w
  · exact hy p hp
  · exact (hx (fun z v => ¬ p z v) (h p w hp) rfl).elim

theorem positive_possible (h1 : A1a m) (h2 : A2 m a)
    (p : E → W → Prop) (w : W) (hp : m.positive p w) :
    ∃ v, m.rel w v ∧ ∃ x, guard m a x v ∧ p x v := by
  classical
  apply Classical.byContradiction
  intro hn
  apply h1 p w (h2 p (fun x v => ¬ p x v) w hp ?_) hp
  intro v hv x hx hpx
  exact (hn ⟨v, hv, x, hx, hpx⟩).elim

theorem poss_of_A1a_A2_A3 (h1 : A1a m) (h2 : A2 m a)
    (h3 : ∀ w, m.positive (G m) w) :
    ∀ w, ∃ v, m.rel w v ∧ ∃ x, guard m a x v ∧ G m x v :=
  fun w => positive_possible m a h1 h2 (G m) w (h3 w)

theorem singleton_essence (x : E) (w : W) :
    Ess m a (fun y v => y = x ∧ v = w) x w := by
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  intro q hq v _ y _ hy
  rcases hy with ⟨rfl, rfl⟩
  exact hq

theorem id_of_KB_A1a_A2_A5 (symm : ∀ w v, m.rel w v → m.rel v w)
    (h1 : A1a m) (h2 : A2 m a) (h5 : ∀ w, m.positive (NE m a) w) :
    ∀ w v, m.rel w v → w = v := by
  intro w v hwv
  obtain ⟨t, hwt, x, _, hx⟩ := positive_possible m a h1 h2 (NE m a) w (h5 w)
  have htw := symm w t hwt
  have hwtEq : w = t := (hx _ (singleton_essence m a x t) w htw).choose_spec.2.2
  subst t
  exact ((hx _ (singleton_essence m a x w) v hwv).choose_spec.2.2).symm

theorem mc_of_KB_A1a_A2_A5 (symm : ∀ w v, m.rel w v → m.rel v w)
    (h1 : A1a m) (h2 : A2 m a) (h5 : ∀ w, m.positive (NE m a) w) : MC m := by
  intro p w hp v hv
  exact id_of_KB_A1a_A2_A5 m a symm h1 h2 h5 w v hv ▸ hp

theorem t3_of_KB_A1a_A2_A3_A5 (symm : ∀ w v, m.rel w v → m.rel v w)
    (h1 : A1a m) (h2 : A2 m a) (h3 : ∀ w, m.positive (G m) w)
    (h5 : ∀ w, m.positive (NE m a) w) : T3 m a := by
  intro w v hv
  obtain ⟨t, ht, x, hx⟩ := poss_of_A1a_A2_A3 m a h1 h2 h3 v
  have he := id_of_KB_A1a_A2_A5 m a symm h1 h2 h5 v t ht
  exact ⟨x, he.symm ▸ hx⟩

#print axioms mono_of_A1b
#print axioms poss_of_A1a_A2_A3
#print axioms id_of_KB_A1a_A2_A5
#print axioms mc_of_KB_A1a_A2_A5
#print axioms t3_of_KB_A1a_A2_A3_A5
end Programme.«20261021-1639-ontological».Atlas.Scott
