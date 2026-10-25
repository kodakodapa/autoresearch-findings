import Notes.HOMLinHOL

/- Parameterized copies of the shallow semantics in Notes.HOMLinHOL.
No global postulate from that module is used in the proofs below.
The test theories have no positivity axioms; positivity is included as free model data.
All witnesses have nonempty finite world and entity types. -/
attribute [-instance] Classical.propDecidable

namespace Programme.«20261021-1639-ontological».Countermodels.Tests
instance (p : Unit → Prop) [Decidable (p ())] : Decidable (∀ x, p x) :=
  decidable_of_iff (p ()) ⟨fun h x => by cases x; exact h, fun h => h ()⟩
instance (p : Unit → Prop) [Decidable (p ())] : Decidable (∃ x, p x) :=
  decidable_of_iff (p ()) ⟨fun h => ⟨(), h⟩, fun ⟨x, h⟩ => by cases x; exact h⟩

structure Model (W E : Type) where
  rel : W → W → Prop
  actual : E → W → Prop
  positive : (E → W → Prop) → W → Prop

def S4 {W E} (m : Model W E) : Prop :=
  (∀ w, m.rel w w) ∧ (∀ w v u, m.rel w v → m.rel v u → m.rel w u)
def S5 {W E} (m : Model W E) : Prop :=
  S4 m ∧ (∀ w v, m.rel w v → m.rel v w)
def valid {W} (p : W → Prop) := ∀ w, p w
def box {W E} (m : Model W E) (p : W → Prop) := fun w => ∀ v, m.rel w v → p v
def dia {W E} (m : Model W E) (p : W → Prop) := fun w => ∃ v, m.rel w v ∧ p v
def allAct {W E} (m : Model W E) (p : E → W → Prop) :=
  fun w => ∀ x, m.actual x w → p x w
def exAct {W E} (m : Model W E) (p : E → W → Prop) :=
  fun w => ∃ x, m.actual x w ∧ p x w
def leib {W α : Type} (x y : α) : W → Prop := fun w =>
  ∀ p : α → W → Prop, p x w → p y w

def full (a : Unit → Bool → Prop) : Model Bool Unit :=
  ⟨fun _ _ => True, a, fun _ _ => False⟩
theorem full_s5 (a) : S5 (full a) :=
  ⟨⟨fun _ => trivial, fun _ _ _ _ _ => trivial⟩, fun _ _ _ => trivial⟩

def chain : Model Bool Unit :=
  ⟨fun w v => w = false ∨ v = true, fun _ _ => True, fun _ _ => False⟩
theorem chain_s4 : S4 chain := by
  unfold S4 chain
  dsimp [valid, box, dia, allAct, exAct, full, chain]
  decide

-- TestsHOMLinS4:11 (axB)
theorem axB_countermodel : ∃ m : Model Bool Unit, S4 m ∧
    ∃ p : Bool → Prop, ¬ valid (fun w => p w → box m (dia m p) w) := by
  refine ⟨chain, chain_s4, (fun w => w = false), ?_⟩
  dsimp [valid, box, dia, allAct, exAct, full, chain]
  decide
-- TestsHOMLinS4:14 (ax5)
theorem ax5_countermodel : ∃ m : Model Bool Unit, S4 m ∧
    ∃ p : Bool → Prop, ¬ valid (fun w => dia m p w → box m (dia m p) w) := by
  refine ⟨chain, chain_s4, (fun w => w = false), ?_⟩
  dsimp [valid, box, dia, allAct, exAct, full, chain]
  decide

-- TestsHOML:17; TestsHOMLinS4:18. The S5 witness is also S4.
theorem barcan_countermodel : ∃ m : Model Bool Unit, S5 m ∧
    ∃ p : Unit → Bool → Prop,
      ¬ valid (fun w => allAct m (fun x => box m (p x)) w → box m (allAct m p) w) := by
  refine ⟨full (fun _ w => w = true), full_s5 _, (fun _ _ => False), ?_⟩
  dsimp [valid, box, dia, allAct, exAct, full, chain]
  decide
-- TestsHOML:19; TestsHOMLinS4:20.
theorem converseBarcan_countermodel : ∃ m : Model Bool Unit, S5 m ∧
    ∃ p : Unit → Bool → Prop,
      ¬ valid (fun w => box m (allAct m p) w → allAct m (fun x => box m (p x)) w) := by
  refine ⟨full (fun _ w => w = false), full_s5 _, (fun _ w => w = false), ?_⟩
  dsimp [valid, box, dia, allAct, exAct, full, chain]
  decide

-- TestsHOML:43; TestsHOMLinS4:44.
theorem exImActualist1_countermodel : ∃ m : Model Bool Unit, S5 m ∧
    ¬ valid (exAct m (fun x _ => x = x)) := by
  refine ⟨full (fun _ _ => False), full_s5 _, ?_⟩
  dsimp [valid, box, dia, allAct, exAct, full, chain]
  decide
-- TestsHOML:45; TestsHOMLinS4:46.
theorem exImActualist2_countermodel : ∃ m : Model Bool Unit, S5 m ∧
    ¬ valid (exAct m (fun x => leib x x)) := by
  refine ⟨full (fun _ _ => False), full_s5 _, ?_⟩
  intro h
  exact (h false).elim (fun _ hx => hx.1)
-- TestsHOML:47; TestsHOMLinS4:48.
theorem exImActualist3_countermodel : ∃ m : Model Bool Unit, S5 m ∧
    ∃ t : Unit, ¬ valid (exAct m (fun x _ => x = t)) := by
  refine ⟨full (fun _ _ => False), full_s5 _, (), ?_⟩
  dsimp [valid, box, dia, allAct, exAct, full, chain]
  decide
-- TestsHOML:49; TestsHOMLinS4:50.
theorem exImActualist_countermodel : ∃ m : Model Bool Unit, S5 m ∧
    ¬ valid (exAct m (fun _ _ => True)) := by
  refine ⟨full (fun _ _ => False), full_s5 _, ?_⟩
  dsimp [valid, box, dia, allAct, exAct, full, chain]
  decide

-- TestsHOML:59; TestsHOMLinS4:60.
theorem eqBoolExt2_countermodel : ∃ m : Model Bool Unit, S5 m ∧
    ∃ p q : Bool → Prop, ¬ valid (fun w => (p w ↔ q w) → p = q) := by
  refine ⟨full (fun _ _ => True), full_s5 _, (fun _ => True), (fun w => w = false), ?_⟩
  intro h
  have heq := h false (by simp)
  have ht : (fun w : Bool => w = false) true := heq ▸ True.intro
  cases ht
-- TestsHOML:74; TestsHOMLinS4:75.
theorem modalCollapse_countermodel : ∃ m : Model Bool Unit, S5 m ∧
    ¬ valid (fun w => ∀ p : Bool → Prop, p w → box m p w) := by
  refine ⟨full (fun _ _ => True), full_s5 _, ?_⟩
  intro h
  have hbad := h false (fun w => w = false) rfl true trivial
  cases hbad
-- TestsHOML:86; TestsHOMLinS4:87.
theorem emptyProperty4_countermodel : ∃ m : Model Bool Unit, S5 m ∧
    ∃ p : Unit → Bool → Prop,
    ¬ ((valid (fun _ : Bool => p ≠ (fun _ _ => False))) → valid (fun w => ∃ x, p x w)) := by
  refine ⟨full (fun _ _ => True), full_s5 _, (fun _ w => w = false), ?_⟩
  intro h
  have hn : (fun (_ : Unit) (w : Bool) => w = false) ≠ (fun _ _ => False) := by
    intro heq
    have hf : (fun (_ : Unit) (_ : Bool) => False) () false := heq ▸ (Eq.refl false)
    exact hf
  obtain ⟨x, hx⟩ := h (fun _ => hn) true
  cases hx
-- TestsHOML:88; TestsHOMLinS4:89.
theorem emptyProperty5_countermodel : ∃ m : Model Bool Unit, S5 m ∧
    ∃ p : Unit → Bool → Prop,
    ¬ ((valid (fun _ : Bool => p ≠ (fun _ _ => False))) → valid (exAct m p)) := by
  obtain ⟨m, hm, p, hp⟩ := emptyProperty4_countermodel
  refine ⟨m, hm, p, ?_⟩
  intro h
  apply hp
  intro hn w
  obtain ⟨x, _, hx⟩ := h hn w
  exact ⟨x, hx⟩

#print axioms axB_countermodel
#print axioms ax5_countermodel
#print axioms barcan_countermodel
#print axioms converseBarcan_countermodel
#print axioms exImActualist1_countermodel
#print axioms exImActualist2_countermodel
#print axioms exImActualist3_countermodel
#print axioms exImActualist_countermodel
#print axioms eqBoolExt2_countermodel
#print axioms modalCollapse_countermodel
#print axioms emptyProperty4_countermodel
#print axioms emptyProperty5_countermodel
end Programme.«20261021-1639-ontological».Countermodels.Tests
