import Programme.«20261021-1639-ontological».Countermodels.Essence
/- Postulate-free re-expression of the Notes axiom formulas with explicit model data.
The operator definitions below are parameterized versions of HOMLinHOL. This is a
formula audit, not specialization at the library's global postulates. -/
namespace Programme.«20261021-1639-ontological».Countermodels.NotesBridge
open Tests Scott Essence
variable {W E : Type} (m : Model W E)
def imp (p q : W → Prop) := fun w => p w → q w
def conj (p q : W → Prop) := fun w => p w ∧ q w
def all {T : Type} (p : T → W → Prop) := fun w => ∀ x, p x w
def allGuard (a : Bool) (p : E → W → Prop) :=
  fun w => ∀ x, guard m a x w → p x w
def exGuard (a : Bool) (p : E → W → Prop) :=
  fun w => ∃ x, guard m a x w ∧ p x w
def god : E → W → Prop := fun x => all (fun p => imp (m.positive p) (p x))
def essence (a : Bool) : (E → W → Prop) → E → W → Prop := fun p x =>
  conj (p x) (all (fun (q : E → W → Prop) => imp (q x) (box m (allGuard m a (fun y => imp (p y) (q y))))))
def necessary (a b : Bool) : E → W → Prop := fun x =>
  all (fun p => imp (essence m a p x) (box m (exGuard m b p)))
def inclusion (a : Bool) (p q : E → W → Prop) :=
  box m (allGuard m a (fun x => imp (p x) (q x)))
def neg (p : E → W → Prop) := fun x w => ¬ p x w

def ScottFormula (a b : Bool) : Prop :=
  (∀ p, valid (fun w => (¬ m.positive p w) ↔ m.positive (neg p) w)) ∧
  (∀ p q, valid (imp (conj (m.positive p) (inclusion m a p q)) (m.positive q))) ∧
  valid (m.positive (god m)) ∧
  (∀ p, valid (imp (m.positive p) (box m (m.positive p)))) ∧
  valid (m.positive (necessary m a b))

theorem scott_bridge (a b : Bool) : ScottAxioms m a b ↔ ScottFormula m a b := by
  constructor
  · intro h
    exact ⟨h.A1, fun p q w hp => h.A2 p q w hp.1 hp.2, h.A3, h.A4, h.A5⟩
  · intro h
    exact ⟨h.1, fun p q w hp hi => h.2.1 p q w ⟨hp, hi⟩,
      h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem scott_same_guard_bridge (a : Bool) : Axioms m a ↔ ScottFormula m a a := by
  constructor
  · intro h
    exact ⟨h.A1, fun p q w hp => h.A2 p q w hp.1 hp.2, h.A3, h.A4, h.A5⟩
  · intro h
    exact ⟨h.1, fun p q w hp hi => h.2.1 p q w ⟨hp, hi⟩,
      h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

def GoedelFormula (a b : Bool) : Prop :=
  (∀ p q, valid (imp (conj (m.positive p) (m.positive q))
    (m.positive (fun x => conj (p x) (q x))))) ∧
  (∀ p, valid (fun w => (m.positive p w ∨ m.positive (neg p) w) ∧
    ¬ (m.positive p w ∧ m.positive (neg p) w))) ∧
  (∀ p, valid (imp (m.positive p) (box m (m.positive p)))) ∧
  valid (m.positive (necessary m a b)) ∧
  (∀ p q, valid (imp (conj (m.positive p) (inclusion m a p q)) (m.positive q))) ∧
  (∀ (s : (E → W → Prop) → W → Prop) p, valid (imp
    (conj (all (fun q => imp (s q) (m.positive q)))
      (box m (allGuard m a (fun y w => p y w ↔ all (fun q => imp (s q) (q y)) w))))
    (m.positive p)))

theorem goedel_bridge (a b : Bool) : GoedelAxioms m a b ↔ GoedelFormula m a b := by
  constructor
  · intro h
    exact ⟨fun p q w hp => h.Ax1 p q w hp.1 hp.2, h.Ax2a, h.Ax2b, h.Ax3,
      fun p q w hp => h.Ax4 p q w hp.1 hp.2,
      fun s p w hp => h.Ax1Gen s p w hp.1 hp.2⟩
  · intro h
    exact ⟨fun p q w hp hq => h.1 p q w ⟨hp, hq⟩, h.2.1, h.2.2.1, h.2.2.2.1,
      fun p q w hp hi => h.2.2.2.2.1 p q w ⟨hp, hi⟩,
      fun s p w hs hc => h.2.2.2.2.2 s p w ⟨hs, hc⟩⟩

def EvilFormula : Prop :=
  (∀ p, valid (fun w => (¬ m.positive p w) ↔ m.positive (neg p) w)) ∧
  (∀ p q, valid (imp (conj (fun w => ¬ m.positive p w) (inclusion m true p q))
    (fun w => ¬ m.positive q w))) ∧
  (∀ p, valid (imp (fun w => ¬ m.positive p w) (box m (fun w => ¬ m.positive p w)))) ∧
  valid (fun w => ¬ m.positive (fun x => all (fun p => imp (fun v => ¬ m.positive p v) (p x))) w) ∧
  valid (fun w => ¬ m.positive (necessary m true true) w)

theorem evil_bridge : EvilAxioms m ↔ EvilFormula m := by
  constructor
  · intro h
    exact ⟨h.A1, fun p q w hp => h.A2 p q w hp.1 hp.2, h.A3, h.A4, h.A5⟩
  · intro h
    exact ⟨h.1, fun p q w hp hi => h.2.1 p q w ⟨hp, hi⟩,
      h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem actual_guard (x : E) (w : W) : guard m true x w ↔ m.actual x w :=
  ⟨fun h => h rfl, fun h _ => h⟩
theorem poss_guard (x : E) (w : W) : guard m false x w ↔ True :=
  ⟨fun _ => trivial, fun _ h => Bool.noConfusion h⟩

#print axioms scott_bridge
#print axioms scott_same_guard_bridge
#print axioms goedel_bridge
#print axioms evil_bridge
#print axioms actual_guard
#print axioms poss_guard
end Programme.«20261021-1639-ontological».Countermodels.NotesBridge
