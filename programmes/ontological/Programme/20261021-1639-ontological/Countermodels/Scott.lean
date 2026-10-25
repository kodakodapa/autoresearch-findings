import Programme.«20261021-1639-ontological».Countermodels.Tests

namespace Programme.«20261021-1639-ontological».Countermodels.Scott
open Tests

-- true selects actualist and false possibilist entity quantification.
-- Higher-order quantifiers range over the full property type.
def guard {W E} (m : Model W E) (actualist : Bool) (x : E) (w : W) : Prop :=
  actualist = true → m.actual x w
def G {W E} (m : Model W E) (x : E) (w : W) : Prop :=
  ∀ p : E → W → Prop, m.positive p w → p x w
def Ess {W E} (m : Model W E) (a : Bool) (p : E → W → Prop) (x : E) (w : W) : Prop :=
  p x w ∧ ∀ q : E → W → Prop, q x w →
    ∀ v, m.rel w v → ∀ y, guard m a y v → p y v → q y v
def NE {W E} (m : Model W E) (a : Bool) (x : E) (w : W) : Prop :=
  ∀ p : E → W → Prop, Ess m a p x w →
    ∀ v, m.rel w v → ∃ y, guard m a y v ∧ p y v
structure Axioms {W E} (m : Model W E) (a : Bool) : Prop where
  A1 : ∀ p w, (¬ m.positive p w) ↔ m.positive (fun x v => ¬ p x v) w
  A2 : ∀ p q w, m.positive p w →
    (∀ v, m.rel w v → ∀ y, guard m a y v → p y v → q y v) → m.positive q w
  A3 : ∀ w, m.positive (G m) w
  A4 : ∀ p w, m.positive p w → ∀ v, m.rel w v → m.positive p v
  A5 : ∀ w, m.positive (NE m a) w

def T3 {W E} (m : Model W E) (a : Bool) : Prop :=
  ∀ w v, m.rel w v → ∃ x, guard m a x v ∧ G m x v
def MC {W E} (m : Model W E) : Prop :=
  ∀ p : W → Prop, ∀ w, p w → box m p w

-- 0 sees both worlds; 1 sees only itself. Positivity evaluates at world 1.
def witness : Model Bool Unit :=
  ⟨fun w v => w = false ∨ v = true, fun _ _ => True, fun p _ => p () true⟩
theorem witness_s4 : S4 witness := by
  unfold S4 witness
  dsimp
  decide

theorem witness_axioms (a : Bool) : Axioms witness a := by
  constructor
  · intro p w; rfl
  · intro p q w hp h
    exact h true (Or.inr rfl) () (fun _ => trivial) hp
  · intro w p hp; exact hp
  · intro p w hp v hv; exact hp
  · intro w p hp v hv
    have hvt : v = true := by
      cases hv with
      | inl h => cases h
      | inr h => exact h
    subst v
    exact ⟨(), (fun _ => trivial), hp.1⟩

theorem witness_not_t3 (a : Bool) : ¬ T3 witness a := by
  intro h
  obtain ⟨x, _, hg⟩ := h false false (Or.inl rfl)
  have hf := hg (fun _ w => w = true) rfl
  cases hf

theorem witness_not_mc : ¬ MC witness := by
  intro h
  have hf := h (fun w => w = false) false rfl true (Or.inl rfl)
  cases hf

-- ScottVariantHOMLinS4:44,47; ScottVariantHOMLinK:45,48.
theorem actualist_countermodel : ∃ m : Model Bool Unit,
    S4 m ∧ Axioms m true ∧ ¬ T3 m true ∧ ¬ MC m :=
  ⟨witness, witness_s4, witness_axioms true, witness_not_t3 true, witness_not_mc⟩
-- ScottVariantHOMLpossInS4:44,47.
theorem possibilist_countermodel : ∃ m : Model Bool Unit,
    S4 m ∧ Axioms m false ∧ ¬ T3 m false ∧ ¬ MC m :=
  ⟨witness, witness_s4, witness_axioms false, witness_not_t3 false, witness_not_mc⟩

#print axioms actualist_countermodel
#print axioms possibilist_countermodel
end Programme.«20261021-1639-ontological».Countermodels.Scott
