import Programme.«20261021-1639-ontological».Countermodels.Scott

namespace Programme.«20261021-1639-ontological».Countermodels.Essence
open Tests Scott

def mixedNE {W E} (m : Model W E) (a b : Bool) (x : E) (w : W) : Prop :=
  ∀ p, Ess m a p x w → ∀ v, m.rel w v → ∃ y, guard m b y v ∧ p y v
structure ScottAxioms {W E} (m : Model W E) (a b : Bool) : Prop where
  A1 : ∀ p w, (¬ m.positive p w) ↔ m.positive (fun x v => ¬ p x v) w
  A2 : ∀ p q w, m.positive p w →
    (∀ v, m.rel w v → ∀ y, guard m a y v → p y v → q y v) → m.positive q w
  A3 : ∀ w, m.positive (G m) w
  A4 : ∀ p w, m.positive p w → ∀ v, m.rel w v → m.positive p v
  A5 : ∀ w, m.positive (mixedNE m a b) w
structure GoedelAxioms {W E} (m : Model W E) (a b : Bool) : Prop where
  Ax1 : ∀ p q w, m.positive p w → m.positive q w → m.positive (fun x v => p x v ∧ q x v) w
  Ax2a : ∀ p w, (m.positive p w ∨ m.positive (fun x v => ¬ p x v) w) ∧
    ¬ (m.positive p w ∧ m.positive (fun x v => ¬ p x v) w)
  Ax2b : ∀ p w, m.positive p w → ∀ v, m.rel w v → m.positive p v
  Ax3 : ∀ w, m.positive (mixedNE m a b) w
  Ax4 : ∀ p q w, m.positive p w →
    (∀ v, m.rel w v → ∀ y, guard m a y v → p y v → q y v) → m.positive q w
  Ax1Gen : ∀ (s : (E → W → Prop) → W → Prop) p w,
    (∀ q, s q w → m.positive q w) →
    (∀ v, m.rel w v → ∀ y, guard m a y v → (p y v ↔ ∀ q, s q v → q y v)) →
    m.positive p w

def Evil {W E} (m : Model W E) (x : E) (w : W) : Prop :=
  ∀ p, (¬ m.positive p w) → p x w
structure EvilAxioms {W E} (m : Model W E) : Prop where
  A1 : ∀ p w, (¬ m.positive p w) ↔ m.positive (fun x v => ¬ p x v) w
  A2 : ∀ p q w, (¬ m.positive p w) →
    (∀ v, m.rel w v → ∀ y, guard m true y v → p y v → q y v) → ¬ m.positive q w
  A3 : ∀ p w, (¬ m.positive p w) → ∀ v, m.rel w v → ¬ m.positive p v
  A4 : ∀ w, ¬ m.positive (Evil m) w
  A5 : ∀ w, ¬ m.positive (mixedNE m true true) w

-- Primitive equality and Leibniz equality are kept separate, as in the Notes.
def UniquePrim {W E} (m : Model W E) (a : Bool) : Prop :=
  ∀ p q x w, Ess m a p x w → Ess m a q x w → box m (fun _ => p = q) w
def UniqueLeib {W E} (m : Model W E) (a : Bool) : Prop :=
  ∀ p q x w, Ess m a p x w → Ess m a q x w → box m (leib p q) w

def localModel : Model Bool Unit :=
  ⟨Eq, fun _ _ => True, fun p w => p () w⟩
def evilModel : Model Bool Unit :=
  ⟨Eq, fun _ _ => True, fun p w => ¬ p () w⟩
theorem local_s5 : S5 localModel :=
  ⟨⟨fun _ => rfl, fun _ _ _ => Eq.trans⟩, fun _ _ => Eq.symm⟩
theorem evil_s5 : S5 evilModel := local_s5

theorem local_scott (a b : Bool) : ScottAxioms localModel a b := by
  constructor
  · intro p w; rfl
  · intro p q w hp h; exact h w rfl () (fun _ => trivial) hp
  · intro w p hp; exact hp
  · intro p w hp v hv; cases hv; exact hp
  · intro w p hp v hv; cases hv; exact ⟨(), (fun _ => trivial), hp.1⟩
theorem local_goedel (a b : Bool) : GoedelAxioms localModel a b := by
  constructor
  · intro p q w hp hq; exact ⟨hp, hq⟩
  · intro p w; exact ⟨Classical.em _, fun h => h.2 h.1⟩
  · exact (local_scott a b).A4
  · exact (local_scott a b).A5
  · exact (local_scott a b).A2
  · intro s p w hs hp
    exact (hp w rfl () (fun _ => trivial)).2 hs

theorem evil_axioms : EvilAxioms evilModel := by
  constructor
  · intro p w; rfl
  · intro p q w hp h hn
    exact hn (h w rfl () (fun _ => trivial) (Classical.not_not.mp hp))
  · intro p w hp v hv; cases hv; exact hp
  · intro w hn
    apply hn
    intro p hp
    exact Classical.not_not.mp hp
  · intro w hn
    apply hn
    intro p hp v hv
    cases hv
    exact ⟨(), (fun _ => trivial), hp.1⟩

-- On identity frames with a singleton entity, every locally exemplified
-- property is an essence. The two chosen properties differ at the other world.
theorem local_ess (a : Bool) (p : Unit → Bool → Prop) (h : p () false) :
    Ess localModel a p () false := by
  refine ⟨h, ?_⟩
  intro q hq v hv y _ _
  cases hv; cases y; exact hq

theorem local_not_prim (a : Bool) : ¬ UniquePrim localModel a := by
  intro h
  have he := h (fun _ _ => True) (fun _ w => w = false) () false
    (local_ess a _ trivial) (local_ess a _ rfl) false rfl
  have hf : (fun (_ : Unit) (w : Bool) => w = false) () true := he ▸ True.intro
  cases hf

theorem local_not_leib (a : Bool) : ¬ UniqueLeib localModel a := by
  intro h
  have he := h (fun _ _ => True) (fun _ w => w = false) () false
    (local_ess a _ trivial) (local_ess a _ rfl) false rfl
  have hf := he (fun p _ => p () true) trivial
  cases hf

-- B01 EvilDerivable: primitive equality.
theorem evil_countermodel : ∃ m : Model Bool Unit,
    S5 m ∧ EvilAxioms m ∧ ¬ UniquePrim m true :=
  ⟨evilModel, evil_s5, evil_axioms, local_not_prim true⟩
-- B02/B03/B04: GoedelVariantHOML2, AndersonQuant, poss.
theorem goedel_actualist_countermodel : ∃ m : Model Bool Unit,
    S5 m ∧ GoedelAxioms m true true ∧ ¬ UniqueLeib m true :=
  ⟨localModel, local_s5, local_goedel true true, local_not_leib true⟩
theorem goedel_mixed_countermodel : ∃ m : Model Bool Unit,
    S5 m ∧ GoedelAxioms m false true ∧ ¬ UniqueLeib m false :=
  ⟨localModel, local_s5, local_goedel false true, local_not_leib false⟩
theorem goedel_possibilist_countermodel : ∃ m : Model Bool Unit,
    S5 m ∧ GoedelAxioms m false false ∧ ¬ UniqueLeib m false :=
  ⟨localModel, local_s5, local_goedel false false, local_not_leib false⟩
-- B05/B06/B11: ScottVariantHOML, AndersonQuant (primitive!), poss.
theorem scott_actualist_countermodel : ∃ m : Model Bool Unit,
    S5 m ∧ ScottAxioms m true true ∧ ¬ UniqueLeib m true :=
  ⟨localModel, local_s5, local_scott true true, local_not_leib true⟩
theorem scott_mixed_countermodel : ∃ m : Model Bool Unit,
    S5 m ∧ ScottAxioms m false true ∧ ¬ UniquePrim m false :=
  ⟨localModel, local_s5, local_scott false true, local_not_prim false⟩
theorem scott_possibilist_countermodel : ∃ m : Model Bool Unit,
    S5 m ∧ ScottAxioms m false false ∧ ¬ UniqueLeib m false :=
  ⟨localModel, local_s5, local_scott false false, local_not_leib false⟩

#print axioms evil_countermodel
#print axioms goedel_actualist_countermodel
#print axioms goedel_mixed_countermodel
#print axioms goedel_possibilist_countermodel
#print axioms scott_actualist_countermodel
#print axioms scott_mixed_countermodel
#print axioms scott_possibilist_countermodel
end Programme.«20261021-1639-ontological».Countermodels.Essence
