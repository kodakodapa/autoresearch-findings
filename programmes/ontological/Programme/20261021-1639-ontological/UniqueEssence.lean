import Notes.HOMLinHOL

/- Parameterized translations of the seven Notes UniqueEss2 targets.
Worlds and entities are Bool and Unit, both inhabited; quantifiers over
properties and predicates on properties retain their full function types.
The Bool flags select actualist (true) versus possibilist (false) quantification.
No Notes global postulate is used. -/
namespace Programme.«20261021-1639-ontological».UniqueEssence
abbrev PropI := Unit → Bool → Prop
structure Model where
  rel : Bool → Bool → Prop
  actual : Unit → Bool → Prop
  positive : PropI → Bool → Prop

def S5 (m : Model) := (∀ w, m.rel w w) ∧
  (∀ w v, m.rel w v → m.rel v w) ∧
  (∀ w v u, m.rel w v → m.rel v u → m.rel w u)
def box (m : Model) (p : Bool → Prop) (w : Bool) := ∀ v, m.rel w v → p v
def guard (m : Model) (a : Bool) (x : Unit) (w : Bool) := a = true → m.actual x w
def inc (m : Model) (a : Bool) (p q : PropI) :=
  box m (fun w => ∀ x, guard m a x w → p x w → q x w)
def ess (m : Model) (a : Bool) (p : PropI) (x : Unit) (w : Bool) :=
  p x w ∧ ∀ q : PropI, q x w → inc m a p q w
def ne (m : Model) (a b : Bool) (x : Unit) (w : Bool) :=
  ∀ p : PropI, ess m a p x w → box m (fun v => ∃ y, guard m b y v ∧ p y v) w
def god (m : Model) (x : Unit) (w : Bool) := ∀ p : PropI, m.positive p w → p x w
def leib (p q : PropI) (w : Bool) := ∀ Q : PropI → Bool → Prop, Q p w → Q q w
def unique (m : Model) (a primitive : Bool) := ∀ p q x w,
  ess m a p x w ∧ ess m a q x w →
  box m (fun v => if primitive then p = q else leib p q v) w

def Scott (m : Model) (a b : Bool) :=
  (∀ p w, (¬ m.positive p w) ↔ m.positive (fun x v => ¬ p x v) w) ∧
  (∀ p q w, m.positive p w ∧ inc m a p q w → m.positive q w) ∧
  (∀ w, m.positive (god m) w) ∧
  (∀ p w, m.positive p w → box m (m.positive p) w) ∧
  (∀ w, m.positive (ne m a b) w)

def witness : Model := ⟨Eq, fun _ _ => True, fun p w => p () w⟩
theorem witness_s5 : S5 witness :=
  ⟨fun _ => rfl, fun _ _ h => h.symm, fun _ _ _ h k => h.trans k⟩
theorem witness_guard (a x w) : guard witness a x w := fun _ => trivial
theorem witness_ess (a p x w) : ess witness a p x w ↔ p x w := by
  constructor
  · exact And.left
  · intro hp
    refine ⟨hp, ?_⟩
    intro q hq v hv y _ _
    cases hv
    cases x
    cases y
    exact hq
theorem witness_ne (a b x w) : ne witness a b x w := by
  intro p hp v hv
  cases hv
  exact ⟨x, witness_guard b x w, hp.1⟩
theorem witness_scott (a b) : Scott witness a b := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p w; exact Iff.rfl
  · intro p q w h
    exact h.2 w rfl () (witness_guard a () w) h.1
  · intro w p hp; exact hp
  · intro p w hp v hv; cases hv; exact hp
  · intro w; exact witness_ne a b () w

theorem witness_not_unique (a primitive) : ¬ unique witness a primitive := by
  intro h
  let p : PropI := fun _ _ => True
  let q : PropI := fun _ w => w = false
  have hpq := h p q () false
    ⟨(witness_ess a p () false).2 trivial, (witness_ess a q () false).2 rfl⟩ false rfl
  cases primitive with
  | false =>
    have bad := hpq (fun z _ => z () true) trivial
    cases bad
  | true =>
    have heq : p = q := hpq
    have bad : q () true := heq ▸ True.intro
    cases bad

-- B05: ScottVariantHOML.lean:73
 theorem scott_actualist_countermodel : ∃ m, S5 m ∧ Scott m true true ∧ ¬ unique m true false :=
  ⟨witness, witness_s5, witness_scott _ _, witness_not_unique _ _⟩
-- B06: ScottVariantHOMLAndersonQuant.lean:71 (primitive equality)
theorem scott_anderson_countermodel : ∃ m, S5 m ∧ Scott m false true ∧ ¬ unique m false true :=
  ⟨witness, witness_s5, witness_scott _ _, witness_not_unique _ _⟩
-- B11: ScottVariantHOMLposs.lean:69
theorem scott_possibilist_countermodel : ∃ m, S5 m ∧ Scott m false false ∧ ¬ unique m false false :=
  ⟨witness, witness_s5, witness_scott _ _, witness_not_unique _ _⟩
#print axioms scott_actualist_countermodel
#print axioms scott_anderson_countermodel
#print axioms scott_possibilist_countermodel

-- GoedelVariantHOML2, its possibilist and Anderson-quantifier variants.
-- Ax2a is exclusive disjunction, Ax1Gen uses the selection at successor v.
def Goedel2 (m : Model) (a b : Bool) :=
  (∀ p q w, m.positive p w ∧ m.positive q w →
    m.positive (fun x v => p x v ∧ q x v) w) ∧
  (∀ p w, (m.positive p w ∨ m.positive (fun x v => ¬ p x v) w) ∧
    ¬ (m.positive p w ∧ m.positive (fun x v => ¬ p x v) w)) ∧
  (∀ p w, m.positive p w → box m (m.positive p) w) ∧
  (∀ w, m.positive (ne m a b) w) ∧
  (∀ p q w, m.positive p w ∧ inc m a p q w → m.positive q w) ∧
  (∀ (selection : PropI → Bool → Prop) p w,
    (∀ q, selection q w → m.positive q w) ∧
    box m (fun v => ∀ z, guard m a z v →
      (p z v ↔ ∀ q, selection q v → q z v)) w → m.positive p w)
theorem witness_goedel2 (a b) : Goedel2 witness a b := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q w h; exact h
  · intro p w
    exact ⟨Classical.em (p () w), fun h => h.2 h.1⟩
  · intro p w hp v hv; cases hv; exact hp
  · intro w; exact witness_ne a b () w
  · intro p q w h
    exact h.2 w rfl () (witness_guard a () w) h.1
  · intro selection p w h
    exact (h.2 w rfl () (witness_guard a () w)).2 h.1
-- B02: GoedelVariantHOML2.lean:110
 theorem goedel2_actualist_countermodel : ∃ m, S5 m ∧ Goedel2 m true true ∧ ¬ unique m true false :=
  ⟨witness, witness_s5, witness_goedel2 _ _, witness_not_unique _ _⟩
-- B03: GoedelVariantHOML2AndersonQuant.lean:102
 theorem goedel2_anderson_countermodel : ∃ m, S5 m ∧ Goedel2 m false true ∧ ¬ unique m false false :=
  ⟨witness, witness_s5, witness_goedel2 _ _, witness_not_unique _ _⟩
-- B04: GoedelVariantHOML2poss.lean:109
 theorem goedel2_possibilist_countermodel : ∃ m, S5 m ∧ Goedel2 m false false ∧ ¬ unique m false false :=
  ⟨witness, witness_s5, witness_goedel2 _ _, witness_not_unique _ _⟩

def evil (m : Model) (x : Unit) (w : Bool) := ∀ p : PropI, (¬ m.positive p w) → p x w
def EvilAxioms (m : Model) :=
  (∀ p w, (¬ m.positive p w) ↔ m.positive (fun x v => ¬ p x v) w) ∧
  (∀ p q w, (¬ m.positive p w) ∧ inc m true p q w → ¬ m.positive q w) ∧
  (∀ w, ¬ m.positive (evil m) w) ∧
  (∀ p w, (¬ m.positive p w) → box m (fun v => ¬ m.positive p v) w) ∧
  (∀ w, ¬ m.positive (ne m true true) w)
def evilWitness : Model := { witness with positive := fun p w => ¬ p () w }
theorem evil_axioms : EvilAxioms evilWitness := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p w; exact Iff.rfl
  · intro p q w h hq
    exact hq (h.2 w rfl () (witness_guard true () w) (Classical.not_not.mp h.1))
  · intro w hn; apply hn; intro p hp; exact Classical.not_not.mp hp
  · intro p w hp v hv; cases hv; exact hp
  · intro w hn; apply hn
    intro p hp v hv; cases hv
    exact ⟨(), witness_guard true () w, hp.1⟩
-- B01: EvilDerivable.lean:78 (primitive equality)
theorem evil_countermodel : ∃ m, S5 m ∧ EvilAxioms m ∧ ¬ unique m true true := by
  exact ⟨evilWitness, witness_s5, evil_axioms, witness_not_unique true true⟩
#print axioms goedel2_actualist_countermodel
#print axioms goedel2_anderson_countermodel
#print axioms goedel2_possibilist_countermodel
#print axioms evil_countermodel
end Programme.«20261021-1639-ontological».UniqueEssence
