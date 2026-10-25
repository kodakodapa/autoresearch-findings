import Programme.«20261021-1639-ontological».Countermodels.Tests

/- Gödel 1970 (Notes variant 1, GoedelVariantHOML1*): the unique minimal inconsistent subset.
Rebased from th P130 onto the shared Model; proof credit to th.
Ax2a (exclusive or) is split into `A1a` (not both φ and ¬φ positive) and `A1b` (one of them is).
Guards: `g` guards the entity quantifier in PInc (⊃ᴺ), `k` the one in E's □∃.
Actualist file: g = k = true; AndersonQuant: g = false, k = true; poss: g = k = false.
No frame condition is assumed anywhere. -/
namespace Programme.«20261021-1639-ontological».Atlas.Variant1

open Programme.«20261021-1639-ontological».Countermodels.Tests

variable {W E : Type} (m : Model W E) (g k : Bool)

def guard (b : Bool) (x : E) (w : W) : Prop := b = true → m.actual x w
/-- `φ ⊃ᴺ ψ` = `□(∀ y, φ y → ψ y)` with guard `g`. -/
def PInc (p q : E → W → Prop) (w : W) : Prop :=
  ∀ v, m.rel w v → ∀ y, guard m g y v → p y v → q y v
/-- Variant-1 essence: no `φ x` conjunct. -/
def Ess (p : E → W → Prop) (x : E) (w : W) : Prop := ∀ q : E → W → Prop, q x w → PInc m g p q w
def NE (x : E) (w : W) : Prop :=
  ∀ p : E → W → Prop, Ess m g p x w → ∀ v, m.rel w v → ∃ y, guard m k y v ∧ p y v

def Ax1 : Prop := ∀ p q w, m.positive p w → m.positive q w →
  m.positive (fun x u => p x u ∧ q x u) w
def A1a : Prop := ∀ p w, ¬ (m.positive p w ∧ m.positive (fun x u => ¬ p x u) w)
def A1b : Prop := ∀ p w, m.positive p w ∨ m.positive (fun x u => ¬ p x u) w
def Ax2b : Prop := ∀ p w, m.positive p w → ∀ v, m.rel w v → m.positive p v
def Ax3 : Prop := ∀ w, m.positive (NE m g k) w
def Ax4 : Prop := ∀ p q w, m.positive p w → PInc m g p q w → m.positive q w

/-- Dead-end property `λ x u. □⊥ at u`. -/
def D (_ : E) (u : W) : Prop := ∀ v, ¬ m.rel u v

/-- {A1a, Ax3, Ax4} is inconsistent on every frame with a world, in all three regimes. -/
theorem inconsistent [Nonempty W] (h1a : A1a m) (h3 : Ax3 m g k) (h4 : Ax4 m g) : False := by
  classical
  -- E entails D: the empty property is an essence of everything.
  have hD : ∀ w, m.positive (D m) w := by
    intro w
    refine h4 _ _ w (h3 w) ?_
    intro v _ y _ hE u hu
    have hess : Ess m g (fun _ _ => False) y v := fun _ _ _ _ _ _ h => h.elim
    obtain ⟨_, _, hf⟩ := hE _ hess u hu
    exact hf
  have hnot : ∀ w, PInc m g (D m) (fun x u => ¬ D m x u) w → False := fun w hinc =>
    h1a (D m) w ⟨hD w, h4 _ _ w (hD w) hinc⟩
  obtain ⟨w0⟩ := ‹Nonempty W›
  by_cases hdead : ∃ v : W, ∀ u, ¬ m.rel v u
  · obtain ⟨v, hv⟩ := hdead
    exact hnot v fun u hu => (hv u hu).elim
  · -- serial frame: `D` holds nowhere, so `D ⊃ᴺ ¬D` is vacuous at `w0`
    exact hnot w0 fun v _ _ _ hDv _ => hdead ⟨v, hDv⟩

/-! Countermodels: one reflexive world, one always-actual entity (an S5 frame, so they refute
over K, KB, S4, S5), each satisfying every axiom of {Ax1, A1a, A1b, Ax2b, Ax3, Ax4} but one. -/

def one (pos : (Unit → Unit → Prop) → Unit → Prop) : Model Unit Unit :=
  ⟨fun _ _ => True, fun _ _ => True, pos⟩

/-- NE is empty on a reflexive frame: the empty property is an essence but never instantiated. -/
theorem one_not_NE (pos) (x w : Unit) : ¬ NE (one pos) g k x w := by
  intro h
  obtain ⟨_, _, hf⟩ := h (fun _ _ => False) (fun _ _ _ _ _ _ h => h.elim) w trivial
  exact hf

/-- Drop A1a: everything positive. -/
theorem drop_A1a : let m := one (fun _ _ => True)
    Ax1 m ∧ A1b m ∧ Ax2b m ∧ Ax3 m g k ∧ Ax4 m g ∧ ¬ A1a m :=
  ⟨fun _ _ _ _ _ => trivial, fun _ _ => Or.inl trivial, fun _ _ _ _ _ => trivial,
    fun _ => trivial, fun _ _ _ _ _ => trivial, fun h => h (fun _ _ => True) () ⟨trivial, trivial⟩⟩

/-- Drop Ax3: positivity principal at the single entity. -/
theorem drop_Ax3 : let m := one (fun p w => p () w)
    Ax1 m ∧ A1a m ∧ A1b m ∧ Ax2b m ∧ Ax4 m g ∧ ¬ Ax3 m g k := by
  refine ⟨fun _ _ _ hp hq => ⟨hp, hq⟩, fun _ _ h => h.2 h.1, fun p w => Classical.em (p () w),
    fun _ w hp v _ => by cases w; cases v; exact hp, ?_, ?_⟩
  · intro p q w hp hinc
    exact hinc w trivial () (fun _ => trivial) hp
  · intro h
    exact one_not_NE g k _ () () (h ())

/-- Drop Ax4: positivity anti-principal (φ positive iff the entity lacks it). -/
theorem drop_Ax4 : let m := one (fun p w => ¬ p () w)
    Ax1 m ∧ A1a m ∧ A1b m ∧ Ax2b m ∧ Ax3 m g k ∧ ¬ Ax4 m g := by
  refine ⟨fun _ _ _ hp _ h => hp h.1, fun _ _ h => h.2 h.1,
    fun p w => (Classical.em (p () w)).symm.imp id (fun h hn => hn h),
    fun _ w hp v _ => by cases w; cases v; exact hp, fun w => one_not_NE g k _ () w, ?_⟩
  intro h
  exact h (fun _ _ => False) (fun _ _ => True) () (fun h => h) (fun _ _ _ _ _ => trivial) trivial

inductive AxiomName where
  | ax1 | a1a | a1b | ax2b | ax3 | ax4
  deriving DecidableEq

def Holds (m : Model W E) (g k : Bool) : AxiomName → Prop
  | .ax1 => Ax1 m
  | .a1a => A1a m
  | .a1b => A1b m
  | .ax2b => Ax2b m
  | .ax3 => Ax3 m g k
  | .ax4 => Ax4 m g

def Satisfies (m : Model W E) (g k : Bool) (s : AxiomName → Prop) : Prop :=
  ∀ a, s a → Holds m g k a

/-- An exact classification of all 64 subsets, with singleton S5 witnesses. -/
theorem subset_satisfiable_iff (s : AxiomName → Prop) :
    (∃ m : Model Unit Unit, S5 m ∧ Satisfies m g k s) ↔
      ¬ (s .a1a ∧ s .ax3 ∧ s .ax4) := by
  classical
  constructor
  · rintro ⟨m, _, h⟩ ⟨ha, h3, h4⟩
    exact inconsistent m g k (h _ ha) (h _ h3) (h _ h4)
  · intro hn
    have frame : ∀ p, S5 (one p) := fun _ =>
      ⟨⟨fun _ => trivial, fun _ _ _ _ _ => trivial⟩, fun _ _ _ => trivial⟩
    by_cases ha : s .a1a
    · by_cases h3 : s .ax3
      · have h4 : ¬ s .ax4 := fun h => hn ⟨ha, h3, h⟩
        refine ⟨one (fun p w => ¬ p () w), frame _, ?_⟩
        have h := drop_Ax4 g k
        intro a hs
        cases a with
        | ax1 => exact h.1
        | a1a => exact h.2.1
        | a1b => exact h.2.2.1
        | ax2b => exact h.2.2.2.1
        | ax3 => exact h.2.2.2.2.1
        | ax4 => exact (h4 hs).elim
      · refine ⟨one (fun p w => p () w), frame _, ?_⟩
        have h := drop_Ax3 g k
        intro a hs
        cases a with
        | ax1 => exact h.1
        | a1a => exact h.2.1
        | a1b => exact h.2.2.1
        | ax2b => exact h.2.2.2.1
        | ax3 => exact (h3 hs).elim
        | ax4 => exact h.2.2.2.2.1
    · refine ⟨one (fun _ _ => True), frame _, ?_⟩
      have h := drop_A1a g k
      intro a hs
      cases a with
      | ax1 => exact h.1
      | a1a => exact (ha hs).elim
      | a1b => exact h.2.1
      | ax2b => exact h.2.2.1
      | ax3 => exact h.2.2.2.1
      | ax4 => exact h.2.2.2.2.1

#print axioms inconsistent
#print axioms drop_A1a
#print axioms drop_Ax3
#print axioms drop_Ax4
#print axioms subset_satisfiable_iff
end Programme.«20261021-1639-ontological».Atlas.Variant1
