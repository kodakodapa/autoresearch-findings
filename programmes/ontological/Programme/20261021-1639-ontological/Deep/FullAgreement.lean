import Programme.«20261021-1639-ontological».Deep.Syntax

namespace Programme.«20261021-1639-ontological».Deep

/- Parameterized shallow HOL operators; no fixed frame or domain postulates. -/
namespace Shallow
abbrev Proposition (W : Type) := W → Prop
def bot : Proposition W := fun _ => False
def imp (p q : Proposition W) : Proposition W := fun w => p w → q w
def box (r : W → W → Prop) (p : Proposition W) : Proposition W :=
  fun w => ∀ v, r w v → p v
def all (f : A → Proposition W) : Proposition W := fun w => ∀ x, f x w
def equal (x y : A) : Proposition W := fun _ => x = y
def valid (p : Proposition W) := ∀ w, p w
end Shallow

/-- Compositional translation into HOL functions of the free-variable environment.
It is defined separately from eval and uses shallow operators. Carriers are full. -/
def translate (m : Model C W E) : Term C Γ a → (Env W E Γ → Carrier W E a)
  | .var v => fun ρ => ρ v
  | .const c => fun _ => m.interp c
  | .app f x => fun ρ => translate m f ρ (translate m x ρ)
  | .lam t => fun ρ x => translate m t (extend ρ x)
  | .falsum => fun _ => Shallow.bot
  | .imp p q => fun ρ => Shallow.imp (translate m p ρ) (translate m q ρ)
  | .box p => fun ρ => Shallow.box m.rel (translate m p ρ)
  | .all p => fun ρ => Shallow.all (fun x => translate m p (extend ρ x))
  | .equal s t => fun ρ => Shallow.equal (translate m s ρ) (translate m t ρ)

theorem translate_eq_eval (m : Model C W E) (t : Term C Γ a) (ρ : Env W E Γ) :
    translate m t ρ = eval m ρ t := by
  induction t with
  | var v => rfl
  | const c => rfl
  | app f x hf hx => simp only [translate, eval, hf, hx]
  | lam t ih => funext x; exact ih (extend ρ x)
  | falsum => rfl
  | imp p q hp hq => simp only [translate, eval, hp, hq]; rfl
  | box p hp => simp only [translate, eval, hp]; rfl
  | all p hp => simp only [translate, eval, hp]; rfl
  | equal s t hs ht => simp only [translate, eval, hs, ht]; rfl

/-- Agreement at every world, for the same model and assignment. -/
theorem full_valid_iff (m : Model C W E) (p : Term C Γ .prop) (ρ : Env W E Γ) :
    Shallow.valid (translate m p ρ) ↔ ∀ w, eval m ρ p w := by
  rw [translate_eq_eval]
  rfl

/-- Consequence transfer allows arbitrary (including infinite) premise sets. -/
theorem full_consequence_iff (m : Model C W E) (ρ : Env W E Γ)
    (premises : Term C Γ .prop → Prop) (q : Term C Γ .prop) :
    ((∀ p, premises p → Shallow.valid (translate m p ρ)) →
      Shallow.valid (translate m q ρ)) ↔
    ((∀ p, premises p → ∀ w, eval m ρ p w) → ∀ w, eval m ρ q w) := by
  simp only [full_valid_iff]

/-- Actualist quantification is a syntactic abbreviation using a designated guard. -/
def allActual (p : Term OntConst (.entity :: Γ) .prop) : Term OntConst Γ .prop :=
  .all (.imp (.app (.const .actual) (.var .here)) p)

theorem eval_allActual (m : Model OntConst W E) (ρ : Env W E Γ)
    (p : Term OntConst (.entity :: Γ) .prop) (w : W) :
    eval m ρ (allActual p) w ↔
      ∀ x, m.interp OntConst.actual x w → eval m (extend ρ x) p w := Iff.rfl

#print axioms translate_eq_eval
#print axioms full_valid_iff
#print axioms full_consequence_iff
#print axioms eval_allActual
end Programme.«20261021-1639-ontological».Deep
