import Programme.«20261021-1639-ontological».Deep.HenkinScope

namespace Programme.«20261021-1639-ontological».Deep.NotesParameterized

/- Literal HOMLinHOL operators with all model postulates explicit parameters. -/
def Mbot : (W → Prop) := fun _ => False
def Mtop : (W → Prop) := fun _ => True
def Mneg (φ : (W → Prop)) : (W → Prop) := fun w => ¬ φ w
def Mand (φ ψ : (W → Prop)) : (W → Prop) := fun w => φ w ∧ ψ w
def Mor (φ ψ : (W → Prop)) : (W → Prop) := fun w => φ w ∨ ψ w
def Mimp (φ ψ : (W → Prop)) : (W → Prop) := fun w => φ w → ψ w
def Mequiv (φ ψ : (W → Prop)) : (W → Prop) := fun w => φ w ↔ ψ w
def Mbox (r : W → W → Prop) (φ : (W → Prop)) : (W → Prop) := fun w => ∀ v, r w v → φ v
def Mdia (r : W → W → Prop) (φ : (W → Prop)) : (W → Prop) := fun w => ∃ v, r w v ∧ φ v
def Mprimeq {α} (x y : α) : (W → Prop) := fun _ => x = y
def Mprimneg {α} (x y : α) : (W → Prop) := fun _ => x ≠ y
def Mnegpred (Φ : (E → W → Prop)) : (E → W → Prop) := fun x w => ¬ Φ x w
def Mconpred (Φ Ψ : (E → W → Prop)) : (E → W → Prop) := fun x w => Φ x w ∧ Ψ x w
def Mexclor (φ ψ : W → Prop) : W → Prop := Mand (Mor φ ψ) (Mneg (Mand φ ψ))
def Mallposs {α} (Φ : α → (W → Prop)) : (W → Prop) := fun w => ∀ x, Φ x w
def Mexiposs {α} (Φ : α → (W → Prop)) : (W → Prop) := fun w => ∃ x, Φ x w
def Mallact (actual : E → W → Prop) (Φ : E → (W → Prop)) : (W → Prop) := fun w => ∀ x, actual x w → Φ x w
def Mexiact (actual : E → W → Prop) (Φ : E → (W → Prop)) : (W → Prop) := fun w => ∃ x, actual x w ∧ Φ x w
def Mleibeq {α} (x y : α) : W → Prop := Mallposs (fun (P : α → W → Prop) => Mimp (P x) (P y))
def Mvalid (ψ : (W → Prop)) : Prop := ∀ w, ψ w

def toNotes (r : W → W → Prop) (c : ∀ {a}, C a → Carrier W E a) :
    Term C Γ a → Env W E Γ → Carrier W E a
  | .var v => fun ρ => ρ v
  | .const k => fun _ => c k
  | .app f x => fun ρ => toNotes r c f ρ (toNotes r c x ρ)
  | .lam t => fun ρ x => toNotes r c t (extend ρ x)
  | .falsum => fun _ => Mbot
  | .imp p q => fun ρ => Mimp (toNotes r c p ρ) (toNotes r c q ρ)
  | .box p => fun ρ => Mbox r (toNotes r c p ρ)
  | .all p => fun ρ => Mallposs (fun x => toNotes r c p (extend ρ x))
  | .equal s t => fun ρ => Mprimeq (toNotes r c s ρ) (toNotes r c t ρ)

theorem agreement (r : W → W → Prop) (c : ∀ {a}, C a → Carrier W E a)
    (t : Term C Γ a) (ρ : Env W E Γ) :
    toNotes r c t ρ = eval (⟨r, c⟩ : Model C W E) ρ t := by
  induction t with
  | var v => rfl
  | const k => rfl
  | app f x hf hx => simp only [toNotes, eval, hf, hx]
  | lam t ih => funext x; exact ih (extend ρ x)
  | falsum => rfl
  | imp p q hp hq => simp only [toNotes, eval, hp, hq]; rfl
  | box p hp => simp only [toNotes, eval, hp]; rfl
  | all p hp => simp only [toNotes, eval, hp]; rfl
  | equal s t hs ht => simp only [toNotes, eval, hs, ht]; rfl

theorem validity_iff (r : W → W → Prop) (c : ∀ {a}, C a → Carrier W E a)
    (p : Term C Γ .prop) (ρ : Env W E Γ) :
    Mvalid (toNotes (a := .prop) r c p ρ) ↔ ∀ w, eval (⟨r, c⟩ : Model C W E) ρ p w := by
  rw [agreement]
  rfl


def ontInterp (actual : E → W → Prop) (positive : (E → W → Prop) → W → Prop) :
    ∀ {a}, OntConst a → Carrier W E a
  | _, .actual => actual
  | _, .positive => positive

theorem actualist_bridge (r : W → W → Prop) (actual : E → W → Prop)
    (positive : (E → W → Prop) → W → Prop)
    (p : Term OntConst (.entity :: Γ) .prop) (ρ : Env W E Γ) :
    toNotes r (ontInterp actual positive) (allActual p) ρ =
      Mallact actual (fun x => toNotes r (ontInterp actual positive) p (extend (a := .entity) ρ x)) := rfl

/-- Relational Henkin semantics at the full-carrier instance used by Notes. -/
theorem full_henkin_bridge [Nonempty E] (m : Model C W E)
    (ρ : Env W E Γ) (p : Term C Γ .prop) :
    Mvalid (toNotes m.rel m.interp p ρ) ↔ Henkin.DeepValid (Henkin.ofFull m) ρ p := by
  rw [validity_iff]
  constructor
  · intro hp
    exact ⟨_, Henkin.full_denotes m p ρ, hp⟩
  · rintro ⟨v, hv, hp⟩
    have he := (Henkin.agreement hv).symm.trans (Henkin.full_specialization m p ρ)
    change v = eval m ρ p at he
    subst v
    exact hp

/-- All interpretations and assignments, with matching full carriers. -/
theorem class_consequence_iff [Nonempty E]
    (premises : Term C Γ .prop → Prop) (q : Term C Γ .prop) :
    (∀ (m : Model C W E) (ρ : Env W E Γ),
      (∀ p, premises p → Mvalid (toNotes m.rel m.interp p ρ)) →
      Mvalid (toNotes m.rel m.interp q ρ)) ↔
    (∀ (m : Model C W E) (ρ : Env W E Γ),
      (∀ p, premises p → Henkin.DeepValid (Henkin.ofFull m) ρ p) →
      Henkin.DeepValid (Henkin.ofFull m) ρ q) := by
  simp only [full_henkin_bridge]

#print axioms agreement
#print axioms validity_iff
#print axioms actualist_bridge
#print axioms full_henkin_bridge
#print axioms class_consequence_iff
end Programme.«20261021-1639-ontological».Deep.NotesParameterized
