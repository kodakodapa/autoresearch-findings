import Programme.«20261021-1639-ontological».Deep.NotesParameterized

namespace Programme.«20261021-1639-ontological».Deep.NotesHenkin
open Henkin NotesParameterized

/-- Notes operations on truth intensions, reified into the admitted carriers.
Quantifiers range over D a, not the full function space on lower carriers. -/
def toNotes (h : Frame W) (I : ∀ {a}, C a → h.D a) :
    Term C Γ a → Assignment h Γ → h.D a
  | .var v => fun ρ => ρ v
  | .const k => fun _ => I k
  | .app f x => fun ρ => h.app (toNotes h I f ρ) (toNotes h I x ρ)
  | .lam t => fun ρ => h.abstract (fun x => toNotes h I t (push ρ x))
  | .falsum => fun _ => h.reify Mbot
  | .imp p q => fun ρ => h.reify (Mimp (h.truth (toNotes h I p ρ)) (h.truth (toNotes h I q ρ)))
  | .box p => fun ρ => h.reify (Mbox h.rel (h.truth (toNotes h I p ρ)))
  | .all p => fun ρ => h.reify (Mallposs (fun x => h.truth (toNotes h I p (push ρ x))))
  | .equal s t => fun ρ => h.reify (Mprimeq (toNotes h I s ρ) (toNotes h I t ρ))

theorem translation_agreement (h : Frame W) (I : ∀ {a}, C a → h.D a)
    (t : Term C Γ a) (ρ : Assignment h Γ) :
    toNotes h I t ρ = Henkin.translate h I t ρ := by
  induction t with
  | var v => rfl
  | const k => rfl
  | app f x hf hx => simp only [toNotes, Henkin.translate, hf, hx]
  | lam t ih => simp only [toNotes, Henkin.translate, ih]
  | falsum => rfl
  | imp p q hp hq => simp only [toNotes, Henkin.translate, hp, hq]; rfl
  | box p hp => simp only [toNotes, Henkin.translate, hp]; rfl
  | all p hp => simp only [toNotes, Henkin.translate, hp]; rfl
  | equal s t hs ht => simp only [toNotes, Henkin.translate, hs, ht]; rfl

theorem validity_bridge (m : Henkin.Model C W) (ρ : Assignment m.frame Γ)
    (p : Term C Γ .prop) :
    Mvalid (m.frame.truth (toNotes m.frame m.interp p ρ)) ↔ DeepValid m ρ p := by
  rw [translation_agreement]
  exact Henkin.valid_iff m ρ p

theorem class_consequence_bridge (premises : Term C Γ .prop → Prop) (q : Term C Γ .prop) :
    (∀ (m : Henkin.Model C W) (ρ : Assignment m.frame Γ),
      (∀ p, premises p → Mvalid (m.frame.truth (toNotes m.frame m.interp p ρ))) →
      Mvalid (m.frame.truth (toNotes m.frame m.interp q ρ))) ↔
    (∀ (m : Henkin.Model C W) (ρ : Assignment m.frame Γ),
      (∀ p, premises p → DeepValid m ρ p) → DeepValid m ρ q) := by
  simp only [validity_bridge]

theorem actualist_bridge (m : Henkin.Model OntConst W) (ρ : Assignment m.frame Γ)
    (p : Term OntConst (.entity :: Γ) .prop) :
    m.frame.truth (toNotes m.frame m.interp (allActual p) ρ) =
    Mallact (fun x => m.frame.truth (m.frame.app (m.interp OntConst.actual) x))
      (fun x => m.frame.truth (toNotes m.frame m.interp p (push ρ x))) := by
  simp only [translation_agreement]
  funext w
  exact propext (Henkin.actualist_agreement m ρ p w)

/-- Restricted Leibniz quantification agrees with primitive identity, but is not
identified definitionally with Notes' full predicate quantifier. -/
theorem restricted_leibniz (m : Henkin.Model C W) (x y : m.frame.D a) :
    Mallposs (fun p : m.frame.D (.arr a .prop) =>
      Mimp (m.frame.truth (m.frame.app p x)) (m.frame.truth (m.frame.app p y))) =
      Mprimeq (W := W) x y := by
  funext w
  exact propext (Henkin.leibniz_iff m x y w)

theorem full_specialization [Nonempty E] (m : Programme.«20261021-1639-ontological».Deep.Model C W E)
    (t : Term C Γ a) (ρ : Env W E Γ) :
    toNotes (Henkin.fullFrame m) m.interp t ρ =
      NotesParameterized.toNotes m.rel m.interp t ρ := by
  exact (translation_agreement (Henkin.fullFrame m) m.interp t ρ).trans
    ((Henkin.full_specialization m t ρ).trans (NotesParameterized.agreement m.rel m.interp t ρ).symm)

#print axioms full_specialization
#print axioms translation_agreement
#print axioms validity_bridge
#print axioms class_consequence_bridge
#print axioms actualist_bridge
#print axioms restricted_leibniz
end Programme.«20261021-1639-ontological».Deep.NotesHenkin
