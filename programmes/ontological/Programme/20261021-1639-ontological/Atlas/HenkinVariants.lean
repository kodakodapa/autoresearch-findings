import Programme.«20261021-1639-ontological».Atlas.HenkinScott
/- Restricted-carrier audit for variants 2/3. No world-naming collections are used.
   Higher admission is explicit; this file does not assert full term closure. -/
namespace Programme.«20261021-1639-ontological».Atlas.HenkinVariants
open Programme.«20261021-1639-ontological».Atlas.HenkinScott
variable {W E : Type} (m : GModel W E)
abbrev Property := E → W → Prop
def neg (p : Property (W := W) (E := E)) := fun x w => ¬ p x w
def Ax2a : Prop := ∀ p w, m.adm p →
  (m.positive p w ∨ m.positive (neg p) w) ∧
  ¬ (m.positive p w ∧ m.positive (neg p) w)
def Gen (Q : E → W → Prop)
    (hadm : ((E → W → Prop) → W → Prop) → Prop) : Prop :=
  ∀ s p w, hadm s → m.adm p →
    (∀ q, m.adm q → s q w → m.positive q w) →
    (∀ v, m.rel w v → ∀ x, Q x v →
      (p x v ↔ ∀ q, m.adm q → s q v → q x v)) → m.positive p w
structure FiniteClosure (hadm : ((E → W → Prop) → W → Prop) → Prop) : Prop where
  bot : m.adm (fun _ _ => False)
  neg : ∀ p, m.adm p → m.adm (neg p)
  empty : hadm (fun _ _ => False)
  pair : ∀ p q, m.adm p → m.adm q → hadm (fun r _ => r = p ∨ r = q)

/-- Variant-2 monotheism needs entity separation, not world names. -/
theorem mono (h2 : Ax2a m)
    (hn : ∀ p, m.adm p → m.adm (neg p))
    (hi : ∀ x, m.adm (fun z (_ : W) => z = x))
    (x y : E) (w : W) (hx : GH m x w) (hy : GH m y w) : x = y := by
  rcases (h2 _ w (hi x)).1 with h | h
  · exact (hy _ (hi x) h).symm
  · exact (hx _ (hn _ (hi x)) h rfl).elim

/-- Restricted Ax1Gen and dichotomy imply guarded upward closure using only
    empty and two-element higher collections. This is enough for variant-3 Ax4. -/
theorem upward (Q A : E → W → Prop)
    (hadm : ((E → W → Prop) → W → Prop) → Prop)
    (hc : FiniteClosure m hadm) (hQA : ∀ x v, Q x v → A x v)
    (h2 : Ax2a m) (hg : Gen m Q hadm)
    (p q : E → W → Prop) (w : W) (hp : m.adm p) (hq : m.adm q)
    (hpos : m.positive p w)
    (hinc : ∀ v, m.rel w v → ∀ x, A x v → p x v → q x v) :
    m.positive q w := by
  apply Classical.byContradiction
  intro hnot
  have hn := (h2 q w hq).1.resolve_left hnot
  have hb : m.positive (fun _ _ => False) w := by
    apply hg (fun r _ => r = p ∨ r = neg q) _ w (hc.pair p (neg q) hp (hc.neg q hq)) hc.bot
    · intro r _ hr
      rcases hr with rfl | rfl
      · exact hpos
      · exact hn
    · intro v hv x hx
      refine ⟨False.elim, fun h => ?_⟩
      exact h (neg q) (hc.neg q hq) (Or.inr rfl)
        (hinc v hv x (hQA x v hx) (h p hp (Or.inl rfl)))
  have ht : m.positive (neg (fun _ _ => False)) w := by
    apply hg (fun _ _ => False) _ w hc.empty (hc.neg _ hc.bot)
    · intro _ _ h; exact h.elim
    · intro _ _ _ _
      exact ⟨fun _ _ _ h => h.elim, fun _ h => h⟩
  exact (h2 _ w hc.bot).2 ⟨hb, ht⟩

#print axioms mono
#print axioms upward
end Programme.«20261021-1639-ontological».Atlas.HenkinVariants
