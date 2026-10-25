import Programme.«20261022-0733-ontological».Run2.KRow
import Programme.«20261022-0733-ontological».Run2.V3NoSym
/-! # The 3' row of the atlas: exact consistency for full carriers

Gap 4 of th's minimality table (P222).  Variant 3' (`Ax3v3`, plain `Ax4`), every proposition,
property and collection admitted, arbitrary frame `R` and actuality `act`.

* `v3_consistent_iff`: some positivity satisfies `Ax2a`, `Ax3v3`, `Ax4` iff there is at most one
  world, and at every world `R w w` holds, some entity is actual, and *every* entity is actual.
  (A non-actual entity `d` makes `λz u. z = d` a vacuous essence of everything, so `E3` is
  empty and `P ⊥` would follow.)
* MC holds trivially in such models; God need not exist (K14's majority model is one). -/
namespace Programme.«20261022-0733-ontological».Run2.V3Row

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.StandardKB Programme.«20261022-0733-ontological».Run2.KRow

variable {W D : Type}

/-- The frame/actuality condition for 3'. -/
def OneWorld (R : W → W → Prop) (act : D → W → Prop) : Prop :=
  (∀ a b : W, a = b) ∧ ∀ w, R w w ∧ (∃ y, act y w) ∧ ∀ y, act y w

theorem nec {R : W → W → Prop} {act : D → W → Prop} {P}
    (h2a : Ax2a (full R act P)) (h3 : Ax3v3 (full R act P)) (h4 : Ax4 (full R act P)) :
    OneWorld R act := by
  have hF := fullT R act P
  have hsub := Programme.«20261022-0733-ontological».Run2.V3NoSym.v3_singleton hF h2a h4 h3
  refine ⟨hsub, fun w => ?_⟩
  obtain ⟨v, y, hv, hy, hE⟩ := somewhere (hF _) (hF _) h2a h4 (hF _) (h3 w)
  have e := hsub v w
  subst e
  refine ⟨hv, ⟨y, hy⟩, fun d => Classical.byContradiction fun hd => ?_⟩
  have ess : Ess3 (full R act P) (fun z _ => z = d) y v := by
    intro ψ _ _ r hr
    refine ⟨fun e => ?_, fun z hz hzd => ?_⟩
    · have : (fun (z : D) (_ : W) => z = d) d v := rfl
      rw [e] at this; exact this
    · have er := hsub r v
      subst er; subst hzd
      exact absurd hz hd
  obtain ⟨z, hz, hzd⟩ := hE _ trivial ess v hv
  subst hzd
  exact hd hz

/-- Witness: positivity is truth of a chosen actual entity. -/
noncomputable def owm (R : W → W → Prop) (act : D → W → Prop) (h : OneWorld R act) :
    Model W D :=
  full R act fun φ w => φ ((h.2 w).2.1.choose) w

theorem suff {R : W → W → Prop} {act : D → W → Prop} (h : OneWorld R act) :
    Ax2a (owm R act h) ∧ Ax3v3 (owm R act h) ∧ Ax4 (owm R act h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro φ _ w
    show (φ _ _ ∨ ¬ φ _ _) ∧ ¬ (φ _ _ ∧ ¬ φ _ _)
    exact ⟨Classical.em _, fun ⟨a, b⟩ => b a⟩
  · intro w
    show E3 (owm R act h) (h.2 w).2.1.choose w
    intro φ _ hess v hv
    have ev := h.1 v w
    subst ev
    have hrefl := (h.2 v).1
    have hne := (hess (fun z _ => z = (h.2 v).2.1.choose) trivial rfl v hrefl).1
    -- `φ ≠ ⊥` on one world: some entity has `φ`; it is actual, hence the chosen one
    have : ∃ d, φ d v := by
      refine Classical.byContradiction fun hn => hne (funext fun d => funext fun u => ?_)
      have eu := h.1 u v
      subst eu
      exact propext ⟨fun hd => hn ⟨d, hd⟩, False.elim⟩
    obtain ⟨d, hd⟩ := this
    exact ⟨d, (h.2 v).2.2 d, hd⟩
  · intro φ ψ _ _ w hφ hinc
    exact hinc w (h.2 w).1 _ (h.2 w).2.1.choose_spec hφ

/-- **3' row, full carriers.** A positivity with `Ax2a`, `Ax3v3`, `Ax4` exists iff there is at
most one world and each world is reflexive, has an actual entity, and has every entity actual. -/
theorem v3_consistent_iff (R : W → W → Prop) (act : D → W → Prop) :
    (∃ P, Ax2a (full R act P) ∧ Ax3v3 (full R act P) ∧ Ax4 (full R act P)) ↔
      OneWorld R act :=
  ⟨fun ⟨_, h2a, h3, h4⟩ => nec h2a h3 h4, fun h => ⟨_, suff h⟩⟩

end Programme.«20261022-0733-ontological».Run2.V3Row

#print axioms Programme.«20261022-0733-ontological».Run2.V3Row.v3_consistent_iff
