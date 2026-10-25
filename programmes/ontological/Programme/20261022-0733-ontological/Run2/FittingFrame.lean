import Programme.«20261022-0733-ontological».Run2.FittingColumn

/-! # Fitting column: the exact frame condition for existence

For a frame `R`, A1–A5 (Fitting's extensional positivity, full carriers) force an actual
God-like entity at every world of every model on `R` iff `R` is serial and every world has an
`R`-predecessor. On non-serial frames there is no model (`serial`). The witness on a serial frame
has one entity, actual exactly at worlds with a predecessor, and `P Y w := Y ()`. -/

namespace Programme.«20261022-0733-ontological».Run2.FittingFrame

open Programme.«20261022-0733-ontological».Run2.FittingColumn

/-- One entity, actual exactly where some world sees the current one. -/
def predModel {W : Type} (R : W → W → Prop) : FModel W Unit where
  R := R
  act := fun _ v => ∃ u, R u v
  P := fun Y _ => Y ()

theorem predModel_axioms {W : Type} (R : W → W → Prop) (hser : ∀ w, ∃ v, R w v) :
    A1 (predModel R) ∧ A2 (predModel R) ∧ A3 (predModel R) ∧ A4 (predModel R) ∧
    A5 (predModel R) := by
  refine ⟨fun _ _ => Iff.rfl, fun Y Z w hY hi => ?_, fun _ _ h => h, fun _ _ h _ _ => h,
    fun w _ hE v hv => ⟨(), ⟨w, hv⟩, hE.1⟩⟩
  obtain ⟨v, hv⟩ := hser w
  exact hi v hv () ⟨w, hv⟩ hY

theorem predModel_exG {W : Type} (R : W → W → Prop) (w : W) :
    ExG (predModel R) w ↔ ∃ u, R u w :=
  ⟨fun ⟨_, ha, _⟩ => ha, fun ha => ⟨(), ha, fun _ h => h⟩⟩

/-- Exact frame row: on a frame `R`, every Fitting model of A1–A5 (any entity type, any
actuality) has `∃ᴱ G` at every world, and some model exists, iff `R` is serial and every world
has a predecessor. -/
theorem frame_iff {W : Type} (R : W → W → Prop) :
    ((∃ (D : Type) (M : FModel W D), M.R = R ∧ A1 M ∧ A2 M ∧ A3 M ∧ A4 M ∧ A5 M) ∧
      ∀ (D : Type) (M : FModel W D), M.R = R → A1 M → A2 M → A3 M → A4 M → A5 M →
        ∀ w, ExG M w) ↔
    (∀ w, ∃ v, R w v) ∧ ∀ w, ∃ u, R u w := by
  constructor
  · rintro ⟨⟨D, M, hR, h1, h2, -, -, -⟩, hall⟩
    have hser : ∀ w, ∃ v, R w v := fun w => hR ▸ serial h1 h2 w
    obtain ⟨a1, a2, a3, a4, a5⟩ := predModel_axioms R hser
    exact ⟨hser, fun w => (predModel_exG R w).1 (hall _ _ rfl a1 a2 a3 a4 a5 w)⟩
  · rintro ⟨hser, hpred⟩
    obtain ⟨a1, a2, a3, a4, a5⟩ := predModel_axioms R hser
    refine ⟨⟨Unit, predModel R, rfl, a1, a2, a3, a4, a5⟩, fun D M hR h1 h2 h3 h4 h5 w => ?_⟩
    obtain ⟨u, hu⟩ := hpred w
    exact gex_of_pred h1 h2 h3 h4 h5 (u := u) (hR ▸ hu)

/-- On the predecessor model, MC fails as soon as some edge `R w v` has `v ≠ w`. -/
theorem predModel_not_MC {W : Type} (R : W → W → Prop) {w v : W} (hwv : R w v) (hne : v ≠ w) :
    ¬ MC (predModel R) :=
  fun h => hne (h (fun u => u = w) w rfl v hwv)

end Programme.«20261022-0733-ontological».Run2.FittingFrame

#print axioms Programme.«20261022-0733-ontological».Run2.FittingFrame.frame_iff
#print axioms Programme.«20261022-0733-ontological».Run2.FittingFrame.predModel_axioms
#print axioms Programme.«20261022-0733-ontological».Run2.FittingFrame.predModel_not_MC
