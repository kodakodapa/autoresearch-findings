import Programme.«20261022-0733-ontological».Run2.KRow
/-! # Frame-class rows of the atlas (variant 2, all carriers full)

Corollaries of `KRow.consistent_iff` (some positivity satisfies `Ax2a`, `Ax3`, `Ax4` iff every
world sees a reflexive dead end with an actual entity) for standard frame classes.

* `symm_iff` (KB, B, S5): on a symmetric frame a model exists iff `R` is the identity and every
  world has an actual entity.
* `refl_iff` (T, S4): on a reflexive frame iff every world sees a dead end with an actual entity.
* `eucl_iff` (K5, KD45): on a Euclidean frame iff every world `w` has exactly one successor `d`,
  `d` sees exactly itself, and some entity is actual at `d`.
* `mc_iff_id`: in any full model of `Ax2a`, `Ax3`, `Ax4`, admitted MC holds iff `R ⊆ id`. -/
namespace Programme.«20261022-0733-ontological».Run2.FrameRows

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.KRow

variable {W D : Type}

abbrev Cons (R : W → W → Prop) (act : D → W → Prop) : Prop :=
  ∃ P, Ax2a (full R act P) ∧ Ax3 (full R act P) ∧ Ax4 (full R act P)

/-- **KB / B / S5 rows.** -/
theorem symm_iff (R : W → W → Prop) (act : D → W → Prop) (hs : ∀ w v, R w v → R v w) :
    Cons R act ↔ (∀ w v, R w v ↔ v = w) ∧ ∀ w, ∃ y, act y w := by
  unfold Cons; rw [consistent_iff]
  constructor
  · intro h
    have key : ∀ w, R w w ∧ (∀ u, R w u → u = w) ∧ ∃ y, act y w := by
      intro w
      obtain ⟨v, y, hwv, hvv, hd, hy⟩ := h w
      have : w = v := hd w (hs _ _ hwv)
      subst this
      exact ⟨hvv, hd, y, hy⟩
    exact ⟨fun w v => ⟨(key w).2.1 v, fun e => e ▸ (key w).1⟩, fun w => (key w).2.2⟩
  · rintro ⟨hid, hact⟩ w
    obtain ⟨y, hy⟩ := hact w
    exact ⟨w, y, (hid w w).2 rfl, (hid w w).2 rfl, fun u h => (hid w u).1 h, hy⟩

/-- **T / S4 rows.** -/
theorem refl_iff (R : W → W → Prop) (act : D → W → Prop) (hr : ∀ w, R w w) :
    Cons R act ↔ ∀ w, ∃ v y, R w v ∧ (∀ u, R v u → u = v) ∧ act y v := by
  unfold Cons; rw [consistent_iff]
  constructor
  · intro h w
    obtain ⟨v, y, hwv, -, hd, hy⟩ := h w
    exact ⟨v, y, hwv, hd, hy⟩
  · intro h w
    obtain ⟨v, y, hwv, hd, hy⟩ := h w
    exact ⟨v, y, hwv, hr v, hd, hy⟩

/-- **K5 / KD45 rows.** -/
theorem eucl_iff (R : W → W → Prop) (act : D → W → Prop)
    (he : ∀ w v u, R w v → R w u → R v u) :
    Cons R act ↔ ∀ w, ∃ d, (∀ v, R w v ↔ v = d) ∧ (∀ v, R d v ↔ v = d) ∧ ∃ y, act y d := by
  unfold Cons; rw [consistent_iff]
  constructor
  · intro h w
    obtain ⟨d, y, hwd, hdd, hd, hy⟩ := h w
    refine ⟨d, fun v => ⟨fun hwv => hd v (he _ _ _ hwd hwv), fun e => e ▸ hwd⟩,
      fun v => ⟨hd v, fun e => e ▸ hdd⟩, y, hy⟩
  · intro h w
    obtain ⟨d, hw, hd, y, hy⟩ := h w
    exact ⟨d, y, (hw d).2 rfl, (hd d).2 rfl, fun u h => (hd u).1 h, hy⟩

/-- In a full model of `Ax2a`, `Ax3`, `Ax4` (any frame), MC holds iff `R ⊆ id`. -/
theorem mc_iff_id (R : W → W → Prop) (act : D → W → Prop) (P) :
    MC (full R act P) ↔ ∀ w v, R w v → v = w := by
  constructor
  · intro h w v hwv
    exact Classical.byContradiction fun hne =>
      hne (h (fun u => u = w) trivial w rfl v hwv)
  · intro h X _ w hX v hwv
    exact (h w v hwv) ▸ hX

/-- Hence in the KB/B/S5 rows every full model of `Ax2a`, `Ax3`, `Ax4` collapses. -/
theorem symm_mc (R : W → W → Prop) (act : D → W → Prop) (hs : ∀ w v, R w v → R v w) (P)
    (h2a : Ax2a (full R act P)) (h3 : Ax3 (full R act P)) (h4 : Ax4 (full R act P)) :
    MC (full R act P) :=
  (mc_iff_id R act P).2 fun w v hwv =>
    ((((symm_iff R act hs).1 ⟨P, h2a, h3, h4⟩).1 w v).1 hwv)

/-- The KD45 frame `R w v ↔ v = false` on `Bool` (with everything actual) carries a full model
of `Ax2a`, `Ax3`, `Ax4`, and every such model refutes MC. -/
theorem kd45_example :
    Cons (fun (_ v : Bool) => v = false) (fun (_ : Unit) _ => True) ∧
    ∀ P, ¬ MC (full (fun (_ v : Bool) => v = false) (fun (_ : Unit) _ => True) P) := by
  refine ⟨(eucl_iff _ _ fun _ _ _ h1 h2 => h2).2 fun _ =>
    ⟨false, fun _ => Iff.rfl, fun _ => Iff.rfl, (), trivial⟩, fun P h => ?_⟩
  have := ((mc_iff_id _ _ P).1 h) true false rfl
  exact Bool.noConfusion this

end Programme.«20261022-0733-ontological».Run2.FrameRows

#print axioms Programme.«20261022-0733-ontological».Run2.FrameRows.symm_iff
#print axioms Programme.«20261022-0733-ontological».Run2.FrameRows.refl_iff
#print axioms Programme.«20261022-0733-ontological».Run2.FrameRows.eucl_iff
#print axioms Programme.«20261022-0733-ontological».Run2.FrameRows.mc_iff_id
#print axioms Programme.«20261022-0733-ontological».Run2.FrameRows.symm_mc
#print axioms Programme.«20261022-0733-ontological».Run2.FrameRows.kd45_example
