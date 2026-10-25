import Programme.«20261022-0733-ontological».Run2.FrameRows
import Programme.«20261022-0733-ontological».Run2.TwoClosedMixed
/-! # Mixed-regime and possibilist rows of the atlas (all carriers full)

Mixed (Anderson) regime of arXiv 2609.36279v4: possibilist inclusion in the essence and in `Ax4P`,
actualist necessary existence.  Fix a frame `R` and actuality `act`; admit everything.

* `mixed_iff`: variant 2, some positivity satisfies `Ax2a`, mixed `Ax3` and `Ax4P` iff every world
  sees a reflexive dead end with an actual entity: the same criterion as the actualist K row
  (`KRow.consistent_iff`), so `mixed_iff_actualist` transfers every frame row of `FrameRows`
  (`symm_iff_mixed`, `refl_iff_mixed`, `eucl_iff_mixed`).
* `possibilist_iff`: with every entity actual (possibilist quantifiers) and `D` nonempty, a model
  exists iff every world sees a reflexive dead end.
* `mixed_v3_iff`: variant 3′, some positivity satisfies `Ax2a`, mixed `Ax3` (with `E₃`) and `Ax4P`
  iff there is at most one world, it is reflexive and some entity is actual there.  Unlike the
  actualist 3′ row (K25), non-actual entities are allowed: `mixed_v3_example` has one world and
  two entities, one of them not actual. -/
namespace Programme.«20261022-0733-ontological».Run2.MixedRows

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.TwoClosedMixed Programme.«20261022-0733-ontological».Run2.KRow

variable {W D : Type}

abbrev ConsMixed (R : W → W → Prop) (act : D → W → Prop) : Prop :=
  ∃ P, Ax2a (full R act P) ∧ (∀ w, (full R act P).P (E2 (full R act P)) w) ∧
    Ax4P (full R act P)

abbrev ConsMixed3 (R : W → W → Prop) (act : D → W → Prop) : Prop :=
  ∃ P, Ax2a (full R act P) ∧ (∀ w, (full R act P).P (TwoClosedMixed.E3 (full R act P)) w) ∧
    Ax4P (full R act P)

section common
variable {R : W → W → Prop} {act : D → W → Prop} {P : (D → W → Prop) → W → Prop}

theorem not_pBot (h2a : Ax2a (full R act P)) (h4 : Ax4P (full R act P)) (w : W) :
    ¬ P bot w := fun hb =>
  (h2a bot trivial w).2 ⟨hb, h4 bot (neg bot) trivial trivial w hb fun _ _ _ h => h.elim⟩

/-- A positive property is exemplified (possibilistically) at some successor. -/
theorem somewhere_P (h2a : Ax2a (full R act P)) (h4 : Ax4P (full R act P)) {φ} {w : W}
    (hp : P φ w) : ∃ v x, R w v ∧ φ x v :=
  Classical.byContradiction fun hn =>
    not_pBot h2a h4 w (h4 φ bot trivial trivial w hp fun v hv y hy => hn ⟨v, y, hv, hy⟩)

theorem serial (h2a : Ax2a (full R act P)) (h4 : Ax4P (full R act P)) (w : W) :
    ∃ v, R w v := by
  rcases (h2a top trivial w).1 with h | h
  · obtain ⟨v, _, hv, _⟩ := somewhere_P h2a h4 h; exact ⟨v, hv⟩
  · obtain ⟨v, _, hv, _⟩ := somewhere_P h2a h4 h; exact ⟨v, hv⟩

end common

/-! ## Variant 2 -/

/-- Mixed necessary existence at `v` makes `v` a dead end at which `x` is actual
(singleton essence `λ z u. z = x ∧ u = v`). -/
theorem deadEnd_of_E2 {R : W → W → Prop} {act : D → W → Prop} {P} {x : D} {v : W}
    (hE : E2 (full R act P) x v) : ∀ u, R v u → u = v ∧ act x v := by
  intro u hu
  obtain ⟨y, hy, hyx, huv⟩ := hE (fun z u => z = x ∧ u = v) trivial
    ⟨⟨rfl, rfl⟩, fun ψ _ hψ u _ y ⟨hyx, huv⟩ => hyx ▸ huv ▸ hψ⟩ u hu
  subst hyx huv
  exact ⟨rfl, hy⟩

theorem mixed_iff (R : W → W → Prop) (act : D → W → Prop) :
    ConsMixed R act ↔ SeesRDE R act := by
  constructor
  · rintro ⟨P, h2a, h3, h4⟩ w
    obtain ⟨v, x, hv, hE⟩ := somewhere_P h2a h4 (h3 w)
    have hd := deadEnd_of_E2 hE
    obtain ⟨u, hu⟩ := serial h2a h4 v
    obtain ⟨e, hx⟩ := hd u hu
    exact ⟨v, x, hv, e ▸ hu, fun u h => (hd u h).1, hx⟩
  · intro h
    refine ⟨fun φ w => φ (gw h w) (dw h w), ?_, ?_, ?_⟩
    · intro φ _ w
      show (φ _ _ ∨ ¬ φ _ _) ∧ ¬ (φ _ _ ∧ ¬ φ _ _)
      exact ⟨Classical.em _, fun ⟨a, b⟩ => b a⟩
    · intro w
      show E2 (full R act _) (gw h w) (dw h w)
      intro φ _ hess u hu
      obtain ⟨_, _, hd, hy⟩ := spec h w
      have := hd u hu
      subst this
      exact ⟨_, hy, hess.1⟩
    · intro φ ψ _ _ w hφ hinc
      exact hinc _ (spec h w).1 _ hφ

/-- The mixed and actualist variant-2 rows coincide on every frame and actuality. -/
theorem mixed_iff_actualist (R : W → W → Prop) (act : D → W → Prop) :
    ConsMixed R act ↔ FrameRows.Cons R act := by
  rw [mixed_iff, FrameRows.Cons, consistent_iff]

theorem symm_iff_mixed (R : W → W → Prop) (act : D → W → Prop) (hs : ∀ w v, R w v → R v w) :
    ConsMixed R act ↔ (∀ w v, R w v ↔ v = w) ∧ ∀ w, ∃ y, act y w := by
  rw [mixed_iff_actualist]; exact FrameRows.symm_iff R act hs

theorem refl_iff_mixed (R : W → W → Prop) (act : D → W → Prop) (hr : ∀ w, R w w) :
    ConsMixed R act ↔ ∀ w, ∃ v y, R w v ∧ (∀ u, R v u → u = v) ∧ act y v := by
  rw [mixed_iff_actualist]; exact FrameRows.refl_iff R act hr

theorem eucl_iff_mixed (R : W → W → Prop) (act : D → W → Prop)
    (he : ∀ w v u, R w v → R w u → R v u) :
    ConsMixed R act ↔ ∀ w, ∃ d, (∀ v, R w v ↔ v = d) ∧ (∀ v, R d v ↔ v = d) ∧ ∃ y, act y d := by
  rw [mixed_iff_actualist]; exact FrameRows.eucl_iff R act he

/-- **Possibilist row** (every entity actual): a model exists iff every world sees a reflexive
dead end. -/
theorem possibilist_iff [Nonempty D] (R : W → W → Prop) :
    FrameRows.Cons R (fun (_ : D) (_ : W) => True) ↔
      ∀ w, ∃ v, R w v ∧ R v v ∧ ∀ u, R v u → u = v := by
  rw [FrameRows.Cons, consistent_iff]
  constructor
  · intro h w
    obtain ⟨v, _, a, b, c, _⟩ := h w
    exact ⟨v, a, b, c⟩
  · intro h w
    obtain ⟨v, a, b, c⟩ := h w
    exact ⟨v, Classical.choice ‹Nonempty D›, a, b, c, trivial⟩

/-! ## Variant 3′ -/

theorem mixed_v3_iff (R : W → W → Prop) (act : D → W → Prop) :
    ConsMixed3 R act ↔ (∀ w v : W, w = v) ∧ (∀ w, R w w) ∧ ∀ w, ∃ y, act y w := by
  constructor
  · rintro ⟨P, h2a, h3, h4⟩
    -- every world `w` sees a dead end `v` where some `x` is actual, and every world is `v`
    have key : ∀ w : W, ∃ v x, R v v ∧ act x v ∧ ∀ b : W, b = v := by
      intro w
      obtain ⟨v, x, _, hE⟩ := somewhere_P h2a h4 (h3 w)
      have h0 : ∀ u, R v u → u = v ∧ act x v := by
        intro u hu
        obtain ⟨y, hy, hyx, huv⟩ := hE (fun z u => z = x ∧ u = v) trivial
          (fun ψ _ hψ u _ => ⟨fun e => by have h := congrFun (congrFun e x) v; simp [bot] at h,
            fun y ⟨hyx, huv⟩ => hyx ▸ huv ▸ hψ⟩) u hu
        subst hyx huv
        exact ⟨rfl, hy⟩
      obtain ⟨u, hu⟩ := serial h2a h4 v
      obtain ⟨e, hx⟩ := h0 u hu
      subst e
      refine ⟨u, x, hu, hx, fun b => Classical.byContradiction fun hb => ?_⟩
      obtain ⟨y, _, hyb⟩ := hE (fun _ t => t = b) trivial
        (fun ψ _ _ t ht => ⟨fun e => by have h := congrFun (congrFun e x) b; simp [bot] at h,
          fun y hy => absurd (hy.symm.trans (h0 t ht).1) hb⟩) u hu
      exact hb hyb.symm
    refine ⟨fun a b => ?_, fun w => ?_, fun w => ?_⟩
    · obtain ⟨v, -, -, -, hall⟩ := key a
      exact (hall a).trans (hall b).symm
    · obtain ⟨v, -, hv, -, hall⟩ := key w
      exact hall w ▸ hv
    · obtain ⟨v, x, -, hx, hall⟩ := key w
      exact ⟨x, hall w ▸ hx⟩
  · rintro ⟨hsub, hr, ha⟩
    refine ⟨fun φ w => φ (ha w).choose w, ?_, ?_, ?_⟩
    · intro φ _ w
      show (φ _ _ ∨ ¬ φ _ _) ∧ ¬ (φ _ _ ∧ ¬ φ _ _)
      exact ⟨Classical.em _, fun ⟨a, b⟩ => b a⟩
    · intro w
      show TwoClosedMixed.E3 (full R act _) (ha w).choose w
      intro φ _ hess v _
      obtain ⟨hne, hsubφ⟩ := hess (fun z _ => z = (ha w).choose) trivial rfl w (hr w)
      have : ∃ y u, φ y u := Classical.byContradiction fun hn =>
        hne (funext fun y => funext fun u => propext ⟨fun h => hn ⟨y, u, h⟩, False.elim⟩)
      obtain ⟨y, u, hy⟩ := this
      have hu : u = w := hsub u w
      have hv : v = w := hsub v w
      subst hu hv
      have := hsubφ y hy
      subst this
      exact ⟨_, (ha _).choose_spec, hy⟩
    · intro φ ψ _ _ w hφ hinc
      exact hinc w (hr w) _ hφ

/-- One world, two entities, only `false` actual: a mixed variant-3′ model, which the actualist
3′ row (K25: every entity actual) rules out. -/
theorem mixed_v3_example :
    ConsMixed3 (fun (_ _ : Unit) => True) (fun (b : Bool) (_ : Unit) => b = false) ∧
      ¬ ∀ (b : Bool) (w : Unit), b = false :=
  ⟨(mixed_v3_iff _ _).2 ⟨fun _ _ => rfl, fun _ => trivial, fun _ => ⟨false, rfl⟩⟩,
    fun h => Bool.noConfusion (h true ())⟩

end Programme.«20261022-0733-ontological».Run2.MixedRows

#print axioms Programme.«20261022-0733-ontological».Run2.MixedRows.mixed_iff
#print axioms Programme.«20261022-0733-ontological».Run2.MixedRows.mixed_iff_actualist
#print axioms Programme.«20261022-0733-ontological».Run2.MixedRows.symm_iff_mixed
#print axioms Programme.«20261022-0733-ontological».Run2.MixedRows.refl_iff_mixed
#print axioms Programme.«20261022-0733-ontological».Run2.MixedRows.eucl_iff_mixed
#print axioms Programme.«20261022-0733-ontological».Run2.MixedRows.possibilist_iff
#print axioms Programme.«20261022-0733-ontological».Run2.MixedRows.mixed_v3_iff
#print axioms Programme.«20261022-0733-ontological».Run2.MixedRows.mixed_v3_example
