import Programme.«20261022-0733-ontological».Run2.DeadEndFrame
import Programme.«20261022-0733-ontological».Run2.Separating
/-! # The K row of the atlas: exact consistency conditions for full carriers (variant 2)

Fix a frame `R` and actuality `act`; admit every proposition, property and collection.

* `consistent_iff`: some positivity satisfies variant-2 `Ax2a`, `Ax3`, `Ax4` iff every world sees
  a reflexive dead end at which some entity is actual.  (`→` is `DeadEndFrame.sees_rdeadEnd`
  plus the actual witness; `←` takes positivity to be truth of the dead end's actual witness.)
* `consistent_ax1Gen_iff`: adding `Ax1Gen`, a model exists iff `R` is the identity and every world
  has an actual entity (`→` from `Separating.standard_collapse` and seriality).
* `ax1Gen_god`: in every such model God exists at every world, so with `Ax1Gen` existence,
  necessary existence and MC hold on every frame that carries a model at all.

Without `Ax1Gen` the witness model of `consistent_iff` refutes MC on every frame that is not
`DeadEndFrame.CondC`, and has a godless world wherever `w` sees its dead end `v ≠ w`
(`godless_off_deadEnd`). -/
namespace Programme.«20261022-0733-ontological».Run2.KRow

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.StandardKB Programme.«20261022-0733-ontological».Run2.KBMinimal
open Programme.«20261022-0733-ontological».Run2.DeadEndFrame

variable {W D : Type}

/-- All carriers full. -/
def full (R : W → W → Prop) (act : D → W → Prop) (P : (D → W → Prop) → W → Prop) :
    Model W D where
  R := R
  act := act
  AS := fun _ => True
  AT := fun _ => True
  AH := fun _ => True
  P := P

/-- Every world sees a reflexive dead end with an actual entity. -/
def SeesRDE (R : W → W → Prop) (act : D → W → Prop) : Prop :=
  ∀ w, ∃ v y, R w v ∧ R v v ∧ (∀ u, R v u → u = v) ∧ act y v

theorem fullT (R : W → W → Prop) (act : D → W → Prop) P : FullT (full R act P) :=
  fun _ => trivial

/-- Necessity direction, with the actual witness. -/
theorem sees_of_model {R : W → W → Prop} {act : D → W → Prop} {P}
    (h2a : Ax2a (full R act P)) (h3 : Ax3 (full R act P)) (h4 : Ax4 (full R act P)) :
    SeesRDE R act := by
  intro w
  have hF := fullT R act P
  have hp := h3 w
  obtain ⟨v, y, hv, hy, hE⟩ := somewhere (hF _) (hF _) h2a h4 (hF _) hp
  have hd := deadEnd_of_E hF hE
  obtain ⟨u, hu⟩ := serial (hF _) (hF _) h2a h4 v
  exact ⟨v, y, hv, hd u hu ▸ hu, hd, hy⟩

section witness
variable {R : W → W → Prop} {act : D → W → Prop} (h : SeesRDE R act)

noncomputable def dw (w : W) : W := (h w).choose
noncomputable def gw (w : W) : D := (h w).choose_spec.choose

theorem spec (w : W) :
    R w (dw h w) ∧ R (dw h w) (dw h w) ∧ (∀ u, R (dw h w) u → u = dw h w) ∧
      act (gw h w) (dw h w) :=
  (h w).choose_spec.choose_spec

/-- Positivity at `w`: truth of the witness at the dead end `w` sees. -/
noncomputable def wit : Model W D := full R act fun φ w => φ (gw h w) (dw h w)

theorem wit_ax2a : Ax2a (wit h) := by
  intro φ _ w
  show (φ _ _ ∨ ¬ φ _ _) ∧ ¬ (φ _ _ ∧ ¬ φ _ _)
  exact ⟨Classical.em _, fun ⟨a, b⟩ => b a⟩

theorem wit_ax4 : Ax4 (wit h) := by
  intro φ ψ _ _ w hφ hinc
  obtain ⟨hv, _, _, hy⟩ := spec h w
  exact hinc _ hv _ hy hφ

theorem wit_ax3 : Ax3 (wit h) := by
  intro w
  show E (wit h) (gw h w) (dw h w)
  intro φ _ hess u hu
  obtain ⟨_, _, hd, hy⟩ := spec h w
  have := hd u hu
  subst this
  exact ⟨_, hy, hess.1⟩

/-- Off a dead end, the witness model is godless (nominal world property). -/
theorem godless_off_deadEnd (w : W) (hne : dw h w ≠ w) : ¬ ExG (wit h) w := by
  rintro ⟨y, _, hG⟩
  have := hG (fun _ u => u ≠ w) trivial (show dw h w ≠ w from hne)
  exact this rfl

/-- The witness model refutes MC at every world that sees a dead end other than itself. -/
theorem not_mc_off (w : W) (hne : dw h w ≠ w) : ¬ MC (wit h) := by
  intro hmc
  have := hmc (fun u => u = w) trivial w rfl _ (spec h w).1
  exact hne this

end witness

/-- **K row, variant 2, full carriers.** A positivity with `Ax2a`, `Ax3`, `Ax4` exists iff every
world sees a reflexive dead end where some entity is actual. -/
theorem consistent_iff (R : W → W → Prop) (act : D → W → Prop) :
    (∃ P, Ax2a (full R act P) ∧ Ax3 (full R act P) ∧ Ax4 (full R act P)) ↔ SeesRDE R act :=
  ⟨fun ⟨_, h2a, h3, h4⟩ => sees_of_model h2a h3 h4,
    fun h => ⟨_, wit_ax2a h, wit_ax3 h, wit_ax4 h⟩⟩

/-! ## What `Ax1Gen` adds -/

theorem fullTH (R : W → W → Prop) (act : D → W → Prop) P :
    Programme.«20261022-0733-ontological».Run2.Separating.FullTH (full R act P) :=
  ⟨fun _ => trivial, fun _ => trivial⟩

/-- Identity frame, positivity = truth of a chosen actual entity at the current world. -/
noncomputable def idm (act : D → W → Prop) (h : ∀ w, ∃ y, act y w) : Model W D :=
  full (fun w v => v = w) act fun φ w => φ (h w).choose w

theorem consistent_ax1Gen_iff (R : W → W → Prop) (act : D → W → Prop) :
    (∃ P, Ax2a (full R act P) ∧ Ax3 (full R act P) ∧ Ax4 (full R act P) ∧
        Ax1Gen (full R act P)) ↔
      (∀ w v, R w v ↔ v = w) ∧ ∀ w, ∃ y, act y w := by
  constructor
  · rintro ⟨P, h2a, h3, h4, h1⟩
    have hid := (Programme.«20261022-0733-ontological».Run2.Separating.standard_collapse (fullTH R act P) h1 h2a
      (Or.inl h3)).1
    have hs := sees_of_model h2a h3 h4
    refine ⟨fun w v => ⟨hid w v, fun e => ?_⟩, fun w => ?_⟩
    · subst e
      obtain ⟨u, _, hu, _, _, _⟩ := hs v
      exact hid _ _ hu ▸ hu
    · obtain ⟨u, y, hu, _, _, hy⟩ := hs w
      exact ⟨y, hid _ _ hu ▸ hy⟩
  · rintro ⟨hR, ha⟩
    have eR : R = fun w v => v = w := funext fun w => funext fun v => propext (hR w v)
    subst eR
    refine ⟨fun φ w => φ (ha w).choose w, ?_, ?_, ?_, ?_⟩
    · intro φ _ w
      show (φ _ _ ∨ ¬ φ _ _) ∧ ¬ (φ _ _ ∧ ¬ φ _ _)
      exact ⟨Classical.em _, fun ⟨a, b⟩ => b a⟩
    · intro w
      show E (full _ act _) (ha w).choose w
      intro φ _ hess u hu
      have hu' : u = w := hu
      subst hu'
      exact ⟨_, (ha u).choose_spec, hess.1⟩
    · intro φ ψ _ _ w hφ hinc
      exact hinc w rfl _ (ha w).choose_spec hφ
    · intro Φ φ _ _ w hpos hconj
      show φ (ha w).choose w
      refine (hconj w rfl _ (ha w).choose_spec).2 fun ψ _ hψ => hpos ψ trivial hψ

/-- With `Ax1Gen`, God exists at every world of every full model of `Ax2a`, `Ax3`, `Ax4`. -/
theorem ax1Gen_god {R : W → W → Prop} {act : D → W → Prop} {P}
    (h2a : Ax2a (full R act P)) (h3 : Ax3 (full R act P)) (h4 : Ax4 (full R act P))
    (h1 : Ax1Gen (full R act P)) (w : W) : ExG (full R act P) w := by
  have hid := (Programme.«20261022-0733-ontological».Run2.Separating.standard_collapse (fullTH R act P) h1 h2a
    (Or.inl h3)).1
  obtain ⟨u, y, hu, _, _, hy⟩ := sees_of_model h2a h3 h4 w
  have e := hid _ _ hu
  subst e
  -- `Φ` = all positive properties; their conjunction `γ` is positive by `Ax1Gen`
  let γ : D → W → Prop := fun z v => ∀ ψ, P ψ v → ψ z v
  have hγ : P γ u := h1 (fun ψ v => P ψ v) γ trivial trivial u (fun ψ _ h => h)
    (fun v _ z _ => ⟨fun h ψ _ hψ => h ψ hψ, fun h ψ hψ => h ψ trivial hψ⟩)
  obtain ⟨v, z, hv, hz, hzγ⟩ := somewhere (fullT R act P _) (fullT R act P _) h2a h4
    (fullT R act P _) hγ
  have e := hid _ _ hv
  subst e
  exact ⟨z, hz, fun ψ _ hψ => hzγ ψ hψ⟩


/-- S4 example: the reflexive transitive chain `(ℕ, ≤)` carries no full model of `Ax2a`, `Ax3`,
`Ax4` (no dead end), whatever the actuality. -/
theorem nat_le_none (act : D → Nat → Prop) (P) :
    ¬ (Ax2a (full (· ≤ ·) act P) ∧ Ax3 (full (· ≤ ·) act P) ∧ Ax4 (full (· ≤ ·) act P)) := by
  rintro ⟨h2a, h3, h4⟩
  obtain ⟨v, _, _, _, hd, _⟩ := sees_of_model h2a h3 h4 0
  have := hd (v + 1) (Nat.le_succ v)
  omega

/-- Two-world S5 cluster: no full model either (the only dead ends are singletons). -/
theorem s5_two_none (act : D → Bool → Prop) (P) :
    ¬ (Ax2a (full (fun _ _ => True) act P) ∧ Ax3 (full (fun _ _ => True) act P) ∧
      Ax4 (full (fun _ _ => True) act P)) := by
  rintro ⟨h2a, h3, h4⟩
  obtain ⟨v, _, _, _, hd, _⟩ := sees_of_model h2a h3 h4 true
  have h1 := hd true trivial
  have h2 := hd false trivial
  rw [← h2] at h1
  exact Bool.noConfusion h1

end Programme.«20261022-0733-ontological».Run2.KRow

#print axioms Programme.«20261022-0733-ontological».Run2.KRow.consistent_iff
#print axioms Programme.«20261022-0733-ontological».Run2.KRow.consistent_ax1Gen_iff
#print axioms Programme.«20261022-0733-ontological».Run2.KRow.ax1Gen_god
#print axioms Programme.«20261022-0733-ontological».Run2.KRow.godless_off_deadEnd
#print axioms Programme.«20261022-0733-ontological».Run2.KRow.not_mc_off
#print axioms Programme.«20261022-0733-ontological».Run2.KRow.nat_le_none
#print axioms Programme.«20261022-0733-ontological».Run2.KRow.s5_two_none
