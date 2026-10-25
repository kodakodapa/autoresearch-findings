import Programme.«20261022-0733-ontological».Run2.TwoClosedMixed
import Programme.«20261022-0733-ontological».Run2.LGeneralFullInst

/-! # `Ax1GenTwo ↔ Ax1Gen` in the mixed (Anderson) regime without `Ax2b`

The mixed copies of arXiv 2609.36279v4 (`Ax1GenTwoVariant2AndersonQuant`,
`Ax1GenTwoVariant3PlainAndersonQuant`): property inclusion in the essence and in `Ax4` is
possibilist (`TwoClosedMixed.PIncP`, `Ax4P`); necessary existence and the conjunction clause are
actualist.  `TwoClosedMixed` (K2) proved the equivalence with `Ax2b` and `∃ y. G y` admitted.

* `ax1Gen_of_two_mixed`: over `Closed`, `Ax2a`, `⊤` positive, possibilist `Ax4P` and `hact`
  ("a world where only `⊤` is positive sees an actual entity"), `Ax1GenTwo → Ax1Gen`.  The proof
  pads as in `TwoNoRigidity`; in the small case, every admitted property is `⊤` or `⊥` and the
  actual entity at a successor shows the conjunction is not `⊥`.
* `equivalence_v2`, `equivalence_v3`: each variant's mixed `Ax3` gives `⊤` positive and `hact`.
  No `Ax2b`, no `∃ y. G y` admitted, any frame and actuality.
* `ax3_needed`: unlike the actualist regime (K28: `Ax2a`, `Ax4` suffice), `Ax3` cannot be dropped:
  a full one-world model with no actual entity, `P φ w :↔ φ () w`, satisfies `Ax2a`, `Ax2b`,
  `Ax4P`, `Ax1GenTwo`, not `Ax1Gen`, not mixed `Ax3` (variant 2 nor 3′), not actualist `Ax4`. -/

namespace Programme.«20261022-0733-ontological».Run2.MixedNoRigidity

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.TwoClosedMixed
open Programme.«20261022-0733-ontological».Run2.LGeneralFullInst (lgenF_full)
open Programme.«20261022-0733-ontological».Run2.LGeneralFull (LGenF)

variable {W D : Type} {M : Model W D}

/-- With `Ax2a`, if only `⊤` is positive at `w`, every admitted property is `⊤` or `⊥`. -/
theorem top_or_bot (h2a : Ax2a M) {w : W} (only : ∀ ψ, M.AT ψ → M.P ψ w → ψ = top)
    (C : Closed M) (φ : D → W → Prop) (hφ : M.AT φ) : φ = top ∨ φ = bot := by
  rcases (h2a φ hφ w).1 with hp | hn
  · exact Or.inl (only φ hφ hp)
  · right
    have e := only _ (C.neg _ hφ) hn
    funext x u
    have := congrFun (congrFun e x) u
    exact propext ⟨fun h => by simp [neg, top] at this; exact this h, False.elim⟩

theorem ax1Gen_of_two_mixed [Nonempty D] (C : Closed M) (h2a : Ax2a M)
    (h3 : ∀ w, M.P top w) (h4 : Ax4P M)
    (hact : ∀ w, (∀ ψ, M.AT ψ → M.P ψ w → ψ = top) → ∃ v, M.R w v ∧ ∃ z, M.act z v)
    (hT : Ax1GenTwo M) : Ax1Gen M := by
  intro Φ φ hΦ hφ w pos cj
  by_cases hψ : ∃ ψ₀, M.AT ψ₀ ∧ M.P ψ₀ w ∧ ψ₀ ≠ top
  · obtain ⟨ψ₀, hA₀, hP₀, hne⟩ := hψ
    let Φ' : (D → W → Prop) → W → Prop := fun ψ u => Φ ψ u ∨ (ψ = top ∨ ψ = ψ₀)
    have hΦ' : M.AH Φ' := C.union _ _ hΦ (C.union _ _ (C.single _ C.top) (C.single _ hA₀))
    have two : TwoMembers M Φ' w :=
      ⟨top, ψ₀, C.top, hA₀, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), fun e => hne e.symm⟩
    have pos' : PosProps M Φ' w := by
      intro ψ hA hm
      rcases hm with hm | rfl | rfl
      · exact pos ψ hA hm
      · exact h3 w
      · exact hP₀
    have cj' : ConjOf M (conj φ ψ₀) Φ' w := by
      intro v hv z hz
      constructor
      · intro ⟨hφz, h₀⟩ ψ hA hm
        rcases hm with hm | rfl | rfl
        · exact (cj v hv z hz).1 hφz ψ hA hm
        · trivial
        · exact h₀
      · intro hall
        exact ⟨(cj v hv z hz).2 fun ψ hA hm => hall ψ hA (Or.inl hm),
          hall ψ₀ hA₀ (Or.inr (Or.inr rfl))⟩
    have hP : M.P (conj φ ψ₀) w := hT Φ' _ hΦ' (C.conj _ _ hφ hA₀) w two pos' cj'
    exact h4 _ φ (C.conj _ _ hφ hA₀) hφ w hP fun _ _ _ h => h.1
  · have only : ∀ ψ, M.AT ψ → M.P ψ w → ψ = top := fun ψ hA hP =>
      Classical.byContradiction fun hne => hψ ⟨ψ, hA, hP, hne⟩
    have tb := top_or_bot h2a only C
    rcases tb φ hφ with e | e
    · rw [e]; exact h3 w
    · exfalso
      obtain ⟨v, hv, z, hz⟩ := hact w only
      have hφz : φ z v := (cj v hv z hz).2 fun ψ hA hm => by
        rcases tb ψ hA with rfl | rfl
        · trivial
        · -- `⊥ ∈ Φ` at `v`: collapse of "every member of `Φ` is `⊤`" fails at `v`, but the
          -- proposition is `⊤` or `⊥` after lifting, and it holds at `w`.
          have hs : M.AS (fun u => ∀ ψ, M.AT ψ → Φ ψ u → ψ = top) := C.atMost Φ top hΦ C.top
          have x : D := Classical.ofNonempty
          have sub : ∀ ψ, M.AT ψ → Φ ψ w → ψ = top := fun ψ hA hm => only ψ hA (pos ψ hA hm)
          rcases tb _ (C.lift _ hs) with e' | e'
          · have := congrFun (congrFun e' x) v
            have hsv : ∀ ψ, M.AT ψ → Φ ψ v → ψ = top := by simpa [top] using this
            have hb := hsv bot C.bot hm
            have := congrFun (congrFun hb x) v
            simp [bot, top] at this
          · have := congrFun (congrFun e' x) w
            exact absurd sub (by simpa [bot] using this)
      rw [e] at hφz; exact hφz

/-! ## The variants: `⊤` positive and `hact` from mixed `Ax3` -/

theorem hact_v2 [Nonempty D] (C : Closed M) (h2a : Ax2a M) (h4 : Ax4P M) (hE : M.AT (E2 M))
    (h3 : ∀ w, M.P (E2 M) w) (w : W) (only : ∀ ψ, M.AT ψ → M.P ψ w → ψ = top) :
    ∃ v, M.R w v ∧ ∃ z, M.act z v := by
  obtain ⟨v, hv⟩ := serial_of C h2a h4 hE h3 w
  have x : D := Classical.ofNonempty
  have hEx : E2 M x w := by rw [only _ hE (h3 w)]; trivial
  have ess : Ess2 M top x w := ⟨trivial, fun ψ hA hψ u _ y _ => by
    rcases top_or_bot h2a only C ψ hA with rfl | rfl
    · trivial
    · exact hψ.elim⟩
  obtain ⟨z, hz, _⟩ := hEx top C.top ess v hv
  exact ⟨v, hv, z, hz⟩

theorem hact_v3 [Nonempty D] (C : Closed M) (h2a : Ax2a M) (h4 : Ax4P M) (hE : M.AT (TwoClosedMixed.E3 M))
    (h3 : ∀ w, M.P (TwoClosedMixed.E3 M) w) (w : W) (only : ∀ ψ, M.AT ψ → M.P ψ w → ψ = top) :
    ∃ v, M.R w v ∧ ∃ z, M.act z v := by
  obtain ⟨v, hv⟩ := serial_of C h2a h4 hE h3 w
  have x : D := Classical.ofNonempty
  have hEx : TwoClosedMixed.E3 M x w := by rw [only _ hE (h3 w)]; trivial
  have ess : TwoClosedMixed.Ess3 M top x w := fun ψ hA hψ u _ => ⟨fun e => by
      have := congrFun (congrFun e x) w; simp [top, bot] at this,
    fun y _ => by
      rcases top_or_bot h2a only C ψ hA with rfl | rfl
      · trivial
      · exact hψ.elim⟩
  obtain ⟨z, hz, _⟩ := hEx top C.top ess v hv
  exact ⟨v, hv, z, hz⟩

/-- **Variant 2, mixed quantifiers, no `Ax2b`.** -/
theorem equivalence_v2 [Nonempty D] (C : Closed M) (hE : M.AT (E2 M)) (h2a : Ax2a M)
    (h3 : ∀ w, M.P (E2 M) w) (h4 : Ax4P M) : Ax1GenTwo M ↔ Ax1Gen M :=
  ⟨ax1Gen_of_two_mixed C h2a (pTop_of C h4 hE h3) h4 (hact_v2 C h2a h4 hE h3),
    two_of_ax1Gen⟩

/-- **Variant 3′, mixed quantifiers, no `Ax2b`.** -/
theorem equivalence_v3 [Nonempty D] (C : Closed M) (hE : M.AT (TwoClosedMixed.E3 M)) (h2a : Ax2a M)
    (h3 : ∀ w, M.P (TwoClosedMixed.E3 M) w) (h4 : Ax4P M) : Ax1GenTwo M ↔ Ax1Gen M :=
  ⟨ax1Gen_of_two_mixed C h2a (pTop_of C h4 hE h3) h4 (hact_v3 C h2a h4 hE h3),
    two_of_ax1Gen⟩

/-! ## `Ax3` is needed in the mixed regime: one world, nothing actual -/

/-- Full carriers, one reflexive world, one entity that is not actual, `P φ w :↔ φ () w`. -/
def ghost : Model Unit Unit where
  R := fun _ _ => True
  act := fun _ _ => False
  AS := fun _ => True
  AT := fun _ => True
  AH := fun _ => True
  P := fun φ w => φ () w

theorem closed_ghost : Closed ghost where
  top := trivial
  bot := trivial
  neg := fun _ _ => trivial
  conj := fun _ _ _ _ => trivial
  lift := fun _ _ => trivial
  negS := fun _ _ => trivial
  god := trivial
  exG := trivial
  pos := trivial
  single := fun _ _ => trivial
  union := fun _ _ _ _ => trivial
  guard := fun _ _ _ _ => trivial
  atMost := fun _ _ _ _ => trivial

theorem ghost_eq_top (φ : Unit → Unit → Prop) (h : φ () ()) : φ = top := by
  funext x u; cases x; cases u; exact propext (iff_true_intro h)

theorem ax2a_ghost : Ax2a ghost := fun φ _ w =>
  ⟨(Classical.em (φ () w)).imp id id, fun ⟨a, b⟩ => b a⟩

theorem ax2b_ghost : Ax2b ghost := fun _ _ w h v _ => by cases w; cases v; exact h

theorem ax4P_ghost : Ax4P ghost := fun _ _ _ _ w hφ hinc => hinc w trivial () hφ

theorem ax1GenTwo_ghost : Ax1GenTwo ghost := fun _ _ _ _ w ⟨ψ₁, ψ₂, _, _, m1, m2, hne⟩ pos _ => by
  cases w
  exact absurd ((ghost_eq_top ψ₁ (pos ψ₁ trivial m1)).trans
    (ghost_eq_top ψ₂ (pos ψ₂ trivial m2)).symm) hne

theorem not_ax1Gen_ghost : ¬ Ax1Gen ghost := fun h =>
  h (fun _ _ => False) bot trivial trivial () (fun _ _ hm => hm.elim)
    (fun _ _ _ hz => hz.elim) |>.elim

theorem not_E2_ghost : ¬ ghost.P (E2 ghost) () := fun h => by
  obtain ⟨_, hz, _⟩ := h top trivial ⟨trivial, fun ψ _ hψ u _ y _ => by
    cases y; cases u; exact hψ⟩ () trivial
  exact hz

theorem not_E3_ghost : ¬ ghost.P (TwoClosedMixed.E3 ghost) () := fun h => by
  obtain ⟨_, hz, _⟩ := h top trivial (fun ψ _ hψ u _ => ⟨fun e => by
      have := congrFun (congrFun e ()) (); simp [top, bot] at this,
    fun y _ => by cases y; cases u; exact hψ⟩) () trivial
  exact hz

theorem not_ax4_ghost : ¬ Ax4 ghost := fun h =>
  h top bot trivial trivial () trivial (fun _ _ _ hz _ => hz) |>.elim

/-- **`Ax3` is needed in the mixed regime.**  A full (so `𝓛`-general) one-world model satisfies
`Closed`, `Ax2a`, `Ax2b`, possibilist `Ax4P` and `Ax1GenTwo`, but not `Ax1Gen`; mixed `Ax3`
(variant 2 and 3′) and actualist `Ax4` fail. -/
theorem ax3_needed :
    LGenF ghost ∧ Closed ghost ∧ Ax2a ghost ∧ Ax2b ghost ∧ Ax4P ghost ∧ Ax1GenTwo ghost ∧
      (∀ w v, ghost.R w v) ∧ ¬ Ax1Gen ghost ∧ ¬ (∀ w, ghost.P (E2 ghost) w) ∧
      ¬ (∀ w, ghost.P (TwoClosedMixed.E3 ghost) w) ∧ ¬ Ax4 ghost :=
  ⟨lgenF_full ghost (fun _ => trivial) (fun _ => trivial) (fun _ => trivial), closed_ghost,
    ax2a_ghost, ax2b_ghost, ax4P_ghost, ax1GenTwo_ghost, fun _ _ => trivial, not_ax1Gen_ghost,
    fun h => not_E2_ghost (h ()), fun h => not_E3_ghost (h ()), not_ax4_ghost⟩

end Programme.«20261022-0733-ontological».Run2.MixedNoRigidity

#print axioms Programme.«20261022-0733-ontological».Run2.MixedNoRigidity.equivalence_v2
#print axioms Programme.«20261022-0733-ontological».Run2.MixedNoRigidity.equivalence_v3
#print axioms Programme.«20261022-0733-ontological».Run2.MixedNoRigidity.ax3_needed
