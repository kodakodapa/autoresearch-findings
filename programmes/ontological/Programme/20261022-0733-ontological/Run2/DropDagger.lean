import Programme.«20261022-0733-ontological».Run2.TwoClosed

/-! # Variant 3 with `Ax1GenTwo` and `Th4`: side condition (†) dropped, in closed models

Target E, open item A2 of arXiv 2609.36279v4 (`sec:open`): the hybrid-free proof of `G_ex_Two`
in `OpenQuestions/Ax1GenTwoVariant3Th4.lean` assumes the side condition `someNonGod` (†).
th's witness (conjecture E2, `agents/th/lean/Programme/Th/DropDaggerV3.lean`) removes it:
the constant property `D := λz. ∃ᴱ y. G y` is positive by `Ax4` from `G`, and the paper's `Φ`
with `D` in place of `ψs` has the empty property as conjunction, so `Ax1GenTwo` makes `⊥`
positive at a godless world.

Here that argument is carried out over K1's Henkin-style `Model` with the `Closed` interface
(every witness is an admitted, nominal-free term: `D` by `lift`/`exG`, `Φ` by `union`, `guard`,
`single`, `negS`).  Variant 3: Gödel's essence without the conjunct `φ x`, the clause `φ ≠ ⊥`
inside the box of the inclusion, both in the essence (`Ess3`, `E3` of K1) and in `Ax4`. -/

namespace Programme.«20261022-0733-ontological».Run2.DropDagger

open Programme.«20261022-0733-ontological».Run2.TwoClosed

variable {W D : Type} (M : Model W D)

/-- Variant 3's inclusion: `□(φ ≠ ⊥ ∧ ∀ᴱ y, φ y → ψ y)`. -/
def PInc3 (φ ψ : D → W → Prop) (w : W) : Prop :=
  ∀ v, M.R w v → φ ≠ bot ∧ ∀ y, M.act y v → φ y v → ψ y v

/-- Variant 3's `Ax4`, over admitted properties. -/
def Ax4c : Prop := ∀ φ ψ, M.AT φ → M.AT ψ → ∀ w, M.P φ w → PInc3 M φ ψ w → M.P ψ w

/-- `Th4`, postulated in the library module: `◇ ∃ᴱ x. G x`. -/
def Th4 : Prop := ∀ w, ∃ v, M.R w v ∧ ExG M v

variable {M}

section
variable [Nonempty W] [Nonempty D] (C : Closed M) (hE : M.AT (E3 M)) (h2a : Ax2a M)
  (h3 : Ax3v3 M) (h4 : Ax4c M) (h4' : Th4 M)

include h4' in
theorem G_ne : G M ≠ bot := fun h => by
  obtain ⟨v, _, x, _, hG⟩ := h4' (Classical.ofNonempty : W)
  have := congrFun (congrFun h x) v
  exact (this ▸ hG : bot x v)

include hE h3 h4' in
theorem E_ne : E3 M ≠ bot := fun h => by
  obtain ⟨v, _, x, _, hG⟩ := h4' (Classical.ofNonempty : W)
  have hEx : E3 M x v := hG _ hE (h3 v)
  exact (congrFun (congrFun h x) v ▸ hEx : bot x v)

include C hE h3 h4 h4' in
theorem pTop (w : W) : M.P top w :=
  h4 _ top hE C.top w (h3 w) fun _ _ => ⟨E_ne hE h3 h4', fun _ _ _ => trivial⟩

include C hE h2a h3 h4 h4' in
/-- `L_Two` of the library module, over admitted carriers. -/
theorem L_two (hT : Ax1GenTwo M) (w : W) : M.P (G M) w := by
  by_cases h : TwoMembers M M.P w
  · exact hT M.P (G M) C.pos C.god w h (fun _ _ hψ => hψ) (fun _ _ _ _ => Iff.rfl)
  · have one : ∀ φ, M.AT φ → M.P φ w → φ = top := fun φ hA hφ =>
      Classical.byContradiction fun hne =>
        h ⟨φ, top, hA, C.top, hφ, pTop C hE h3 h4 h4' w, hne⟩
    have Gw : ∀ x, G M x w := fun x φ hA hφ => by rw [one φ hA hφ]; trivial
    rcases (h2a (G M) C.god w).1 with hG | hnG
    · exact hG
    · have e := one _ (C.neg _ C.god) hnG
      have x : D := Classical.ofNonempty
      have := congrFun (congrFun e x) w
      exact absurd (Gw x) (by simpa [neg, top] using this)

/-- The constant property "an actual God-like being exists". -/
def Dp (M : Model W D) : D → W → Prop := fun _ => ExG M

include C hE h2a h3 h4 h4' in
theorem pD (hT : Ax1GenTwo M) (w : W) : M.P (Dp M) w :=
  h4 (G M) (Dp M) C.god (C.lift _ C.exG) w (L_two C hE h2a h3 h4 h4' hT w)
    fun _ _ => ⟨G_ne h4', fun y hy hG => ⟨y, hy, hG⟩⟩

include C hE h2a h3 h4 h4' in
/-- **(†) dropped.** An actual God-like being exists at every world, with no side condition,
in every closed model of variant 3 with `Ax2a`, `Ax3`, `Ax4`, `Ax1GenTwo` and `Th4`, on any frame.
`Ax2b` is not used. -/
theorem gex (hT : Ax1GenTwo M) (w : W) : ExG M w :=
  Classical.byContradiction fun hn => by
    let ng : W → Prop := fun u => ¬ ExG M u
    have hng : M.AS ng := C.negS _ C.exG
    have hD : M.AT (Dp M) := C.lift _ C.exG
    let Φ : (D → W → Prop) → W → Prop := fun ψ' u =>
      (ng u ∧ (ψ' = top ∨ ψ' = Dp M)) ∨ (ExG M u ∧ ψ' = bot)
    have hΦ : M.AH Φ :=
      C.union _ _ (C.guard _ _ hng (C.union _ _ (C.single _ C.top) (C.single _ hD)))
        (C.guard _ _ C.exG (C.single _ C.bot))
    have hne : top ≠ Dp M := fun h => by
      have x : D := Classical.ofNonempty
      have t : top x w := trivial
      rw [h] at t
      exact hn t
    have two : TwoMembers M Φ w :=
      ⟨top, Dp M, C.top, hD, Or.inl ⟨hn, Or.inl rfl⟩, Or.inl ⟨hn, Or.inr rfl⟩, hne⟩
    have pos : PosProps M Φ w := by
      intro ψ' _ hψ'
      rcases hψ' with ⟨_, h | h⟩ | ⟨hex, _⟩
      · subst h; exact pTop C hE h3 h4 h4' w
      · subst h; exact pD C hE h2a h3 h4 h4' hT w
      · exact (hn hex).elim
    have cj : ConjOf M bot Φ w := by
      intro v _ z _
      refine ⟨False.elim, fun hall => ?_⟩
      by_cases hg : ExG M v
      · exact hall bot C.bot (Or.inr ⟨hg, rfl⟩)
      · exact hg (hall (Dp M) hD (Or.inl ⟨hg, Or.inr rfl⟩))
    have Pbot : M.P bot w := hT Φ bot hΦ C.bot w two pos cj
    have e1 : neg (top : D → W → Prop) = bot := by
      funext x v; exact propext ⟨fun h => h trivial, False.elim⟩
    exact (h2a top C.top w).2 ⟨pTop C hE h3 h4 h4' w, e1 ▸ Pbot⟩

include C hE h2a h3 h4 h4' in
/-- `Th5`: necessarily an actual God-like being exists. -/
theorem th5 (hT : Ax1GenTwo M) (w : W) : ∀ v, M.R w v → ExG M v :=
  fun v _ => gex C hE h2a h3 h4 h4' hT v

include C hE h2a h3 h4 h4' in
/-- Modal collapse for admitted propositions, on any frame, with `Ax2b`. -/
theorem mc (h2b : Ax2b M) (hT : Ax1GenTwo M) : MC M := by
  intro p hp w hpw v hv
  obtain ⟨g, _, hg⟩ := gex C hE h2a h3 h4 h4' hT w
  obtain ⟨k, _, hGk⟩ := gex C hE h2a h3 h4 h4' hT v
  have hl : M.AT (fun _ => p) := C.lift _ hp
  have hP : M.P (fun _ => p) w := Classical.byContradiction fun hn =>
    have hneg : M.P (neg (fun _ => p)) w := ((h2a _ hl w).1).resolve_left hn
    hg _ (C.neg _ hl) hneg hpw
  exact hGk _ hl (h2b _ hl w hP v hv)

end

/-! ## Non-vacuity: K1's one-world model satisfies all hypotheses -/

theorem unitModel_sat :
    Closed unitModel ∧ unitModel.AT (E3 unitModel) ∧ Ax2a unitModel ∧ Ax2b unitModel ∧
      Ax3v3 unitModel ∧ Ax4c unitModel ∧ Th4 unitModel ∧ Ax1GenTwo unitModel := by
  obtain ⟨C, _, h2a, h2b, _, _, hT⟩ := TwoClosed.unitModel_sat
  obtain ⟨hE, h3⟩ := unitModel_v3
  refine ⟨C, hE, h2a, h2b, h3, ?_, ?_, hT⟩
  · intro φ ψ _ _ w hφ hinc
    exact (hinc w trivial).2 () trivial hφ
  · intro w
    refine ⟨(), trivial, (), trivial, fun φ _ hφ => hφ⟩

end Programme.«20261022-0733-ontological».Run2.DropDagger

#print axioms Programme.«20261022-0733-ontological».Run2.DropDagger.gex
#print axioms Programme.«20261022-0733-ontological».Run2.DropDagger.th5
#print axioms Programme.«20261022-0733-ontological».Run2.DropDagger.mc
#print axioms Programme.«20261022-0733-ontological».Run2.DropDagger.unitModel_sat
