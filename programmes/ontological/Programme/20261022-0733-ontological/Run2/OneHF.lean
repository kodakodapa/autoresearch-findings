import Programme.«20261022-0733-ontological».Run2.DropDagger

/-! # Variant 3 with `Ax1GenOne`, hybrid-free, in closed models

Target E, open item A5 of arXiv 2609.36279v4 (`sec:one`, `sec:open`): in variant 3 under the
one-conjunct reading `Ax1GenOne` (library `OpenQuestions/Ax1GenOneVariant3.lean`), the paper
reaches `P ⊤`, `G_ex`, `Th4` only through `OneWorld`, whose witnesses are nominals.
th's conjecture E4 (`agents/th/lean/Programme/Th/OneV3HybridFree.lean`) derives them without.

Here that argument is carried out over K1's Henkin-style `Model` with the `Closed` interface, plus
one more closure: the actuality predicate `λz. z@` (a constant of the signature) is an admitted
property.  Variant 3 as in `DropDagger`: clause `φ ≠ ⊥` inside the box, in `Ess3`/`E3` and `Ax4c`.
Witnesses: `ν := λz. ¬ z@` (`neg`, `act`), the singleton `{⊥}` (`single`), `D := λz. ∃ᴱ G`
(`lift`, `exG`) and the two-branch `Φ` of E2 (`union`, `guard`, `single`, `negS`). -/

namespace Programme.«20261022-0733-ontological».Run2.OneHF

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.DropDagger

variable {W D : Type} (M : Model W D)

/-- `Φ` has an admitted member at `w`. -/
def NonEmptyS (Φ : (D → W → Prop) → W → Prop) (w : W) : Prop := ∃ ψ, M.AT ψ ∧ Φ ψ w

/-- The conjunction axiom, one-conjunct reading, over admitted carriers. -/
def Ax1GenOne : Prop := ∀ Φ φ, M.AH Φ → M.AT φ → ∀ w,
  NonEmptyS M Φ w → PosProps M Φ w → ConjOf M φ Φ w → M.P φ w

variable {M}

section
variable [Nonempty D] (C : Closed M) (hact : M.AT (fun z u => M.act z u)) (hE : M.AT (E3 M))
  (h2a : Ax2a M) (h3 : Ax3v3 M) (h4 : Ax4c M) (h1 : Ax1GenOne M)

theorem negTop : neg (top : D → W → Prop) = bot := by
  funext x v; exact propext ⟨fun h => h trivial, False.elim⟩

theorem negBot : neg (bot : D → W → Prop) = top := by
  funext x v; exact propext ⟨fun _ => trivial, fun _ h => h⟩

include C h2a h4 in
/-- `Ax4` from a positive non-empty property gives every admitted property, against `Ax2a`. -/
theorem no_vacuous {w : W} {φ : D → W → Prop} (hA : M.AT φ) (hP : M.P φ w) (hne : φ ≠ bot)
    (hv : ∀ v, M.R w v → ∀ y, M.act y v → ¬ φ y v) : False :=
  (h2a top C.top w).2
    ⟨h4 φ _ hA C.top w hP fun v hv' => ⟨hne, fun y hy hφ => (hv v hv' y hy hφ).elim⟩,
     h4 φ _ hA (C.neg _ C.top) w hP fun v hv' => ⟨hne, fun y hy hφ => (hv v hv' y hy hφ).elim⟩⟩

include C hact h2a h4 h1 in
/-- `AllActual_of_PBot`: if `⊥` is positive then every entity is actual at every world.
Witness `ν := λz. ¬ z@` with `Φ := {⊥}`. -/
theorem allActual {w : W} (pb : M.P bot w) : ∀ z u, M.act z u :=
  Classical.byContradiction fun h => by
    let ν : D → W → Prop := neg (fun z u => M.act z u)
    have hν : M.AT ν := C.neg _ hact
    have Pν : M.P ν w := h1 (fun ψ' _ => ψ' = bot) ν (C.single _ C.bot) hν w
      ⟨bot, C.bot, rfl⟩ (fun ψ _ hψ => hψ ▸ pb)
      (fun _ _ z hz => ⟨fun hn => (hn hz).elim, fun hall => (hall bot C.bot rfl).elim⟩)
    have ne : ν ≠ bot := fun e => h fun z u =>
      Classical.byContradiction fun hn => (congrFun (congrFun e z) u ▸ (hn : ν z u) : bot z u)
    exact no_vacuous C h2a h4 hν Pν ne fun _ _ y hy hν => hν hy

include C hact hE h2a h3 h4 h1 in
/-- `¬ P ⊥` at every world, with no nominal. -/
theorem notPBot (w : W) : ¬ M.P bot w := fun pb => by
  have act := allActual C hact h2a h4 h1 pb
  have nT : ¬ M.P top w := fun ht => (h2a top C.top w).2 ⟨ht, (negTop (W := W) (D := D)) ▸ pb⟩
  have onlyBot : ∀ φ, M.AT φ → M.P φ w → φ = bot := fun φ hA hp =>
    Classical.byContradiction fun hne =>
      nT (h4 φ top hA C.top w hp fun _ _ => ⟨hne, fun _ _ _ => trivial⟩)
  have dich : ∀ φ, M.AT φ → φ = bot ∨ φ = top := fun φ hA =>
    (h2a φ hA w).1.elim (fun h => Or.inl (onlyBot φ hA h)) fun h => Or.inr (by
      have h2 := onlyBot _ (C.neg _ hA) h
      funext x v; apply propext; constructor
      · intro _; trivial
      · intro _; exact Classical.byContradiction fun hn =>
          (congrFun (congrFun h2 x) v ▸ (hn : neg φ x v) : bot x v))
  have x0 : D := Classical.ofNonempty
  have Ex : E3 M x0 w := fun φ hA hess u hu => by
    have ne := (hess top C.top trivial u hu).1
    rcases dich φ hA with h | h
    · exact (ne h).elim
    · exact ⟨x0, act x0 u, by rw [h]; trivial⟩
  have Ene : E3 M ≠ bot := fun e => (congrFun (congrFun e x0) w ▸ Ex : bot x0 w)
  exact nT (h4 _ top hE C.top w (h3 w) fun _ _ => ⟨Ene, fun _ _ _ => trivial⟩)

include C hact hE h2a h3 h4 h1 in
theorem pTop (w : W) : M.P top w :=
  negBot (W := W) (D := D) ▸ (h2a bot C.bot w).1.resolve_left (notPBot C hact hE h2a h3 h4 h1 w)

include C hE h1 h3 in
/-- `L_One`: `Φ := P` is non-empty by `Ax3`. -/
theorem L_one (w : W) : M.P (G M) w :=
  h1 M.P (G M) C.pos C.god w ⟨E3 M, hE, h3 w⟩ (fun _ _ h => h) (fun _ _ _ _ => Iff.rfl)

include C hact hE h2a h3 h4 h1 in
theorem pD (w : W) : M.P (Dp M) w :=
  h4 (G M) (Dp M) C.god (C.lift _ C.exG) w (L_one C hE h3 h1 w) fun _ _ =>
    ⟨fun e => notPBot C hact hE h2a h3 h4 h1 w (e ▸ L_one C hE h3 h1 w),
     fun y hy hG => ⟨y, hy, hG⟩⟩

include C hact hE h2a h3 h4 h1 in
/-- **`G_ex` under `Ax1GenOne`, hybrid-free**: an actual God-like being at every world, on any
frame, in every closed model of variant 3 with `Ax2a`, `Ax3`, `Ax4`, `Ax1GenOne`. -/
theorem gex (w : W) : ExG M w :=
  Classical.byContradiction fun hn => by
    let ng : W → Prop := fun u => ¬ ExG M u
    have hng : M.AS ng := C.negS _ C.exG
    have hD : M.AT (Dp M) := C.lift _ C.exG
    let Φ : (D → W → Prop) → W → Prop := fun ψ' u =>
      (ng u ∧ (ψ' = top ∨ ψ' = Dp M)) ∨ (ExG M u ∧ ψ' = bot)
    have hΦ : M.AH Φ :=
      C.union _ _ (C.guard _ _ hng (C.union _ _ (C.single _ C.top) (C.single _ hD)))
        (C.guard _ _ C.exG (C.single _ C.bot))
    have pos : PosProps M Φ w := by
      intro ψ' _ hψ'
      rcases hψ' with ⟨_, h | h⟩ | ⟨hex, _⟩
      · subst h; exact pTop C hact hE h2a h3 h4 h1 w
      · subst h; exact pD C hact hE h2a h3 h4 h1 w
      · exact (hn hex).elim
    have cj : ConjOf M bot Φ w := by
      intro v _ z _
      refine ⟨False.elim, fun hall => ?_⟩
      by_cases hg : ExG M v
      · exact hall bot C.bot (Or.inr ⟨hg, rfl⟩)
      · exact hg (hall (Dp M) hD (Or.inl ⟨hg, Or.inr rfl⟩))
    exact notPBot C hact hE h2a h3 h4 h1 w
      (h1 Φ bot hΦ C.bot w ⟨top, C.top, Or.inl ⟨hn, Or.inl rfl⟩⟩ pos cj)

include C hE h2a h3 h4 in
/-- `Serial`: the definitions force every world to see a world. -/
theorem serial (w : W) : ∃ v, M.R w v :=
  Classical.byContradiction fun dead =>
    no_vacuous C h2a h4 hE (h3 w)
      (fun e => by
        -- with no successor, `E3` holds of every entity: so it is not `⊥`
        have x0 : D := Classical.ofNonempty
        have : E3 M x0 w := fun _ _ _ v hv => (dead ⟨v, hv⟩).elim
        exact (congrFun (congrFun e x0) w ▸ this : bot x0 w))
      fun v hv => (dead ⟨v, hv⟩).elim

include C hact hE h2a h3 h4 h1 in
/-- `Th4`: possibly an actual God-like being exists. -/
theorem th4 (w : W) : ∃ v, M.R w v ∧ ExG M v :=
  let ⟨v, hv⟩ := serial C hE h2a h3 h4 w
  ⟨v, hv, gex C hact hE h2a h3 h4 h1 v⟩

include C hact hE h2a h3 h4 h1 in
/-- Modal collapse for admitted propositions, with `Ax2b`, on any frame. -/
theorem mc (h2b : Ax2b M) : MC M := by
  intro p hp w hpw v hv
  obtain ⟨g, _, hg⟩ := gex C hact hE h2a h3 h4 h1 w
  obtain ⟨k, _, hGk⟩ := gex C hact hE h2a h3 h4 h1 v
  have hl : M.AT (fun _ => p) := C.lift _ hp
  have hP : M.P (fun _ => p) w := Classical.byContradiction fun hn =>
    hg _ (C.neg _ hl) (((h2a _ hl w).1).resolve_left hn) hpw
  exact hGk _ hl (h2b _ hl w hP v hv)

end

/-! ## Non-vacuity: K1's one-world model satisfies all hypotheses -/

theorem unitModel_sat :
    Closed unitModel ∧ unitModel.AT (fun z u => unitModel.act z u) ∧
      unitModel.AT (E3 unitModel) ∧ Ax2a unitModel ∧ Ax2b unitModel ∧ Ax3v3 unitModel ∧
      Ax4c unitModel ∧ Ax1GenOne unitModel := by
  obtain ⟨C, hE, h2a, h2b, h3, h4, _, _⟩ := DropDagger.unitModel_sat
  refine ⟨C, trivial, hE, h2a, h2b, h3, h4, ?_⟩
  intro Φ φ _ _ w _ hpos hc
  exact (hc w trivial () trivial).2 fun ψ hA hm => hpos ψ hA hm

end Programme.«20261022-0733-ontological».Run2.OneHF

#print axioms Programme.«20261022-0733-ontological».Run2.OneHF.notPBot
#print axioms Programme.«20261022-0733-ontological».Run2.OneHF.pTop
#print axioms Programme.«20261022-0733-ontological».Run2.OneHF.gex
#print axioms Programme.«20261022-0733-ontological».Run2.OneHF.th4
#print axioms Programme.«20261022-0733-ontological».Run2.OneHF.mc
#print axioms Programme.«20261022-0733-ontological».Run2.OneHF.unitModel_sat
