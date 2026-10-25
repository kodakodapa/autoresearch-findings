import Programme.«20261022-0733-ontological».Run2.TwoClosed

/-! # Ax1GenTwo and Ax1Gen in closed models, mixed (Anderson) quantifiers

Target E, the two mixed-quantifier copies of arXiv 2609.36279v4:
`OpenQuestions/Ax1GenTwoVariant2AndersonQuant.lean` and
`OpenQuestions/Ax1GenTwoVariant3PlainAndersonQuant.lean`.  Both close `Ax1GenTwo → Ax1Gen` with
`openproblem`.  The setting: property inclusion (in the essence and in `Ax4`) quantifies
possibilistically; necessary existence and the conjunction clause quantify actualistically.

Here, as in `TwoClosed`, quantifiers range over admitted carriers of a Henkin-style model, and the
carriers are closed under the nominal-free operations of `TwoClosed.Closed`, plus the closed
term `∃ y. G y` with the possibilist existential (`hpg`).

Route, following the library's mixed module: `PossGod_at`/`PossGod` give a possibilist God-like
being at every world; actualist necessary existence turns it into an actual one at every
successor (`Th5_Two`); `Serial` comes from `Ax3` and `Ax4`.  Then collapse for admitted
propositions follows on every frame.  For `Ax1Gen` with fewer than two members, if `φ` were not
positive then `~φ` would be, and an actual God-like being at a successor would satisfy `~φ` and,
through collapse of "every member of `Φ` is `ψ₀`", every member of `Φ`, hence `φ`. -/

namespace Programme.«20261022-0733-ontological».Run2.TwoClosedMixed

open Programme.«20261022-0733-ontological».Run2.TwoClosed

variable {W D : Type} (M : Model W D)

/-- Possibilist necessary property inclusion `□(∀ y, φ y → ψ y)`. -/
def PIncP (φ ψ : D → W → Prop) (w : W) : Prop :=
  ∀ v, M.R w v → ∀ y, φ y v → ψ y v

/-- Variant 2's essence with the possibilist inclusion. -/
def Ess2 (φ : D → W → Prop) (x : D) (w : W) : Prop :=
  φ x w ∧ ∀ ψ, M.AT ψ → ψ x w → PIncP M φ ψ w

/-- Variant 3′'s essence: Gödel's, the clause `φ ≠ ⊥` inside the box, possibilist inclusion. -/
def Ess3 (φ : D → W → Prop) (x : D) (w : W) : Prop :=
  ∀ ψ, M.AT ψ → ψ x w → ∀ v, M.R w v → φ ≠ bot ∧ ∀ y, φ y v → ψ y v

/-- Actualist necessary existence relative to an essence. -/
def NE (Ess : (D → W → Prop) → D → W → Prop) (x : D) (w : W) : Prop :=
  ∀ φ, M.AT φ → Ess φ x w → ∀ v, M.R w v → ∃ y, M.act y v ∧ φ y v

def E2 : D → W → Prop := NE M (Ess2 M)
def E3 : D → W → Prop := NE M (Ess3 M)

/-- `Ax4` with the possibilist inclusion. -/
def Ax4P : Prop := ∀ φ ψ, M.AT φ → M.AT ψ → ∀ w, M.P φ w → PIncP M φ ψ w → M.P ψ w

/-- `∃ y. G y`, possibilist. -/
def PExG (w : W) : Prop := ∃ y, G M y w

section core
/-! The core uses: `Closed`, `∃ y. G y` admitted, `Ax2a`, `Ax2b`, `Ax4P`, positive `⊤`, a
successor at every world, and `Th5` (a God-like being at `w` gives an actual one at every
successor).  Each variant derives the last three from its own `Ax3`. -/
variable {M} (C : Closed M) (hpg : M.AS (PExG M)) (h2a : Ax2a M) (h2b : Ax2b M)
  (h4 : Ax4P M) (h3 : ∀ w, M.P top w) (ser : ∀ w : W, ∃ v, M.R w v)
  (h5 : ∀ w x, G M x w → ∀ v, M.R w v → ExG M v)

include C h2a h3 in
theorem L_two [Nonempty D] (hT : Ax1GenTwo M) (w : W) : M.P (G M) w := by
  by_cases h : TwoMembers M M.P w
  · exact hT M.P (G M) C.pos C.god w h (fun _ _ hψ => hψ) (fun _ _ _ _ => Iff.rfl)
  · have one : ∀ φ, M.AT φ → M.P φ w → φ = top := fun φ hA hφ =>
      Classical.byContradiction fun hne =>
        h ⟨φ, top, hA, C.top, hφ, h3 w, hne⟩
    have Gw : ∀ x, G M x w := fun x φ hA hφ => by rw [one φ hA hφ]; trivial
    rcases (h2a (G M) C.god w).1 with hG | hnG
    · exact hG
    · have e := one _ (C.neg _ C.god) hnG
      have x : D := Classical.ofNonempty
      have := congrFun (congrFun e x) w
      exact absurd (Gw x) (by simpa [neg, top] using this)

include C hpg h2a h3 h4 in
/-- `PossGod_at` over admitted carriers. -/
theorem possGod_at [Nonempty D] (hT : Ax1GenTwo M) {w : W}
    (h2 : ∃ ψ, M.AT ψ ∧ M.P ψ w ∧ ψ ≠ top) : PExG M w :=
  Classical.byContradiction fun hn => by
    obtain ⟨ψ, hAψ, hPψ, hψ⟩ := h2
    let ng : W → Prop := fun u => ¬ PExG M u
    have hng : M.AS ng := C.negS _ hpg
    let χ : D → W → Prop := conj (fun _ => ng) ψ
    have hχ : M.AT χ := C.conj _ _ (C.lift _ hng) hAψ
    let Φ : (D → W → Prop) → W → Prop := fun ψ' u =>
      (ng u ∧ (ψ' = top ∨ ψ' = ψ)) ∨ (PExG M u ∧ ψ' = bot)
    have hΦ : M.AH Φ :=
      C.union _ _ (C.guard _ _ hng (C.union _ _ (C.single _ C.top) (C.single _ hAψ)))
        (C.guard _ _ hpg (C.single _ C.bot))
    have two : TwoMembers M Φ w :=
      ⟨top, ψ, C.top, hAψ, Or.inl ⟨hn, Or.inl rfl⟩, Or.inl ⟨hn, Or.inr rfl⟩,
        fun e => hψ e.symm⟩
    have pos : PosProps M Φ w := by
      intro ψ' _ hψ'
      rcases hψ' with ⟨_, h | h⟩ | ⟨hex, _⟩
      · subst h; exact h3 w
      · subst h; exact hPψ
      · exact (hn hex).elim
    have cj : ConjOf M χ Φ w := by
      intro v _ z _
      by_cases hg : PExG M v
      · constructor
        · intro ⟨hnot, _⟩; exact (hnot hg).elim
        · intro hall; exact (hall bot C.bot (Or.inr ⟨hg, rfl⟩)).elim
      · constructor
        · intro ⟨_, hψz⟩ ψ' _ hψ'
          rcases hψ' with ⟨_, h | h⟩ | ⟨hg', _⟩
          · subst h; trivial
          · subst h; exact hψz
          · exact (hg hg').elim
        · intro hall; exact ⟨hg, hall ψ hAψ (Or.inl ⟨hg, Or.inr rfl⟩)⟩
    have Pχ : M.P χ w := hT Φ χ hΦ hχ w two pos cj
    have incl : PIncP M χ (neg (G M)) w := fun _ _ y ⟨hnot, _⟩ hGy => hnot ⟨y, hGy⟩
    exact (h2a (G M) C.god w).2 ⟨L_two C h2a h3 hT w,
      h4 χ (neg (G M)) hχ (C.neg _ C.god) w Pχ incl⟩

include C hpg h2a h3 h4 in
/-- `PossGod`: a possibilist God-like being at every world. -/
theorem possGod [Nonempty D] (hT : Ax1GenTwo M) (w : W) : PExG M w := by
  by_cases h2 : ∃ ψ, M.AT ψ ∧ M.P ψ w ∧ ψ ≠ top
  · exact possGod_at C hpg h2a h4 h3 hT h2
  · refine ⟨Classical.ofNonempty, fun φ hA hP => ?_⟩
    have : φ = top := Classical.byContradiction fun hne => h2 ⟨φ, hA, hP, hne⟩
    rw [this]; trivial

include C h2a h2b in
/-- `PosOfGod` + `Ax2b`: a God-like being at `w` and one at a successor `v` carry every admitted
proposition true at `w` to `v`. -/
theorem carry {p : W → Prop} (hp : M.AS p) {w v : W} {g k : D} (hg : G M g w) (hpw : p w)
    (hv : M.R w v) (hk : G M k v) : p v := by
  have hl : M.AT (fun _ => p) := C.lift _ hp
  have hP : M.P (fun _ => p) w := Classical.byContradiction fun hn =>
    hg _ (C.neg _ hl) (((h2a _ hl w).1).resolve_left hn) hpw
  exact hk _ hl (h2b _ hl w hP v hv)

include C hpg h2a h2b h3 h4 in
/-- Modal collapse for admitted propositions, on every frame, with no nominal. -/
theorem mc [Nonempty D] (hT : Ax1GenTwo M) : MC M := by
  intro p hp w hpw v hv
  obtain ⟨g, hg⟩ := possGod C hpg h2a h4 h3 hT w
  obtain ⟨k, hk⟩ := possGod C hpg h2a h4 h3 hT v
  exact carry C h2a h2b hp hg hpw hv hk

include C hpg h2a h2b h3 h4 ser h5 in
/-- **`Ax1GenTwo` gives `Ax1Gen`** in the mixed setting, over admitted carriers. -/
theorem ax1Gen_of_two [Nonempty D] (hT : Ax1GenTwo M) : Ax1Gen M := by
  intro Φ φ hΦ hφ w pos cj
  by_cases two : TwoMembers M Φ w
  · exact hT Φ φ hΦ hφ w two pos cj
  rcases (h2a φ hφ w).1 with hp | hneg
  · exact hp
  exfalso
  have hmc := mc C hpg h2a h2b h4 h3 hT
  obtain ⟨v, hv⟩ := ser w
  obtain ⟨g₀, hg₀⟩ := possGod C hpg h2a h4 h3 hT w
  obtain ⟨g, ag, hG⟩ := h5 w g₀ hg₀ v hv
  have nφ : ¬ φ g v := hG _ (C.neg _ hφ) (h2b _ (C.neg _ hφ) w hneg v hv)
  -- every member of `Φ` at `w` is `ψ₀`, a positive admitted property
  have key : ∀ ψ₀, M.AT ψ₀ → M.P ψ₀ w → (∀ ψ, M.AT ψ → Φ ψ w → ψ = ψ₀) → False :=
    fun ψ₀ hA₀ hP₀ hsub => by
      have hsubv := hmc _ (C.atMost Φ ψ₀ hΦ hA₀) w hsub v hv
      apply nφ
      refine (cj v hv g ag).2 fun ψ hA hm => ?_
      rw [hsubv ψ hA hm]
      exact hG ψ₀ hA₀ (h2b ψ₀ hA₀ w hP₀ v hv)
  by_cases hex : ∃ ψ, M.AT ψ ∧ Φ ψ w
  · obtain ⟨ψ₀, hA₀, m₀⟩ := hex
    exact key ψ₀ hA₀ (pos ψ₀ hA₀ m₀) fun ψ hA hψ =>
      Classical.byContradiction fun hne => two ⟨ψ, ψ₀, hA, hA₀, hψ, m₀, hne⟩
  · exact key top C.top (h3 w) fun ψ hA hψ => (hex ⟨ψ, hA, hψ⟩).elim

end core

/-! ## The variants: positive `⊤`, `Serial` and `Th5` from each variant's own `Ax3` -/

section variants
variable {M} (C : Closed M) (h2a : Ax2a M) (h2b : Ax2b M) (h4 : Ax4P M)

include C h4 in
theorem pTop_of {Ess} (hE : M.AT (NE M Ess)) (h3 : ∀ w, M.P (NE M Ess) w) (w : W) :
    M.P top w :=
  h4 _ top hE (by exact C.top) w (h3 w) (fun _ _ _ _ => trivial)

include C h2a h4 in
theorem serial_of {Ess} (hE : M.AT (NE M Ess)) (h3 : ∀ w, M.P (NE M Ess) w) (w : W) :
    ∃ v, M.R w v :=
  Classical.byContradiction fun dead =>
    have all : ∀ ψ, M.AT ψ → M.P ψ w := fun ψ hA =>
      h4 _ ψ hE hA w (h3 w) fun v hv => absurd ⟨v, hv⟩ dead
    (h2a top C.top w).2 ⟨all _ C.top, all _ (C.neg _ C.top)⟩

/-- `Th5`, given that a God-like being has `G` as an essence (`Th1`). -/
theorem th5_of {Ess} (hE : M.AT (NE M Ess)) (h3 : ∀ w, M.P (NE M Ess) w) (C : Closed M)
    (th1 : ∀ w x, G M x w → Ess (G M) x w) (w : W) (x : D) (hx : G M x w) (v : W)
    (hv : M.R w v) : ExG M v :=
  hx _ hE (h3 w) (G M) C.god (th1 w x hx) v hv

include C h2a h2b in
theorem th1_v2 (w : W) (x : D) (hx : G M x w) : Ess2 M (G M) x w :=
  ⟨hx, fun ψ hA hψ v hv y hGy => by
    have hP : M.P ψ w := Classical.byContradiction fun hn =>
      hx _ (C.neg _ hA) (((h2a _ hA w).1).resolve_left hn) hψ
    exact hGy ψ hA (h2b ψ hA w hP v hv)⟩

include C h2a h2b in
theorem th1_v3 (w : W) (x : D) (hx : G M x w) : Ess3 M (G M) x w := by
  intro ψ hA hψ v hv
  refine ⟨fun e => ?_, fun y hGy => ?_⟩
  · have := (th1_v2 C h2a h2b w x hx).1
    rw [e] at this; exact this
  · exact (th1_v2 C h2a h2b w x hx).2 ψ hA hψ v hv y hGy

include C h2a h2b h4 in
/-- **Variant 2, mixed quantifiers** (`Ax1GenTwoVariant2AndersonQuant`): in every closed model
with `E` and possibilist `∃ y. G y` admitted, `Ax2a`, `Ax2b`, `Ax3`, possibilist `Ax4` give
`Ax1GenTwo ↔ Ax1Gen`, on any frame and for any actuality predicate. -/
theorem equivalence_v2 [Nonempty D] (hpg : M.AS (PExG M)) (hE : M.AT (E2 M))
    (h3 : ∀ w, M.P (E2 M) w) : Ax1GenTwo M ↔ Ax1Gen M :=
  ⟨ax1Gen_of_two C hpg h2a h2b h4 (pTop_of C h4 hE h3) (serial_of C h2a h4 hE h3)
      (th5_of hE h3 C (th1_v2 C h2a h2b)),
    two_of_ax1Gen⟩

include C h2a h2b h4 in
theorem mc_v2 [Nonempty D] (hpg : M.AS (PExG M)) (hE : M.AT (E2 M))
    (h3 : ∀ w, M.P (E2 M) w) (hT : Ax1GenTwo M) : MC M :=
  mc C hpg h2a h2b h4 (pTop_of C h4 hE h3) hT

include C h2a h2b h4 in
/-- **Variant 3′, mixed quantifiers** (`Ax1GenTwoVariant3PlainAndersonQuant`). -/
theorem equivalence_v3 [Nonempty D] (hpg : M.AS (PExG M)) (hE : M.AT (E3 M))
    (h3 : ∀ w, M.P (E3 M) w) : Ax1GenTwo M ↔ Ax1Gen M :=
  ⟨ax1Gen_of_two C hpg h2a h2b h4 (pTop_of C h4 hE h3) (serial_of C h2a h4 hE h3)
      (th5_of hE h3 C (th1_v3 C h2a h2b)),
    two_of_ax1Gen⟩

include C h2a h2b h4 in
theorem mc_v3 [Nonempty D] (hpg : M.AS (PExG M)) (hE : M.AT (E3 M))
    (h3 : ∀ w, M.P (E3 M) w) (hT : Ax1GenTwo M) : MC M :=
  mc C hpg h2a h2b h4 (pTop_of C h4 hE h3) hT

end variants

/-! ## Non-vacuity: the one-world model of `TwoClosed` satisfies every hypothesis -/

theorem unitModel_mixed :
    Closed unitModel ∧ unitModel.AS (PExG unitModel) ∧ unitModel.AT (E2 unitModel) ∧
      unitModel.AT (E3 unitModel) ∧ Ax2a unitModel ∧ Ax2b unitModel ∧ Ax4P unitModel ∧
      (∀ w, unitModel.P (E2 unitModel) w) ∧ (∀ w, unitModel.P (E3 unitModel) w) ∧
      Ax1GenTwo unitModel := by
  obtain ⟨C, _, h2a, h2b, _, _, hT⟩ := unitModel_sat
  refine ⟨C, trivial, trivial, trivial, h2a, h2b, ?_, ?_, ?_, hT⟩
  · intro φ ψ _ _ w hφ hinc
    exact hinc w trivial () hφ
  · intro w φ _ hess v _
    exact ⟨(), trivial, hess.1⟩
  · intro w φ _ hess v _
    have hne := (hess top trivial trivial v trivial).1
    refine ⟨(), trivial, Classical.byContradiction fun hn => hne ?_⟩
    funext x u
    cases x; cases u; cases v
    exact propext ⟨hn, False.elim⟩

end Programme.«20261022-0733-ontological».Run2.TwoClosedMixed

#print axioms Programme.«20261022-0733-ontological».Run2.TwoClosedMixed.equivalence_v2
#print axioms Programme.«20261022-0733-ontological».Run2.TwoClosedMixed.mc_v2
#print axioms Programme.«20261022-0733-ontological».Run2.TwoClosedMixed.equivalence_v3
#print axioms Programme.«20261022-0733-ontological».Run2.TwoClosedMixed.mc_v3
#print axioms Programme.«20261022-0733-ontological».Run2.TwoClosedMixed.unitModel_mixed
