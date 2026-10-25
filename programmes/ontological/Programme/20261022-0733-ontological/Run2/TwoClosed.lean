/-! # Ax1GenTwo and Ax1Gen in closed (L-general) models of variant 2

Target E of the programme (arXiv 2609.36279v4, Section "What stays open"): whether `Ax1GenTwo`
is equivalent to unrestricted `Ax1Gen` in variant 2 without nominals.

The library file `OpenQuestions/Ax1GenTwoVariant2.lean` proves the equivalence (`Two_equivalent`)
in full models, through `R_Id`, which substitutes the nominal `fun u => u = w` into modal collapse.
Here the setting is a Henkin-style model whose quantifiers range over *admitted* propositions,
properties and collections of properties only.  The admitted carriers are closed under the
operations listed in `Closed`; each is the denotation of a term of the object language
(no nominal among them), so every model closed under the definable operations satisfies them.

Result: in every such model, variant 2's `Ax2a`, `Ax2b`, `Ax3`, `Ax4` give
`Ax1GenTwo ↔ Ax1Gen` (both quantified over admitted collections and properties), for any
actuality predicate (the possibilist reading is `act := fun _ _ => True`) and any frame.
The route: `L_Two`, `Th4_Two`, `ae_Two`, `G_ex_Two_at` of the library carried over to
admitted witnesses give an actual God-like being at every world and modal collapse for admitted
propositions; the one-member and empty cases of `Ax1Gen` then substitute the admitted
proposition "every member of `Φ` is `ψ₀`" into the collapse, where the library used `R_Id`. -/

namespace Programme.«20261022-0733-ontological».Run2.TwoClosed

/-- A Henkin-style model of the embedding: worlds `W`, entities `D`, accessibility, actuality,
admitted carriers at the types of propositions, properties and collections of properties, and
positivity. -/
structure Model (W D : Type) where
  R : W → W → Prop
  act : D → W → Prop
  AS : (W → Prop) → Prop
  AT : (D → W → Prop) → Prop
  AH : ((D → W → Prop) → W → Prop) → Prop
  P : (D → W → Prop) → W → Prop

variable {W D : Type} (M : Model W D)

def top : D → W → Prop := fun _ _ => True
def bot : D → W → Prop := fun _ _ => False
def neg (φ : D → W → Prop) : D → W → Prop := fun x w => ¬ φ x w
def conj (φ ψ : D → W → Prop) : D → W → Prop := fun x w => φ x w ∧ ψ x w

/-- Property inclusion of variant 2: `□(∀ᴱ y, φ y → ψ y)`. -/
def PInc (φ ψ : D → W → Prop) (w : W) : Prop :=
  ∀ v, M.R w v → ∀ y, M.act y v → φ y v → ψ y v

/-- God-like: every admitted positive property. -/
def G (x : D) (w : W) : Prop := ∀ φ, M.AT φ → M.P φ w → φ x w

/-- Essence of variant 2 (modified essence), quantifying over admitted properties. -/
def Ess (φ : D → W → Prop) (x : D) (w : W) : Prop :=
  φ x w ∧ ∀ ψ, M.AT ψ → ψ x w → PInc M φ ψ w

/-- Necessary existence. -/
def E (x : D) (w : W) : Prop :=
  ∀ φ, M.AT φ → Ess M φ x w → ∀ v, M.R w v → ∃ y, M.act y v ∧ φ y v

/-- `∃ᴱ y, G y`. -/
def ExG (w : W) : Prop := ∃ y, M.act y w ∧ G M y w

def PosProps (Φ : (D → W → Prop) → W → Prop) (w : W) : Prop :=
  ∀ ψ, M.AT ψ → Φ ψ w → M.P ψ w

/-- `□(∀ᴱ z, φ z ↔ ∀ ψ, Φ ψ → ψ z)`. -/
def ConjOf (φ : D → W → Prop) (Φ : (D → W → Prop) → W → Prop) (w : W) : Prop :=
  ∀ v, M.R w v → ∀ z, M.act z v → (φ z v ↔ ∀ ψ, M.AT ψ → Φ ψ v → ψ z v)

def TwoMembers (Φ : (D → W → Prop) → W → Prop) (w : W) : Prop :=
  ∃ ψ₁ ψ₂, M.AT ψ₁ ∧ M.AT ψ₂ ∧ Φ ψ₁ w ∧ Φ ψ₂ w ∧ ψ₁ ≠ ψ₂

/-! ## Variant 2's axioms, over admitted carriers -/

def Ax2a : Prop := ∀ φ, M.AT φ → ∀ w, (M.P φ w ∨ M.P (neg φ) w) ∧ ¬ (M.P φ w ∧ M.P (neg φ) w)
def Ax2b : Prop := ∀ φ, M.AT φ → ∀ w, M.P φ w → ∀ v, M.R w v → M.P φ v
def Ax3 : Prop := ∀ w, M.P (E M) w
def Ax4 : Prop := ∀ φ ψ, M.AT φ → M.AT ψ → ∀ w, M.P φ w → PInc M φ ψ w → M.P ψ w

def Ax1GenTwo : Prop := ∀ Φ φ, M.AH Φ → M.AT φ → ∀ w,
  TwoMembers M Φ w → PosProps M Φ w → ConjOf M φ Φ w → M.P φ w
def Ax1Gen : Prop := ∀ Φ φ, M.AH Φ → M.AT φ → ∀ w,
  PosProps M Φ w → ConjOf M φ Φ w → M.P φ w

/-- Modal collapse for admitted propositions. -/
def MC : Prop := ∀ p, M.AS p → ∀ w, p w → ∀ v, M.R w v → p v

/-- Closure of the admitted carriers.  Each field is the denotation of an object-language term
with admitted parameters; none is a nominal. -/
structure Closed : Prop where
  /-- `λx. ⊤` and `λx. ⊥` -/
  top : M.AT top
  bot : M.AT bot
  /-- `λx. ¬ φ x` -/
  neg : ∀ φ, M.AT φ → M.AT (neg φ)
  /-- `λx. φ x ∧ ψ x` -/
  conj : ∀ φ ψ, M.AT φ → M.AT ψ → M.AT (conj φ ψ)
  /-- `λx. p` (vacuous abstraction) -/
  lift : ∀ p, M.AS p → M.AT (fun _ => p)
  /-- `¬ p` -/
  negS : ∀ p, M.AS p → M.AS (fun w => ¬ p w)
  /-- `G`, `∃ᴱ y. G y`: closed terms of the language -/
  god : M.AT (G M)
  exG : M.AS (ExG M)
  /-- the constant `P`, as a collection of properties -/
  pos : M.AH M.P
  /-- `λψ'. ψ' = ψ` (primitive equality at property type) -/
  single : ∀ ψ, M.AT ψ → M.AH (fun ψ' _ => ψ' = ψ)
  /-- `λψ'. Φ ψ' ∨ Ψ ψ'` -/
  union : ∀ Φ Ψ, M.AH Φ → M.AH Ψ → M.AH (fun ψ w => Φ ψ w ∨ Ψ ψ w)
  /-- `λψ'. p ∧ Φ ψ'` -/
  guard : ∀ p Φ, M.AS p → M.AH Φ → M.AH (fun ψ w => p w ∧ Φ ψ w)
  /-- `∀ψ. Φ ψ → ψ = ψ₀` -/
  atMost : ∀ Φ ψ₀, M.AH Φ → M.AT ψ₀ → M.AS (fun u => ∀ ψ, M.AT ψ → Φ ψ u → ψ = ψ₀)

/-! ## Derivations -/

section
/-! The core results assume only that `⊤` is positive (`h3`), which each variant derives from
its own necessary existence (`pTop_v2`, `pTop_v3`); the essence is not used otherwise. -/
variable {M} (C : Closed M) (h2a : Ax2a M) (h3 : ∀ w, M.P top w) (h4 : Ax4 M)

include h3 in
theorem pTop (w : W) : M.P top w := h3 w

include C h2a h3 h4 in
/-- `L_Two` over admitted carriers. -/
theorem L_two [Nonempty D] (hT : Ax1GenTwo M) (w : W) : M.P (G M) w := by
  by_cases h : TwoMembers M M.P w
  · exact hT M.P (G M) C.pos C.god w h (fun _ _ hψ => hψ) (fun _ _ _ _ => Iff.rfl)
  · have one : ∀ φ, M.AT φ → M.P φ w → φ = top := fun φ hA hφ =>
      Classical.byContradiction fun hne =>
        h ⟨φ, top, hA, C.top, hφ, pTop h3 w, hne⟩
    have Gw : ∀ x, G M x w := fun x φ hA hφ => by rw [one φ hA hφ]; trivial
    rcases (h2a (G M) C.god w).1 with hG | hnG
    · exact hG
    · have e := one _ (C.neg _ C.god) hnG
      have x : D := Classical.ofNonempty
      have := congrFun (congrFun e x) w
      exact absurd (Gw x) (by simpa [neg, top] using this)

include C h2a h3 h4 in
/-- `Th4_Two`: every world sees an actual God-like being. -/
theorem th4 [Nonempty D] (hT : Ax1GenTwo M) (w : W) : ∃ v, M.R w v ∧ ExG M v :=
  Classical.byContradiction fun hn =>
    (h2a (G M) C.god w).2 ⟨L_two C h2a h3 h4 hT w,
      h4 (G M) (neg (G M)) C.god (C.neg _ C.god) w (L_two C h2a h3 h4 hT w)
        (fun v hv y hy hg => fun _ => hn ⟨v, hv, y, hy, hg⟩)⟩

include C h2a h3 h4 in
/-- `G_ex_Two_at`: where an admitted property other than `⊤` is positive, an actual God-like
being exists.  The witness collection is admitted by `single`, `union`, `guard`. -/
theorem gex_at [Nonempty D] (hT : Ax1GenTwo M) {w : W}
    (h2 : ∃ ψ, M.AT ψ ∧ M.P ψ w ∧ ψ ≠ top) : ExG M w :=
  Classical.byContradiction fun hn => by
    obtain ⟨ψ, hAψ, hPψ, hψ⟩ := h2
    let ng : W → Prop := fun u => ¬ ExG M u
    have hng : M.AS ng := C.negS _ C.exG
    let χ : D → W → Prop := conj (fun _ => ng) ψ
    have hχ : M.AT χ := C.conj _ _ (C.lift _ hng) hAψ
    let Φ : (D → W → Prop) → W → Prop := fun ψ' u =>
      (ng u ∧ (ψ' = top ∨ ψ' = ψ)) ∨ (ExG M u ∧ ψ' = bot)
    have hΦ : M.AH Φ :=
      C.union _ _ (C.guard _ _ hng (C.union _ _ (C.single _ C.top) (C.single _ hAψ)))
        (C.guard _ _ C.exG (C.single _ C.bot))
    have two : TwoMembers M Φ w :=
      ⟨top, ψ, C.top, hAψ, Or.inl ⟨hn, Or.inl rfl⟩, Or.inl ⟨hn, Or.inr rfl⟩,
        fun e => hψ e.symm⟩
    have pos : PosProps M Φ w := by
      intro ψ' _ hψ'
      rcases hψ' with ⟨_, h | h⟩ | ⟨hex, _⟩
      · subst h; exact pTop h3 w
      · subst h; exact hPψ
      · exact (hn hex).elim
    have cj : ConjOf M χ Φ w := by
      intro v _ z _
      by_cases hg : ExG M v
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
    have incl : PInc M χ (neg (G M)) w := fun _ _ y hy ⟨hnot, _⟩ hGy => hnot ⟨y, hy, hGy⟩
    exact (h2a (G M) C.god w).2 ⟨L_two C h2a h3 h4 hT w,
      h4 χ (neg (G M)) hχ (C.neg _ C.god) w Pχ incl⟩

include C h2a h3 h4 in
/-- `G_ex_Two_unconditional` (through `ae_Two`): an actual God-like being at every world. -/
theorem gex [Nonempty D] (hT : Ax1GenTwo M) (w : W) : ExG M w := by
  by_cases h2 : ∃ ψ, M.AT ψ ∧ M.P ψ w ∧ ψ ≠ top
  · exact gex_at C h2a h3 h4 hT h2
  · have onlytop : ∀ ψ, M.AT ψ → M.P ψ w → ψ = top := fun ψ hA hP =>
      Classical.byContradiction fun hne => h2 ⟨ψ, hA, hP, hne⟩
    have x : D := Classical.ofNonempty
    let κ : D → W → Prop := fun _ => ExG M
    have hκ : M.AT κ := C.lift _ C.exG
    rcases (h2a κ hκ w).1 with hp | hn
    · have := congrFun (congrFun (onlytop κ hκ hp) x) w
      simpa [κ, top] using this
    · have e := onlytop _ (C.neg _ hκ) hn
      obtain ⟨v, _, hv⟩ := th4 C h2a h3 h4 hT w
      have := congrFun (congrFun e x) v
      exact absurd hv (by simpa [κ, neg, top] using this)

include C h2a h3 h4 in
/-- Modal collapse for admitted propositions, on every frame, with no nominal. -/
theorem mc [Nonempty D] (h2b : Ax2b M) (hT : Ax1GenTwo M) : MC M := by
  intro p hp w hpw v hv
  obtain ⟨g, _, hg⟩ := gex C h2a h3 h4 hT w
  obtain ⟨k, hk, hGk⟩ := gex C h2a h3 h4 hT v
  have hl : M.AT (fun _ => p) := C.lift _ hp
  -- `PosOfGod`: the constant property `λx. p` is positive at `w`
  have hP : M.P (fun _ => p) w := Classical.byContradiction fun hn =>
    have hneg : M.P (neg (fun _ => p)) w := ((h2a _ hl w).1).resolve_left hn
    hg _ (C.neg _ hl) hneg hpw
  exact hGk _ hl (h2b _ hl w hP v hv)

include C h2a h3 h4 in
/-- **`Ax1GenTwo` gives `Ax1Gen`**, over admitted carriers, without a nominal.  With fewer than
two members at `w`, every member of `Φ` is some `ψ₀` (`⊤` if `Φ` is empty there); collapse
carries the admitted proposition "every member of `Φ` is `ψ₀`" to the successors, so
`ψ₀ ⊃ᴺ φ`, and `Ax4` closes. -/
theorem ax1Gen_of_two [Nonempty D] (h2b : Ax2b M) (hT : Ax1GenTwo M) : Ax1Gen M := by
  intro Φ φ hΦ hφ w pos cj
  by_cases two : TwoMembers M Φ w
  · exact hT Φ φ hΦ hφ w two pos cj
  · have hmc := mc C h2a h3 h4 h2b hT
    -- the single candidate member `ψ₀`
    have key : ∀ ψ₀, M.AT ψ₀ → M.P ψ₀ w → (∀ ψ, M.AT ψ → Φ ψ w → ψ = ψ₀) → M.P φ w :=
      fun ψ₀ hA₀ hP₀ hsub =>
        h4 ψ₀ φ hA₀ hφ w hP₀ fun v hv y hy hy₀ => by
          have hsubv := hmc _ (C.atMost Φ ψ₀ hΦ hA₀) w hsub v hv
          exact (cj v hv y hy).2 fun ψ hA hm => (hsubv ψ hA hm) ▸ hy₀
    by_cases hex : ∃ ψ, M.AT ψ ∧ Φ ψ w
    · obtain ⟨ψ₀, hA₀, m₀⟩ := hex
      exact key ψ₀ hA₀ (pos ψ₀ hA₀ m₀) fun ψ hA hψ =>
        Classical.byContradiction fun hne => two ⟨ψ, ψ₀, hA, hA₀, hψ, m₀, hne⟩
    · exact key top C.top (pTop h3 w) fun ψ hA hψ => (hex ⟨ψ, hA, hψ⟩).elim

/-- The converse is immediate. -/
theorem two_of_ax1Gen (hG : Ax1Gen M) : Ax1GenTwo M :=
  fun Φ φ hΦ hφ w _ pos cj => hG Φ φ hΦ hφ w pos cj

include C h2a h3 h4 in
/-- The equivalence from positive `⊤`. -/
theorem equivalence_core [Nonempty D] (h2b : Ax2b M) : Ax1GenTwo M ↔ Ax1Gen M :=
  ⟨ax1Gen_of_two C h2a h3 h4 h2b, two_of_ax1Gen⟩

end

/-! ## Variant 2 and variant 3′ -/

/-- Essence of variant 3′ (`Ax1GenTwoVariant3Plain`): Gödel's essence, with the non-emptiness
clause `φ ≠ ⊥` inside the box, and no conjunct `φ x`. -/
def Ess3 (φ : D → W → Prop) (x : D) (w : W) : Prop :=
  ∀ ψ, M.AT ψ → ψ x w → ∀ v, M.R w v → φ ≠ bot ∧ ∀ y, M.act y v → φ y v → ψ y v

def E3 (x : D) (w : W) : Prop :=
  ∀ φ, M.AT φ → Ess3 M φ x w → ∀ v, M.R w v → ∃ y, M.act y v ∧ φ y v

def Ax3v3 : Prop := ∀ w, M.P (E3 M) w

variable {M}

theorem pTop_v2 (hE : M.AT (E M)) (C : Closed M) (h3 : Ax3 M) (h4 : Ax4 M) (w : W) :
    M.P top w :=
  h4 (E M) top hE C.top w (h3 w) (fun _ _ _ _ _ => trivial)

theorem pTop_v3 (hE : M.AT (E3 M)) (C : Closed M) (h3 : Ax3v3 M) (h4 : Ax4 M) (w : W) :
    M.P top w :=
  h4 (E3 M) top hE C.top w (h3 w) (fun _ _ _ _ _ => trivial)

/-- **Variant 2**: in every closed model (with `E` admitted) of `Ax2a`, `Ax2b`, `Ax3`, `Ax4`,
on any frame, for any actuality predicate and nonempty entity type, `Ax1GenTwo ↔ Ax1Gen`. -/
theorem equivalence [Nonempty D] (C : Closed M) (hE : M.AT (E M)) (h2a : Ax2a M)
    (h2b : Ax2b M) (h3 : Ax3 M) (h4 : Ax4 M) : Ax1GenTwo M ↔ Ax1Gen M :=
  equivalence_core C h2a (pTop_v2 hE C h3 h4) h4 h2b

/-- Variant 2: `Ax1GenTwo` gives modal collapse for admitted propositions, on any frame. -/
theorem mc_v2 [Nonempty D] (C : Closed M) (hE : M.AT (E M)) (h2a : Ax2a M)
    (h2b : Ax2b M) (h3 : Ax3 M) (h4 : Ax4 M) (hT : Ax1GenTwo M) : MC M :=
  mc C h2a (pTop_v2 hE C h3 h4) h4 h2b hT

/-- **Variant 3′** (Gödel's essence with the clause, plain `Ax4`): the same equivalence. -/
theorem equivalence_v3 [Nonempty D] (C : Closed M) (hE : M.AT (E3 M)) (h2a : Ax2a M)
    (h2b : Ax2b M) (h3 : Ax3v3 M) (h4 : Ax4 M) : Ax1GenTwo M ↔ Ax1Gen M :=
  equivalence_core C h2a (pTop_v3 hE C h3 h4) h4 h2b

theorem mc_v3 [Nonempty D] (C : Closed M) (hE : M.AT (E3 M)) (h2a : Ax2a M)
    (h2b : Ax2b M) (h3 : Ax3v3 M) (h4 : Ax4 M) (hT : Ax1GenTwo M) : MC M :=
  mc C h2a (pTop_v3 hE C h3 h4) h4 h2b hT


/-! ## The hypotheses are jointly satisfiable
A one-world, one-entity full model (every carrier element admitted), positivity being truth of
the property at the entity: `Closed`, `Ax2a`, `Ax2b`, `Ax3`, `Ax4` and `Ax1GenTwo` all hold. -/

def unitModel : Model Unit Unit where
  R := fun _ _ => True
  act := fun _ _ => True
  AS := fun _ => True
  AT := fun _ => True
  AH := fun _ => True
  P := fun φ w => φ () w

theorem unitModel_closed : Closed unitModel where
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

theorem unitModel_sat :
    Closed unitModel ∧ unitModel.AT (E unitModel) ∧ Ax2a unitModel ∧ Ax2b unitModel ∧ Ax3 unitModel ∧ Ax4 unitModel ∧
      Ax1GenTwo unitModel := by
  refine ⟨unitModel_closed, trivial, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ _ w
    show (φ () w ∨ ¬ φ () w) ∧ ¬ (φ () w ∧ ¬ φ () w)
    exact ⟨Classical.em _, fun h => h.2 h.1⟩
  · intro φ _ w h v _
    cases w; cases v; exact h
  · intro w φ _ hess v _
    exact ⟨(), trivial, hess.1⟩
  · intro φ ψ _ _ w hφ hinc
    exact hinc w trivial () trivial hφ
  · intro Φ φ _ _ w _ hpos hc
    exact (hc w trivial () trivial).2 fun ψ hA hm => hpos ψ hA hm

/-- The same model satisfies variant 3′'s `Ax3`. -/
theorem unitModel_v3 : unitModel.AT (E3 unitModel) ∧ Ax3v3 unitModel := by
  refine ⟨trivial, ?_⟩
  intro w φ _ hess v _
  have hne := (hess top trivial trivial v trivial).1
  refine ⟨(), trivial, Classical.byContradiction fun hn => hne ?_⟩
  funext x u
  cases x; cases u; cases v
  exact propext ⟨hn, False.elim⟩

end Programme.«20261022-0733-ontological».Run2.TwoClosed

#print axioms Programme.«20261022-0733-ontological».Run2.TwoClosed.equivalence
#print axioms Programme.«20261022-0733-ontological».Run2.TwoClosed.mc_v2
#print axioms Programme.«20261022-0733-ontological».Run2.TwoClosed.equivalence_v3
#print axioms Programme.«20261022-0733-ontological».Run2.TwoClosed.mc_v3
#print axioms Programme.«20261022-0733-ontological».Run2.TwoClosed.unitModel_sat
#print axioms Programme.«20261022-0733-ontological».Run2.TwoClosed.unitModel_v3
