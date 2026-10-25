import Notes.HOMLinHOL

/- Proofs by th, P422; rebased by pr. All model data remain parameters. -/
/-! Ax1GenTwo gives back Ax1Gen without a nominal (owner P409, item 3; arXiv 2609.36279v4,
"What stays open").

The paper proves `Ax1GenTwo → Ax1Gen` in variants 2 and 3' only through `OneWorld`/`R_Id`
(nominals) and leaves the object-language question open; its possibilist and Anderson copies
leave it as `openproblem`. Here the step is factored through modal collapse *applied to
object-language propositions only*:
* `uniq := ∀ψ. Φ ψ → ψ = ψ₀` (Φ has at most the member ψ₀), and
* `none := ∀ψ. ¬ Φ ψ` (Φ is empty).
MC carries these from `w` to every successor, so the conjunction of `Φ` at a successor is ψ₀
(resp. ⊤), and positivity follows from `Ax4` (resp. from `P ⊤`). For mixed (Anderson) guards,
where `Ax4`'s inclusion is possibilist but the conjunction clause actualist, an actual
God-like being at a successor refutes `P ~φ` instead.

MC itself is hybrid-free in the paper (`MC_Two_unconditional`, `MC_Two` in the possibilist and
Anderson copies). The lemmas below take it as a hypothesis, so they hold in every model,
any frame, any guards; all postulates are discharged into hypotheses. -/

namespace Programme.«20261021-1639-ontological».Atlas.TwoGen

variable {W E : Type} (R : W → W → Prop)

/-- Conjunction clause with guard `A`: `□ ∀^A z. φ z ↔ ∀ψ. Φ ψ → ψ z`. -/
def Conj (A : E → W → Prop) (φ : E → W → Prop) (Φ : (E → W → Prop) → W → Prop) (w : W) : Prop :=
  ∀ v, R w v → ∀ z, A z v → (φ z v ↔ ∀ ψ, Φ ψ v → ψ z v)

def TwoMembers (Φ : (E → W → Prop) → W → Prop) (w : W) : Prop :=
  ∃ ψ₁ ψ₂, Φ ψ₁ w ∧ Φ ψ₂ w ∧ ψ₁ ≠ ψ₂

def PosProps (P : (E → W → Prop) → W → Prop) (Φ : (E → W → Prop) → W → Prop) (w : W) : Prop :=
  ∀ ψ, Φ ψ w → P ψ w

/-- Modal collapse for all propositions. -/
def MC : Prop := ∀ (p : W → Prop) w, p w → ∀ v, R w v → p v

/-- `Ax4` with inclusion guard `B`. -/
def Ax4 (B : E → W → Prop) (P : (E → W → Prop) → W → Prop) : Prop :=
  ∀ φ ψ w, P φ w → (∀ v, R w v → ∀ y, B y v → φ y v → ψ y v) → P ψ w

def Ax1GenTwo (A : E → W → Prop) (P : (E → W → Prop) → W → Prop) : Prop :=
  ∀ Φ φ w, TwoMembers Φ w → PosProps P Φ w → Conj R A φ Φ w → P φ w

def Ax1Gen (A : E → W → Prop) (P : (E → W → Prop) → W → Prop) : Prop :=
  ∀ Φ φ w, PosProps P Φ w → Conj R A φ Φ w → P φ w

/-- Uniform guards (actualist `A = B = existsAt`, possibilist `A = B = ⊤`), or any inclusion
guard contained in the conjunction guard: MC, `Ax4`, `P ⊤` and `Ax1GenTwo` give `Ax1Gen`. -/
theorem ax1Gen_of_two (A B : E → W → Prop) (hBA : ∀ y v, B y v → A y v)
    (P : (E → W → Prop) → W → Prop) (mc : MC R) (ax4 : Ax4 R B P)
    (ptop : ∀ w, P (fun _ _ => True) w) (two : Ax1GenTwo R A P) : Ax1Gen R A P := by
  intro Φ φ w pos conj
  by_cases h2 : TwoMembers Φ w
  · exact two Φ φ w h2 pos conj
  by_cases hex : ∃ ψ, Φ ψ w
  · obtain ⟨ψ₀, m0⟩ := hex
    -- object-language witness: ∀ψ. Φ ψ → ψ = ψ₀
    have uniq : ∀ ψ, Φ ψ w → ψ = ψ₀ := fun ψ hψ =>
      Classical.byContradiction fun hne => h2 ⟨ψ, ψ₀, hψ, m0, hne⟩
    have buniq := mc (fun u => ∀ ψ, Φ ψ u → ψ = ψ₀) w uniq
    refine ax4 ψ₀ φ w (pos ψ₀ m0) fun v rv y hb h => ?_
    exact (conj v rv y (hBA y v hb)).2 fun ψ hψ => (buniq v rv ψ hψ) ▸ h
  · -- object-language witness: ∀ψ. ¬ Φ ψ
    have bnone := mc (fun u => ∀ ψ, ¬ Φ ψ u) w (fun ψ hψ => hex ⟨ψ, hψ⟩)
    refine ax4 _ φ w (ptop w) fun v rv y hb _ => ?_
    exact (conj v rv y (hBA y v hb)).2 fun ψ hψ => absurd hψ (bnone v rv ψ)

/-- Same with `Ax1GenOne` (non-empty `Φ`): only the empty case is left, discharged by MC on
`∀ψ. ¬ Φ ψ` and `P ⊤` (closes the `openproblem` `Ax1GenOne → Ax1Gen` of
`Ax1GenOneVariant2.lean`, whose `MC_One` is hybrid-free). -/
theorem ax1Gen_of_one (A B : E → W → Prop) (hBA : ∀ y v, B y v → A y v)
    (P : (E → W → Prop) → W → Prop) (mc : MC R) (ax4 : Ax4 R B P)
    (ptop : ∀ w, P (fun _ _ => True) w)
    (one : ∀ Φ φ w, (∃ ψ, Φ ψ w) → PosProps P Φ w → Conj R A φ Φ w → P φ w) :
    Ax1Gen R A P := by
  intro Φ φ w pos conj
  by_cases hex : ∃ ψ, Φ ψ w
  · exact one Φ φ w hex pos conj
  · have bnone := mc (fun u => ∀ ψ, ¬ Φ ψ u) w (fun ψ hψ => hex ⟨ψ, hψ⟩)
    refine ax4 _ φ w (ptop w) fun v rv y hb _ => ?_
    exact (conj v rv y (hBA y v hb)).2 fun ψ hψ => absurd hψ (bnone v rv ψ)

/-- Mixed (Anderson) guards: conjunction clause with guard `A` (actual), no condition on the
inclusion guard. Uses `Ax2a` (one of `φ`, `~φ` positive), `Ax2b` (rigidity), seriality and an
`A`-guarded God-like being at every world, all theorems of the paper's Anderson copies. -/
theorem ax1Gen_of_two_mixed (A : E → W → Prop) (P : (E → W → Prop) → W → Prop) (mc : MC R)
    (ax2a : ∀ φ w, P φ w ∨ P (fun x u => ¬ φ x u) w)
    (ax2b : ∀ φ w, P φ w → ∀ v, R w v → P φ v)
    (serial : ∀ w, ∃ v, R w v)
    (god : ∀ w, ∃ g, A g w ∧ ∀ φ, P φ w → φ g w)
    (two : Ax1GenTwo R A P) : Ax1Gen R A P := by
  intro Φ φ w pos conj
  by_cases h2 : TwoMembers Φ w
  · exact two Φ φ w h2 pos conj
  rcases ax2a φ w with hp | hneg
  · exact hp
  exfalso
  obtain ⟨v, rv⟩ := serial w
  obtain ⟨g, ag, hG⟩ := god v
  have nφ : ¬ φ g v := hG _ (ax2b _ w hneg v rv)
  apply nφ
  refine (conj v rv g ag).2 ?_
  by_cases hex : ∃ ψ, Φ ψ w
  · obtain ⟨ψ₀, m0⟩ := hex
    have uniq : ∀ ψ, Φ ψ w → ψ = ψ₀ := fun ψ hψ =>
      Classical.byContradiction fun hne => h2 ⟨ψ, ψ₀, hψ, m0, hne⟩
    have buniq := mc (fun u => ∀ ψ, Φ ψ u → ψ = ψ₀) w uniq
    intro ψ hψ
    rw [buniq v rv ψ hψ]
    exact hG ψ₀ (ax2b ψ₀ w (pos ψ₀ m0) v rv)
  · have bnone := mc (fun u => ∀ ψ, ¬ Φ ψ u) w (fun ψ hψ => hex ⟨ψ, hψ⟩)
    intro ψ hψ
    exact absurd hψ (bnone v rv ψ)

/-- Converse (trivial): `Ax1Gen → Ax1GenTwo`. -/
theorem two_of_ax1Gen (A : E → W → Prop) (P : (E → W → Prop) → W → Prop)
    (h : Ax1Gen R A P) : Ax1GenTwo R A P :=
  fun Φ φ w _ pos conj => h Φ φ w pos conj

#print axioms ax1Gen_of_two
#print axioms ax1Gen_of_one
#print axioms ax1Gen_of_two_mixed

end Programme.«20261021-1639-ontological».Atlas.TwoGen
