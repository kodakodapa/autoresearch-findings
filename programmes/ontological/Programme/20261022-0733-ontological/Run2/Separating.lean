import Programme.«20261022-0733-ontological».Run2.FM
import Programme.«20261022-0733-ontological».Run2.Minimal

/-! # Standard models collapse, the FM model does not; and `L` is needed for `G_ex` (sk's majority model)

**1. Standard side** (th's E10, P103, `agents/th/lean/Programme/Th/StandardCollapse.lean`, restated
over `TwoClosed`'s definitions, imported, not copied).  If every property and every collection of
properties is admitted, `Ax1Gen`, `Ax2a` and `Ax3` (variant 2 or 3') force every world to see at
most itself, hence admitted MC and `Ax2b`.  The proof uses nominal witnesses: the property
`λz v. v = w`, the world-dependent collection `λψ v. (v = w ∧ ψ = ⊤) ∨ (v ≠ w ∧ ψ = ⊥)`, and the
essence `λy v. y = x ∧ v = w`.

**2. Separation.**  `FM.fm` (the carriers of v4 `ex:separating`, positivity = truth at `w`)
satisfies `Closed`, `Ax1Gen`, `Ax2a`, `Ax3`, `Ax3v3`, `Ax4`, `L`, but not MC or `Ax2b`.

**3. `L` is needed** (sk's majority model, P101).  One world, three entities, everything admitted,
`P φ` iff at least two entities have `φ`.  Ax2a, Ax2b, Ax3 (2 and 3'), Ax4 hold; nothing is
God-like, so `L` and `G_ex` fail.  Full, hence `LGeneral`. -/
namespace Programme.«20261022-0733-ontological».Run2.Separating

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.DropDagger Programme.«20261022-0733-ontological».Run2.LGeneral
  Programme.«20261022-0733-ontological».Run2.BoxIdle

section standard
variable {W D : Type} {M : Model W D}

/-- Full carriers at properties and collections of properties. -/
def FullTH (M : Model W D) : Prop := (∀ φ, M.AT φ) ∧ (∀ Φ, M.AH Φ)

theorem pTop_f (hF : FullTH M) (h1 : Ax1Gen M) (w : W) : M.P top w :=
  h1 (fun _ _ => False) top (hF.2 _) (hF.1 _) w (fun _ _ h => h.elim)
    (fun _ _ _ _ => ⟨fun _ _ _ h => h.elim, fun _ => trivial⟩)

theorem not_pBot_f (hF : FullTH M) (h1 : Ax1Gen M) (h2a : Ax2a M) (w : W) : ¬ M.P bot w := by
  intro hb
  have e : neg (top : D → W → Prop) = bot := by
    funext x v; exact propext ⟨fun h => h trivial, False.elim⟩
  exact (h2a top (hF.1 _) w).2 ⟨pTop_f hF h1 w, e ▸ hb⟩

/-- The nominal property of `w` is positive at `w`. -/
theorem pNom (hF : FullTH M) (h1 : Ax1Gen M) (w : W) : M.P (fun _ v => v = w) w := by
  refine h1 (fun ψ v => (v = w ∧ ψ = top) ∨ (v ≠ w ∧ ψ = bot)) _ (hF.2 _) (hF.1 _) w ?_ ?_
  · rintro ψ _ (⟨_, rfl⟩ | ⟨h, _⟩)
    · exact pTop_f hF h1 w
    · exact absurd rfl h
  · intro v _ z _
    constructor
    · rintro rfl ψ _ (⟨_, rfl⟩ | ⟨h, _⟩)
      · trivial
      · exact absurd rfl h
    · intro h
      by_cases hv : v = w
      · exact hv
      · exact (h bot (hF.1 _) (Or.inr ⟨hv, rfl⟩)).elim

/-- Positive properties are exemplified at the world (conjoin with the nominal). -/
theorem exemplified (hF : FullTH M) (h1 : Ax1Gen M) (h2a : Ax2a M) {φ : D → W → Prop} {w : W}
    (hφ : M.P φ w) : ∃ x, φ x w := by
  have hc : M.P (fun x v => φ x v ∧ v = w) w := by
    refine h1 (fun ψ _ => ψ = φ ∨ ψ = fun _ v => v = w) _ (hF.2 _) (hF.1 _) w ?_ ?_
    · rintro ψ _ (rfl | rfl)
      · exact hφ
      · exact pNom hF h1 w
    · intro v _ z _
      constructor
      · rintro ⟨h, h'⟩ ψ _ (rfl | rfl)
        · exact h
        · exact h'
      · intro h; exact ⟨h φ (hF.1 _) (Or.inl rfl), h _ (hF.1 _) (Or.inr rfl)⟩
  refine Classical.byContradiction fun hn => not_pBot_f hF h1 h2a w ?_
  have e : (fun x v => φ x v ∧ v = w) = (bot : D → W → Prop) := by
    funext x v
    exact propext ⟨fun ⟨h, hv⟩ => hn ⟨x, hv ▸ h⟩, False.elim⟩
  exact e ▸ hc

theorem refl_only (hF : FullTH M) (h1 : Ax1Gen M) (h2a : Ax2a M) (h3 : Ax3 M) :
    ∀ w v, M.R w v → v = w := by
  intro w v hwv
  obtain ⟨x, hx⟩ := exemplified hF h1 h2a (h3 w)
  have ess : Ess M (fun y u => y = x ∧ u = w) x w :=
    ⟨⟨rfl, rfl⟩, fun ψ _ hψ u _ y _ ⟨hy, hu⟩ => hy ▸ hu ▸ hψ⟩
  obtain ⟨_, _, _, hu⟩ := hx _ (hF.1 _) ess v hwv
  exact hu

theorem refl_only3 (hF : FullTH M) (h1 : Ax1Gen M) (h2a : Ax2a M) (h3 : Ax3v3 M) :
    ∀ w v, M.R w v → v = w := by
  intro w v hwv
  obtain ⟨x, hx⟩ := exemplified hF h1 h2a (h3 w)
  have ess : Ess3 M (fun y u => y = x ∧ u = w) x w := by
    intro ψ _ hψ u _
    refine ⟨fun e => ?_, fun y _ ⟨hy, hu⟩ => hy ▸ hu ▸ hψ⟩
    have : (fun y u => y = x ∧ u = w) x w := ⟨rfl, rfl⟩
    rw [e] at this; exact this
  obtain ⟨_, _, _, hu⟩ := hx _ (hF.1 _) ess v hwv
  exact hu

/-- **Standard side.** Full property and collection carriers, `Ax1Gen`, `Ax2a`, `Ax3` (variant 2
or 3'): every world sees at most itself; admitted MC and `Ax2b` hold. -/
theorem standard_collapse (hF : FullTH M) (h1 : Ax1Gen M) (h2a : Ax2a M)
    (h3 : Ax3 M ∨ Ax3v3 M) : (∀ w v, M.R w v → v = w) ∧ MC M ∧ Ax2b M := by
  have h := h3.elim (refl_only hF h1 h2a) (refl_only3 hF h1 h2a)
  exact ⟨h, fun _ _ _ hp _ hwv => (h _ _ hwv) ▸ hp, fun _ _ _ hp _ hwv => (h _ _ hwv) ▸ hp⟩

end standard

/-- **Separation** (E10).  MC and `Ax2b` follow from `Ax1Gen`, `Ax2a`, `Ax3` in every model with
full property and collection carriers, but fail in `FM.fm`, a model of the `Closed` interface on
the carriers of v4 `ex:separating` satisfying the same axioms and `Ax3v3`, `Ax4`, `L`. -/
theorem separating :
    (∀ (W D : Type) (M : Model W D), FullTH M → Ax1Gen M → Ax2a M → (Ax3 M ∨ Ax3v3 M) →
      MC M ∧ Ax2b M) ∧
    (Closed FM.fm ∧ Ax1Gen FM.fm ∧ Ax2a FM.fm ∧ Ax3 FM.fm ∧ Ax3v3 FM.fm ∧ Ax4 FM.fm ∧
      L FM.fm ∧ ¬ MC FM.fm ∧ ¬ Ax2b FM.fm) := by
  obtain ⟨hC, _, _, _, h2a, h3, h3', h4, _, _, hL, h1, _, _, _, _, _, _, hb, hm⟩ :=
    FM.rigidity_independent_fm
  exact ⟨fun _ _ _ hF h1 h2a h3 => (standard_collapse hF h1 h2a h3).2,
    hC, h1, h2a, h3, h3', h4, hL, hm, hb⟩

/-! ## sk's majority model: `L` is needed for `G_ex` -/

/-- One world, three entities, everything admitted, `P φ` iff two distinct entities have `φ`. -/
def maj : Model Unit (Fin 3) where
  R := fun _ _ => True
  act := fun _ _ => True
  AS := fun _ => True
  AT := fun _ => True
  AH := fun _ => True
  P := fun φ _ => ∃ a b, a ≠ b ∧ φ a () ∧ φ b ()

theorem maj_lgeneral : LGeneral maj := lgeneral_full (fun _ => trivial) (fun _ => trivial)
  (fun _ => trivial)

theorem pig : ∀ a b c d : Fin 3, a ≠ b → c ≠ d → a = c ∨ a = d ∨ b = c ∨ b = d := by decide

theorem two_of (p : Fin 3 → Prop) :
    (∃ a b, a ≠ b ∧ p a ∧ p b) ∨ (∃ a b, a ≠ b ∧ ¬ p a ∧ ¬ p b) := by
  by_cases h0 : p 0 <;> by_cases h1 : p 1 <;> by_cases h2 : p 2 <;>
    first
    | exact Or.inl ⟨0, 1, by decide, h0, h1⟩ | exact Or.inl ⟨0, 2, by decide, h0, h2⟩
    | exact Or.inl ⟨1, 2, by decide, h1, h2⟩ | exact Or.inr ⟨0, 1, by decide, h0, h1⟩
    | exact Or.inr ⟨0, 2, by decide, h0, h2⟩ | exact Or.inr ⟨1, 2, by decide, h1, h2⟩

theorem maj_ax2a : Ax2a maj := by
  intro φ _ w
  cases w
  refine ⟨two_of (fun a => φ a ()), ?_⟩
  rintro ⟨⟨a, b, hab, ha, hb⟩, ⟨c, d, hcd, hc, hd⟩⟩
  rcases pig a b c d hab hcd with rfl | rfl | rfl | rfl
  · exact hc ha
  · exact hd ha
  · exact hc hb
  · exact hd hb

theorem maj_ax2b : Ax2b maj := fun _ _ w hp v _ => by cases w; cases v; exact hp

theorem maj_ax4 : Ax4 maj := by
  rintro φ ψ _ _ w ⟨a, b, hab, ha, hb⟩ hinc
  cases w
  exact ⟨a, b, hab, hinc () trivial a trivial ha, hinc () trivial b trivial hb⟩

theorem maj_E (x : Fin 3) (w : Unit) : E maj x w := fun _ _ h v _ => by
  cases w; cases v; exact ⟨x, trivial, h.1⟩

theorem maj_E3 (x : Fin 3) (w : Unit) : E3 maj x w := fun φ _ h v hv => by
  have hne := (h top trivial trivial v hv).1
  refine Classical.byContradiction fun hn => hne ?_
  funext y u
  cases u; cases v
  exact propext ⟨fun hy => hn ⟨y, trivial, hy⟩, False.elim⟩

theorem maj_ax3 : Ax3 maj := fun _ => ⟨0, 1, by decide, maj_E 0 (), maj_E 1 ()⟩
theorem maj_ax3v3 : Ax3v3 maj := fun _ => ⟨0, 1, by decide, maj_E3 0 (), maj_E3 1 ()⟩

theorem others : ∀ x : Fin 3, ∃ a b : Fin 3, a ≠ b ∧ a ≠ x ∧ b ≠ x := by decide

theorem maj_no_god (x : Fin 3) (w : Unit) : ¬ G maj x w := fun h => by
  obtain ⟨a, b, hab, ha, hb⟩ := others x
  exact h (fun y _ => y ≠ x) trivial ⟨a, b, hab, ha, hb⟩ rfl

theorem maj_not_L : ¬ L maj := fun h => by
  obtain ⟨a, _, _, ha, _⟩ := h ()
  exact maj_no_god a () ha

theorem maj_not_gex : ¬ ExG maj () := fun ⟨y, _, hy⟩ => maj_no_god y () hy

/-- **`L` is needed.** The majority model is `LGeneral`, satisfies `Ax2a`, `Ax2b`, `Ax3` (both
variants), `Ax4`, `Ax4c`, but no entity is God-like: `L` and `∃ᴱ G` fail. -/
theorem majority :
    LGeneral maj ∧ Ax2a maj ∧ Ax2b maj ∧ Ax3 maj ∧ Ax3v3 maj ∧ Ax4 maj ∧ Ax4c maj ∧
      (∀ w v, maj.R w v) ∧ ¬ L maj ∧ ¬ ExG maj () :=
  ⟨maj_lgeneral, maj_ax2a, maj_ax2b, maj_ax3, maj_ax3v3, maj_ax4, Minimal.ax4c_of_ax4 maj_ax4,
    fun _ _ => trivial, maj_not_L, maj_not_gex⟩

/-- Hence `L` cannot be dropped from K6's `gex_L` (with K11: no single hypothesis among Ax2a,
Ax3, Ax4, `L` can be dropped in `𝓛`-general-fragment models). -/
theorem l_needed :
    ¬ (∀ M : Model Unit (Fin 3), LGeneral M → Ax2a M → Ax2b M → Ax3 M → Ax3v3 M → Ax4 M →
      ∀ w, ExG M w) :=
  fun h => maj_not_gex (h maj maj_lgeneral maj_ax2a maj_ax2b maj_ax3 maj_ax3v3 maj_ax4 ())

end Programme.«20261022-0733-ontological».Run2.Separating

#print axioms Programme.«20261022-0733-ontological».Run2.Separating.separating
#print axioms Programme.«20261022-0733-ontological».Run2.Separating.majority
#print axioms Programme.«20261022-0733-ontological».Run2.Separating.l_needed
