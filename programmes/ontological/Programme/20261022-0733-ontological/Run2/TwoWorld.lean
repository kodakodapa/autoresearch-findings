import Programme.«20261022-0733-ontological».Run2.DropDagger

/-! # A two-world closed model for K1 and the (†)-free variant-3 result

Worlds `Bool`, one entity, universal accessibility and actuality.  Admitted are exactly the
world-constant propositions, properties and collections; positivity is truth of a world-constant
property at the entity.  The model is `Closed`, satisfies variant 2's and variant 3's axioms, `Th4`
and `Ax1GenTwo`, and has two distinct, mutually accessible worlds; the non-admitted
proposition `fun w => w = true` is true at `true` and false at its successor `false`.  So the
hypotheses do not force one world, and modal collapse fails for non-admitted propositions. -/

namespace Programme.«20261022-0733-ontological».Run2.TwoWorld

open Programme.«20261022-0733-ontological».Run2.TwoClosed Programme.«20261022-0733-ontological».Run2.DropDagger

def Rig {α : Type} (f : Bool → α) : Prop := f true = f false

theorem rig_iff {α : Type} {f : Bool → α} : Rig f ↔ ∀ u v, f u = f v := by
  constructor
  · intro h u v; cases u <;> cases v <;> simp_all [Rig]
  · intro h; exact h true false

def twoModel : Model Bool Unit where
  R := fun _ _ => True
  act := fun _ _ => True
  AS := fun p => Rig p
  AT := fun φ => Rig (φ ())
  AH := fun Φ => ∀ ψ, Rig (Φ ψ)
  P := fun φ w => Rig (φ ()) ∧ φ () w

theorem G_all (x : Unit) (w : Bool) : G twoModel x w := fun φ _ h => by cases x; exact h.2

theorem exG_all (w : Bool) : ExG twoModel w := ⟨(), trivial, G_all () w⟩

theorem closed : Closed twoModel where
  top := rfl
  bot := rfl
  neg := fun φ h => by
    show (fun w => ¬ φ () w) true = (fun w => ¬ φ () w) false
    simp only; rw [show φ () true = φ () false from h]
  conj := fun φ ψ h1 h2 => by
    show (φ () true ∧ ψ () true) = (φ () false ∧ ψ () false)
    rw [show φ () true = φ () false from h1, show ψ () true = ψ () false from h2]
  lift := fun p h => h
  negS := fun p h => by
    show (¬ p true) = (¬ p false)
    rw [show p true = p false from h]
  god := by
    show G twoModel () true = G twoModel () false
    exact propext ⟨fun _ => G_all () false, fun _ => G_all () true⟩
  exG := propext ⟨fun _ => exG_all false, fun _ => exG_all true⟩
  pos := fun ψ => by
    show (Rig (ψ ()) ∧ ψ () true) = (Rig (ψ ()) ∧ ψ () false)
    exact propext ⟨fun h => ⟨h.1, h.1 ▸ h.2⟩, fun h => ⟨h.1, h.1.symm ▸ h.2⟩⟩
  single := fun ψ _ ψ' => rfl
  union := fun Φ Ψ h1 h2 ψ => by
    show (Φ ψ true ∨ Ψ ψ true) = (Φ ψ false ∨ Ψ ψ false)
    rw [show Φ ψ true = Φ ψ false from h1 ψ, show Ψ ψ true = Ψ ψ false from h2 ψ]
  guard := fun p Φ hp hΦ ψ => by
    show (p true ∧ Φ ψ true) = (p false ∧ Φ ψ false)
    rw [show p true = p false from hp, show Φ ψ true = Φ ψ false from hΦ ψ]
  atMost := fun Φ ψ₀ hΦ _ => by
    show (∀ ψ, twoModel.AT ψ → Φ ψ true → ψ = ψ₀) = (∀ ψ, twoModel.AT ψ → Φ ψ false → ψ = ψ₀)
    exact propext ⟨fun h ψ hA hm => h ψ hA ((hΦ ψ) ▸ hm), fun h ψ hA hm => h ψ hA ((hΦ ψ).symm ▸ hm)⟩

theorem rigid_at {φ : Unit → Bool → Prop} (h : twoModel.AT φ) (u v : Bool) (hu : φ () u) :
    φ () v :=
  (rig_iff.mp h u v) ▸ hu

theorem E_all (x : Unit) (w : Bool) : E twoModel x w := fun φ hA hess v _ =>
  ⟨(), trivial, by cases x; exact rigid_at hA w v hess.1⟩

theorem E3_all (x : Unit) (w : Bool) : E3 twoModel x w := fun φ hA hess v _ => by
  have hne := (hess top rfl trivial w trivial).1
  refine ⟨(), trivial, ?_⟩
  have : ∃ u, φ () u := Classical.byContradiction fun hn => hne (by
    funext y u; cases y; exact propext ⟨fun h => hn ⟨u, h⟩, False.elim⟩)
  obtain ⟨u, hu⟩ := this
  exact rigid_at hA u v hu

/-- All hypotheses of K1 (variants 2 and 3′) and of the (†)-free variant-3 result hold. -/
theorem sat :
    Closed twoModel ∧ twoModel.AT (E twoModel) ∧ twoModel.AT (E3 twoModel) ∧
      Ax2a twoModel ∧ Ax2b twoModel ∧ Ax3 twoModel ∧ Ax3v3 twoModel ∧ Ax4 twoModel ∧
      Ax4c twoModel ∧ Th4 twoModel ∧ Ax1GenTwo twoModel := by
  have hE : twoModel.AT (E twoModel) :=
    propext ⟨fun _ => E_all () false, fun _ => E_all () true⟩
  have hE3 : twoModel.AT (E3 twoModel) :=
    propext ⟨fun _ => E3_all () false, fun _ => E3_all () true⟩
  refine ⟨closed, hE, hE3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ hA w
    have hn : twoModel.AT (neg φ) := closed.neg φ hA
    refine ⟨?_, fun ⟨h1, h2⟩ => h2.2 h1.2⟩
    by_cases h : φ () w
    · exact Or.inl ⟨hA, h⟩
    · exact Or.inr ⟨hn, h⟩
  · intro φ hA w h v _
    exact ⟨h.1, rigid_at hA w v h.2⟩
  · intro w; exact ⟨hE, E_all () w⟩
  · intro w; exact ⟨hE3, E3_all () w⟩
  · intro φ ψ _ hψ w hφ hinc
    exact ⟨hψ, hinc w trivial () trivial hφ.2⟩
  · intro φ ψ _ hψ w hφ hinc
    exact ⟨hψ, (hinc w trivial).2 () trivial hφ.2⟩
  · intro w; exact ⟨w, trivial, exG_all w⟩
  · intro Φ φ _ hφ w _ hpos hc
    exact ⟨hφ, (hc w trivial () trivial).2 fun ψ hA hm => (hpos ψ hA hm).2⟩

/-- The frame has two distinct worlds, `true` sees `false`, and the non-admitted proposition
`w = true` is not carried along accessibility. -/
theorem nontrivial :
    (true ≠ false) ∧ twoModel.R true false ∧ ¬ twoModel.AS (fun w => w = true) ∧
      ¬ (∀ p : Bool → Prop, ∀ w, p w → ∀ v, twoModel.R w v → p v) := by
  refine ⟨Bool.noConfusion, trivial, fun h => ?_, fun h => ?_⟩
  · have : (true = true) = (false = true) := h
    exact absurd (this ▸ rfl : false = true) Bool.noConfusion
  · exact absurd (h (fun w => w = true) true rfl false trivial) Bool.noConfusion

end Programme.«20261022-0733-ontological».Run2.TwoWorld

#print axioms Programme.«20261022-0733-ontological».Run2.TwoWorld.sat
#print axioms Programme.«20261022-0733-ontological».Run2.TwoWorld.nontrivial
