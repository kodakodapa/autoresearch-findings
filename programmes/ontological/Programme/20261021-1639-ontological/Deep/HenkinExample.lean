import Programme.«20261021-1639-ontological».Deep.Henkin

namespace Programme.«20261021-1639-ontological».Deep.Henkin

/-- Two accessible worlds, but only constant proposition intensions. -/
def constantFrame : Frame Bool where
  D := Carrier Unit Unit
  nonempty := carrierNonempty Unit
  app := fun f x => f x
  ext := fun _ _ h => funext h
  truth := fun p _ => p ()
  truth_inj := by
    intro p q h
    funext u
    cases u
    exact congrFun h false
  abstract := id
  abstract_spec := fun _ _ _ => rfl
  reify := fun p _ => p false
  reify_spec := by
    intro p hp
    obtain ⟨q, hq⟩ := hp
    funext w
    exact (congrFun hq false).symm.trans (congrFun hq w)
  rel := fun _ _ => True

def unitModel (I : ∀ {a}, C a → Carrier Unit Unit a) : Programme.«20261021-1639-ontological».Deep.Model C Unit Unit where
  rel := fun _ _ => True
  interp := I

theorem constant_denotes (I : ∀ {a}, C a → Carrier Unit Unit a)
    (t : Term C Γ a) (ρ : Env Unit Unit Γ) :
    Denotes constantFrame I ρ t (eval (unitModel I) ρ t) := by
  induction t with
  | var v => exact .var
  | const c => exact .const
  | app f x hf hx => exact .app (hf ρ) (hx ρ)
  | lam t ih => exact .lam (fun x => ih (extend ρ x))
  | falsum => exact .falsum rfl
  | imp p q hp hq => exact .imp (hp ρ) (hq ρ) rfl
  | box p hp =>
    apply Denotes.box (hp ρ)
    funext w
    apply propext
    constructor
    · intro h v _
      exact h () True.intro
    · intro h v _
      cases v
      exact h false True.intro
  | all p hp => exact .all (fun x => hp (extend ρ x)) rfl
  | equal s t hs ht => exact .equal (hs ρ) (ht ρ) rfl

def constantModel (I : ∀ {a}, C a → Carrier Unit Unit a) : Model C Bool where
  frame := constantFrame
  interp := I
  closed := fun ρ t => ⟨eval (unitModel I) ρ t, constant_denotes I t ρ⟩

/-- This proposition cannot be represented, despite definable-term closure. -/
theorem no_world_name : ¬ ∃ p : constantFrame.D .prop,
    constantFrame.truth p = (fun w => w = true) := by
  rintro ⟨p, hp⟩
  have ht : p () := (congrFun hp true).mpr rfl
  have hf : false = true := (congrFun hp false).mp ht
  cases hf

/-- Quantifying only over admitted propositions does not detect the proper edge. -/
theorem admitted_collapse : ∀ p : constantFrame.D .prop, ∀ w,
    constantFrame.truth p w → ∀ v, constantFrame.rel w v → constantFrame.truth p v := by
  intro p w hp v _
  exact hp

theorem proper_edge : constantFrame.rel false true ∧ false ≠ true := by
  exact ⟨True.intro, Bool.noConfusion⟩

#print axioms constant_denotes
#print axioms no_world_name
#print axioms admitted_collapse
#print axioms proper_edge
end Programme.«20261021-1639-ontological».Deep.Henkin
