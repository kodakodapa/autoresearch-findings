import Programme.«20261021-1639-ontological».Deep.CantorQuantifiers
import Programme.«20261021-1639-ontological».Deep.Syntax

namespace Programme.«20261021-1639-ontological».Deep.CantorSupport

/-- Commuting involutions suffice for the binary-mask construction. -/
structure CommutingAction (A : Type) extends MaskAction A where
  commute : ∀ s t x, act s (act t x) = act t (act s x)

def FixesPrefix (n : Nat) (s : World) : Prop := ∀ k, k < n → s k = false

def Supported (a : MaskAction A) (n : Nat) (x : A) : Prop :=
  ∀ s, FixesPrefix n s → a.act s x = x

def conjugate (a : MaskAction A) (b : MaskAction B) (s : World) (f : A → B) : A → B :=
  fun x => b.act s (f (a.act s x))

def arrowAction (a : CommutingAction A) (b : CommutingAction B) :
    CommutingAction (A → B) where
  act := conjugate a.toMaskAction b.toMaskAction
  involutive := by
    intro s f
    funext x
    simp only [conjugate, a.involutive, b.involutive]
  commute := by
    intro s t f
    funext x
    simp only [conjugate]
    rw [a.commute t s x, b.commute s t]

theorem support_mono (a : MaskAction A) {n m : Nat} (hnm : n ≤ m)
    {x : A} (hx : Supported a n x) : Supported a m x := by
  intro s hs
  exact hx s (fun k hk => hs k (Nat.lt_of_lt_of_le hk hnm))

theorem support_action (a : CommutingAction A) {n : Nat} {x : A}
    (hx : Supported a.toMaskAction n x) (t : World) :
    Supported a.toMaskAction n (a.act t x) := by
  intro s hs
  rw [a.commute, hx s hs]

/-- Restricted arrows: only functions with a finite symmetry support. -/
def SupportedArrow (a : CommutingAction A) (b : CommutingAction B) :=
  {f : A → B // ∃ n, Supported (arrowAction a b).toMaskAction n f}

def supportedArrowAction (a : CommutingAction A) (b : CommutingAction B) :
    CommutingAction (SupportedArrow a b) where
  act := fun s f => ⟨(arrowAction a b).act s f.val, by
    obtain ⟨n, hn⟩ := f.property
    exact ⟨n, support_action (arrowAction a b) hn s⟩⟩
  involutive := by
    intro s f
    apply Subtype.ext
    exact (arrowAction a b).involutive s f.val
  commute := by
    intro s t f
    apply Subtype.ext
    exact (arrowAction a b).commute s t f.val

/-- Application is equivariant, even before restricting to supported elements. -/
theorem application_equivariant (a : CommutingAction A) (b : CommutingAction B)
    (s : World) (f : A → B) (x : A) :
    (arrowAction a b).act s f (a.act s x) = b.act s (f x) := by
  simp only [arrowAction, conjugate, a.involutive]

theorem application_supported (a : CommutingAction A) (b : CommutingAction B)
    {n m : Nat} {f : A → B} {x : A}
    (hf : Supported (arrowAction a b).toMaskAction n f)
    (hx : Supported a.toMaskAction m x) :
    Supported b.toMaskAction (max n m) (f x) := by
  intro s hs
  have hf' := support_mono _ (Nat.le_max_left n m) hf s hs
  have hx' := support_mono _ (Nat.le_max_right n m) hx s hs
  have h := application_equivariant a b s f x
  rw [hf', hx'] at h
  exact h.symm

/-- A jointly equivariant family is an admitted lambda at the same support. -/
theorem abstraction_supported (a : CommutingAction A) (b : CommutingAction B)
    (n : Nat) (f : A → B)
    (hf : ∀ s, FixesPrefix n s → ∀ x, f (a.act s x) = b.act s (f x)) :
    Supported (arrowAction a b).toMaskAction n f := by
  intro s hs
  funext x
  change b.act s (f (a.act s x)) = f x
  rw [hf s hs x, b.involutive]

/-- Binary worlds supply commuting mask actions. -/
def worldAction : CommutingAction World where
  act := flipBy
  involutive := flipBy_involutive
  commute := by
    intro s t v
    funext k
    simp only [flipBy]
    cases v k <;> cases s k <;> cases t k <;> rfl

/-- Proposition action is precomposition with the inverse world action. -/
def propositionAction : CommutingAction (World → Prop) where
  act := fun s p => fun v => p (flipBy s v)
  involutive := by
    intro s p
    funext v
    change p (flipBy s (flipBy s v)) = p v
    rw [flipBy_involutive]
  commute := by
    intro s t p
    funext v
    exact congrArg p (worldAction.commute t s v)

theorem proposition_supported_iff (n : Nat) (p : World → Prop) :
    Supported propositionAction.toMaskAction n p ↔ Based n p := by
  rw [based_iff_all_tail_flips]
  constructor
  · intro h s hs v
    exact Iff.of_eq (congrFun (h s hs) v)
  · intro h s hs
    funext v
    exact propext (h s hs v)

/-- A carrier together with its action and elementwise finite support. -/
structure SupportedCarrier where
  D : Type
  action : CommutingAction D
  supported : ∀ x, ∃ n, Supported action.toMaskAction n x
  inhabited : Nonempty D

def entityCarrier : SupportedCarrier where
  D := Unit
  action := {
    act := fun _ x => x
    involutive := fun _ _ => rfl
    commute := fun _ _ _ => rfl }
  supported := fun _ => ⟨0, fun _ _ => rfl⟩
  inhabited := ⟨()⟩

def propCarrier : SupportedCarrier where
  D := {p : World → Prop // ∃ n, Supported propositionAction.toMaskAction n p}
  action := {
    act := fun s p => ⟨propositionAction.act s p.val, by
      obtain ⟨n, hn⟩ := p.property
      exact ⟨n, support_action propositionAction hn s⟩⟩
    involutive := fun s p => Subtype.ext (propositionAction.involutive s p.val)
    commute := fun s t p => Subtype.ext (propositionAction.commute s t p.val) }
  supported := by
    intro p
    obtain ⟨n, hn⟩ := p.property
    exact ⟨n, fun s hs => Subtype.ext (hn s hs)⟩
  inhabited := ⟨⟨fun _ => False, 0, fun _ _ => rfl⟩⟩

def arrowCarrier (a b : SupportedCarrier) : SupportedCarrier where
  D := SupportedArrow a.action b.action
  action := supportedArrowAction a.action b.action
  supported := by
    intro f
    obtain ⟨n, hn⟩ := f.property
    exact ⟨n, fun s hs => Subtype.ext (hn s hs)⟩
  inhabited := by
    obtain ⟨y⟩ := b.inhabited
    obtain ⟨n, hn⟩ := b.supported y
    exact ⟨⟨fun _ => y, n, by
      intro s hs
      funext x
      exact hn s hs⟩⟩

/-- Hereditarily supported simple-type carriers. No closure claim is hidden
in this definition: term closure still requires a simultaneous symmetry proof. -/
def typedCarrier : Programme.«20261021-1639-ontological».Deep.Ty → SupportedCarrier
  | .entity => entityCarrier
  | .prop => propCarrier
  | .arr a b => arrowCarrier (typedCarrier a) (typedCarrier b)

theorem typed_finite_support (a : Programme.«20261021-1639-ontological».Deep.Ty) (x : (typedCarrier a).D) :
    ∃ n, Supported (typedCarrier a).action.toMaskAction n x :=
  (typedCarrier a).supported x

theorem typed_prop_based (p : (typedCarrier .prop).D) : ∃ n, Based n p.val := by
  obtain ⟨n, hn⟩ := p.property
  exact ⟨n, (proposition_supported_iff n p.val).mp hn⟩

#print axioms typed_finite_support
#print axioms typed_prop_based
#print axioms supportedArrowAction
#print axioms application_equivariant
#print axioms application_supported
#print axioms abstraction_supported
#print axioms proposition_supported_iff
end Programme.«20261021-1639-ontological».Deep.CantorSupport
