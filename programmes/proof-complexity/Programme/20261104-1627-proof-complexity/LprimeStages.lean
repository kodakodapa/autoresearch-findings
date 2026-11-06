import Programme.«20261104-1627-proof-complexity».OmissionEnumeration

/-! Stages 1–2 interface work only. No field duality or Lprime theorem. -/
namespace Programme.«20261104-1627-proof-complexity».LprimeStages
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC

abbrev Ix (m n d : Nat) := {M : Matching // M ∈ matchings m n d}
abbrev Jx (m n d : Nat) := {g : Label // g ∈ labels m n d}
abbrev ValidVector (m n d : Nat) := {v : Vector // valid m n d v}

def lift (m n d h : Nat) (M : Ix m n d) : Ix m (n+1) d :=
  ⟨pushMatching h M.val, matching_push_mem h M.val M.property⟩

def liftLabel (m n d h : Nat) (g : Jx m n d) : Jx m (n+1) d :=
  ⟨pushLabel h g.val, label_push_mem h g.val g.property⟩

theorem lift_injective (m n d h : Nat) : Function.Injective (lift m n d h) := by
  intro M N he
  apply Subtype.ext
  exact pushMatching_injective h (congrArg Subtype.val he)

theorem lift_avoids (m n d h : Nat) (M : Ix m n d) :
    ∀ e ∈ (lift m n d h M).val, e.2 ≠ h := by
  intro e he
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp he
  exact omitHole_ne h a.2

/-- Entry in the finite top matrix, still an integer rather than a field element. -/
def entry (m n d : Nat) (M : Ix m n d) (g : Jx m n d) : Int :=
  coeff (topLabel m n g.val) (mono n M.val)

/-- Integer top coordinates of a valid raw vector. This avoids assuming an
unproved aggregation theorem from raw lists to field label functions. -/
def topCoordinates (m n d : Nat) (a : ValidVector m n d) : Ix m n d → Int :=
  fun M => coeff (top m n a.val) (mono n M.val)

def IntegerImage (p m n d : Nat) (v : Ix m n d → Int) : Prop :=
  ∃ a : ValidVector m n d, ∀ M, (p : Int) ∣ v M - topCoordinates m n d a M

theorem topImage_iff_integerImage (p m n d : Nat) (v : Matching → Int) :
    TopImage p m n d v ↔ IntegerImage p m n d (fun M => v M.val) := by
  constructor
  · rintro ⟨a, ha, hv⟩
    exact ⟨⟨a, ha⟩, fun M => hv M.val M.property⟩
  · rintro ⟨a, hv⟩
    exact ⟨a.val, a.property, fun M hM => hv ⟨M, hM⟩⟩

end Programme.«20261104-1627-proof-complexity».LprimeStages
#print axioms Programme.«20261104-1627-proof-complexity».LprimeStages.lift_injective
#print axioms Programme.«20261104-1627-proof-complexity».LprimeStages.lift_avoids
#print axioms Programme.«20261104-1627-proof-complexity».LprimeStages.topImage_iff_integerImage
