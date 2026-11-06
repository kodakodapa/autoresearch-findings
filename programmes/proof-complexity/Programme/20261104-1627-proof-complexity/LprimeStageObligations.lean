import Programme.«20261104-1627-proof-complexity».LprimeStages
import Programme.«20261104-1627-proof-complexity».OmissionPairing

/-! Typed stages 1–2. Definitions ending in Obligation are propositions,
not proofs or assumed axioms. No field or duality theorem is asserted. -/
namespace Programme.«20261104-1627-proof-complexity».LprimeStages
open Programme.«20261104-1627-proof-complexity».MatchingLabels

abbrev AvoidingIx (m n d h : Nat) :=
  {M : Ix m (n+1) d // ∀ e ∈ M.val, e.2 ≠ h}

def avoidingLift (m n d h : Nat) (M : Ix m n d) : AvoidingIx m n d h :=
  ⟨lift m n d h M, lift_avoids m n d h M⟩

theorem avoidingLift_bijective (m n d h : Nat) (hh : h ≤ n) :
    Function.Injective (avoidingLift m n d h) ∧
      (∀ M : AvoidingIx m n d h, ∃ N, avoidingLift m n d h N = M) := by
  constructor
  · intro M N he
    exact lift_injective m n d h (congrArg Subtype.val he)
  · intro M
    obtain ⟨N, hN, he⟩ := matching_omission_coverage hh M.val.val M.val.property M.property
    refine ⟨⟨N, hN⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact he

/-- Aggregate the raw list at a label; repeated raw entries add. -/
def aggregate (a : Vector) (g : Label) : Int :=
  (a.map fun t => if t.2 = g then t.1 else 0).sum

/-- Finite integer matrix multiplication using the actual label enumeration.
The matrix interpretation still needs multiplicity control for this list. -/
def matrixCoordinates (m n d : Nat) (c : Jx m n d → Int) : Ix m n d → Int :=
  fun M => ((labels m n d).attach.map fun g => c g * entry m n d M g).sum

/-- UNPROVED: raw top coefficients equal matrix multiplication after aggregation. -/
def AggregationObligation (m n d : Nat) : Prop :=
  ∀ a : ValidVector m n d, ∀ M : Ix m n d,
    topCoordinates m n d a M = matrixCoordinates m n d (fun g => aggregate a.val g.val) M

/-- UNPROVED: arbitrary integer label coordinates have a valid raw-list lift
modulo p. This is a residue interface, not a finite-field declaration. -/
def ResidueLiftObligation (p m n d : Nat) : Prop :=
  ∀ c : Jx m n d → Int, ∃ a : ValidVector m n d,
    ∀ g : Jx m n d, (p : Int) ∣ aggregate a.val g.val - c g

/-- UNPROVED: the exact integer TopImage interface is the matrix range modulo p. -/
def MatrixImageObligation (p m n d : Nat) : Prop :=
  ∀ v : Matching → Int, TopImage p m n d v ↔
    ∃ c : Jx m n d → Int, ∀ M : Ix m n d,
      (p : Int) ∣ v M.val - matrixCoordinates m n d c M

/-- The previously missing whole-board pairing is now available from K24.
This is an application of the peer theorem, not an independent reproof. -/
theorem whole_board_pairing (m n d h : Nat) (hh : h ≤ n) (x z : Matching → Int) :
    ((matchings m n d).map (fun M => restrictCoordinates h x M * z M)).sum =
    ((matchings m (n+1) d).map
      (fun M => x M * zeroExtendCoordinates h z M)).sum :=
  pairing_omission m n d h hh x z

end Programme.«20261104-1627-proof-complexity».LprimeStages
#print axioms Programme.«20261104-1627-proof-complexity».LprimeStages.avoidingLift_bijective
#print axioms Programme.«20261104-1627-proof-complexity».LprimeStages.whole_board_pairing
