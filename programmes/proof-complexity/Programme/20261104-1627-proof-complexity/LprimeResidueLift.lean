import Programme.«20261104-1627-proof-complexity».LprimeStageObligations

/-! A multiplicity-safe raw lift. Duplicate enumeration entries are corrected,
not counted as independent coordinates. No field assumptions are needed. -/
namespace Programme.«20261104-1627-proof-complexity».LprimeStages
open Programme.«20261104-1627-proof-complexity».MatchingLabels

def rawLift (L : List Label) (c : Label → Int) : Vector :=
  match L with
  | [] => []
  | g :: gs =>
    let a := rawLift gs c
    (c g - aggregate a g, g) :: a

theorem aggregate_cons (z : Int) (g : Label) (a : Vector) (h : Label) :
    aggregate ((z,g)::a) h = (if g = h then z else 0) + aggregate a h := by
  simp [aggregate]

theorem rawLift_support (L : List Label) (c : Label → Int) :
    ∀ t ∈ rawLift L c, t.2 ∈ L := by
  induction L with
  | nil => simp [rawLift]
  | cons g gs ih =>
    intro t ht
    simp only [rawLift, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem g (ih t ht)

theorem rawLift_coordinates (L : List Label) (c : Label → Int) :
    ∀ g ∈ L, aggregate (rawLift L c) g = c g := by
  induction L with
  | nil => simp
  | cons h hs ih =>
    intro g hg
    rw [rawLift, aggregate_cons]
    by_cases he : h = g
    · subst g
      simp
    · have hg' : g ∈ hs := (List.mem_cons.mp hg).resolve_left (Ne.symm he)
      simp [he, ih g hg']

/-- Exact lifting is stronger than residue lifting. -/
theorem integerLift (m n d : Nat) (c : Jx m n d → Int) :
    ∃ a : ValidVector m n d, ∀ g : Jx m n d, aggregate a.val g.val = c g := by
  let ext : Label → Int := fun g => if hg : g ∈ labels m n d then c ⟨g,hg⟩ else 0
  let a := rawLift (labels m n d) ext
  refine ⟨⟨a,rawLift_support (labels m n d) ext⟩, ?_⟩
  intro g
  rw [rawLift_coordinates (labels m n d) ext g.val g.property]
  simp [ext, g.property]

/-- Matrix image assembly needs only aggregation; lifting adds no hypothesis. -/
theorem matrixImage_of_aggregation (p m n d : Nat)
    (ha : AggregationObligation m n d) : MatrixImageObligation p m n d := by
  intro v
  rw [topImage_iff_integerImage]
  constructor
  · rintro ⟨a,hv⟩
    refine ⟨fun g => aggregate a.val g.val, ?_⟩
    intro M
    rw [← ha a M]
    exact hv M
  · rintro ⟨c,hv⟩
    obtain ⟨a,hc⟩ := integerLift m n d c
    refine ⟨a, ?_⟩
    intro M
    have he : (fun g : Jx m n d => aggregate a.val g.val) = c := funext hc
    rw [ha a M, he]
    exact hv M

/-- Exact integer representatives, even when the label enumeration repeats. -/
theorem residueLift (p m n d : Nat) : ResidueLiftObligation p m n d := by
  intro c
  let ext : Label → Int := fun g => if hg : g ∈ labels m n d then c ⟨g,hg⟩ else 0
  let a := rawLift (labels m n d) ext
  have ha : valid m n d a := rawLift_support (labels m n d) ext
  refine ⟨⟨a,ha⟩, ?_⟩
  intro g
  have he : aggregate a g.val = c g := by
    rw [rawLift_coordinates (labels m n d) ext g.val g.property]
    simp [ext, g.property]
  rw [he, Int.sub_self]
  exact ⟨0, by simp⟩

end Programme.«20261104-1627-proof-complexity».LprimeStages
#print axioms Programme.«20261104-1627-proof-complexity».LprimeStages.rawLift_coordinates
#print axioms Programme.«20261104-1627-proof-complexity».LprimeStages.residueLift

#print axioms Programme.«20261104-1627-proof-complexity».LprimeStages.integerLift
#print axioms Programme.«20261104-1627-proof-complexity».LprimeStages.matrixImage_of_aggregation
