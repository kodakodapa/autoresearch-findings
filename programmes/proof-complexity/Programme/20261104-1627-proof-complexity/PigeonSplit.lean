import Programme.«20261104-1627-proof-complexity».HoleRestriction

namespace Programme.«20261104-1627-proof-complexity».MatchingLabels

/-- Labels whose base uses the last pigeon belong to block three. -/
def usesPigeon (w : Nat) (g : Label) : Bool :=
  g.base.any fun e => e.1 == w

/-- The three actual raw-vector blocks in the pigeon-induction proof. -/
def pigeonBlock (w : Nat) (g : Label) : Nat :=
  if usesPigeon w g then 3 else if g.isRow && g.mark == w then 2 else 1

def splitPigeon (w b : Nat) (v : Vector) : Vector :=
  v.filter fun t => pigeonBlock w t.2 == b

theorem pigeonBlock_cases (w : Nat) (g : Label) :
    pigeonBlock w g = 1 ∨ pigeonBlock w g = 2 ∨ pigeonBlock w g = 3 := by
  unfold pigeonBlock
  split <;> simp_all
  split <;> simp_all

theorem splitPigeon_valid {m n d : Nat} (w b : Nat) {v : Vector}
    (hv : valid m n d v) : valid m n d (splitPigeon w b v) := by
  intro t ht
  exact hv t (List.mem_filter.mp ht).1

theorem vectorCoeff_splitPigeon (w : Nat) (v : Vector) (g : Label) :
    vectorCoeff v g = vectorCoeff (splitPigeon w 1 v) g +
      vectorCoeff (splitPigeon w 2 v) g + vectorCoeff (splitPigeon w 3 v) g := by
  induction v with
  | nil => simp [vectorCoeff, splitPigeon]
  | cons t v ih =>
    rcases pigeonBlock_cases w t.2 with h | h | h
    all_goals
      simp only [splitPigeon, List.filter_cons, h, beq_self_eq_true,
        List.cons_append, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]
      simp only [vectorCoeff, List.filter_cons, List.map_cons, List.sum_cons]
      split <;> simp_all [vectorCoeff, splitPigeon] <;> omega

/-- The requested Lemma 4 type. This is a goal declaration, not a theorem.
The stable-range inequality activates the conditional Lprime definition. -/
def PigeonInductionGoal : Prop :=
  ∀ p m n d : Nat, 0 < m → 1 < d → 2*(d-1) < n →
    Spanning p (m-1) n d → Spanning p (m-1) (n-1) (d-1) →
    Lprime p (m-1) n (d-1) → Spanning p m n d

end Programme.«20261104-1627-proof-complexity».MatchingLabels
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.vectorCoeff_splitPigeon
#print axioms Programme.«20261104-1627-proof-complexity».MatchingLabels.splitPigeon_valid
