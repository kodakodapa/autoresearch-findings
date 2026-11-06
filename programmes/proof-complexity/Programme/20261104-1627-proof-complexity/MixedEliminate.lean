import Programme.«20261104-1627-proof-complexity».MixedAggregate

namespace Programme.«20261104-1627-proof-complexity».MixedEliminate
open Programme.«20261104-1627-proof-complexity».MatchingLabels Programme.«20261104-1627-proof-complexity».MixedAggregate

/-- A base hole distinct from the extension hole, on every board with two holes. -/
def anchor (r : Nat) : Nat := if r = 0 then 1 else 0

theorem anchor_valid {n r : Nat} (hn : 2 ≤ n) :
    anchor r < n ∧ anchor r ≠ r := by
  unfold anchor
  split <;> omega

/-- Choose mixed weights so that their column coordinates are the anchored ones. -/
def weights (v : Vector) (a r : Nat) : Int :=
  -vectorCoeff v (edgeColLabel a (anchor r) r)

def residual (m n : Nat) (v : Vector) : Vector :=
  v ++ (combine (rcSum m n (weights v))).map (fun t => (-1 * t.1, t.2))

theorem residual_coeff (m n : Nat) (v : Vector) (g : Label) :
    vectorCoeff (residual m n v) g =
      vectorCoeff v g - vectorCoeff (combine (rcSum m n (weights v))) g := by
  unfold residual
  rw [vectorCoeff_append, coeff_scale]
  omega

/-- Actual column cancellation, conditional on base-hole independence.
This hypothesis is not inferred from kernel membership here. -/
theorem residual_columns {p m n : Nat} (hn : 2 ≤ n) (v : Vector)
    (hind : ∀ a < m, ∀ r < n, ∀ b < n, b ≠ r →
      (p : Int) ∣ vectorCoeff v (edgeColLabel a b r) -
        vectorCoeff v (edgeColLabel a (anchor r) r)) :
    ∀ a < m, ∀ b < n, ∀ r < n, b ≠ r →
      (p : Int) ∣ vectorCoeff (residual m n v) (edgeColLabel a b r) := by
  intro a ha b hb r hr hbr
  rw [residual_coeff, rcSum_col_exact m n a b r (weights v) ha hr hb hbr]
  simpa [weights] using hind a ha r hr b hb hbr

/-- The same cancellation changes rows by the opposite anchored column coordinate. -/
theorem residual_rows {m n a b r : Nat} (v : Vector)
    (ha : a < m) (hr : r < m) (hb : b < n) (har : a ≠ r) :
    vectorCoeff (residual m n v) (edgeRowLabel a b r) =
      vectorCoeff v (edgeRowLabel a b r) +
        vectorCoeff v (edgeColLabel r (anchor b) b) := by
  rw [residual_coeff, rcSum_row_exact m n a b r (weights v) ha hr hb har]
  simp [weights]

end Programme.«20261104-1627-proof-complexity».MixedEliminate
#print axioms Programme.«20261104-1627-proof-complexity».MixedEliminate.residual_columns
#print axioms Programme.«20261104-1627-proof-complexity».MixedEliminate.residual_rows
