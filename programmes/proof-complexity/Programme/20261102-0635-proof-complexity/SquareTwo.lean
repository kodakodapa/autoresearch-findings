import Programme.«20261102-0635-proof-complexity».IntegralDual

namespace Programme.«20261102-0635-proof-complexity».SquareTwo
open Programme.«20261102-0635-proof-complexity».IntegralDual

/-- Two-edge matchings of the 3 by 3 board, encoded by edge bit masks. -/
def masks : List Nat :=
  [10,12,17,20,33,34,66,68,80,96,129,132,136,160,257,258,264,272]
def mask (m : Fin 18) : Nat := masks[m.val]!
def sign (m : Fin 18) : Int :=
  if m.val ∈ [0,3,4,7,8,10,13,15,16] then -1 else 1
def contains (m : Fin 18) (edge : Nat) : Bool :=
  (mask m / 2^edge) % 2 == 1
/-- All extensions of an edge using the indicated free row or free column. -/
def row (a : Fin 9) (i : Fin 3) : List (Fin 18) :=
  (List.finRange 18).filter fun m => contains m a.val &&
    (List.finRange 3).any (fun j => contains m (3*i.val+j.val))
def col (a : Fin 9) (j : Fin 3) : List (Fin 18) :=
  (List.finRange 18).filter fun m => contains m a.val &&
    (List.finRange 3).any (fun i => contains m (3*i.val+j.val))
def relations : List (List (Fin 18)) :=
  (List.finRange 9).flatMap fun a =>
    ((List.finRange 3).filter (fun i => i.val != a.val / 3)).map (row a) ++
    ((List.finRange 3).filter (fun j => j.val != a.val % 3)).map (col a)

set_option maxRecDepth 10000
set_option maxHeartbeats 0
/-- The enumeration is exactly the compatible pairs of distinct board edges. -/
theorem masks_complete : ∀ b : Fin 512,
    b.val ∈ masks ↔ ∃ a c : Fin 9,
      a.val < c.val ∧ a.val / 3 ≠ c.val / 3 ∧
      a.val % 3 ≠ c.val % 3 ∧ b.val = 2^a.val + 2^c.val := by decide

/-- Each relation is the two extensions in a free row or column. -/
theorem relations_size : relations.length = 36 ∧
    ∀ xs ∈ relations, xs.length = 2 := by decide

theorem exact_relations : ∀ xs ∈ relations, total sign xs = 0 := by decide

theorem odd_sign : ∀ m, (2 : Int) ∣ sign m - 1 := by decide

/-- Rank-one coordinate data from the signed completion functional.
This is not asserted to be a basis presentation of the entire quotient. -/
def coordinates : CoordinateLift 2 1 relations where
  coord := fun m _ => sign m
  weights := fun _ => 1
  relation_zero := by
    intro xs hx j hj
    exact exact_relations xs hx
  residue_one := by
    intro m
    simpa [dot] using odd_sign m

theorem square_lift : ∃ K : Fin 18 → Int,
    (∀ m, (2 : Int) ∣ K m - 1) ∧
    ∀ xs ∈ relations, total K xs = 0 :=
  lift_exists coordinates

end Programme.«20261102-0635-proof-complexity».SquareTwo
#print axioms Programme.«20261102-0635-proof-complexity».SquareTwo.relations_size
#print axioms Programme.«20261102-0635-proof-complexity».SquareTwo.exact_relations
#print axioms Programme.«20261102-0635-proof-complexity».SquareTwo.square_lift

#print axioms Programme.«20261102-0635-proof-complexity».SquareTwo.masks_complete
