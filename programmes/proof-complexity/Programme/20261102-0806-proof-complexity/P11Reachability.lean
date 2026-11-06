import Programme.«20261102-0806-proof-complexity».P11Candidate

namespace Programme.«20261102-0806-proof-complexity».P11Reachability
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261102-0806-proof-complexity».P11Candidate
open Programme.«20261025-1627-proof-complexity».MomGen (canon)

def digit (x j : Nat) : Nat := if j = 0 then x % 11 else if j = 1 then x / 11 % 11 else x / 121

def capacity (i : Nat) : Nat := if i < 14 then 10 else 2

def holeCapacity (j : Nat) : Nat := if j < 2 then 10 else 1

def occupied (s : List Nat) (j : Nat) : Nat :=
  (s.map fun x => digit x j).foldl (· + ·) 0

def normal (s : List Nat) : List Nat :=
  let a := ordered s
  let b := ordered (s.map fun x => x / 11 % 11 + 11 * (x % 11) + 121 * (x / 121))
  if compare a b == Ordering.gt then b else a

def bump (s : List Nat) (i j : Nat) : List Nat :=
  s.zipIdx |>.map fun (x,a) => if a = i then x + 11^j else x

def successors (s : List Nat) : List (List Nat) :=
  (List.range 15).flatMap fun i =>
    (List.range 3).filterMap fun j =>
      if digit (s[i]!) 0 + digit (s[i]!) 1 + digit (s[i]!) 2 < capacity i &&
          occupied s j < holeCapacity j
      then some (normal (bump s i j)) else none

/-- Missing normalization/labelled-extension correspondence, not an established theorem. -/
def TransitionGoal : Prop :=
  ∀ g, CM 21 121 g → g.length ≤ 10 →
  ∀ i < 142, pfree 21 g i → ∀ j < 21, hfree 21 g j →
    state (canon (142 * 21) ((i * 21 + j) :: g)) ∈ successors (state g)

/-- Saved-level coverage target, with data explicit and not instantiated. -/
def CoverageGoal (levels : Nat → List (List Nat)) : Prop :=
  ∀ d ≤ 11, ∀ g, CM 21 121 g → g.length = d → state g ∈ levels d

end Programme.«20261102-0806-proof-complexity».P11Reachability
