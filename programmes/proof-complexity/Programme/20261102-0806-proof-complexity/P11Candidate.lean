import Programme.«20261026-1402-proof-complexity».ExtLemma
import Init.Data.List.Sort.Basic

namespace Programme.«20261102-0806-proof-complexity».P11Candidate
open Programme.«20261026-1402-proof-complexity».ExtLemma

/-- Fourteen ten-pigeon classes and the final two-pigeon class. -/
def pigeonClass (i : Nat) : Nat := if i < 140 then i / 10 else 14

def count (g : List Nat) (a b : Nat) : Nat :=
  (g.filter fun v => pigeonClass (v / 21) == a && (v % 21) / 10 == b).length

/-- Base-eleven class counts in the checker's coordinate convention. -/
def rows (g : List Nat) (flip : Bool) : List Nat :=
  (List.range 15).map fun a =>
    if flip then count g a 1 + 11 * count g a 0 + 121 * count g a 2
    else count g a 0 + 11 * count g a 1 + 121 * count g a 2

def ordered (s : List Nat) : List Nat :=
  (s.take 10).mergeSort (fun a b => a ≤ b) ++
  ((s.drop 10).take 4).mergeSort (fun a b => a ≤ b) ++ s.drop 14

/-- Lexicographic minimum, as in the Python tuple minimum. -/
def state (g : List Nat) : List Nat :=
  let a := ordered (rows g false)
  let b := ordered (rows g true)
  if compare a b == Ordering.gt then b else a

/-- Explicit data parameter: no saved payload has yet been imported into Lean. -/
def U (savedTop : List (List Nat × Int)) (g : List Nat) : Int :=
  match savedTop.find? (fun entry => entry.1 == state g) with
  | some entry => entry.2
  | none => 0

/-- The exact remaining canonical obligation; this is a definition, not a proof. -/
def TopGoal (savedTop : List (List Nat × Int)) : Prop :=
  Bal 11 21 121 (U savedTop) (fun _ => -1) 10

end Programme.«20261102-0806-proof-complexity».P11Candidate
