import Programme.«20261101-1618-proof-complexity».ClauseLinearCondition

namespace Programme.«20261101-1618-proof-complexity».LinearCertificate
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-1618-proof-complexity».ClauseLinear

/-- Explicit generators: a literal cell, or a clause slack times a cell. -/
inductive Generator where
  | cell (m : List Lit)
  | clause (c m : List Lit)
  deriving DecidableEq

def Generator.eval : Generator → Assignment → Rat
  | .cell m => conjunction m
  | .clause c m => fun a => conjunction m a * slack c a

def Generator.valid (F : List Clause) (d : Nat) : Generator → Bool
  | .cell m => decide (m.length ≤ d)
  | .clause c m => decide (c ∈ F ∧ m.length + 1 ≤ d)

theorem Generator.sound {F d} {g : Generator} (h : g.valid F d = true) :
    Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone F d g.eval := by
  cases g with
  | cell m => exact positive_cell m (of_decide_eq_true h)
  | clause c m =>
    have hh : c ∈ F ∧ m.length + 1 ≤ d := of_decide_eq_true h
    exact clause_cell c m hh.1 hh.2

abbrev Certificate := List (Rat × Generator)

def valid (F : List Clause) (d : Nat) (cert : Certificate) : Bool :=
  cert.all (fun t => decide (0 ≤ t.1) && t.2.valid F d)

def eval (cert : Certificate) (a : Assignment) : Rat :=
  (cert.map (fun t => t.1 * t.2.eval a)).sum

theorem sound {F d cert} (h : valid F d cert = true) :
    Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone F d (eval cert) := by
  induction cert with
  | nil => exact .zero
  | cons t ts ih =>
    have hh : (decide (0 ≤ t.1) && t.2.valid F d) = true ∧ valid F d ts = true := by
      simpa only [valid, List.all_cons, Bool.and_eq_true] using h
    have ht : decide (0 ≤ t.1) = true ∧ t.2.valid F d = true := by
      simpa only [Bool.and_eq_true] using hh.1
    exact .add (.scale t.1 (of_decide_eq_true ht.1) (Generator.sound ht.2)) (ih hh.2)

theorem refutes {F d cert} (hv : valid F d cert = true)
    (hi : ∀ a, eval cert a = -1) : Programme.«20261101-1618-proof-complexity».ClauseLinear.Refutes F d := by
  have hh := sound hv
  have he : eval cert = (fun _ => (-1 : Rat)) := funext hi
  rwa [he] at hh

#print axioms sound
#print axioms refutes
end Programme.«20261101-1618-proof-complexity».LinearCertificate
