import Programme.«20261102-1249-proof-complexity».UniformC3.BlockBridge

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Programme.«20261102-1249-proof-complexity».UniformC3.Block
open Programme.«20261025-0459-proof-complexity».OntoFPHP (rsum)
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr)

/-- Three blocks of sizes p-1, p-1, 1. -/
def capacity (p : Nat) (i : Ix) : Nat := if i = 2 then 1 else p-1

def blockOf (p t : Nat) : Ix := if t < p-1 then 0 else if t < 2*(p-1) then 1 else 2

theorem rsum_below (a : Nat) : ∀ n,
    rsum n (fun t => if t < a then (1 : Int) else 0) = (min n a : Nat) := by
  intro n; induction n with
  | zero => simp [rsum]
  | succ n ih =>
    simp only [rsum]
    rw [ih]
    by_cases h : n < a <;> simp [h] <;> omega

theorem square_card (p : Nat) (hp : 1 ≤ p) (i : Ix) :
    rsum (2*p-1) (fun t => if blockOf p t = i then 1 else 0) = (capacity p i : Int) := by
  have h0 := rsum_below (p-1) (2*p-1)
  have h1 := rsum_below (2*(p-1)) (2*p-1)
  have h2 := rsum_below (2*p-1) (2*p-1)
  rcases fin3_cases i with rfl | rfl | rfl
  · have e : ∀ t < 2*p-1,
        (if blockOf p t = 0 then (1 : Int) else 0) = (if t < p-1 then 1 else 0) := by
      intro t ht; unfold blockOf; split <;> simp_all
      split <;> simp
    rw [rsum_congr _ _ _ e,h0]
    simp [capacity]; omega
  · have e : ∀ t < 2*p-1,
        (if blockOf p t = 1 then (1 : Int) else 0) =
          (if t < 2*(p-1) then 1 else 0) - (if t < p-1 then 1 else 0) := by
      intro t ht; unfold blockOf
      split <;> split <;> simp_all <;> omega
    rw [rsum_congr _ _ _ e,Programme.«20261025-1627-proof-complexity».OntoExt3.rsum_sub',h1,h0]
    simp [capacity]; omega
  · have e : ∀ t < 2*p-1,
        (if blockOf p t = 2 then (1 : Int) else 0) =
          (if t < 2*p-1 then 1 else 0) - (if t < 2*(p-1) then 1 else 0) := by
      intro t ht; unfold blockOf
      split <;> split <;> simp_all <;> omega
    rw [rsum_congr _ _ _ e,Programme.«20261025-1627-proof-complexity».OntoExt3.rsum_sub',h2,h1]
    simp [capacity]; omega

def squarePartition (p : Nat) (hp : 1 ≤ p) : Partition (2*p-1) where
  block := blockOf p
  size := capacity p
  card := square_card p hp

def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n

/-- The signed numerator after cancelling the four interior factorials.
Only used on feasible matrices of total p. -/
def numerator (p : Nat) (M : Matrix) : Int :=
  if M 2 2 = 1 then (p-1 : Nat)
  else if rc M 2 = 0 then
    if cc M 2 = 0 then (M 0 0 : Int)*M 1 1 - (M 0 1 : Int)*M 1 0
    else if M 0 2 = 1 then -((M 1 0 : Int) + M 1 1)
    else -((M 0 0 : Int) + M 0 1)
  else if cc M 2 = 0 then
    if M 2 0 = 1 then -((M 0 1 : Int) + M 1 1)
    else -((M 0 0 : Int) + M 1 0)
  else if M 0 2 = M 2 0 then -1 else 1

/-- Explicit integer lift formula. Zero outside the relevant feasible degree.
The written proof identifies this with -F(M)[y^M]z^(p-2)(zd-bc). -/
def explicitValue (p : Nat) (M : Matrix) : Int :=
  if Feasible (capacity p) M ∧ total M = p then
    - ((-1 : Int) ^ (M 0 1 + M 1 0)) * (factorial (p-2) : Int) *
      numerator p M *
      (factorial (p-1-rc M 0) : Int) *
      (factorial (p-1-rc M 1) : Int) *
      (factorial (p-1-cc M 0) : Int) *
      (factorial (p-1-cc M 1) : Int)
  else 0

/-- Exact remaining elementary theorem, stated as a Prop rather than an axiom.
No quotient-basis or integral-lift conclusion is built into its fields. -/
def ExplicitIdentities (p : Nat) : Prop :=
  (∀ M, Feasible (capacity p) M → total M = p →
    (p : Int) ∣ explicitValue p M - 1) ∧
  (∀ M, Feasible (capacity p) M → total M = p-1 → ∀ i,
    sum3 (fun j => ((capacity p j : Int) - cc M j) * explicitValue p (inc M i j)) = 0) ∧
  (∀ M, Feasible (capacity p) M → total M = p-1 → ∀ j,
    sum3 (fun i => ((capacity p i : Int) - rc M i) * explicitValue p (inc M i j)) = 0)

def certificateOfIdentities {p : Nat} (hp : 1 ≤ p) (h : ExplicitIdentities p) :
    Certificate p (squarePartition p hp) where
  value := explicitValue p
  unit := h.1
  row := h.2.1
  col := h.2.2

theorem squareLift_of_explicitIdentities {p : Nat} (hp : 2 ≤ p)
    (h : ExplicitIdentities p) : SquareLiftAssumption p :=
  ⟨(certificateOfIdentities (by omega) h).toIntegralLift hp _⟩

#print axioms squareLift_of_explicitIdentities
end Programme.«20261102-1249-proof-complexity».UniformC3.Block
