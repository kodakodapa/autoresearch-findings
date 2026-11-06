import Programme.«20261031-2024-proof-complexity».NativeIter

namespace Programme.«20261101-1618-proof-complexity».ClauseLinear
open Programme.«20261031-2024-proof-complexity».NativeIter

/-- Truth value of a literal, as a rational Boolean function. -/
def literal (l : Lit) (a : Assignment) : Rat := if holds a l then 1 else 0
/-- Standard linear clause inequality, regardless of clause width. -/
def slack (c : Clause) (a : Assignment) : Rat := (c.map (fun l => literal l a)).sum - 1

/-- Formal clause-linear degree is multiplier length plus one, before reduction. -/
inductive Cone (F : List Clause) (d : Nat) : (Assignment → Rat) → Prop where
  | positive (m) : Multiplier m → m.length ≤ d → Cone F d (conjunction m)
  | clause (c m) : c ∈ F → Multiplier m → m.length + 1 ≤ d →
      Cone F d (fun a => conjunction m a * slack c a)
  | zero : Cone F d (fun _ => 0)
  | add {f g} : Cone F d f → Cone F d g → Cone F d (fun a => f a + g a)
  | scale {f} (r : Rat) : 0 ≤ r → Cone F d f → Cone F d (fun a => r * f a)

def Refutes (F : List Clause) (d : Nat) : Prop := Cone F d (fun _ => -1)

theorem zero_nonneg {F f} (h : Cone F 0 f) (a : Assignment) : 0 ≤ f a := by
  induction h with
  | positive m _ _ => exact conjunction_nonneg m a
  | clause c m _ _ hd => omega
  | zero => exact Rat.le_refl
  | add _ _ ih jh => exact Rat.add_nonneg ih jh
  | scale r hr _ ih => exact Rat.mul_nonneg hr ih

theorem no_degree_zero (F : List Clause) : ¬ Refutes F 0 := by
  intro h
  have hn : (0 : Rat) ≤ -1 := zero_nonneg h (fun _ => false)
  contradiction

/-- Transport reduces to representing the images of the two generator families.
This allows constant restrictions and variable identifications once their images
have been checked; no injectivity assumption is made. -/
theorem transport {F G : List Clause} {d e : Nat} (rho : Assignment → Assignment)
    (hp : ∀ m, Multiplier m → m.length ≤ d →
      Cone G e (fun a => conjunction m (rho a)))
    (hc : ∀ c m, c ∈ F → Multiplier m → m.length + 1 ≤ d →
      Cone G e (fun a => conjunction m (rho a) * slack c (rho a)))
    {f : Assignment → Rat} (h : Cone F d f) : Cone G e (fun a => f (rho a)) := by
  induction h with
  | positive m hm hd => exact hp m hm hd
  | clause c m hcm hm hd => exact hc c m hcm hm hd
  | zero => exact Cone.zero
  | add _ _ ih jh => exact Cone.add ih jh
  | scale r hr _ ih => exact Cone.scale r hr ih

#print axioms no_degree_zero
#print axioms transport
end Programme.«20261101-1618-proof-complexity».ClauseLinear
