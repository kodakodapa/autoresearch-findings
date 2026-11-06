import Programme.«20261031-2024-proof-complexity».NativeIter

namespace Programme.«20261101-0614-proof-complexity».ConeDual
open Programme.«20261031-2024-proof-complexity».NativeIter

/-- A linear functional on Boolean functions. It need only be positive on
admitted literal products, not on every nonnegative Boolean function. -/
structure Functional where
  eval : (Assignment → Rat) → Rat
  zero : eval (fun _ => 0) = 0
  add : ∀ f g, eval (fun a => f a + g a) = eval f + eval g
  scale : ∀ (r : Rat) f, eval (fun a => r * f a) = r * eval f
  unit : eval (fun _ => 1) = 1

/-- These are precisely the two finite constraint families needed by a
rational degree-d dual certificate once variable support is bounded. -/
structure Certificate (F : List Clause) (d : Nat) where
  functional : Functional
  positive : ∀ m, Multiplier m → m.length ≤ d →
    0 ≤ functional.eval (conjunction m)
  equation : ∀ c ∈ F, ∀ m, Admitted d c m →
    functional.eval (conjunction (m ++ falsity c)) = 0

theorem nonnegative {F d} (C : Certificate F d) {f} (h : Cone F d f) :
    0 ≤ C.functional.eval f := by
  induction h with
  | positive m hm hd => exact C.positive m hm hd
  | equation c m r hc hd =>
    rw [C.functional.scale, C.equation c hc m hd]
    simp
  | zero => rw [C.functional.zero]; exact Rat.le_refl
  | add _ _ ih jh => rw [C.functional.add]; exact Rat.add_nonneg ih jh
  | scale r hr _ ih => rw [C.functional.scale]; exact Rat.mul_nonneg hr ih

theorem no_refutation {F d} (C : Certificate F d) : ¬ Refutes F d := by
  intro h
  have hh := nonnegative C h
  have he : C.functional.eval (fun _ => (-1 : Rat)) = -1 := by
    have hs := C.functional.scale (-1) (fun _ => 1)
    simpa [C.functional.unit] using hs
  rw [he] at hh
  contradiction

#print axioms nonnegative
#print axioms no_refutation
end Programme.«20261101-0614-proof-complexity».ConeDual
