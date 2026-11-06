import Programme.«20261026-1402-proof-complexity».ExtLemma

namespace Programme.«20261102-0635-proof-complexity».IntegralDual

/-- Sum a finite family of integer values, retaining repeated entries. -/
def total {M : Type} (f : M → Int) : List M → Int
  | [] => 0
  | x :: xs => f x + total f xs

/-- Evaluation of integral dual coordinates on the first r basis coordinates. -/
def dot (r : Nat) (w c : Nat → Int) : Int :=
  match r with
  | 0 => 0
  | r+1 => dot r w c + w r * c r

theorem total_add {M : Type} (f g : M → Int) (xs : List M) :
    total (fun x => f x + g x) xs = total f xs + total g xs := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih => simp [total, ih, Int.add_assoc, Int.add_left_comm]

theorem total_scale {M : Type} (a : Int) (f : M → Int) (xs : List M) :
    total (fun x => a * f x) xs = a * total f xs := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih => simp [total, ih, Int.mul_add]

theorem total_dot {M : Type} (r : Nat) (w : Nat → Int)
    (coord : M → Nat → Int) (xs : List M) :
    total (fun x => dot r w (coord x)) xs =
      dot r w (fun j => total (fun x => coord x j) xs) := by
  induction r with
  | zero => induction xs <;> simp_all [dot, total]
  | succ r ih => simp only [dot, total_add, total_scale, ih]

theorem dot_zero (r : Nat) (w c : Nat → Int)
    (h : ∀ j < r, c j = 0) : dot r w c = 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [dot, ih (fun j hj => h j (by omega)), h r (by omega)]
    simp

/-- A finite coordinate presentation of the integral quotient, together with
one modular functional in dual coordinates. No freeness assertion is built in:
constructing these coordinates from the square matching quotient is a separate task. -/
structure CoordinateLift {M : Type} (p r : Nat) (relations : List (List M)) where
  coord : M → Nat → Int
  weights : Nat → Int
  relation_zero : ∀ xs ∈ relations, ∀ j < r, total (fun x => coord x j) xs = 0
  residue_one : ∀ x, (p : Int) ∣ dot r weights (coord x) - 1

/-- Lifting dual coordinates preserves every integral relation exactly and
has residue one on every generator. The only hypothesis is the displayed
finite coordinate presentation and modular-functional data. -/
theorem lift_exists {M : Type} {p r : Nat} {relations : List (List M)}
    (C : CoordinateLift p r relations) :
    ∃ K : M → Int, (∀ x, (p : Int) ∣ K x - 1) ∧
      ∀ xs ∈ relations, total K xs = 0 := by
  refine ⟨fun x => dot r C.weights (C.coord x), C.residue_one, ?_⟩
  intro xs hx
  rw [total_dot]
  exact dot_zero r C.weights _ (C.relation_zero xs hx)

end Programme.«20261102-0635-proof-complexity».IntegralDual
#print axioms Programme.«20261102-0635-proof-complexity».IntegralDual.lift_exists
