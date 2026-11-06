import Programme.«20261104-1627-proof-complexity».RCCoordinates

namespace Programme.«20261104-1627-proof-complexity».MixedAggregate
open Programme.«20261104-1627-proof-complexity».MatchingLabels

theorem coeff_scale (v : Vector) (c : Int) (g : Label) :
    vectorCoeff (v.map fun t => (c*t.1,t.2)) g = c * vectorCoeff v g := by
  induction v with
  | nil => simp [vectorCoeff]
  | cons t v ih =>
    by_cases h : t.2 = g <;> simp [vectorCoeff, h] at ih ⊢ <;>
      simp_all [Int.mul_add]

theorem coeff_combine (L : List (Int × Vector)) (g : Label) :
    vectorCoeff (combine L) g = (L.map fun t => t.1 * vectorCoeff t.2 g).sum := by
  induction L with
  | nil => simp [combine, vectorCoeff]
  | cons t L ih =>
    simp only [combine, List.flatMap_cons, vectorCoeff_append]
    rw [coeff_scale]
    change t.1 * vectorCoeff t.2 g + vectorCoeff (combine L) g = _
    rw [ih]
    rfl

/-- A finite, explicit sum of the mixed generators, with arbitrary integer weights. -/
def rcSum (m n : Nat) (A : Nat → Nat → Int) : List (Int × Vector) :=
  (List.range m).flatMap fun i => (List.range n).map fun j => (A i j, rc m n [] i j)

theorem rcSum_generators (m n : Nat) (A : Nat → Nat → Int) :
    ∀ t ∈ rcSum m n A, t.2 ∈ syzygies m n 2 := by
  intro t ht
  obtain ⟨i, hi, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
  exact rc_mem_syzygies (List.mem_range.mp hi) (List.mem_range.mp hj)

private theorem sum_flat (L : List Nat) (f : Nat → List Int) :
    (L.flatMap f).sum = (L.map fun i => (f i).sum).sum := by
  induction L with
  | nil => rfl
  | cons i L ih => simp [ih, List.sum_append]

theorem rcSum_row (m n a b r : Nat) (A : Nat → Nat → Int) :
    vectorCoeff (combine (rcSum m n A)) (edgeRowLabel a b r) =
    ((List.range m).map fun i => ((List.range n).map fun j =>
      A i j * (if b = j ∧ r = i ∧ a < m ∧ a ≠ i then 1 else 0)).sum).sum := by
  rw [coeff_combine]
  simp [rcSum, List.map_flatMap, sum_flat, List.map_map, Function.comp_def, rc_row_coefficient]

theorem rcSum_col (m n a b r : Nat) (A : Nat → Nat → Int) :
    vectorCoeff (combine (rcSum m n A)) (edgeColLabel a b r) =
    ((List.range m).map fun i => ((List.range n).map fun j =>
      A i j * (if a = i ∧ r = j ∧ b < n ∧ b ≠ j then -1 else 0)).sum).sum := by
  rw [coeff_combine]
  simp [rcSum, List.map_flatMap, sum_flat, List.map_map, Function.comp_def, rc_col_coefficient]

@[simp] private theorem sum_zero (L : List Nat) :
    (L.map fun _ => (0 : Int)).sum = 0 := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih]

private theorem sum_select (N x : Nat) (f : Nat → Int) :
    ((List.range N).map fun i => if i = x then f i else 0).sum =
      if x < N then f x else 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Int.add_zero, ih]
    by_cases h : N = x
    · subst x; simp
    · by_cases hx : x < N
      · simp [h, hx, show x < N+1 by omega]
      · simp [h, hx, show ¬x < N+1 by omega]

theorem rcSum_row_exact (m n a b r : Nat) (A : Nat → Nat → Int)
    (ha : a < m) (hr : r < m) (hb : b < n) (har : a ≠ r) :
    vectorCoeff (combine (rcSum m n A)) (edgeRowLabel a b r) = A r b := by
  rw [rcSum_row]
  have he (i j : Nat) :
      A i j * (if b = j ∧ r = i ∧ a < m ∧ a ≠ i then 1 else 0) =
        if i = r then (if j = b then A i j else 0) else 0 := by
    by_cases hi : i = r <;> by_cases hj : j = b <;> simp_all [eq_comm]
  simp only [he]
  have hh (i : Nat) :
      ((List.range n).map fun j => if i = r then (if j = b then A i j else 0) else 0).sum =
        if i = r then A i b else 0 := by
    by_cases hi : i = r <;> simp [hi, sum_select, hb]
  simp only [hh]
  simp [sum_select, hr]

theorem rcSum_col_exact (m n a b r : Nat) (A : Nat → Nat → Int)
    (ha : a < m) (hr : r < n) (hb : b < n) (hbr : b ≠ r) :
    vectorCoeff (combine (rcSum m n A)) (edgeColLabel a b r) = -A a r := by
  rw [rcSum_col]
  have he (i j : Nat) :
      A i j * (if a = i ∧ r = j ∧ b < n ∧ b ≠ j then -1 else 0) =
        if i = a then (if j = r then -A i j else 0) else 0 := by
    by_cases hi : i = a <;> by_cases hj : j = r <;> simp_all [eq_comm]
  simp only [he]
  have hh (i : Nat) :
      ((List.range n).map fun j => if i = a then (if j = r then -A i j else 0) else 0).sum =
        if i = a then -A i r else 0 := by
    by_cases hi : i = a <;> simp [hi, sum_select, hr]
  simp only [hh]
  simp [sum_select, ha]

end Programme.«20261104-1627-proof-complexity».MixedAggregate
#print axioms Programme.«20261104-1627-proof-complexity».MixedAggregate.rcSum_row
#print axioms Programme.«20261104-1627-proof-complexity».MixedAggregate.rcSum_col
#print axioms Programme.«20261104-1627-proof-complexity».MixedAggregate.rcSum_generators

#print axioms Programme.«20261104-1627-proof-complexity».MixedAggregate.rcSum_row_exact
#print axioms Programme.«20261104-1627-proof-complexity».MixedAggregate.rcSum_col_exact
