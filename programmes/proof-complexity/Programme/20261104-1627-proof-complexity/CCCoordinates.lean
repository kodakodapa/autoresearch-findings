import Programme.«20261104-1627-proof-complexity».MixedCirculation

namespace Programme.«20261104-1627-proof-complexity».CCCoordinates
open Programme.«20261104-1627-proof-complexity».MatchingLabels

 theorem cc_empty (m a b : Nat) : cc m [] a b =
    (List.range m).map (fun i => (1, edgeColLabel i b a)) ++
    (List.range m).map (fun i => (-1, edgeColLabel i a b)) := by
  have hr : freeRow [] = fun _ => true := rfl
  have hh (L : List Nat) : L.filter (fun _ => true) = L := List.filter_eq_self.mpr (by simp)
  simp [cc, rows, hr, hh, ordered, edgeColLabel]

private theorem select (N x : Nat) (c : Int) (f : Nat → Label) (g : Label)
    (P : Prop) [Decidable P] (hf : ∀ i, f i = g ↔ i = x ∧ P) :
    vectorCoeff ((List.range N).map fun i => (c, f i)) g =
      if x < N ∧ P then c else 0 := by
  induction N with
  | zero => simp [vectorCoeff]
  | succ N ih =>
    rw [List.range_succ, List.map_append, vectorCoeff_append, ih]
    have he : vectorCoeff [(c,f N)] g = if N = x ∧ P then c else 0 := by
      by_cases h : f N = g <;> simp [vectorCoeff, h, ← hf N]
    simp only [List.map_cons, List.map_nil]
    rw [he]
    by_cases h : P <;> by_cases hn : N = x <;> by_cases hx : x < N <;>
      simp_all <;> omega

 theorem cc_col (m i j a b r : Nat) :
    vectorCoeff (cc m [] i j) (edgeColLabel a b r) =
      (if a < m ∧ b = j ∧ r = i then 1 else 0) -
      (if a < m ∧ b = i ∧ r = j then 1 else 0) := by
  rw [cc_empty, vectorCoeff_append]
  rw [select m a 1 _ _ (b = j ∧ r = i) (by
    intro x; simp [edgeColLabel]; omega)]
  rw [select m a (-1) _ _ (b = i ∧ r = j) (by
    intro x; simp [edgeColLabel]; omega)]
  split <;> split <;> omega

 theorem cc_row (m i j a b r : Nat) :
    vectorCoeff (cc m [] i j) (edgeRowLabel a b r) = 0 := by
  rw [cc_empty, vectorCoeff_append]
  rw [select m 0 1 _ _ False (by intro x; simp [edgeColLabel,edgeRowLabel])]
  rw [select m 0 (-1) _ _ False (by intro x; simp [edgeColLabel,edgeRowLabel])]
  simp

 theorem cc_pigeon_independent (m i j a a' b r : Nat)
    (ha : a < m) (ha' : a' < m) :
    vectorCoeff (cc m [] i j) (edgeColLabel a b r) =
    vectorCoeff (cc m [] i j) (edgeColLabel a' b r) := by
  simp [cc_col, ha, ha']

end Programme.«20261104-1627-proof-complexity».CCCoordinates
#print axioms Programme.«20261104-1627-proof-complexity».CCCoordinates.cc_col
#print axioms Programme.«20261104-1627-proof-complexity».CCCoordinates.cc_row
#print axioms Programme.«20261104-1627-proof-complexity».CCCoordinates.cc_pigeon_independent
