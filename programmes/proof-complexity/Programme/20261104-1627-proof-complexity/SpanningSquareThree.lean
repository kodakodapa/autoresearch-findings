import Programme.«20261104-1627-proof-complexity».RowResidualNormalize

namespace Programme.«20261104-1627-proof-complexity».SpanningSquareThree
open Programme.«20261104-1627-proof-complexity».MatchingLabels Programme.«20261104-1627-proof-complexity».MixedAggregate Programme.«20261104-1627-proof-complexity».MixedEliminate
open Programme.«20261104-1627-proof-complexity».AnchoredColumnNormalize Programme.«20261104-1627-proof-complexity».RowResidualNormalize

def negCombination (c : List (Int × Vector)) : List (Int × Vector) :=
  c.map fun t => (-t.1,t.2)

theorem combine_append_coeff (c d : List (Int × Vector)) (g : Label) :
    vectorCoeff (combine (c ++ d)) g =
      vectorCoeff (combine c) g + vectorCoeff (combine d) g := by
  simp [combine, List.flatMap_append, vectorCoeff_append]

theorem negCombination_coeff (c : List (Int × Vector)) (g : Label) :
    vectorCoeff (combine (negCombination c)) g = -vectorCoeff (combine c) g := by
  induction c with
  | nil => simp [negCombination, combine, vectorCoeff]
  | cons t c ih =>
    change vectorCoeff ((t.2.map fun a => (-t.1*a.1,a.2)) ++
      combine (negCombination c)) g =
      -vectorCoeff ((t.2.map fun a => (t.1*a.1,a.2)) ++ combine c) g
    rw [vectorCoeff_append, vectorCoeff_append, coeff_scale, coeff_scale, ih]
    simp [Int.neg_mul, Int.neg_add]

def totalCorrections (v : Vector) : List (Int × Vector) :=
  allCorrections v ++ negCombination (rcSum 3 3
    (weights (normalized (Programme.«20261104-1627-proof-complexity».CCNormalize.corrected 3 v)))) ++
  rowCombination (Programme.«20261104-1627-proof-complexity».NormalizedResidual.finalResidual v)

theorem totalCorrections_generators (v : Vector) :
    ∀ t ∈ totalCorrections v, t.2 ∈ syzygies 3 3 2 := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · rcases List.mem_append.mp ht with ht | ht
    · exact allCorrections_generators v t ht
    · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
      exact rcSum_generators 3 3 _ s hs
  · exact rowCombination_generators _ t ht

theorem totalCorrections_coeff (v : Vector) (g : Label) :
    vectorCoeff (rowResidual (Programme.«20261104-1627-proof-complexity».NormalizedResidual.finalResidual v)) g =
      vectorCoeff v g + vectorCoeff (combine (totalCorrections v)) g := by
  have hf : vectorCoeff (Programme.«20261104-1627-proof-complexity».NormalizedResidual.finalResidual v) g =
      vectorCoeff v g + vectorCoeff (combine (allCorrections v)) g -
      vectorCoeff (combine (rcSum 3 3
        (weights (normalized (Programme.«20261104-1627-proof-complexity».CCNormalize.corrected 3 v))))) g := by
    unfold Programme.«20261104-1627-proof-complexity».NormalizedResidual.finalResidual
    rw [residual_coeff, normalized_eq, vectorCoeff_append]
  simp only [rowResidual, vectorCoeff_append, totalCorrections,
    combine_append_coeff, negCombination_coeff]
  omega

/-- Exact coordinate spanning by the enumerated syzygies on the first nontrivial square. -/
theorem spanning_square_three : Spanning 3 3 3 2 := by
  intro v hv
  refine ⟨negCombination (totalCorrections v), ?_, ?_⟩
  · intro t ht
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
    exact totalCorrections_generators v s hs
  · intro g
    have h := normalized_all_labels v hv g
    rw [totalCorrections_coeff] at h
    rw [negCombination_coeff]
    simpa using h

end Programme.«20261104-1627-proof-complexity».SpanningSquareThree
#print axioms Programme.«20261104-1627-proof-complexity».SpanningSquareThree.spanning_square_three
