import Programme.«20261101-1618-proof-complexity».ClausePresentation
import Programme.«20261101-1618-proof-complexity».LossySource

namespace Programme.«20261101-1618-proof-complexity».LossyPresentation
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-1618-proof-complexity».ClauseLinear

theorem slack_reverse (c : Clause) : slack c.reverse = slack c := by
  funext a
  simp [slack, List.map_reverse, List.sum_reverse]

theorem refutes_reverse_coverage {F G : List Clause} {d : Nat}
    (hFG : ∀ c ∈ F, c ∈ G ∨ c.reverse ∈ G)
    (hGF : ∀ c ∈ G, c ∈ F ∨ c.reverse ∈ F) :
    Programme.«20261101-1618-proof-complexity».ClauseLinear.Refutes F d ↔ Programme.«20261101-1618-proof-complexity».ClauseLinear.Refutes G d := by
  constructor
  · apply Programme.«20261101-1618-proof-complexity».ClausePresentation.cone_map
    intro c hc
    rcases hFG c hc with h | h
    · exact ⟨c, h, rfl⟩
    · exact ⟨c.reverse, h, (slack_reverse c).symm⟩
  · apply Programme.«20261101-1618-proof-complexity».ClausePresentation.cone_map
    intro c hc
    rcases hGF c hc with h | h
    · exact ⟨c, h, rfl⟩
    · exact ⟨c.reverse, h, (slack_reverse c).symm⟩

#print axioms refutes_reverse_coverage
end Programme.«20261101-1618-proof-complexity».LossyPresentation
