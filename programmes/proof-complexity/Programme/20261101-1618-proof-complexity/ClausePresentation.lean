import Programme.«20261101-1618-proof-complexity».ClauseLinear

namespace Programme.«20261101-1618-proof-complexity».ClausePresentation
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-1618-proof-complexity».ClauseLinear

/-- Clause presentation changes preserve degree when each slack has an exact image. -/
theorem cone_map {F G : List Clause} {d : Nat} {f : Assignment → Rat}
    (hFG : ∀ c ∈ F, ∃ c' ∈ G, slack c = slack c')
    (h : Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone F d f) : Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone G d f := by
  induction h with
  | positive m hm hd => exact .positive m hm hd
  | clause c m hc hm hd =>
    obtain ⟨c', hc', he⟩ := hFG c hc
    simpa only [he] using (Programme.«20261101-1618-proof-complexity».ClauseLinear.Cone.clause c' m hc' hm hd)
  | zero => exact .zero
  | add _ _ ih jh => exact .add ih jh
  | scale r hr _ ih => exact .scale r hr ih

/-- Order and multiplicity of whole clauses do not affect formal degree. -/
theorem refutes_membership {F G : List Clause} {d : Nat}
    (hFG : ∀ c, c ∈ F ↔ c ∈ G) : Programme.«20261101-1618-proof-complexity».ClauseLinear.Refutes F d ↔ Programme.«20261101-1618-proof-complexity».ClauseLinear.Refutes G d := by
  constructor
  · exact cone_map (fun c hc => ⟨c, (hFG c).mp hc, rfl⟩)
  · exact cone_map (fun c hc => ⟨c, (hFG c).mpr hc, rfl⟩)

#print axioms cone_map
#print axioms refutes_membership
end Programme.«20261101-1618-proof-complexity».ClausePresentation
