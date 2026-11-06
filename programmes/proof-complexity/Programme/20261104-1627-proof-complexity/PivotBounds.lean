import Programme.«20261104-1627-proof-complexity».PivotFiniteCertificates
namespace Programme.«20261104-1627-proof-complexity».PivotBounds
open Programme.«20261104-1627-proof-complexity».RectangularSparse Programme.«20261104-1627-proof-complexity».PivotFiniteCertificates
def bounded (count limit : Nat) (v : Array Sparse) : Bool :=
  (List.range count).all fun i => (v[i]?.getD []).all fun z => z.1 < limit
theorem sound {count limit : Nat} (v : Array Sparse) (h : bounded count limit v = true) :
    ∀ i, i < count → ∀ z ∈ v[i]?.getD [], z.1 < limit := by
  intro i hi z hz
  have hh := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  have hh' := List.all_eq_true.mp hh z hz
  exact of_decide_eq_true hh'
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem bounds3 : bounded 360 90 C3 = true ∧ bounded 60 240 H3 = true := by decide +kernel
theorem bounds4 : bounded 600 140 C4 = true ∧ bounded 120 600 H4 = true := by decide +kernel
#print axioms bounds3
#print axioms bounds4
end Programme.«20261104-1627-proof-complexity».PivotBounds
