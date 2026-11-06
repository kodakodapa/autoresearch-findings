import Programme.«20261104-1627-proof-complexity».PivotExecutable
namespace Programme.«20261104-1627-proof-complexity».PivotRowAssembly
open Programme.«20261104-1627-proof-complexity».RectangularSparse
theorem check_of_rows {p o l s a : Nat} (P G T : Nat → Nat → Int) (C H : Nat → Sparse)
    (h : ∀ i, i < o → check p 1 l s a (fun z => P (z+i)) (fun z => G (z+i)) T C (fun z => H (z+i)) = true) :
    check p o l s a P G T C H = true := by
  unfold check
  apply List.all_eq_true.mpr
  intro i hi
  have hh := h i (List.mem_range.mp hi)
  simpa only [check, List.range_one, List.all_cons, List.all_nil, Bool.and_true, Nat.zero_add] using hh
end Programme.«20261104-1627-proof-complexity».PivotRowAssembly
