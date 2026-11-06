import Programme.«20261025-1627-proof-complexity».K5Sup

/-! Kernel check of the K5 design condition for `M = {0, 83, w}`, all `w < 105`. -/

namespace Programme.«20261025-1627-proof-complexity».K5Defs

theorem chkU83 : allB 105 (fun w => pairOk sup 83 w) = true := by decide +kernel

end Programme.«20261025-1627-proof-complexity».K5Defs
