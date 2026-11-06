import Programme.«20261025-1627-proof-complexity».K5Sup

/-! Kernel check of the K5 design condition for `M = {0, 85, w}`, all `w < 105`. -/

namespace Programme.«20261025-1627-proof-complexity».K5Defs

theorem chkU85 : allB 105 (fun w => pairOk sup 85 w) = true := by decide +kernel

end Programme.«20261025-1627-proof-complexity».K5Defs
