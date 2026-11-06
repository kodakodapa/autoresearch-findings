import Programme.«20261025-1627-proof-complexity».K5Sup

/-! Kernel check of the K5 design condition for `M = {0, 50, w}`, all `w < 105`. -/

namespace Programme.«20261025-1627-proof-complexity».K5Defs

theorem chkU50 : allB 105 (fun w => pairOk sup 50 w) = true := by decide +kernel

end Programme.«20261025-1627-proof-complexity».K5Defs
