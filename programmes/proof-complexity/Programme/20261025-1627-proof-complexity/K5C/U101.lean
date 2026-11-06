import Programme.«20261025-1627-proof-complexity».K5Sup

/-! Kernel check of the K5 design condition for `M = {0, 101, w}`, all `w < 105`. -/

namespace Programme.«20261025-1627-proof-complexity».K5Defs

theorem chkU101 : allB 105 (fun w => pairOk sup 101 w) = true := by decide +kernel

end Programme.«20261025-1627-proof-complexity».K5Defs
