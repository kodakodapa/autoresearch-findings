import Programme.«20261025-1627-proof-complexity».K5Sup

/-! Kernel check of the K5 design condition for `M = {0, 52, w}`, all `w < 105`. -/

namespace Programme.«20261025-1627-proof-complexity».K5Defs

theorem chkU52 : allB 105 (fun w => pairOk sup 52 w) = true := by decide +kernel

end Programme.«20261025-1627-proof-complexity».K5Defs
