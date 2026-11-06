import Programme.«20261104-1627-proof-complexity».PivotRow3_8
import Programme.«20261104-1627-proof-complexity».PivotExecutable
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace Programme.«20261104-1627-proof-complexity».PivotRow3_9
open Programme.«20261104-1627-proof-complexity».PivotFiniteCertificates Programme.«20261104-1627-proof-complexity».PivotExecutable
theorem checked : Programme.«20261104-1627-proof-complexity».RectangularSparse.check 3 1 360 90 240
    (fun z => P 3 5 (z+9)) (fun z => g 3 5 (z+9)) (T 3 5)
    (fun j => C3[j]?.getD []) (fun z => H3[z+9]?.getD []) = true := by
  decide +kernel
end Programme.«20261104-1627-proof-complexity».PivotRow3_9
