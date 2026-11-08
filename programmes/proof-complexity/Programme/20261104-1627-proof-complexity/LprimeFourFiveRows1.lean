import Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows1
open Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
theorem row10 : Programme.«20261104-1627-proof-complexity».RectangularSparse.check 3 1 120 140 28
    (fun z => P (z+10)) (fun z => G (z+10)) T C (fun z => H (z+10)) = true := by decide +kernel
theorem row11 : Programme.«20261104-1627-proof-complexity».RectangularSparse.check 3 1 120 140 28
    (fun z => P (z+11)) (fun z => G (z+11)) T C (fun z => H (z+11)) = true := by decide +kernel
theorem row12 : Programme.«20261104-1627-proof-complexity».RectangularSparse.check 3 1 120 140 28
    (fun z => P (z+12)) (fun z => G (z+12)) T C (fun z => H (z+12)) = true := by decide +kernel
theorem row13 : Programme.«20261104-1627-proof-complexity».RectangularSparse.check 3 1 120 140 28
    (fun z => P (z+13)) (fun z => G (z+13)) T C (fun z => H (z+13)) = true := by decide +kernel
theorem row14 : Programme.«20261104-1627-proof-complexity».RectangularSparse.check 3 1 120 140 28
    (fun z => P (z+14)) (fun z => G (z+14)) T C (fun z => H (z+14)) = true := by decide +kernel
theorem row15 : Programme.«20261104-1627-proof-complexity».RectangularSparse.check 3 1 120 140 28
    (fun z => P (z+15)) (fun z => G (z+15)) T C (fun z => H (z+15)) = true := by decide +kernel
theorem row16 : Programme.«20261104-1627-proof-complexity».RectangularSparse.check 3 1 120 140 28
    (fun z => P (z+16)) (fun z => G (z+16)) T C (fun z => H (z+16)) = true := by decide +kernel
theorem row17 : Programme.«20261104-1627-proof-complexity».RectangularSparse.check 3 1 120 140 28
    (fun z => P (z+17)) (fun z => G (z+17)) T C (fun z => H (z+17)) = true := by decide +kernel
theorem row18 : Programme.«20261104-1627-proof-complexity».RectangularSparse.check 3 1 120 140 28
    (fun z => P (z+18)) (fun z => G (z+18)) T C (fun z => H (z+18)) = true := by decide +kernel
theorem row19 : Programme.«20261104-1627-proof-complexity».RectangularSparse.check 3 1 120 140 28
    (fun z => P (z+19)) (fun z => G (z+19)) T C (fun z => H (z+19)) = true := by decide +kernel
end Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows1
