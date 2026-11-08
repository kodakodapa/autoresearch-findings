import Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows10
open Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
theorem row100 : Programme.«20261104-1627-proof-complexity».RectangularSparse.check 3 1 120 140 28
    (fun z => P (z+100)) (fun z => G (z+100)) T C (fun z => H (z+100)) = true := by decide +kernel
theorem row101 : Programme.«20261104-1627-proof-complexity».RectangularSparse.check 3 1 120 140 28
    (fun z => P (z+101)) (fun z => G (z+101)) T C (fun z => H (z+101)) = true := by decide +kernel
theorem row102 : Programme.«20261104-1627-proof-complexity».RectangularSparse.check 3 1 120 140 28
    (fun z => P (z+102)) (fun z => G (z+102)) T C (fun z => H (z+102)) = true := by decide +kernel
theorem row103 : Programme.«20261104-1627-proof-complexity».RectangularSparse.check 3 1 120 140 28
    (fun z => P (z+103)) (fun z => G (z+103)) T C (fun z => H (z+103)) = true := by decide +kernel
theorem row104 : Programme.«20261104-1627-proof-complexity».RectangularSparse.check 3 1 120 140 28
    (fun z => P (z+104)) (fun z => G (z+104)) T C (fun z => H (z+104)) = true := by decide +kernel
theorem row105 : Programme.«20261104-1627-proof-complexity».RectangularSparse.check 3 1 120 140 28
    (fun z => P (z+105)) (fun z => G (z+105)) T C (fun z => H (z+105)) = true := by decide +kernel
theorem row106 : Programme.«20261104-1627-proof-complexity».RectangularSparse.check 3 1 120 140 28
    (fun z => P (z+106)) (fun z => G (z+106)) T C (fun z => H (z+106)) = true := by decide +kernel
theorem row107 : Programme.«20261104-1627-proof-complexity».RectangularSparse.check 3 1 120 140 28
    (fun z => P (z+107)) (fun z => G (z+107)) T C (fun z => H (z+107)) = true := by decide +kernel
theorem row108 : Programme.«20261104-1627-proof-complexity».RectangularSparse.check 3 1 120 140 28
    (fun z => P (z+108)) (fun z => G (z+108)) T C (fun z => H (z+108)) = true := by decide +kernel
theorem row109 : Programme.«20261104-1627-proof-complexity».RectangularSparse.check 3 1 120 140 28
    (fun z => P (z+109)) (fun z => G (z+109)) T C (fun z => H (z+109)) = true := by decide +kernel
end Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows10
