import Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries7
open Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC
theorem entry70 : (List.range 140).all (fun j => G 70 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[70]?.getD []))) = true := by decide +kernel
theorem entry71 : (List.range 140).all (fun j => G 71 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[71]?.getD []))) = true := by decide +kernel
theorem entry72 : (List.range 140).all (fun j => G 72 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[72]?.getD []))) = true := by decide +kernel
theorem entry73 : (List.range 140).all (fun j => G 73 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[73]?.getD []))) = true := by decide +kernel
theorem entry74 : (List.range 140).all (fun j => G 74 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[74]?.getD []))) = true := by decide +kernel
theorem entry75 : (List.range 140).all (fun j => G 75 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[75]?.getD []))) = true := by decide +kernel
theorem entry76 : (List.range 140).all (fun j => G 76 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[76]?.getD []))) = true := by decide +kernel
theorem entry77 : (List.range 140).all (fun j => G 77 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[77]?.getD []))) = true := by decide +kernel
theorem entry78 : (List.range 140).all (fun j => G 78 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[78]?.getD []))) = true := by decide +kernel
theorem entry79 : (List.range 140).all (fun j => G 79 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[79]?.getD []))) = true := by decide +kernel
end Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries7
