import Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries8
open Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC
theorem entry80 : (List.range 140).all (fun j => G 80 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[80]?.getD []))) = true := by decide +kernel
theorem entry81 : (List.range 140).all (fun j => G 81 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[81]?.getD []))) = true := by decide +kernel
theorem entry82 : (List.range 140).all (fun j => G 82 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[82]?.getD []))) = true := by decide +kernel
theorem entry83 : (List.range 140).all (fun j => G 83 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[83]?.getD []))) = true := by decide +kernel
theorem entry84 : (List.range 140).all (fun j => G 84 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[84]?.getD []))) = true := by decide +kernel
theorem entry85 : (List.range 140).all (fun j => G 85 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[85]?.getD []))) = true := by decide +kernel
theorem entry86 : (List.range 140).all (fun j => G 86 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[86]?.getD []))) = true := by decide +kernel
theorem entry87 : (List.range 140).all (fun j => G 87 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[87]?.getD []))) = true := by decide +kernel
theorem entry88 : (List.range 140).all (fun j => G 88 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[88]?.getD []))) = true := by decide +kernel
theorem entry89 : (List.range 140).all (fun j => G 89 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[89]?.getD []))) = true := by decide +kernel
end Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries8
