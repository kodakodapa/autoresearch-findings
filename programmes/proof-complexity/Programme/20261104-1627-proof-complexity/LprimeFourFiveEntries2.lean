import Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries2
open Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC
theorem entry20 : (List.range 140).all (fun j => G 20 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[20]?.getD []))) = true := by decide +kernel
theorem entry21 : (List.range 140).all (fun j => G 21 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[21]?.getD []))) = true := by decide +kernel
theorem entry22 : (List.range 140).all (fun j => G 22 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[22]?.getD []))) = true := by decide +kernel
theorem entry23 : (List.range 140).all (fun j => G 23 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[23]?.getD []))) = true := by decide +kernel
theorem entry24 : (List.range 140).all (fun j => G 24 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[24]?.getD []))) = true := by decide +kernel
theorem entry25 : (List.range 140).all (fun j => G 25 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[25]?.getD []))) = true := by decide +kernel
theorem entry26 : (List.range 140).all (fun j => G 26 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[26]?.getD []))) = true := by decide +kernel
theorem entry27 : (List.range 140).all (fun j => G 27 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[27]?.getD []))) = true := by decide +kernel
theorem entry28 : (List.range 140).all (fun j => G 28 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[28]?.getD []))) = true := by decide +kernel
theorem entry29 : (List.range 140).all (fun j => G 29 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[29]?.getD []))) = true := by decide +kernel
end Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries2
