import Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries4
open Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC
theorem entry40 : (List.range 140).all (fun j => G 40 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[40]?.getD []))) = true := by decide +kernel
theorem entry41 : (List.range 140).all (fun j => G 41 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[41]?.getD []))) = true := by decide +kernel
theorem entry42 : (List.range 140).all (fun j => G 42 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[42]?.getD []))) = true := by decide +kernel
theorem entry43 : (List.range 140).all (fun j => G 43 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[43]?.getD []))) = true := by decide +kernel
theorem entry44 : (List.range 140).all (fun j => G 44 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[44]?.getD []))) = true := by decide +kernel
theorem entry45 : (List.range 140).all (fun j => G 45 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[45]?.getD []))) = true := by decide +kernel
theorem entry46 : (List.range 140).all (fun j => G 46 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[46]?.getD []))) = true := by decide +kernel
theorem entry47 : (List.range 140).all (fun j => G 47 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[47]?.getD []))) = true := by decide +kernel
theorem entry48 : (List.range 140).all (fun j => G 48 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[48]?.getD []))) = true := by decide +kernel
theorem entry49 : (List.range 140).all (fun j => G 49 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[49]?.getD []))) = true := by decide +kernel
end Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries4
