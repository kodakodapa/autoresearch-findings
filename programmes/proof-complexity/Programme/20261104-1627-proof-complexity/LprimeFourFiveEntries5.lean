import Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries5
open Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC
theorem entry50 : (List.range 140).all (fun j => G 50 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[50]?.getD []))) = true := by decide +kernel
theorem entry51 : (List.range 140).all (fun j => G 51 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[51]?.getD []))) = true := by decide +kernel
theorem entry52 : (List.range 140).all (fun j => G 52 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[52]?.getD []))) = true := by decide +kernel
theorem entry53 : (List.range 140).all (fun j => G 53 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[53]?.getD []))) = true := by decide +kernel
theorem entry54 : (List.range 140).all (fun j => G 54 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[54]?.getD []))) = true := by decide +kernel
theorem entry55 : (List.range 140).all (fun j => G 55 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[55]?.getD []))) = true := by decide +kernel
theorem entry56 : (List.range 140).all (fun j => G 56 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[56]?.getD []))) = true := by decide +kernel
theorem entry57 : (List.range 140).all (fun j => G 57 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[57]?.getD []))) = true := by decide +kernel
theorem entry58 : (List.range 140).all (fun j => G 58 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[58]?.getD []))) = true := by decide +kernel
theorem entry59 : (List.range 140).all (fun j => G 59 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[59]?.getD []))) = true := by decide +kernel
end Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries5
