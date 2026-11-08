import Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries0
open Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC
theorem entry0 : (List.range 140).all (fun j => G 0 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[0]?.getD []))) = true := by decide +kernel
theorem entry1 : (List.range 140).all (fun j => G 1 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[1]?.getD []))) = true := by decide +kernel
theorem entry2 : (List.range 140).all (fun j => G 2 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[2]?.getD []))) = true := by decide +kernel
theorem entry3 : (List.range 140).all (fun j => G 3 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[3]?.getD []))) = true := by decide +kernel
theorem entry4 : (List.range 140).all (fun j => G 4 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[4]?.getD []))) = true := by decide +kernel
theorem entry5 : (List.range 140).all (fun j => G 5 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[5]?.getD []))) = true := by decide +kernel
theorem entry6 : (List.range 140).all (fun j => G 6 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[6]?.getD []))) = true := by decide +kernel
theorem entry7 : (List.range 140).all (fun j => G 7 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[7]?.getD []))) = true := by decide +kernel
theorem entry8 : (List.range 140).all (fun j => G 8 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[8]?.getD []))) = true := by decide +kernel
theorem entry9 : (List.range 140).all (fun j => G 9 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[9]?.getD []))) = true := by decide +kernel
end Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries0
