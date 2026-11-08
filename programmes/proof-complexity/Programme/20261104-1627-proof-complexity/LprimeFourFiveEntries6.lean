import Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries6
open Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC
theorem entry60 : (List.range 140).all (fun j => G 60 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[60]?.getD []))) = true := by decide +kernel
theorem entry61 : (List.range 140).all (fun j => G 61 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[61]?.getD []))) = true := by decide +kernel
theorem entry62 : (List.range 140).all (fun j => G 62 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[62]?.getD []))) = true := by decide +kernel
theorem entry63 : (List.range 140).all (fun j => G 63 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[63]?.getD []))) = true := by decide +kernel
theorem entry64 : (List.range 140).all (fun j => G 64 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[64]?.getD []))) = true := by decide +kernel
theorem entry65 : (List.range 140).all (fun j => G 65 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[65]?.getD []))) = true := by decide +kernel
theorem entry66 : (List.range 140).all (fun j => G 66 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[66]?.getD []))) = true := by decide +kernel
theorem entry67 : (List.range 140).all (fun j => G 67 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[67]?.getD []))) = true := by decide +kernel
theorem entry68 : (List.range 140).all (fun j => G 68 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[68]?.getD []))) = true := by decide +kernel
theorem entry69 : (List.range 140).all (fun j => G 69 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[69]?.getD []))) = true := by decide +kernel
end Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries6
