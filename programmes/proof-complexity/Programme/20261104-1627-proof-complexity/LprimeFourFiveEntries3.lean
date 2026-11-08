import Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries3
open Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC
theorem entry30 : (List.range 140).all (fun j => G 30 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[30]?.getD []))) = true := by decide +kernel
theorem entry31 : (List.range 140).all (fun j => G 31 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[31]?.getD []))) = true := by decide +kernel
theorem entry32 : (List.range 140).all (fun j => G 32 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[32]?.getD []))) = true := by decide +kernel
theorem entry33 : (List.range 140).all (fun j => G 33 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[33]?.getD []))) = true := by decide +kernel
theorem entry34 : (List.range 140).all (fun j => G 34 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[34]?.getD []))) = true := by decide +kernel
theorem entry35 : (List.range 140).all (fun j => G 35 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[35]?.getD []))) = true := by decide +kernel
theorem entry36 : (List.range 140).all (fun j => G 36 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[36]?.getD []))) = true := by decide +kernel
theorem entry37 : (List.range 140).all (fun j => G 37 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[37]?.getD []))) = true := by decide +kernel
theorem entry38 : (List.range 140).all (fun j => G 38 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[38]?.getD []))) = true := by decide +kernel
theorem entry39 : (List.range 140).all (fun j => G 39 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[39]?.getD []))) = true := by decide +kernel
end Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries3
