import Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries9
open Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC
theorem entry90 : (List.range 140).all (fun j => G 90 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[90]?.getD []))) = true := by decide +kernel
theorem entry91 : (List.range 140).all (fun j => G 91 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[91]?.getD []))) = true := by decide +kernel
theorem entry92 : (List.range 140).all (fun j => G 92 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[92]?.getD []))) = true := by decide +kernel
theorem entry93 : (List.range 140).all (fun j => G 93 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[93]?.getD []))) = true := by decide +kernel
theorem entry94 : (List.range 140).all (fun j => G 94 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[94]?.getD []))) = true := by decide +kernel
theorem entry95 : (List.range 140).all (fun j => G 95 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[95]?.getD []))) = true := by decide +kernel
theorem entry96 : (List.range 140).all (fun j => G 96 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[96]?.getD []))) = true := by decide +kernel
theorem entry97 : (List.range 140).all (fun j => G 97 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[97]?.getD []))) = true := by decide +kernel
theorem entry98 : (List.range 140).all (fun j => G 98 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[98]?.getD []))) = true := by decide +kernel
theorem entry99 : (List.range 140).all (fun j => G 99 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[99]?.getD []))) = true := by decide +kernel
end Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries9
