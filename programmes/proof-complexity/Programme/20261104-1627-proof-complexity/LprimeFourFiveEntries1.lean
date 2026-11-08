import Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries1
open Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC
theorem entry10 : (List.range 140).all (fun j => G 10 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[10]?.getD []))) = true := by decide +kernel
theorem entry11 : (List.range 140).all (fun j => G 11 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[11]?.getD []))) = true := by decide +kernel
theorem entry12 : (List.range 140).all (fun j => G 12 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[12]?.getD []))) = true := by decide +kernel
theorem entry13 : (List.range 140).all (fun j => G 13 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[13]?.getD []))) = true := by decide +kernel
theorem entry14 : (List.range 140).all (fun j => G 14 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[14]?.getD []))) = true := by decide +kernel
theorem entry15 : (List.range 140).all (fun j => G 15 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[15]?.getD []))) = true := by decide +kernel
theorem entry16 : (List.range 140).all (fun j => G 16 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[16]?.getD []))) = true := by decide +kernel
theorem entry17 : (List.range 140).all (fun j => G 17 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[17]?.getD []))) = true := by decide +kernel
theorem entry18 : (List.range 140).all (fun j => G 18 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[18]?.getD []))) = true := by decide +kernel
theorem entry19 : (List.range 140).all (fun j => G 19 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[19]?.getD []))) = true := by decide +kernel
end Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries1
