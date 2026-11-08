import Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries11
open Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC
theorem entry110 : (List.range 140).all (fun j => G 110 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[110]?.getD []))) = true := by decide +kernel
theorem entry111 : (List.range 140).all (fun j => G 111 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[111]?.getD []))) = true := by decide +kernel
theorem entry112 : (List.range 140).all (fun j => G 112 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[112]?.getD []))) = true := by decide +kernel
theorem entry113 : (List.range 140).all (fun j => G 113 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[113]?.getD []))) = true := by decide +kernel
theorem entry114 : (List.range 140).all (fun j => G 114 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[114]?.getD []))) = true := by decide +kernel
theorem entry115 : (List.range 140).all (fun j => G 115 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[115]?.getD []))) = true := by decide +kernel
theorem entry116 : (List.range 140).all (fun j => G 116 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[116]?.getD []))) = true := by decide +kernel
theorem entry117 : (List.range 140).all (fun j => G 117 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[117]?.getD []))) = true := by decide +kernel
theorem entry118 : (List.range 140).all (fun j => G 118 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[118]?.getD []))) = true := by decide +kernel
theorem entry119 : (List.range 140).all (fun j => G 119 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[119]?.getD []))) = true := by decide +kernel
end Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries11
