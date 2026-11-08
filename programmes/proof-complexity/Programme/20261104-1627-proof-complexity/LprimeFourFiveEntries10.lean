import Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries10
open Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC
theorem entry100 : (List.range 140).all (fun j => G 100 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[100]?.getD []))) = true := by decide +kernel
theorem entry101 : (List.range 140).all (fun j => G 101 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[101]?.getD []))) = true := by decide +kernel
theorem entry102 : (List.range 140).all (fun j => G 102 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[102]?.getD []))) = true := by decide +kernel
theorem entry103 : (List.range 140).all (fun j => G 103 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[103]?.getD []))) = true := by decide +kernel
theorem entry104 : (List.range 140).all (fun j => G 104 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[104]?.getD []))) = true := by decide +kernel
theorem entry105 : (List.range 140).all (fun j => G 105 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[105]?.getD []))) = true := by decide +kernel
theorem entry106 : (List.range 140).all (fun j => G 106 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[106]?.getD []))) = true := by decide +kernel
theorem entry107 : (List.range 140).all (fun j => G 107 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[107]?.getD []))) = true := by decide +kernel
theorem entry108 : (List.range 140).all (fun j => G 108 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[108]?.getD []))) = true := by decide +kernel
theorem entry109 : (List.range 140).all (fun j => G 109 j == coeff
    (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
    (mono 5 (matchingData[109]?.getD []))) = true := by decide +kernel
end Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries10
