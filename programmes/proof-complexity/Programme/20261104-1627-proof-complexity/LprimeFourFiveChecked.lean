import Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows0
import Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries0
import Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows1
import Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries1
import Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows2
import Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries2
import Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows3
import Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries3
import Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows4
import Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries4
import Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows5
import Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries5
import Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows6
import Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries6
import Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows7
import Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries7
import Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows8
import Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries8
import Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows9
import Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries9
import Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows10
import Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries10
import Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows11
import Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries11
import Programme.«20261104-1627-proof-complexity».PivotRowAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Programme.«20261104-1627-proof-complexity».LprimeFourFiveChecked
open Programme.«20261104-1627-proof-complexity».LprimeFourFiveData
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261029-1156-proof-complexity».StdPC
open Programme.«20261104-1627-proof-complexity».RectangularSparse
open Programme.«20261104-1627-proof-complexity».RectangularReconstruction

theorem checked : Programme.«20261104-1627-proof-complexity».RectangularSparse.check
    3 120 120 140 28 P G T C H = true := by
  apply Programme.«20261104-1627-proof-complexity».PivotRowAssembly.check_of_rows
  intro i hi
  have hr : List.range 120 = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119] := by decide +kernel
  have hh := List.mem_range.mpr hi
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77 | h78 | h79 | h80 | h81 | h82 | h83 | h84 | h85 | h86 | h87 | h88 | h89 | h90 | h91 | h92 | h93 | h94 | h95 | h96 | h97 | h98 | h99 | h100 | h101 | h102 | h103 | h104 | h105 | h106 | h107 | h108 | h109 | h110 | h111 | h112 | h113 | h114 | h115 | h116 | h117 | h118 | h119
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows0.row0
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows0.row1
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows0.row2
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows0.row3
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows0.row4
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows0.row5
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows0.row6
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows0.row7
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows0.row8
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows0.row9
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows1.row10
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows1.row11
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows1.row12
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows1.row13
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows1.row14
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows1.row15
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows1.row16
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows1.row17
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows1.row18
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows1.row19
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows2.row20
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows2.row21
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows2.row22
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows2.row23
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows2.row24
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows2.row25
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows2.row26
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows2.row27
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows2.row28
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows2.row29
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows3.row30
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows3.row31
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows3.row32
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows3.row33
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows3.row34
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows3.row35
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows3.row36
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows3.row37
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows3.row38
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows3.row39
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows4.row40
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows4.row41
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows4.row42
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows4.row43
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows4.row44
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows4.row45
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows4.row46
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows4.row47
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows4.row48
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows4.row49
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows5.row50
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows5.row51
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows5.row52
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows5.row53
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows5.row54
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows5.row55
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows5.row56
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows5.row57
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows5.row58
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows5.row59
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows6.row60
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows6.row61
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows6.row62
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows6.row63
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows6.row64
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows6.row65
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows6.row66
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows6.row67
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows6.row68
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows6.row69
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows7.row70
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows7.row71
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows7.row72
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows7.row73
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows7.row74
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows7.row75
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows7.row76
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows7.row77
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows7.row78
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows7.row79
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows8.row80
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows8.row81
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows8.row82
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows8.row83
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows8.row84
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows8.row85
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows8.row86
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows8.row87
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows8.row88
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows8.row89
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows9.row90
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows9.row91
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows9.row92
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows9.row93
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows9.row94
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows9.row95
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows9.row96
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows9.row97
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows9.row98
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows9.row99
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows10.row100
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows10.row101
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows10.row102
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows10.row103
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows10.row104
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows10.row105
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows10.row106
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows10.row107
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows10.row108
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows10.row109
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows11.row110
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows11.row111
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows11.row112
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows11.row113
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows11.row114
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows11.row115
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows11.row116
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows11.row117
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows11.row118
  · subst i
    exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveRows11.row119

theorem canonical_entry (i j : Nat) (hi : i < 120) (hj : j < 140) :
    G i j = coeff (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
      (mono 5 (matchingData[i]?.getD [])) := by
  have he : (List.range 140).all (fun j => G i j == coeff
      (topLabel 4 5 (labelData[j]?.getD ⟨[],true,0⟩))
      (mono 5 (matchingData[i]?.getD []))) = true := by
    have hr : List.range 120 = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119] := by decide +kernel
    have hh := List.mem_range.mpr hi
    rw [hr] at hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77 | h78 | h79 | h80 | h81 | h82 | h83 | h84 | h85 | h86 | h87 | h88 | h89 | h90 | h91 | h92 | h93 | h94 | h95 | h96 | h97 | h98 | h99 | h100 | h101 | h102 | h103 | h104 | h105 | h106 | h107 | h108 | h109 | h110 | h111 | h112 | h113 | h114 | h115 | h116 | h117 | h118 | h119
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries0.entry0
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries0.entry1
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries0.entry2
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries0.entry3
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries0.entry4
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries0.entry5
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries0.entry6
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries0.entry7
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries0.entry8
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries0.entry9
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries1.entry10
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries1.entry11
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries1.entry12
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries1.entry13
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries1.entry14
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries1.entry15
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries1.entry16
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries1.entry17
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries1.entry18
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries1.entry19
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries2.entry20
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries2.entry21
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries2.entry22
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries2.entry23
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries2.entry24
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries2.entry25
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries2.entry26
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries2.entry27
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries2.entry28
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries2.entry29
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries3.entry30
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries3.entry31
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries3.entry32
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries3.entry33
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries3.entry34
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries3.entry35
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries3.entry36
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries3.entry37
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries3.entry38
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries3.entry39
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries4.entry40
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries4.entry41
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries4.entry42
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries4.entry43
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries4.entry44
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries4.entry45
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries4.entry46
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries4.entry47
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries4.entry48
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries4.entry49
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries5.entry50
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries5.entry51
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries5.entry52
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries5.entry53
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries5.entry54
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries5.entry55
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries5.entry56
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries5.entry57
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries5.entry58
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries5.entry59
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries6.entry60
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries6.entry61
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries6.entry62
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries6.entry63
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries6.entry64
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries6.entry65
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries6.entry66
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries6.entry67
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries6.entry68
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries6.entry69
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries7.entry70
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries7.entry71
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries7.entry72
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries7.entry73
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries7.entry74
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries7.entry75
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries7.entry76
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries7.entry77
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries7.entry78
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries7.entry79
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries8.entry80
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries8.entry81
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries8.entry82
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries8.entry83
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries8.entry84
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries8.entry85
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries8.entry86
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries8.entry87
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries8.entry88
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries8.entry89
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries9.entry90
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries9.entry91
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries9.entry92
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries9.entry93
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries9.entry94
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries9.entry95
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries9.entry96
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries9.entry97
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries9.entry98
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries9.entry99
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries10.entry100
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries10.entry101
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries10.entry102
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries10.entry103
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries10.entry104
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries10.entry105
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries10.entry106
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries10.entry107
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries10.entry108
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries10.entry109
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries11.entry110
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries11.entry111
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries11.entry112
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries11.entry113
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries11.entry114
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries11.entry115
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries11.entry116
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries11.entry117
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries11.entry118
    · subst i
      exact Programme.«20261104-1627-proof-complexity».LprimeFourFiveEntries11.entry119
  exact of_decide_eq_true (List.all_eq_true.mp he j (List.mem_range.mpr hj))

theorem reconstruct (x : Nat → Int)
    (hx : ∀ k, k < 28 → (3 : Int) ∣ dot (List.range 120) x (T k)) :
    ∀ i, i < 120 → (3 : Int) ∣ dot (List.range 120) x (P i) -
      dot (List.range 140) (G i)
        (fun k => dot (List.range 120) x (fun j => value (C j) k)) := by
  apply Programme.«20261104-1627-proof-complexity».RectangularSparse.check_sound
    P G T C H ?_ ?_ checked x hx
  · intro j hj z hz
    exact of_decide_eq_true (List.all_eq_true.mp
      (List.all_eq_true.mp boundsC j (List.mem_range.mpr hj)) z hz)
  · intro i hi z hz
    exact of_decide_eq_true (List.all_eq_true.mp
      (List.all_eq_true.mp boundsH i (List.mem_range.mpr hi)) z hz)
end Programme.«20261104-1627-proof-complexity».LprimeFourFiveChecked
#print axioms Programme.«20261104-1627-proof-complexity».LprimeFourFiveChecked.checked
#print axioms Programme.«20261104-1627-proof-complexity».LprimeFourFiveChecked.canonical_entry
#print axioms Programme.«20261104-1627-proof-complexity».LprimeFourFiveChecked.reconstruct
