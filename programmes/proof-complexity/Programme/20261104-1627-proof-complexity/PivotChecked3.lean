import Programme.«20261104-1627-proof-complexity».PivotRowAssembly
import Programme.«20261104-1627-proof-complexity».PivotRow3_0
import Programme.«20261104-1627-proof-complexity».PivotRow3_1
import Programme.«20261104-1627-proof-complexity».PivotRow3_2
import Programme.«20261104-1627-proof-complexity».PivotRow3_3
import Programme.«20261104-1627-proof-complexity».PivotRow3_4
import Programme.«20261104-1627-proof-complexity».PivotRow3_5
import Programme.«20261104-1627-proof-complexity».PivotRow3_6
import Programme.«20261104-1627-proof-complexity».PivotRow3_7
import Programme.«20261104-1627-proof-complexity».PivotRow3_8
import Programme.«20261104-1627-proof-complexity».PivotRow3_9
import Programme.«20261104-1627-proof-complexity».PivotRow3_10
import Programme.«20261104-1627-proof-complexity».PivotRow3_11
import Programme.«20261104-1627-proof-complexity».PivotRow3_12
import Programme.«20261104-1627-proof-complexity».PivotRow3_13
import Programme.«20261104-1627-proof-complexity».PivotRow3_14
import Programme.«20261104-1627-proof-complexity».PivotRow3_15
import Programme.«20261104-1627-proof-complexity».PivotRow3_16
import Programme.«20261104-1627-proof-complexity».PivotRow3_17
import Programme.«20261104-1627-proof-complexity».PivotRow3_18
import Programme.«20261104-1627-proof-complexity».PivotRow3_19
import Programme.«20261104-1627-proof-complexity».PivotRow3_20
import Programme.«20261104-1627-proof-complexity».PivotRow3_21
import Programme.«20261104-1627-proof-complexity».PivotRow3_22
import Programme.«20261104-1627-proof-complexity».PivotRow3_23
import Programme.«20261104-1627-proof-complexity».PivotRow3_24
import Programme.«20261104-1627-proof-complexity».PivotRow3_25
import Programme.«20261104-1627-proof-complexity».PivotRow3_26
import Programme.«20261104-1627-proof-complexity».PivotRow3_27
import Programme.«20261104-1627-proof-complexity».PivotRow3_28
import Programme.«20261104-1627-proof-complexity».PivotRow3_29
import Programme.«20261104-1627-proof-complexity».PivotRow3_30
import Programme.«20261104-1627-proof-complexity».PivotRow3_31
import Programme.«20261104-1627-proof-complexity».PivotRow3_32
import Programme.«20261104-1627-proof-complexity».PivotRow3_33
import Programme.«20261104-1627-proof-complexity».PivotRow3_34
import Programme.«20261104-1627-proof-complexity».PivotRow3_35
import Programme.«20261104-1627-proof-complexity».PivotRow3_36
import Programme.«20261104-1627-proof-complexity».PivotRow3_37
import Programme.«20261104-1627-proof-complexity».PivotRow3_38
import Programme.«20261104-1627-proof-complexity».PivotRow3_39
import Programme.«20261104-1627-proof-complexity».PivotRow3_40
import Programme.«20261104-1627-proof-complexity».PivotRow3_41
import Programme.«20261104-1627-proof-complexity».PivotRow3_42
import Programme.«20261104-1627-proof-complexity».PivotRow3_43
import Programme.«20261104-1627-proof-complexity».PivotRow3_44
import Programme.«20261104-1627-proof-complexity».PivotRow3_45
import Programme.«20261104-1627-proof-complexity».PivotRow3_46
import Programme.«20261104-1627-proof-complexity».PivotRow3_47
import Programme.«20261104-1627-proof-complexity».PivotRow3_48
import Programme.«20261104-1627-proof-complexity».PivotRow3_49
import Programme.«20261104-1627-proof-complexity».PivotRow3_50
import Programme.«20261104-1627-proof-complexity».PivotRow3_51
import Programme.«20261104-1627-proof-complexity».PivotRow3_52
import Programme.«20261104-1627-proof-complexity».PivotRow3_53
import Programme.«20261104-1627-proof-complexity».PivotRow3_54
import Programme.«20261104-1627-proof-complexity».PivotRow3_55
import Programme.«20261104-1627-proof-complexity».PivotRow3_56
import Programme.«20261104-1627-proof-complexity».PivotRow3_57
import Programme.«20261104-1627-proof-complexity».PivotRow3_58
import Programme.«20261104-1627-proof-complexity».PivotRow3_59
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Programme.«20261104-1627-proof-complexity».PivotChecked3
open Programme.«20261104-1627-proof-complexity».PivotFiniteCertificates Programme.«20261104-1627-proof-complexity».PivotExecutable
theorem checked : Programme.«20261104-1627-proof-complexity».RectangularSparse.check 3 60 360 90 240
    (P 3 5) (g 3 5) (T 3 5) (fun j => C3[j]?.getD []) (fun i => H3[i]?.getD []) = true := by
  apply Programme.«20261104-1627-proof-complexity».PivotRowAssembly.check_of_rows
  intro i hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 := by omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_0.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_1.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_2.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_3.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_4.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_5.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_6.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_7.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_8.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_9.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_10.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_11.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_12.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_13.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_14.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_15.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_16.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_17.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_18.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_19.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_20.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_21.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_22.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_23.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_24.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_25.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_26.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_27.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_28.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_29.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_30.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_31.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_32.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_33.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_34.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_35.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_36.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_37.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_38.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_39.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_40.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_41.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_42.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_43.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_44.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_45.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_46.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_47.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_48.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_49.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_50.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_51.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_52.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_53.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_54.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_55.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_56.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_57.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_58.checked
  · subst i
    exact Programme.«20261104-1627-proof-complexity».PivotRow3_59.checked
theorem canonical_checked : Programme.«20261104-1627-proof-complexity».RectangularSparse.check 3 60 360 90 240
    (P 3 5) (G 3 5) (T 3 5) (fun j => C3[j]?.getD []) (fun i => H3[i]?.getD []) = true := by
  have he : g 3 5 = G 3 5 := funext fun i => funext fun k => g_eq 3 5 i k
  rw [← he]
  exact checked
#print axioms canonical_checked
end Programme.«20261104-1627-proof-complexity».PivotChecked3
