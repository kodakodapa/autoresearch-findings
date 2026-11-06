import Programme.«20261028-0841-proof-complexity».L3.F0
import Programme.«20261028-0841-proof-complexity».L3.F1
import Programme.«20261028-0841-proof-complexity».L3.F2
import Programme.«20261028-0841-proof-complexity».L3.F3
import Programme.«20261028-0841-proof-complexity».L3.F4
import Programme.«20261028-0841-proof-complexity».L3.F5
import Programme.«20261028-0841-proof-complexity».L3.F6
import Programme.«20261028-0841-proof-complexity».L3.F7
import Programme.«20261028-0841-proof-complexity».L3.F8
import Programme.«20261028-0841-proof-complexity».L3.F9
import Programme.«20261028-0841-proof-complexity».L3.F10
import Programme.«20261028-0841-proof-complexity».L3.F11
import Programme.«20261028-0841-proof-complexity».L3.F12
import Programme.«20261028-0841-proof-complexity».L3.F13
import Programme.«20261028-0841-proof-complexity».L3.F14
import Programme.«20261028-0841-proof-complexity».L3.F15
import Programme.«20261028-0841-proof-complexity».L3.F16
import Programme.«20261028-0841-proof-complexity».L3.F17
import Programme.«20261028-0841-proof-complexity».L3.F18
import Programme.«20261028-0841-proof-complexity».L3.F19
import Programme.«20261028-0841-proof-complexity».L3.F20
import Programme.«20261028-0841-proof-complexity».L3.F21
import Programme.«20261028-0841-proof-complexity».L3.F22
import Programme.«20261028-0841-proof-complexity».L3.F23
import Programme.«20261028-0841-proof-complexity».L3.F24
import Programme.«20261028-0841-proof-complexity».L3.F25
import Programme.«20261028-0841-proof-complexity».L3.F26
import Programme.«20261028-0841-proof-complexity».L3.F27
import Programme.«20261028-0841-proof-complexity».L3.F28
import Programme.«20261028-0841-proof-complexity».L3.F29
import Programme.«20261028-0841-proof-complexity».L3.F30
import Programme.«20261028-0841-proof-complexity».L3.F31
import Programme.«20261028-0841-proof-complexity».L3.F32
import Programme.«20261028-0841-proof-complexity».L3.F33
import Programme.«20261028-0841-proof-complexity».L3.F34
import Programme.«20261028-0841-proof-complexity».L3.F35
import Programme.«20261028-0841-proof-complexity».L3.F36
import Programme.«20261028-0841-proof-complexity».L3.F37
import Programme.«20261028-0841-proof-complexity».L3.F38
import Programme.«20261028-0841-proof-complexity».L3.F39
import Programme.«20261028-0841-proof-complexity».L3.F40
import Programme.«20261028-0841-proof-complexity».L3.F41
import Programme.«20261028-0841-proof-complexity».L3.F42
import Programme.«20261028-0841-proof-complexity».L3.F43
import Programme.«20261028-0841-proof-complexity».L3.F44
import Programme.«20261028-0841-proof-complexity».L3.F45
import Programme.«20261028-0841-proof-complexity».L3.F46
import Programme.«20261028-0841-proof-complexity».L3.F47
import Programme.«20261028-0841-proof-complexity».L3.F48
import Programme.«20261028-0841-proof-complexity».L3.F49
import Programme.«20261028-0841-proof-complexity».L3.F50
import Programme.«20261028-0841-proof-complexity».L3.F51
import Programme.«20261028-0841-proof-complexity».L3.F52
import Programme.«20261028-0841-proof-complexity».L3.F53
import Programme.«20261028-0841-proof-complexity».L3.F54
import Programme.«20261028-0841-proof-complexity».L3.F55
import Programme.«20261028-0841-proof-complexity».L3.F56
import Programme.«20261028-0841-proof-complexity».L3.F57
import Programme.«20261028-0841-proof-complexity».L3.F58
import Programme.«20261028-0841-proof-complexity».L3.F59
import Programme.«20261028-0841-proof-complexity».L3.F60
import Programme.«20261028-0841-proof-complexity».L3.F61
import Programme.«20261028-0841-proof-complexity».L3.F62
import Programme.«20261028-0841-proof-complexity».L3.F63
import Programme.«20261028-0841-proof-complexity».L3.F64
import Programme.«20261028-0841-proof-complexity».L3.F65
import Programme.«20261028-0841-proof-complexity».L3.F66
import Programme.«20261028-0841-proof-complexity».L3.F67
import Programme.«20261028-0841-proof-complexity».L3.F68
import Programme.«20261028-0841-proof-complexity».L3.F69
import Programme.«20261028-0841-proof-complexity».L3.F70
import Programme.«20261028-0841-proof-complexity».L3.F71
import Programme.«20261028-0841-proof-complexity».L3.F72
import Programme.«20261028-0841-proof-complexity».L3.F73
import Programme.«20261028-0841-proof-complexity».L3.F74
import Programme.«20261028-0841-proof-complexity».L3.F75
import Programme.«20261028-0841-proof-complexity».L3.F76
import Programme.«20261028-0841-proof-complexity».L3.F77
import Programme.«20261028-0841-proof-complexity».L3.F78
import Programme.«20261028-0841-proof-complexity».L3.F79
import Programme.«20261028-0841-proof-complexity».L3.F80
import Programme.«20261028-0841-proof-complexity».L3.F81
import Programme.«20261028-0841-proof-complexity».L3.F82
import Programme.«20261028-0841-proof-complexity».L3.F83
import Programme.«20261028-0841-proof-complexity».L3.F84
import Programme.«20261028-0841-proof-complexity».L3.F85
import Programme.«20261028-0841-proof-complexity».L3.F86
import Programme.«20261028-0841-proof-complexity».L3.F87
import Programme.«20261028-0841-proof-complexity».L3.F88
import Programme.«20261028-0841-proof-complexity».L3.F89
import Programme.«20261028-0841-proof-complexity».L3.Cov

/-! Discharge of `Ext278d.hard_of_run` (run 1434 K13) with the level-3 certificate in files F0..F89. -/

namespace Programme.«20261028-0841-proof-complexity».L3.Main
open Programme.«20261027-1434-proof-complexity».Peel3
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261026-1402-proof-complexity».ExtLemma

def ssAll : List Step3 := (Programme.«20261028-0841-proof-complexity».L3.F0.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F1.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F2.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F3.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F4.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F5.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F6.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F7.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F8.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F9.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F10.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F11.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F12.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F13.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F14.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F15.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F16.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F17.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F18.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F19.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F20.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F21.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F22.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F23.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F24.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F25.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F26.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F27.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F28.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F29.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F30.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F31.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F32.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F33.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F34.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F35.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F36.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F37.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F38.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F39.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F40.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F41.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F42.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F43.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F44.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F45.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F46.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F47.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F48.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F49.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F50.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F51.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F52.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F53.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F54.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F55.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F56.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F57.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F58.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F59.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F60.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F61.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F62.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F63.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F64.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F65.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F66.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F67.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F68.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F69.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F70.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F71.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F72.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F73.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F74.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F75.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F76.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F77.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F78.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F79.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F80.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F81.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F82.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F83.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F84.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F85.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F86.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F87.ss ++ (Programme.«20261028-0841-proof-complexity».L3.F88.ss ++ Programme.«20261028-0841-proof-complexity».L3.F89.ss)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem lk0 : run3 0 Programme.«20261028-0841-proof-complexity».L3.F0.ss = some Programme.«20261028-0841-proof-complexity».L3.F0.Pout := Programme.«20261028-0841-proof-complexity».L3.F0.r
theorem lk1 : run3 Programme.«20261028-0841-proof-complexity».L3.F0.Pout Programme.«20261028-0841-proof-complexity».L3.F1.ss = some Programme.«20261028-0841-proof-complexity».L3.F1.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F0.Pout = Programme.«20261028-0841-proof-complexity».L3.F1.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F1.r
theorem lk2 : run3 Programme.«20261028-0841-proof-complexity».L3.F1.Pout Programme.«20261028-0841-proof-complexity».L3.F2.ss = some Programme.«20261028-0841-proof-complexity».L3.F2.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F1.Pout = Programme.«20261028-0841-proof-complexity».L3.F2.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F2.r
theorem lk3 : run3 Programme.«20261028-0841-proof-complexity».L3.F2.Pout Programme.«20261028-0841-proof-complexity».L3.F3.ss = some Programme.«20261028-0841-proof-complexity».L3.F3.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F2.Pout = Programme.«20261028-0841-proof-complexity».L3.F3.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F3.r
theorem lk4 : run3 Programme.«20261028-0841-proof-complexity».L3.F3.Pout Programme.«20261028-0841-proof-complexity».L3.F4.ss = some Programme.«20261028-0841-proof-complexity».L3.F4.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F3.Pout = Programme.«20261028-0841-proof-complexity».L3.F4.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F4.r
theorem lk5 : run3 Programme.«20261028-0841-proof-complexity».L3.F4.Pout Programme.«20261028-0841-proof-complexity».L3.F5.ss = some Programme.«20261028-0841-proof-complexity».L3.F5.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F4.Pout = Programme.«20261028-0841-proof-complexity».L3.F5.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F5.r
theorem lk6 : run3 Programme.«20261028-0841-proof-complexity».L3.F5.Pout Programme.«20261028-0841-proof-complexity».L3.F6.ss = some Programme.«20261028-0841-proof-complexity».L3.F6.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F5.Pout = Programme.«20261028-0841-proof-complexity».L3.F6.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F6.r
theorem lk7 : run3 Programme.«20261028-0841-proof-complexity».L3.F6.Pout Programme.«20261028-0841-proof-complexity».L3.F7.ss = some Programme.«20261028-0841-proof-complexity».L3.F7.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F6.Pout = Programme.«20261028-0841-proof-complexity».L3.F7.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F7.r
theorem lk8 : run3 Programme.«20261028-0841-proof-complexity».L3.F7.Pout Programme.«20261028-0841-proof-complexity».L3.F8.ss = some Programme.«20261028-0841-proof-complexity».L3.F8.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F7.Pout = Programme.«20261028-0841-proof-complexity».L3.F8.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F8.r
theorem lk9 : run3 Programme.«20261028-0841-proof-complexity».L3.F8.Pout Programme.«20261028-0841-proof-complexity».L3.F9.ss = some Programme.«20261028-0841-proof-complexity».L3.F9.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F8.Pout = Programme.«20261028-0841-proof-complexity».L3.F9.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F9.r
theorem lk10 : run3 Programme.«20261028-0841-proof-complexity».L3.F9.Pout Programme.«20261028-0841-proof-complexity».L3.F10.ss = some Programme.«20261028-0841-proof-complexity».L3.F10.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F9.Pout = Programme.«20261028-0841-proof-complexity».L3.F10.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F10.r
theorem lk11 : run3 Programme.«20261028-0841-proof-complexity».L3.F10.Pout Programme.«20261028-0841-proof-complexity».L3.F11.ss = some Programme.«20261028-0841-proof-complexity».L3.F11.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F10.Pout = Programme.«20261028-0841-proof-complexity».L3.F11.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F11.r
theorem lk12 : run3 Programme.«20261028-0841-proof-complexity».L3.F11.Pout Programme.«20261028-0841-proof-complexity».L3.F12.ss = some Programme.«20261028-0841-proof-complexity».L3.F12.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F11.Pout = Programme.«20261028-0841-proof-complexity».L3.F12.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F12.r
theorem lk13 : run3 Programme.«20261028-0841-proof-complexity».L3.F12.Pout Programme.«20261028-0841-proof-complexity».L3.F13.ss = some Programme.«20261028-0841-proof-complexity».L3.F13.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F12.Pout = Programme.«20261028-0841-proof-complexity».L3.F13.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F13.r
theorem lk14 : run3 Programme.«20261028-0841-proof-complexity».L3.F13.Pout Programme.«20261028-0841-proof-complexity».L3.F14.ss = some Programme.«20261028-0841-proof-complexity».L3.F14.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F13.Pout = Programme.«20261028-0841-proof-complexity».L3.F14.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F14.r
theorem lk15 : run3 Programme.«20261028-0841-proof-complexity».L3.F14.Pout Programme.«20261028-0841-proof-complexity».L3.F15.ss = some Programme.«20261028-0841-proof-complexity».L3.F15.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F14.Pout = Programme.«20261028-0841-proof-complexity».L3.F15.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F15.r
theorem lk16 : run3 Programme.«20261028-0841-proof-complexity».L3.F15.Pout Programme.«20261028-0841-proof-complexity».L3.F16.ss = some Programme.«20261028-0841-proof-complexity».L3.F16.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F15.Pout = Programme.«20261028-0841-proof-complexity».L3.F16.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F16.r
theorem lk17 : run3 Programme.«20261028-0841-proof-complexity».L3.F16.Pout Programme.«20261028-0841-proof-complexity».L3.F17.ss = some Programme.«20261028-0841-proof-complexity».L3.F17.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F16.Pout = Programme.«20261028-0841-proof-complexity».L3.F17.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F17.r
theorem lk18 : run3 Programme.«20261028-0841-proof-complexity».L3.F17.Pout Programme.«20261028-0841-proof-complexity».L3.F18.ss = some Programme.«20261028-0841-proof-complexity».L3.F18.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F17.Pout = Programme.«20261028-0841-proof-complexity».L3.F18.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F18.r
theorem lk19 : run3 Programme.«20261028-0841-proof-complexity».L3.F18.Pout Programme.«20261028-0841-proof-complexity».L3.F19.ss = some Programme.«20261028-0841-proof-complexity».L3.F19.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F18.Pout = Programme.«20261028-0841-proof-complexity».L3.F19.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F19.r
theorem lk20 : run3 Programme.«20261028-0841-proof-complexity».L3.F19.Pout Programme.«20261028-0841-proof-complexity».L3.F20.ss = some Programme.«20261028-0841-proof-complexity».L3.F20.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F19.Pout = Programme.«20261028-0841-proof-complexity».L3.F20.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F20.r
theorem lk21 : run3 Programme.«20261028-0841-proof-complexity».L3.F20.Pout Programme.«20261028-0841-proof-complexity».L3.F21.ss = some Programme.«20261028-0841-proof-complexity».L3.F21.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F20.Pout = Programme.«20261028-0841-proof-complexity».L3.F21.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F21.r
theorem lk22 : run3 Programme.«20261028-0841-proof-complexity».L3.F21.Pout Programme.«20261028-0841-proof-complexity».L3.F22.ss = some Programme.«20261028-0841-proof-complexity».L3.F22.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F21.Pout = Programme.«20261028-0841-proof-complexity».L3.F22.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F22.r
theorem lk23 : run3 Programme.«20261028-0841-proof-complexity».L3.F22.Pout Programme.«20261028-0841-proof-complexity».L3.F23.ss = some Programme.«20261028-0841-proof-complexity».L3.F23.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F22.Pout = Programme.«20261028-0841-proof-complexity».L3.F23.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F23.r
theorem lk24 : run3 Programme.«20261028-0841-proof-complexity».L3.F23.Pout Programme.«20261028-0841-proof-complexity».L3.F24.ss = some Programme.«20261028-0841-proof-complexity».L3.F24.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F23.Pout = Programme.«20261028-0841-proof-complexity».L3.F24.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F24.r
theorem lk25 : run3 Programme.«20261028-0841-proof-complexity».L3.F24.Pout Programme.«20261028-0841-proof-complexity».L3.F25.ss = some Programme.«20261028-0841-proof-complexity».L3.F25.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F24.Pout = Programme.«20261028-0841-proof-complexity».L3.F25.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F25.r
theorem lk26 : run3 Programme.«20261028-0841-proof-complexity».L3.F25.Pout Programme.«20261028-0841-proof-complexity».L3.F26.ss = some Programme.«20261028-0841-proof-complexity».L3.F26.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F25.Pout = Programme.«20261028-0841-proof-complexity».L3.F26.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F26.r
theorem lk27 : run3 Programme.«20261028-0841-proof-complexity».L3.F26.Pout Programme.«20261028-0841-proof-complexity».L3.F27.ss = some Programme.«20261028-0841-proof-complexity».L3.F27.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F26.Pout = Programme.«20261028-0841-proof-complexity».L3.F27.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F27.r
theorem lk28 : run3 Programme.«20261028-0841-proof-complexity».L3.F27.Pout Programme.«20261028-0841-proof-complexity».L3.F28.ss = some Programme.«20261028-0841-proof-complexity».L3.F28.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F27.Pout = Programme.«20261028-0841-proof-complexity».L3.F28.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F28.r
theorem lk29 : run3 Programme.«20261028-0841-proof-complexity».L3.F28.Pout Programme.«20261028-0841-proof-complexity».L3.F29.ss = some Programme.«20261028-0841-proof-complexity».L3.F29.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F28.Pout = Programme.«20261028-0841-proof-complexity».L3.F29.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F29.r
theorem lk30 : run3 Programme.«20261028-0841-proof-complexity».L3.F29.Pout Programme.«20261028-0841-proof-complexity».L3.F30.ss = some Programme.«20261028-0841-proof-complexity».L3.F30.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F29.Pout = Programme.«20261028-0841-proof-complexity».L3.F30.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F30.r
theorem lk31 : run3 Programme.«20261028-0841-proof-complexity».L3.F30.Pout Programme.«20261028-0841-proof-complexity».L3.F31.ss = some Programme.«20261028-0841-proof-complexity».L3.F31.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F30.Pout = Programme.«20261028-0841-proof-complexity».L3.F31.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F31.r
theorem lk32 : run3 Programme.«20261028-0841-proof-complexity».L3.F31.Pout Programme.«20261028-0841-proof-complexity».L3.F32.ss = some Programme.«20261028-0841-proof-complexity».L3.F32.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F31.Pout = Programme.«20261028-0841-proof-complexity».L3.F32.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F32.r
theorem lk33 : run3 Programme.«20261028-0841-proof-complexity».L3.F32.Pout Programme.«20261028-0841-proof-complexity».L3.F33.ss = some Programme.«20261028-0841-proof-complexity».L3.F33.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F32.Pout = Programme.«20261028-0841-proof-complexity».L3.F33.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F33.r
theorem lk34 : run3 Programme.«20261028-0841-proof-complexity».L3.F33.Pout Programme.«20261028-0841-proof-complexity».L3.F34.ss = some Programme.«20261028-0841-proof-complexity».L3.F34.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F33.Pout = Programme.«20261028-0841-proof-complexity».L3.F34.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F34.r
theorem lk35 : run3 Programme.«20261028-0841-proof-complexity».L3.F34.Pout Programme.«20261028-0841-proof-complexity».L3.F35.ss = some Programme.«20261028-0841-proof-complexity».L3.F35.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F34.Pout = Programme.«20261028-0841-proof-complexity».L3.F35.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F35.r
theorem lk36 : run3 Programme.«20261028-0841-proof-complexity».L3.F35.Pout Programme.«20261028-0841-proof-complexity».L3.F36.ss = some Programme.«20261028-0841-proof-complexity».L3.F36.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F35.Pout = Programme.«20261028-0841-proof-complexity».L3.F36.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F36.r
theorem lk37 : run3 Programme.«20261028-0841-proof-complexity».L3.F36.Pout Programme.«20261028-0841-proof-complexity».L3.F37.ss = some Programme.«20261028-0841-proof-complexity».L3.F37.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F36.Pout = Programme.«20261028-0841-proof-complexity».L3.F37.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F37.r
theorem lk38 : run3 Programme.«20261028-0841-proof-complexity».L3.F37.Pout Programme.«20261028-0841-proof-complexity».L3.F38.ss = some Programme.«20261028-0841-proof-complexity».L3.F38.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F37.Pout = Programme.«20261028-0841-proof-complexity».L3.F38.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F38.r
theorem lk39 : run3 Programme.«20261028-0841-proof-complexity».L3.F38.Pout Programme.«20261028-0841-proof-complexity».L3.F39.ss = some Programme.«20261028-0841-proof-complexity».L3.F39.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F38.Pout = Programme.«20261028-0841-proof-complexity».L3.F39.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F39.r
theorem lk40 : run3 Programme.«20261028-0841-proof-complexity».L3.F39.Pout Programme.«20261028-0841-proof-complexity».L3.F40.ss = some Programme.«20261028-0841-proof-complexity».L3.F40.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F39.Pout = Programme.«20261028-0841-proof-complexity».L3.F40.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F40.r
theorem lk41 : run3 Programme.«20261028-0841-proof-complexity».L3.F40.Pout Programme.«20261028-0841-proof-complexity».L3.F41.ss = some Programme.«20261028-0841-proof-complexity».L3.F41.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F40.Pout = Programme.«20261028-0841-proof-complexity».L3.F41.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F41.r
theorem lk42 : run3 Programme.«20261028-0841-proof-complexity».L3.F41.Pout Programme.«20261028-0841-proof-complexity».L3.F42.ss = some Programme.«20261028-0841-proof-complexity».L3.F42.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F41.Pout = Programme.«20261028-0841-proof-complexity».L3.F42.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F42.r
theorem lk43 : run3 Programme.«20261028-0841-proof-complexity».L3.F42.Pout Programme.«20261028-0841-proof-complexity».L3.F43.ss = some Programme.«20261028-0841-proof-complexity».L3.F43.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F42.Pout = Programme.«20261028-0841-proof-complexity».L3.F43.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F43.r
theorem lk44 : run3 Programme.«20261028-0841-proof-complexity».L3.F43.Pout Programme.«20261028-0841-proof-complexity».L3.F44.ss = some Programme.«20261028-0841-proof-complexity».L3.F44.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F43.Pout = Programme.«20261028-0841-proof-complexity».L3.F44.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F44.r
theorem lk45 : run3 Programme.«20261028-0841-proof-complexity».L3.F44.Pout Programme.«20261028-0841-proof-complexity».L3.F45.ss = some Programme.«20261028-0841-proof-complexity».L3.F45.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F44.Pout = Programme.«20261028-0841-proof-complexity».L3.F45.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F45.r
theorem lk46 : run3 Programme.«20261028-0841-proof-complexity».L3.F45.Pout Programme.«20261028-0841-proof-complexity».L3.F46.ss = some Programme.«20261028-0841-proof-complexity».L3.F46.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F45.Pout = Programme.«20261028-0841-proof-complexity».L3.F46.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F46.r
theorem lk47 : run3 Programme.«20261028-0841-proof-complexity».L3.F46.Pout Programme.«20261028-0841-proof-complexity».L3.F47.ss = some Programme.«20261028-0841-proof-complexity».L3.F47.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F46.Pout = Programme.«20261028-0841-proof-complexity».L3.F47.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F47.r
theorem lk48 : run3 Programme.«20261028-0841-proof-complexity».L3.F47.Pout Programme.«20261028-0841-proof-complexity».L3.F48.ss = some Programme.«20261028-0841-proof-complexity».L3.F48.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F47.Pout = Programme.«20261028-0841-proof-complexity».L3.F48.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F48.r
theorem lk49 : run3 Programme.«20261028-0841-proof-complexity».L3.F48.Pout Programme.«20261028-0841-proof-complexity».L3.F49.ss = some Programme.«20261028-0841-proof-complexity».L3.F49.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F48.Pout = Programme.«20261028-0841-proof-complexity».L3.F49.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F49.r
theorem lk50 : run3 Programme.«20261028-0841-proof-complexity».L3.F49.Pout Programme.«20261028-0841-proof-complexity».L3.F50.ss = some Programme.«20261028-0841-proof-complexity».L3.F50.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F49.Pout = Programme.«20261028-0841-proof-complexity».L3.F50.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F50.r
theorem lk51 : run3 Programme.«20261028-0841-proof-complexity».L3.F50.Pout Programme.«20261028-0841-proof-complexity».L3.F51.ss = some Programme.«20261028-0841-proof-complexity».L3.F51.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F50.Pout = Programme.«20261028-0841-proof-complexity».L3.F51.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F51.r
theorem lk52 : run3 Programme.«20261028-0841-proof-complexity».L3.F51.Pout Programme.«20261028-0841-proof-complexity».L3.F52.ss = some Programme.«20261028-0841-proof-complexity».L3.F52.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F51.Pout = Programme.«20261028-0841-proof-complexity».L3.F52.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F52.r
theorem lk53 : run3 Programme.«20261028-0841-proof-complexity».L3.F52.Pout Programme.«20261028-0841-proof-complexity».L3.F53.ss = some Programme.«20261028-0841-proof-complexity».L3.F53.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F52.Pout = Programme.«20261028-0841-proof-complexity».L3.F53.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F53.r
theorem lk54 : run3 Programme.«20261028-0841-proof-complexity».L3.F53.Pout Programme.«20261028-0841-proof-complexity».L3.F54.ss = some Programme.«20261028-0841-proof-complexity».L3.F54.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F53.Pout = Programme.«20261028-0841-proof-complexity».L3.F54.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F54.r
theorem lk55 : run3 Programme.«20261028-0841-proof-complexity».L3.F54.Pout Programme.«20261028-0841-proof-complexity».L3.F55.ss = some Programme.«20261028-0841-proof-complexity».L3.F55.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F54.Pout = Programme.«20261028-0841-proof-complexity».L3.F55.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F55.r
theorem lk56 : run3 Programme.«20261028-0841-proof-complexity».L3.F55.Pout Programme.«20261028-0841-proof-complexity».L3.F56.ss = some Programme.«20261028-0841-proof-complexity».L3.F56.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F55.Pout = Programme.«20261028-0841-proof-complexity».L3.F56.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F56.r
theorem lk57 : run3 Programme.«20261028-0841-proof-complexity».L3.F56.Pout Programme.«20261028-0841-proof-complexity».L3.F57.ss = some Programme.«20261028-0841-proof-complexity».L3.F57.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F56.Pout = Programme.«20261028-0841-proof-complexity».L3.F57.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F57.r
theorem lk58 : run3 Programme.«20261028-0841-proof-complexity».L3.F57.Pout Programme.«20261028-0841-proof-complexity».L3.F58.ss = some Programme.«20261028-0841-proof-complexity».L3.F58.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F57.Pout = Programme.«20261028-0841-proof-complexity».L3.F58.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F58.r
theorem lk59 : run3 Programme.«20261028-0841-proof-complexity».L3.F58.Pout Programme.«20261028-0841-proof-complexity».L3.F59.ss = some Programme.«20261028-0841-proof-complexity».L3.F59.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F58.Pout = Programme.«20261028-0841-proof-complexity».L3.F59.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F59.r
theorem lk60 : run3 Programme.«20261028-0841-proof-complexity».L3.F59.Pout Programme.«20261028-0841-proof-complexity».L3.F60.ss = some Programme.«20261028-0841-proof-complexity».L3.F60.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F59.Pout = Programme.«20261028-0841-proof-complexity».L3.F60.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F60.r
theorem lk61 : run3 Programme.«20261028-0841-proof-complexity».L3.F60.Pout Programme.«20261028-0841-proof-complexity».L3.F61.ss = some Programme.«20261028-0841-proof-complexity».L3.F61.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F60.Pout = Programme.«20261028-0841-proof-complexity».L3.F61.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F61.r
theorem lk62 : run3 Programme.«20261028-0841-proof-complexity».L3.F61.Pout Programme.«20261028-0841-proof-complexity».L3.F62.ss = some Programme.«20261028-0841-proof-complexity».L3.F62.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F61.Pout = Programme.«20261028-0841-proof-complexity».L3.F62.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F62.r
theorem lk63 : run3 Programme.«20261028-0841-proof-complexity».L3.F62.Pout Programme.«20261028-0841-proof-complexity».L3.F63.ss = some Programme.«20261028-0841-proof-complexity».L3.F63.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F62.Pout = Programme.«20261028-0841-proof-complexity».L3.F63.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F63.r
theorem lk64 : run3 Programme.«20261028-0841-proof-complexity».L3.F63.Pout Programme.«20261028-0841-proof-complexity».L3.F64.ss = some Programme.«20261028-0841-proof-complexity».L3.F64.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F63.Pout = Programme.«20261028-0841-proof-complexity».L3.F64.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F64.r
theorem lk65 : run3 Programme.«20261028-0841-proof-complexity».L3.F64.Pout Programme.«20261028-0841-proof-complexity».L3.F65.ss = some Programme.«20261028-0841-proof-complexity».L3.F65.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F64.Pout = Programme.«20261028-0841-proof-complexity».L3.F65.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F65.r
theorem lk66 : run3 Programme.«20261028-0841-proof-complexity».L3.F65.Pout Programme.«20261028-0841-proof-complexity».L3.F66.ss = some Programme.«20261028-0841-proof-complexity».L3.F66.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F65.Pout = Programme.«20261028-0841-proof-complexity».L3.F66.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F66.r
theorem lk67 : run3 Programme.«20261028-0841-proof-complexity».L3.F66.Pout Programme.«20261028-0841-proof-complexity».L3.F67.ss = some Programme.«20261028-0841-proof-complexity».L3.F67.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F66.Pout = Programme.«20261028-0841-proof-complexity».L3.F67.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F67.r
theorem lk68 : run3 Programme.«20261028-0841-proof-complexity».L3.F67.Pout Programme.«20261028-0841-proof-complexity».L3.F68.ss = some Programme.«20261028-0841-proof-complexity».L3.F68.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F67.Pout = Programme.«20261028-0841-proof-complexity».L3.F68.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F68.r
theorem lk69 : run3 Programme.«20261028-0841-proof-complexity».L3.F68.Pout Programme.«20261028-0841-proof-complexity».L3.F69.ss = some Programme.«20261028-0841-proof-complexity».L3.F69.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F68.Pout = Programme.«20261028-0841-proof-complexity».L3.F69.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F69.r
theorem lk70 : run3 Programme.«20261028-0841-proof-complexity».L3.F69.Pout Programme.«20261028-0841-proof-complexity».L3.F70.ss = some Programme.«20261028-0841-proof-complexity».L3.F70.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F69.Pout = Programme.«20261028-0841-proof-complexity».L3.F70.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F70.r
theorem lk71 : run3 Programme.«20261028-0841-proof-complexity».L3.F70.Pout Programme.«20261028-0841-proof-complexity».L3.F71.ss = some Programme.«20261028-0841-proof-complexity».L3.F71.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F70.Pout = Programme.«20261028-0841-proof-complexity».L3.F71.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F71.r
theorem lk72 : run3 Programme.«20261028-0841-proof-complexity».L3.F71.Pout Programme.«20261028-0841-proof-complexity».L3.F72.ss = some Programme.«20261028-0841-proof-complexity».L3.F72.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F71.Pout = Programme.«20261028-0841-proof-complexity».L3.F72.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F72.r
theorem lk73 : run3 Programme.«20261028-0841-proof-complexity».L3.F72.Pout Programme.«20261028-0841-proof-complexity».L3.F73.ss = some Programme.«20261028-0841-proof-complexity».L3.F73.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F72.Pout = Programme.«20261028-0841-proof-complexity».L3.F73.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F73.r
theorem lk74 : run3 Programme.«20261028-0841-proof-complexity».L3.F73.Pout Programme.«20261028-0841-proof-complexity».L3.F74.ss = some Programme.«20261028-0841-proof-complexity».L3.F74.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F73.Pout = Programme.«20261028-0841-proof-complexity».L3.F74.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F74.r
theorem lk75 : run3 Programme.«20261028-0841-proof-complexity».L3.F74.Pout Programme.«20261028-0841-proof-complexity».L3.F75.ss = some Programme.«20261028-0841-proof-complexity».L3.F75.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F74.Pout = Programme.«20261028-0841-proof-complexity».L3.F75.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F75.r
theorem lk76 : run3 Programme.«20261028-0841-proof-complexity».L3.F75.Pout Programme.«20261028-0841-proof-complexity».L3.F76.ss = some Programme.«20261028-0841-proof-complexity».L3.F76.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F75.Pout = Programme.«20261028-0841-proof-complexity».L3.F76.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F76.r
theorem lk77 : run3 Programme.«20261028-0841-proof-complexity».L3.F76.Pout Programme.«20261028-0841-proof-complexity».L3.F77.ss = some Programme.«20261028-0841-proof-complexity».L3.F77.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F76.Pout = Programme.«20261028-0841-proof-complexity».L3.F77.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F77.r
theorem lk78 : run3 Programme.«20261028-0841-proof-complexity».L3.F77.Pout Programme.«20261028-0841-proof-complexity».L3.F78.ss = some Programme.«20261028-0841-proof-complexity».L3.F78.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F77.Pout = Programme.«20261028-0841-proof-complexity».L3.F78.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F78.r
theorem lk79 : run3 Programme.«20261028-0841-proof-complexity».L3.F78.Pout Programme.«20261028-0841-proof-complexity».L3.F79.ss = some Programme.«20261028-0841-proof-complexity».L3.F79.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F78.Pout = Programme.«20261028-0841-proof-complexity».L3.F79.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F79.r
theorem lk80 : run3 Programme.«20261028-0841-proof-complexity».L3.F79.Pout Programme.«20261028-0841-proof-complexity».L3.F80.ss = some Programme.«20261028-0841-proof-complexity».L3.F80.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F79.Pout = Programme.«20261028-0841-proof-complexity».L3.F80.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F80.r
theorem lk81 : run3 Programme.«20261028-0841-proof-complexity».L3.F80.Pout Programme.«20261028-0841-proof-complexity».L3.F81.ss = some Programme.«20261028-0841-proof-complexity».L3.F81.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F80.Pout = Programme.«20261028-0841-proof-complexity».L3.F81.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F81.r
theorem lk82 : run3 Programme.«20261028-0841-proof-complexity».L3.F81.Pout Programme.«20261028-0841-proof-complexity».L3.F82.ss = some Programme.«20261028-0841-proof-complexity».L3.F82.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F81.Pout = Programme.«20261028-0841-proof-complexity».L3.F82.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F82.r
theorem lk83 : run3 Programme.«20261028-0841-proof-complexity».L3.F82.Pout Programme.«20261028-0841-proof-complexity».L3.F83.ss = some Programme.«20261028-0841-proof-complexity».L3.F83.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F82.Pout = Programme.«20261028-0841-proof-complexity».L3.F83.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F83.r
theorem lk84 : run3 Programme.«20261028-0841-proof-complexity».L3.F83.Pout Programme.«20261028-0841-proof-complexity».L3.F84.ss = some Programme.«20261028-0841-proof-complexity».L3.F84.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F83.Pout = Programme.«20261028-0841-proof-complexity».L3.F84.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F84.r
theorem lk85 : run3 Programme.«20261028-0841-proof-complexity».L3.F84.Pout Programme.«20261028-0841-proof-complexity».L3.F85.ss = some Programme.«20261028-0841-proof-complexity».L3.F85.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F84.Pout = Programme.«20261028-0841-proof-complexity».L3.F85.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F85.r
theorem lk86 : run3 Programme.«20261028-0841-proof-complexity».L3.F85.Pout Programme.«20261028-0841-proof-complexity».L3.F86.ss = some Programme.«20261028-0841-proof-complexity».L3.F86.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F85.Pout = Programme.«20261028-0841-proof-complexity».L3.F86.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F86.r
theorem lk87 : run3 Programme.«20261028-0841-proof-complexity».L3.F86.Pout Programme.«20261028-0841-proof-complexity».L3.F87.ss = some Programme.«20261028-0841-proof-complexity».L3.F87.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F86.Pout = Programme.«20261028-0841-proof-complexity».L3.F87.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F87.r
theorem lk88 : run3 Programme.«20261028-0841-proof-complexity».L3.F87.Pout Programme.«20261028-0841-proof-complexity».L3.F88.ss = some Programme.«20261028-0841-proof-complexity».L3.F88.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F87.Pout = Programme.«20261028-0841-proof-complexity».L3.F88.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F88.r
theorem lk89 : run3 Programme.«20261028-0841-proof-complexity».L3.F88.Pout Programme.«20261028-0841-proof-complexity».L3.F89.ss = some Programme.«20261028-0841-proof-complexity».L3.F89.Pout := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F88.Pout = Programme.«20261028-0841-proof-complexity».L3.F89.Pin by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.F89.r

theorem run_all : run3 0 ssAll = some Programme.«20261028-0841-proof-complexity».L3.F89.Pout := by
  unfold ssAll
  exact (run3_append _ lk0 (run3_append _ lk1 (run3_append _ lk2 (run3_append _ lk3 (run3_append _ lk4 (run3_append _ lk5 (run3_append _ lk6 (run3_append _ lk7 (run3_append _ lk8 (run3_append _ lk9 (run3_append _ lk10 (run3_append _ lk11 (run3_append _ lk12 (run3_append _ lk13 (run3_append _ lk14 (run3_append _ lk15 (run3_append _ lk16 (run3_append _ lk17 (run3_append _ lk18 (run3_append _ lk19 (run3_append _ lk20 (run3_append _ lk21 (run3_append _ lk22 (run3_append _ lk23 (run3_append _ lk24 (run3_append _ lk25 (run3_append _ lk26 (run3_append _ lk27 (run3_append _ lk28 (run3_append _ lk29 (run3_append _ lk30 (run3_append _ lk31 (run3_append _ lk32 (run3_append _ lk33 (run3_append _ lk34 (run3_append _ lk35 (run3_append _ lk36 (run3_append _ lk37 (run3_append _ lk38 (run3_append _ lk39 (run3_append _ lk40 (run3_append _ lk41 (run3_append _ lk42 (run3_append _ lk43 (run3_append _ lk44 (run3_append _ lk45 (run3_append _ lk46 (run3_append _ lk47 (run3_append _ lk48 (run3_append _ lk49 (run3_append _ lk50 (run3_append _ lk51 (run3_append _ lk52 (run3_append _ lk53 (run3_append _ lk54 (run3_append _ lk55 (run3_append _ lk56 (run3_append _ lk57 (run3_append _ lk58 (run3_append _ lk59 (run3_append _ lk60 (run3_append _ lk61 (run3_append _ lk62 (run3_append _ lk63 (run3_append _ lk64 (run3_append _ lk65 (run3_append _ lk66 (run3_append _ lk67 (run3_append _ lk68 (run3_append _ lk69 (run3_append _ lk70 (run3_append _ lk71 (run3_append _ lk72 (run3_append _ lk73 (run3_append _ lk74 (run3_append _ lk75 (run3_append _ lk76 (run3_append _ lk77 (run3_append _ lk78 (run3_append _ lk79 (run3_append _ lk80 (run3_append _ lk81 (run3_append _ lk82 (run3_append _ lk83 (run3_append _ lk84 (run3_append _ lk85 (run3_append _ lk86 (run3_append _ lk87 (run3_append _ lk88 lk89)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem cov_all : ∀ a < 105, covA Programme.«20261028-0841-proof-complexity».L3.F89.Pout a = true := by
  rw [show Programme.«20261028-0841-proof-complexity».L3.F89.Pout = Programme.«20261028-0841-proof-complexity».L3.Cov.Pf by decide +kernel]; exact Programme.«20261028-0841-proof-complexity».L3.Cov.cov

/-- **No degree-4 PC refutation of onto-FPHP^(n+8)_n over Z/2 for n ≥ 7.** -/
theorem no_deg4 (n : Nat) (hn : 7 ≤ n) : ¬ PPCRefutation 2 (ontoFPHP n 8) 4 :=
  Programme.«20261027-1434-proof-complexity».Ext278d.hard_of_run ssAll _ run_all cov_all n hn

end Programme.«20261028-0841-proof-complexity».L3.Main

#print axioms Programme.«20261028-0841-proof-complexity».L3.Main.no_deg4
