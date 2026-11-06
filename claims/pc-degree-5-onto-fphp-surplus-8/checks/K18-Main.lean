import Work.L3.F0
import Work.L3.F1
import Work.L3.F2
import Work.L3.F3
import Work.L3.F4
import Work.L3.F5
import Work.L3.F6
import Work.L3.F7
import Work.L3.F8
import Work.L3.F9
import Work.L3.F10
import Work.L3.F11
import Work.L3.F12
import Work.L3.F13
import Work.L3.F14
import Work.L3.F15
import Work.L3.F16
import Work.L3.F17
import Work.L3.F18
import Work.L3.F19
import Work.L3.F20
import Work.L3.F21
import Work.L3.F22
import Work.L3.F23
import Work.L3.F24
import Work.L3.F25
import Work.L3.F26
import Work.L3.F27
import Work.L3.F28
import Work.L3.F29
import Work.L3.F30
import Work.L3.F31
import Work.L3.F32
import Work.L3.F33
import Work.L3.F34
import Work.L3.F35
import Work.L3.F36
import Work.L3.F37
import Work.L3.F38
import Work.L3.F39
import Work.L3.F40
import Work.L3.F41
import Work.L3.F42
import Work.L3.F43
import Work.L3.F44
import Work.L3.F45
import Work.L3.F46
import Work.L3.F47
import Work.L3.F48
import Work.L3.F49
import Work.L3.F50
import Work.L3.F51
import Work.L3.F52
import Work.L3.F53
import Work.L3.F54
import Work.L3.F55
import Work.L3.F56
import Work.L3.F57
import Work.L3.F58
import Work.L3.F59
import Work.L3.F60
import Work.L3.F61
import Work.L3.F62
import Work.L3.F63
import Work.L3.F64
import Work.L3.F65
import Work.L3.F66
import Work.L3.F67
import Work.L3.F68
import Work.L3.F69
import Work.L3.F70
import Work.L3.F71
import Work.L3.F72
import Work.L3.F73
import Work.L3.F74
import Work.L3.F75
import Work.L3.F76
import Work.L3.F77
import Work.L3.F78
import Work.L3.F79
import Work.L3.F80
import Work.L3.F81
import Work.L3.F82
import Work.L3.F83
import Work.L3.F84
import Work.L3.F85
import Work.L3.F86
import Work.L3.F87
import Work.L3.F88
import Work.L3.F89
import Work.L3.Cov

/-! Discharge of `Ext278d.hard_of_run` (run 1434 K13) with the level-3 certificate in files F0..F89. -/

namespace Work.L3.Main
open Programme.«20261027-1434-proof-complexity».Peel3
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261026-1402-proof-complexity».ExtLemma

def ssAll : List Step3 := (Work.L3.F0.ss ++ (Work.L3.F1.ss ++ (Work.L3.F2.ss ++ (Work.L3.F3.ss ++ (Work.L3.F4.ss ++ (Work.L3.F5.ss ++ (Work.L3.F6.ss ++ (Work.L3.F7.ss ++ (Work.L3.F8.ss ++ (Work.L3.F9.ss ++ (Work.L3.F10.ss ++ (Work.L3.F11.ss ++ (Work.L3.F12.ss ++ (Work.L3.F13.ss ++ (Work.L3.F14.ss ++ (Work.L3.F15.ss ++ (Work.L3.F16.ss ++ (Work.L3.F17.ss ++ (Work.L3.F18.ss ++ (Work.L3.F19.ss ++ (Work.L3.F20.ss ++ (Work.L3.F21.ss ++ (Work.L3.F22.ss ++ (Work.L3.F23.ss ++ (Work.L3.F24.ss ++ (Work.L3.F25.ss ++ (Work.L3.F26.ss ++ (Work.L3.F27.ss ++ (Work.L3.F28.ss ++ (Work.L3.F29.ss ++ (Work.L3.F30.ss ++ (Work.L3.F31.ss ++ (Work.L3.F32.ss ++ (Work.L3.F33.ss ++ (Work.L3.F34.ss ++ (Work.L3.F35.ss ++ (Work.L3.F36.ss ++ (Work.L3.F37.ss ++ (Work.L3.F38.ss ++ (Work.L3.F39.ss ++ (Work.L3.F40.ss ++ (Work.L3.F41.ss ++ (Work.L3.F42.ss ++ (Work.L3.F43.ss ++ (Work.L3.F44.ss ++ (Work.L3.F45.ss ++ (Work.L3.F46.ss ++ (Work.L3.F47.ss ++ (Work.L3.F48.ss ++ (Work.L3.F49.ss ++ (Work.L3.F50.ss ++ (Work.L3.F51.ss ++ (Work.L3.F52.ss ++ (Work.L3.F53.ss ++ (Work.L3.F54.ss ++ (Work.L3.F55.ss ++ (Work.L3.F56.ss ++ (Work.L3.F57.ss ++ (Work.L3.F58.ss ++ (Work.L3.F59.ss ++ (Work.L3.F60.ss ++ (Work.L3.F61.ss ++ (Work.L3.F62.ss ++ (Work.L3.F63.ss ++ (Work.L3.F64.ss ++ (Work.L3.F65.ss ++ (Work.L3.F66.ss ++ (Work.L3.F67.ss ++ (Work.L3.F68.ss ++ (Work.L3.F69.ss ++ (Work.L3.F70.ss ++ (Work.L3.F71.ss ++ (Work.L3.F72.ss ++ (Work.L3.F73.ss ++ (Work.L3.F74.ss ++ (Work.L3.F75.ss ++ (Work.L3.F76.ss ++ (Work.L3.F77.ss ++ (Work.L3.F78.ss ++ (Work.L3.F79.ss ++ (Work.L3.F80.ss ++ (Work.L3.F81.ss ++ (Work.L3.F82.ss ++ (Work.L3.F83.ss ++ (Work.L3.F84.ss ++ (Work.L3.F85.ss ++ (Work.L3.F86.ss ++ (Work.L3.F87.ss ++ (Work.L3.F88.ss ++ Work.L3.F89.ss)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem lk0 : run3 0 Work.L3.F0.ss = some Work.L3.F0.Pout := Work.L3.F0.r
theorem lk1 : run3 Work.L3.F0.Pout Work.L3.F1.ss = some Work.L3.F1.Pout := by
  rw [show Work.L3.F0.Pout = Work.L3.F1.Pin by decide +kernel]; exact Work.L3.F1.r
theorem lk2 : run3 Work.L3.F1.Pout Work.L3.F2.ss = some Work.L3.F2.Pout := by
  rw [show Work.L3.F1.Pout = Work.L3.F2.Pin by decide +kernel]; exact Work.L3.F2.r
theorem lk3 : run3 Work.L3.F2.Pout Work.L3.F3.ss = some Work.L3.F3.Pout := by
  rw [show Work.L3.F2.Pout = Work.L3.F3.Pin by decide +kernel]; exact Work.L3.F3.r
theorem lk4 : run3 Work.L3.F3.Pout Work.L3.F4.ss = some Work.L3.F4.Pout := by
  rw [show Work.L3.F3.Pout = Work.L3.F4.Pin by decide +kernel]; exact Work.L3.F4.r
theorem lk5 : run3 Work.L3.F4.Pout Work.L3.F5.ss = some Work.L3.F5.Pout := by
  rw [show Work.L3.F4.Pout = Work.L3.F5.Pin by decide +kernel]; exact Work.L3.F5.r
theorem lk6 : run3 Work.L3.F5.Pout Work.L3.F6.ss = some Work.L3.F6.Pout := by
  rw [show Work.L3.F5.Pout = Work.L3.F6.Pin by decide +kernel]; exact Work.L3.F6.r
theorem lk7 : run3 Work.L3.F6.Pout Work.L3.F7.ss = some Work.L3.F7.Pout := by
  rw [show Work.L3.F6.Pout = Work.L3.F7.Pin by decide +kernel]; exact Work.L3.F7.r
theorem lk8 : run3 Work.L3.F7.Pout Work.L3.F8.ss = some Work.L3.F8.Pout := by
  rw [show Work.L3.F7.Pout = Work.L3.F8.Pin by decide +kernel]; exact Work.L3.F8.r
theorem lk9 : run3 Work.L3.F8.Pout Work.L3.F9.ss = some Work.L3.F9.Pout := by
  rw [show Work.L3.F8.Pout = Work.L3.F9.Pin by decide +kernel]; exact Work.L3.F9.r
theorem lk10 : run3 Work.L3.F9.Pout Work.L3.F10.ss = some Work.L3.F10.Pout := by
  rw [show Work.L3.F9.Pout = Work.L3.F10.Pin by decide +kernel]; exact Work.L3.F10.r
theorem lk11 : run3 Work.L3.F10.Pout Work.L3.F11.ss = some Work.L3.F11.Pout := by
  rw [show Work.L3.F10.Pout = Work.L3.F11.Pin by decide +kernel]; exact Work.L3.F11.r
theorem lk12 : run3 Work.L3.F11.Pout Work.L3.F12.ss = some Work.L3.F12.Pout := by
  rw [show Work.L3.F11.Pout = Work.L3.F12.Pin by decide +kernel]; exact Work.L3.F12.r
theorem lk13 : run3 Work.L3.F12.Pout Work.L3.F13.ss = some Work.L3.F13.Pout := by
  rw [show Work.L3.F12.Pout = Work.L3.F13.Pin by decide +kernel]; exact Work.L3.F13.r
theorem lk14 : run3 Work.L3.F13.Pout Work.L3.F14.ss = some Work.L3.F14.Pout := by
  rw [show Work.L3.F13.Pout = Work.L3.F14.Pin by decide +kernel]; exact Work.L3.F14.r
theorem lk15 : run3 Work.L3.F14.Pout Work.L3.F15.ss = some Work.L3.F15.Pout := by
  rw [show Work.L3.F14.Pout = Work.L3.F15.Pin by decide +kernel]; exact Work.L3.F15.r
theorem lk16 : run3 Work.L3.F15.Pout Work.L3.F16.ss = some Work.L3.F16.Pout := by
  rw [show Work.L3.F15.Pout = Work.L3.F16.Pin by decide +kernel]; exact Work.L3.F16.r
theorem lk17 : run3 Work.L3.F16.Pout Work.L3.F17.ss = some Work.L3.F17.Pout := by
  rw [show Work.L3.F16.Pout = Work.L3.F17.Pin by decide +kernel]; exact Work.L3.F17.r
theorem lk18 : run3 Work.L3.F17.Pout Work.L3.F18.ss = some Work.L3.F18.Pout := by
  rw [show Work.L3.F17.Pout = Work.L3.F18.Pin by decide +kernel]; exact Work.L3.F18.r
theorem lk19 : run3 Work.L3.F18.Pout Work.L3.F19.ss = some Work.L3.F19.Pout := by
  rw [show Work.L3.F18.Pout = Work.L3.F19.Pin by decide +kernel]; exact Work.L3.F19.r
theorem lk20 : run3 Work.L3.F19.Pout Work.L3.F20.ss = some Work.L3.F20.Pout := by
  rw [show Work.L3.F19.Pout = Work.L3.F20.Pin by decide +kernel]; exact Work.L3.F20.r
theorem lk21 : run3 Work.L3.F20.Pout Work.L3.F21.ss = some Work.L3.F21.Pout := by
  rw [show Work.L3.F20.Pout = Work.L3.F21.Pin by decide +kernel]; exact Work.L3.F21.r
theorem lk22 : run3 Work.L3.F21.Pout Work.L3.F22.ss = some Work.L3.F22.Pout := by
  rw [show Work.L3.F21.Pout = Work.L3.F22.Pin by decide +kernel]; exact Work.L3.F22.r
theorem lk23 : run3 Work.L3.F22.Pout Work.L3.F23.ss = some Work.L3.F23.Pout := by
  rw [show Work.L3.F22.Pout = Work.L3.F23.Pin by decide +kernel]; exact Work.L3.F23.r
theorem lk24 : run3 Work.L3.F23.Pout Work.L3.F24.ss = some Work.L3.F24.Pout := by
  rw [show Work.L3.F23.Pout = Work.L3.F24.Pin by decide +kernel]; exact Work.L3.F24.r
theorem lk25 : run3 Work.L3.F24.Pout Work.L3.F25.ss = some Work.L3.F25.Pout := by
  rw [show Work.L3.F24.Pout = Work.L3.F25.Pin by decide +kernel]; exact Work.L3.F25.r
theorem lk26 : run3 Work.L3.F25.Pout Work.L3.F26.ss = some Work.L3.F26.Pout := by
  rw [show Work.L3.F25.Pout = Work.L3.F26.Pin by decide +kernel]; exact Work.L3.F26.r
theorem lk27 : run3 Work.L3.F26.Pout Work.L3.F27.ss = some Work.L3.F27.Pout := by
  rw [show Work.L3.F26.Pout = Work.L3.F27.Pin by decide +kernel]; exact Work.L3.F27.r
theorem lk28 : run3 Work.L3.F27.Pout Work.L3.F28.ss = some Work.L3.F28.Pout := by
  rw [show Work.L3.F27.Pout = Work.L3.F28.Pin by decide +kernel]; exact Work.L3.F28.r
theorem lk29 : run3 Work.L3.F28.Pout Work.L3.F29.ss = some Work.L3.F29.Pout := by
  rw [show Work.L3.F28.Pout = Work.L3.F29.Pin by decide +kernel]; exact Work.L3.F29.r
theorem lk30 : run3 Work.L3.F29.Pout Work.L3.F30.ss = some Work.L3.F30.Pout := by
  rw [show Work.L3.F29.Pout = Work.L3.F30.Pin by decide +kernel]; exact Work.L3.F30.r
theorem lk31 : run3 Work.L3.F30.Pout Work.L3.F31.ss = some Work.L3.F31.Pout := by
  rw [show Work.L3.F30.Pout = Work.L3.F31.Pin by decide +kernel]; exact Work.L3.F31.r
theorem lk32 : run3 Work.L3.F31.Pout Work.L3.F32.ss = some Work.L3.F32.Pout := by
  rw [show Work.L3.F31.Pout = Work.L3.F32.Pin by decide +kernel]; exact Work.L3.F32.r
theorem lk33 : run3 Work.L3.F32.Pout Work.L3.F33.ss = some Work.L3.F33.Pout := by
  rw [show Work.L3.F32.Pout = Work.L3.F33.Pin by decide +kernel]; exact Work.L3.F33.r
theorem lk34 : run3 Work.L3.F33.Pout Work.L3.F34.ss = some Work.L3.F34.Pout := by
  rw [show Work.L3.F33.Pout = Work.L3.F34.Pin by decide +kernel]; exact Work.L3.F34.r
theorem lk35 : run3 Work.L3.F34.Pout Work.L3.F35.ss = some Work.L3.F35.Pout := by
  rw [show Work.L3.F34.Pout = Work.L3.F35.Pin by decide +kernel]; exact Work.L3.F35.r
theorem lk36 : run3 Work.L3.F35.Pout Work.L3.F36.ss = some Work.L3.F36.Pout := by
  rw [show Work.L3.F35.Pout = Work.L3.F36.Pin by decide +kernel]; exact Work.L3.F36.r
theorem lk37 : run3 Work.L3.F36.Pout Work.L3.F37.ss = some Work.L3.F37.Pout := by
  rw [show Work.L3.F36.Pout = Work.L3.F37.Pin by decide +kernel]; exact Work.L3.F37.r
theorem lk38 : run3 Work.L3.F37.Pout Work.L3.F38.ss = some Work.L3.F38.Pout := by
  rw [show Work.L3.F37.Pout = Work.L3.F38.Pin by decide +kernel]; exact Work.L3.F38.r
theorem lk39 : run3 Work.L3.F38.Pout Work.L3.F39.ss = some Work.L3.F39.Pout := by
  rw [show Work.L3.F38.Pout = Work.L3.F39.Pin by decide +kernel]; exact Work.L3.F39.r
theorem lk40 : run3 Work.L3.F39.Pout Work.L3.F40.ss = some Work.L3.F40.Pout := by
  rw [show Work.L3.F39.Pout = Work.L3.F40.Pin by decide +kernel]; exact Work.L3.F40.r
theorem lk41 : run3 Work.L3.F40.Pout Work.L3.F41.ss = some Work.L3.F41.Pout := by
  rw [show Work.L3.F40.Pout = Work.L3.F41.Pin by decide +kernel]; exact Work.L3.F41.r
theorem lk42 : run3 Work.L3.F41.Pout Work.L3.F42.ss = some Work.L3.F42.Pout := by
  rw [show Work.L3.F41.Pout = Work.L3.F42.Pin by decide +kernel]; exact Work.L3.F42.r
theorem lk43 : run3 Work.L3.F42.Pout Work.L3.F43.ss = some Work.L3.F43.Pout := by
  rw [show Work.L3.F42.Pout = Work.L3.F43.Pin by decide +kernel]; exact Work.L3.F43.r
theorem lk44 : run3 Work.L3.F43.Pout Work.L3.F44.ss = some Work.L3.F44.Pout := by
  rw [show Work.L3.F43.Pout = Work.L3.F44.Pin by decide +kernel]; exact Work.L3.F44.r
theorem lk45 : run3 Work.L3.F44.Pout Work.L3.F45.ss = some Work.L3.F45.Pout := by
  rw [show Work.L3.F44.Pout = Work.L3.F45.Pin by decide +kernel]; exact Work.L3.F45.r
theorem lk46 : run3 Work.L3.F45.Pout Work.L3.F46.ss = some Work.L3.F46.Pout := by
  rw [show Work.L3.F45.Pout = Work.L3.F46.Pin by decide +kernel]; exact Work.L3.F46.r
theorem lk47 : run3 Work.L3.F46.Pout Work.L3.F47.ss = some Work.L3.F47.Pout := by
  rw [show Work.L3.F46.Pout = Work.L3.F47.Pin by decide +kernel]; exact Work.L3.F47.r
theorem lk48 : run3 Work.L3.F47.Pout Work.L3.F48.ss = some Work.L3.F48.Pout := by
  rw [show Work.L3.F47.Pout = Work.L3.F48.Pin by decide +kernel]; exact Work.L3.F48.r
theorem lk49 : run3 Work.L3.F48.Pout Work.L3.F49.ss = some Work.L3.F49.Pout := by
  rw [show Work.L3.F48.Pout = Work.L3.F49.Pin by decide +kernel]; exact Work.L3.F49.r
theorem lk50 : run3 Work.L3.F49.Pout Work.L3.F50.ss = some Work.L3.F50.Pout := by
  rw [show Work.L3.F49.Pout = Work.L3.F50.Pin by decide +kernel]; exact Work.L3.F50.r
theorem lk51 : run3 Work.L3.F50.Pout Work.L3.F51.ss = some Work.L3.F51.Pout := by
  rw [show Work.L3.F50.Pout = Work.L3.F51.Pin by decide +kernel]; exact Work.L3.F51.r
theorem lk52 : run3 Work.L3.F51.Pout Work.L3.F52.ss = some Work.L3.F52.Pout := by
  rw [show Work.L3.F51.Pout = Work.L3.F52.Pin by decide +kernel]; exact Work.L3.F52.r
theorem lk53 : run3 Work.L3.F52.Pout Work.L3.F53.ss = some Work.L3.F53.Pout := by
  rw [show Work.L3.F52.Pout = Work.L3.F53.Pin by decide +kernel]; exact Work.L3.F53.r
theorem lk54 : run3 Work.L3.F53.Pout Work.L3.F54.ss = some Work.L3.F54.Pout := by
  rw [show Work.L3.F53.Pout = Work.L3.F54.Pin by decide +kernel]; exact Work.L3.F54.r
theorem lk55 : run3 Work.L3.F54.Pout Work.L3.F55.ss = some Work.L3.F55.Pout := by
  rw [show Work.L3.F54.Pout = Work.L3.F55.Pin by decide +kernel]; exact Work.L3.F55.r
theorem lk56 : run3 Work.L3.F55.Pout Work.L3.F56.ss = some Work.L3.F56.Pout := by
  rw [show Work.L3.F55.Pout = Work.L3.F56.Pin by decide +kernel]; exact Work.L3.F56.r
theorem lk57 : run3 Work.L3.F56.Pout Work.L3.F57.ss = some Work.L3.F57.Pout := by
  rw [show Work.L3.F56.Pout = Work.L3.F57.Pin by decide +kernel]; exact Work.L3.F57.r
theorem lk58 : run3 Work.L3.F57.Pout Work.L3.F58.ss = some Work.L3.F58.Pout := by
  rw [show Work.L3.F57.Pout = Work.L3.F58.Pin by decide +kernel]; exact Work.L3.F58.r
theorem lk59 : run3 Work.L3.F58.Pout Work.L3.F59.ss = some Work.L3.F59.Pout := by
  rw [show Work.L3.F58.Pout = Work.L3.F59.Pin by decide +kernel]; exact Work.L3.F59.r
theorem lk60 : run3 Work.L3.F59.Pout Work.L3.F60.ss = some Work.L3.F60.Pout := by
  rw [show Work.L3.F59.Pout = Work.L3.F60.Pin by decide +kernel]; exact Work.L3.F60.r
theorem lk61 : run3 Work.L3.F60.Pout Work.L3.F61.ss = some Work.L3.F61.Pout := by
  rw [show Work.L3.F60.Pout = Work.L3.F61.Pin by decide +kernel]; exact Work.L3.F61.r
theorem lk62 : run3 Work.L3.F61.Pout Work.L3.F62.ss = some Work.L3.F62.Pout := by
  rw [show Work.L3.F61.Pout = Work.L3.F62.Pin by decide +kernel]; exact Work.L3.F62.r
theorem lk63 : run3 Work.L3.F62.Pout Work.L3.F63.ss = some Work.L3.F63.Pout := by
  rw [show Work.L3.F62.Pout = Work.L3.F63.Pin by decide +kernel]; exact Work.L3.F63.r
theorem lk64 : run3 Work.L3.F63.Pout Work.L3.F64.ss = some Work.L3.F64.Pout := by
  rw [show Work.L3.F63.Pout = Work.L3.F64.Pin by decide +kernel]; exact Work.L3.F64.r
theorem lk65 : run3 Work.L3.F64.Pout Work.L3.F65.ss = some Work.L3.F65.Pout := by
  rw [show Work.L3.F64.Pout = Work.L3.F65.Pin by decide +kernel]; exact Work.L3.F65.r
theorem lk66 : run3 Work.L3.F65.Pout Work.L3.F66.ss = some Work.L3.F66.Pout := by
  rw [show Work.L3.F65.Pout = Work.L3.F66.Pin by decide +kernel]; exact Work.L3.F66.r
theorem lk67 : run3 Work.L3.F66.Pout Work.L3.F67.ss = some Work.L3.F67.Pout := by
  rw [show Work.L3.F66.Pout = Work.L3.F67.Pin by decide +kernel]; exact Work.L3.F67.r
theorem lk68 : run3 Work.L3.F67.Pout Work.L3.F68.ss = some Work.L3.F68.Pout := by
  rw [show Work.L3.F67.Pout = Work.L3.F68.Pin by decide +kernel]; exact Work.L3.F68.r
theorem lk69 : run3 Work.L3.F68.Pout Work.L3.F69.ss = some Work.L3.F69.Pout := by
  rw [show Work.L3.F68.Pout = Work.L3.F69.Pin by decide +kernel]; exact Work.L3.F69.r
theorem lk70 : run3 Work.L3.F69.Pout Work.L3.F70.ss = some Work.L3.F70.Pout := by
  rw [show Work.L3.F69.Pout = Work.L3.F70.Pin by decide +kernel]; exact Work.L3.F70.r
theorem lk71 : run3 Work.L3.F70.Pout Work.L3.F71.ss = some Work.L3.F71.Pout := by
  rw [show Work.L3.F70.Pout = Work.L3.F71.Pin by decide +kernel]; exact Work.L3.F71.r
theorem lk72 : run3 Work.L3.F71.Pout Work.L3.F72.ss = some Work.L3.F72.Pout := by
  rw [show Work.L3.F71.Pout = Work.L3.F72.Pin by decide +kernel]; exact Work.L3.F72.r
theorem lk73 : run3 Work.L3.F72.Pout Work.L3.F73.ss = some Work.L3.F73.Pout := by
  rw [show Work.L3.F72.Pout = Work.L3.F73.Pin by decide +kernel]; exact Work.L3.F73.r
theorem lk74 : run3 Work.L3.F73.Pout Work.L3.F74.ss = some Work.L3.F74.Pout := by
  rw [show Work.L3.F73.Pout = Work.L3.F74.Pin by decide +kernel]; exact Work.L3.F74.r
theorem lk75 : run3 Work.L3.F74.Pout Work.L3.F75.ss = some Work.L3.F75.Pout := by
  rw [show Work.L3.F74.Pout = Work.L3.F75.Pin by decide +kernel]; exact Work.L3.F75.r
theorem lk76 : run3 Work.L3.F75.Pout Work.L3.F76.ss = some Work.L3.F76.Pout := by
  rw [show Work.L3.F75.Pout = Work.L3.F76.Pin by decide +kernel]; exact Work.L3.F76.r
theorem lk77 : run3 Work.L3.F76.Pout Work.L3.F77.ss = some Work.L3.F77.Pout := by
  rw [show Work.L3.F76.Pout = Work.L3.F77.Pin by decide +kernel]; exact Work.L3.F77.r
theorem lk78 : run3 Work.L3.F77.Pout Work.L3.F78.ss = some Work.L3.F78.Pout := by
  rw [show Work.L3.F77.Pout = Work.L3.F78.Pin by decide +kernel]; exact Work.L3.F78.r
theorem lk79 : run3 Work.L3.F78.Pout Work.L3.F79.ss = some Work.L3.F79.Pout := by
  rw [show Work.L3.F78.Pout = Work.L3.F79.Pin by decide +kernel]; exact Work.L3.F79.r
theorem lk80 : run3 Work.L3.F79.Pout Work.L3.F80.ss = some Work.L3.F80.Pout := by
  rw [show Work.L3.F79.Pout = Work.L3.F80.Pin by decide +kernel]; exact Work.L3.F80.r
theorem lk81 : run3 Work.L3.F80.Pout Work.L3.F81.ss = some Work.L3.F81.Pout := by
  rw [show Work.L3.F80.Pout = Work.L3.F81.Pin by decide +kernel]; exact Work.L3.F81.r
theorem lk82 : run3 Work.L3.F81.Pout Work.L3.F82.ss = some Work.L3.F82.Pout := by
  rw [show Work.L3.F81.Pout = Work.L3.F82.Pin by decide +kernel]; exact Work.L3.F82.r
theorem lk83 : run3 Work.L3.F82.Pout Work.L3.F83.ss = some Work.L3.F83.Pout := by
  rw [show Work.L3.F82.Pout = Work.L3.F83.Pin by decide +kernel]; exact Work.L3.F83.r
theorem lk84 : run3 Work.L3.F83.Pout Work.L3.F84.ss = some Work.L3.F84.Pout := by
  rw [show Work.L3.F83.Pout = Work.L3.F84.Pin by decide +kernel]; exact Work.L3.F84.r
theorem lk85 : run3 Work.L3.F84.Pout Work.L3.F85.ss = some Work.L3.F85.Pout := by
  rw [show Work.L3.F84.Pout = Work.L3.F85.Pin by decide +kernel]; exact Work.L3.F85.r
theorem lk86 : run3 Work.L3.F85.Pout Work.L3.F86.ss = some Work.L3.F86.Pout := by
  rw [show Work.L3.F85.Pout = Work.L3.F86.Pin by decide +kernel]; exact Work.L3.F86.r
theorem lk87 : run3 Work.L3.F86.Pout Work.L3.F87.ss = some Work.L3.F87.Pout := by
  rw [show Work.L3.F86.Pout = Work.L3.F87.Pin by decide +kernel]; exact Work.L3.F87.r
theorem lk88 : run3 Work.L3.F87.Pout Work.L3.F88.ss = some Work.L3.F88.Pout := by
  rw [show Work.L3.F87.Pout = Work.L3.F88.Pin by decide +kernel]; exact Work.L3.F88.r
theorem lk89 : run3 Work.L3.F88.Pout Work.L3.F89.ss = some Work.L3.F89.Pout := by
  rw [show Work.L3.F88.Pout = Work.L3.F89.Pin by decide +kernel]; exact Work.L3.F89.r

theorem run_all : run3 0 ssAll = some Work.L3.F89.Pout := by
  unfold ssAll
  exact (run3_append _ lk0 (run3_append _ lk1 (run3_append _ lk2 (run3_append _ lk3 (run3_append _ lk4 (run3_append _ lk5 (run3_append _ lk6 (run3_append _ lk7 (run3_append _ lk8 (run3_append _ lk9 (run3_append _ lk10 (run3_append _ lk11 (run3_append _ lk12 (run3_append _ lk13 (run3_append _ lk14 (run3_append _ lk15 (run3_append _ lk16 (run3_append _ lk17 (run3_append _ lk18 (run3_append _ lk19 (run3_append _ lk20 (run3_append _ lk21 (run3_append _ lk22 (run3_append _ lk23 (run3_append _ lk24 (run3_append _ lk25 (run3_append _ lk26 (run3_append _ lk27 (run3_append _ lk28 (run3_append _ lk29 (run3_append _ lk30 (run3_append _ lk31 (run3_append _ lk32 (run3_append _ lk33 (run3_append _ lk34 (run3_append _ lk35 (run3_append _ lk36 (run3_append _ lk37 (run3_append _ lk38 (run3_append _ lk39 (run3_append _ lk40 (run3_append _ lk41 (run3_append _ lk42 (run3_append _ lk43 (run3_append _ lk44 (run3_append _ lk45 (run3_append _ lk46 (run3_append _ lk47 (run3_append _ lk48 (run3_append _ lk49 (run3_append _ lk50 (run3_append _ lk51 (run3_append _ lk52 (run3_append _ lk53 (run3_append _ lk54 (run3_append _ lk55 (run3_append _ lk56 (run3_append _ lk57 (run3_append _ lk58 (run3_append _ lk59 (run3_append _ lk60 (run3_append _ lk61 (run3_append _ lk62 (run3_append _ lk63 (run3_append _ lk64 (run3_append _ lk65 (run3_append _ lk66 (run3_append _ lk67 (run3_append _ lk68 (run3_append _ lk69 (run3_append _ lk70 (run3_append _ lk71 (run3_append _ lk72 (run3_append _ lk73 (run3_append _ lk74 (run3_append _ lk75 (run3_append _ lk76 (run3_append _ lk77 (run3_append _ lk78 (run3_append _ lk79 (run3_append _ lk80 (run3_append _ lk81 (run3_append _ lk82 (run3_append _ lk83 (run3_append _ lk84 (run3_append _ lk85 (run3_append _ lk86 (run3_append _ lk87 (run3_append _ lk88 lk89)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem cov_all : ∀ a < 105, covA Work.L3.F89.Pout a = true := by
  rw [show Work.L3.F89.Pout = Work.L3.Cov.Pf by decide +kernel]; exact Work.L3.Cov.cov

/-- **No degree-4 PC refutation of onto-FPHP^(n+8)_n over Z/2 for n ≥ 7.** -/
theorem no_deg4 (n : Nat) (hn : 7 ≤ n) : ¬ PPCRefutation 2 (ontoFPHP n 8) 4 :=
  Programme.«20261027-1434-proof-complexity».Ext278d.hard_of_run ssAll _ run_all cov_all n hn

end Work.L3.Main

#print axioms Work.L3.Main.no_deg4
