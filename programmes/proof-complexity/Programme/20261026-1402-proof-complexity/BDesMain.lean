import Programme.«20261026-1402-proof-complexity».BDes0
import Programme.«20261026-1402-proof-complexity».BDes1
import Programme.«20261026-1402-proof-complexity».BDes2
import Programme.«20261026-1402-proof-complexity».BDes3

/-! K35 (th): the design `B` of `ontoFPHP 4 8` over `Z/2` balances against itself at levels 0, 1, 2. -/

namespace Programme.«20261026-1402-proof-complexity».BDesMain
open Programme.«20261026-1402-proof-complexity».ExtLemma Programme.«20261026-1402-proof-complexity».BDes

theorem chk2 : chk 2 = true := chk2_of fun a ha => by
  have hs : ∀ a, a < 48 → chkS a = true := by
    intro a ha
    match a, ha with
    | 0, _ => exact Programme.«20261026-1402-proof-complexity».BDes0.s0
    | 1, _ => exact Programme.«20261026-1402-proof-complexity».BDes0.s1
    | 2, _ => exact Programme.«20261026-1402-proof-complexity».BDes0.s2
    | 3, _ => exact Programme.«20261026-1402-proof-complexity».BDes0.s3
    | 4, _ => exact Programme.«20261026-1402-proof-complexity».BDes0.s4
    | 5, _ => exact Programme.«20261026-1402-proof-complexity».BDes0.s5
    | 6, _ => exact Programme.«20261026-1402-proof-complexity».BDes0.s6
    | 7, _ => exact Programme.«20261026-1402-proof-complexity».BDes0.s7
    | 8, _ => exact Programme.«20261026-1402-proof-complexity».BDes0.s8
    | 9, _ => exact Programme.«20261026-1402-proof-complexity».BDes0.s9
    | 10, _ => exact Programme.«20261026-1402-proof-complexity».BDes0.s10
    | 11, _ => exact Programme.«20261026-1402-proof-complexity».BDes0.s11
    | 12, _ => exact Programme.«20261026-1402-proof-complexity».BDes1.s12
    | 13, _ => exact Programme.«20261026-1402-proof-complexity».BDes1.s13
    | 14, _ => exact Programme.«20261026-1402-proof-complexity».BDes1.s14
    | 15, _ => exact Programme.«20261026-1402-proof-complexity».BDes1.s15
    | 16, _ => exact Programme.«20261026-1402-proof-complexity».BDes1.s16
    | 17, _ => exact Programme.«20261026-1402-proof-complexity».BDes1.s17
    | 18, _ => exact Programme.«20261026-1402-proof-complexity».BDes1.s18
    | 19, _ => exact Programme.«20261026-1402-proof-complexity».BDes1.s19
    | 20, _ => exact Programme.«20261026-1402-proof-complexity».BDes1.s20
    | 21, _ => exact Programme.«20261026-1402-proof-complexity».BDes1.s21
    | 22, _ => exact Programme.«20261026-1402-proof-complexity».BDes1.s22
    | 23, _ => exact Programme.«20261026-1402-proof-complexity».BDes1.s23
    | 24, _ => exact Programme.«20261026-1402-proof-complexity».BDes2.s24
    | 25, _ => exact Programme.«20261026-1402-proof-complexity».BDes2.s25
    | 26, _ => exact Programme.«20261026-1402-proof-complexity».BDes2.s26
    | 27, _ => exact Programme.«20261026-1402-proof-complexity».BDes2.s27
    | 28, _ => exact Programme.«20261026-1402-proof-complexity».BDes2.s28
    | 29, _ => exact Programme.«20261026-1402-proof-complexity».BDes2.s29
    | 30, _ => exact Programme.«20261026-1402-proof-complexity».BDes2.s30
    | 31, _ => exact Programme.«20261026-1402-proof-complexity».BDes2.s31
    | 32, _ => exact Programme.«20261026-1402-proof-complexity».BDes2.s32
    | 33, _ => exact Programme.«20261026-1402-proof-complexity».BDes2.s33
    | 34, _ => exact Programme.«20261026-1402-proof-complexity».BDes2.s34
    | 35, _ => exact Programme.«20261026-1402-proof-complexity».BDes2.s35
    | 36, _ => exact Programme.«20261026-1402-proof-complexity».BDes3.s36
    | 37, _ => exact Programme.«20261026-1402-proof-complexity».BDes3.s37
    | 38, _ => exact Programme.«20261026-1402-proof-complexity».BDes3.s38
    | 39, _ => exact Programme.«20261026-1402-proof-complexity».BDes3.s39
    | 40, _ => exact Programme.«20261026-1402-proof-complexity».BDes3.s40
    | 41, _ => exact Programme.«20261026-1402-proof-complexity».BDes3.s41
    | 42, _ => exact Programme.«20261026-1402-proof-complexity».BDes3.s42
    | 43, _ => exact Programme.«20261026-1402-proof-complexity».BDes3.s43
    | 44, _ => exact Programme.«20261026-1402-proof-complexity».BDes3.s44
    | 45, _ => exact Programme.«20261026-1402-proof-complexity».BDes3.s45
    | 46, _ => exact Programme.«20261026-1402-proof-complexity».BDes3.s46
    | 47, _ => exact Programme.«20261026-1402-proof-complexity».BDes3.s47
    | _ + 48, h => exact absurd h (by omega)
  exact hs a ha

/-- `B(∅)=1` and `Bal 2 4 8 B B e` for every `e ≤ 2`: a degree-3 design of `ontoFPHP 4 8` over `Z/2`. -/
theorem b_design : B [] = 1 ∧ ∀ e ≤ 2, Bal 2 4 8 B B e := by
  refine ⟨B_nil, fun e he => ?_⟩
  match e, he with
  | 0, _ => exact bal_of_chk chk0
  | 1, _ => exact bal_of_chk chk1
  | 2, _ => exact bal_of_chk chk2

#print axioms b_design

end Programme.«20261026-1402-proof-complexity».BDesMain
