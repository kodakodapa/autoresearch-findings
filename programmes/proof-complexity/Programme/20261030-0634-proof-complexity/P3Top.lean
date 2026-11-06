import Programme.«20261030-0634-proof-complexity».P3Splice
import Programme.«20261030-0634-proof-complexity».P3Row0
import Programme.«20261030-0634-proof-complexity».P3Row1
import Programme.«20261030-0634-proof-complexity».P3Row2
import Programme.«20261030-0634-proof-complexity».P3Row3
import Programme.«20261030-0634-proof-complexity».P3Row4
import Programme.«20261030-0634-proof-complexity».P3Row5
import Programme.«20261030-0634-proof-complexity».P3Row6
import Programme.«20261030-0634-proof-complexity».P3Row7
import Programme.«20261030-0634-proof-complexity».P3Row8
import Programme.«20261030-0634-proof-complexity».P3Row9
import Programme.«20261030-0634-proof-complexity».P3Row10
import Programme.«20261030-0634-proof-complexity».P3Row11
import Programme.«20261030-0634-proof-complexity».P3Row12
import Programme.«20261030-0634-proof-complexity».P3Row13
import Programme.«20261030-0634-proof-complexity».P3Row14
import Programme.«20261030-0634-proof-complexity».P3Row15
import Programme.«20261030-0634-proof-complexity».P3Row16
import Programme.«20261030-0634-proof-complexity».P3Row17
import Programme.«20261030-0634-proof-complexity».P3Row18
import Programme.«20261030-0634-proof-complexity».P3Row19
import Programme.«20261030-0634-proof-complexity».P3Row20
import Programme.«20261030-0634-proof-complexity».P3Row21
import Programme.«20261030-0634-proof-complexity».P3Row22
import Programme.«20261030-0634-proof-complexity».P3Row23
import Programme.«20261030-0634-proof-complexity».P3Row24
import Programme.«20261030-0634-proof-complexity».P3Row25
import Programme.«20261030-0634-proof-complexity».P3Row26
import Programme.«20261030-0634-proof-complexity».P3Row27
import Programme.«20261030-0634-proof-complexity».P3Row28
import Programme.«20261030-0634-proof-complexity».P3Row29
import Programme.«20261030-0634-proof-complexity».P3Row30
import Programme.«20261030-0634-proof-complexity».P3Row31
import Programme.«20261030-0634-proof-complexity».P3Row32
import Programme.«20261030-0634-proof-complexity».P3Row33
import Programme.«20261030-0634-proof-complexity».P3Row34
import Programme.«20261030-0634-proof-complexity».P3Row35
import Programme.«20261030-0634-proof-complexity».P3Row36
import Programme.«20261030-0634-proof-complexity».P3Row37
import Programme.«20261030-0634-proof-complexity».P3Row38
import Programme.«20261030-0634-proof-complexity».P3Row39
import Programme.«20261030-0634-proof-complexity».P3Row40
import Programme.«20261030-0634-proof-complexity».P3Row41
import Programme.«20261030-0634-proof-complexity».P3Row42
import Programme.«20261030-0634-proof-complexity».P3Row43
import Programme.«20261030-0634-proof-complexity».P3Row44
import Programme.«20261030-0634-proof-complexity».P3Row45
import Programme.«20261030-0634-proof-complexity».P3Row46
import Programme.«20261030-0634-proof-complexity».P3Row47
import Programme.«20261030-0634-proof-complexity».P3Row48
import Programme.«20261030-0634-proof-complexity».P3Row49
import Programme.«20261030-0634-proof-complexity».P3Row50
import Programme.«20261030-0634-proof-complexity».P3Row51
import Programme.«20261030-0634-proof-complexity».P3Row52
import Programme.«20261030-0634-proof-complexity».P3Row53
import Programme.«20261030-0634-proof-complexity».P3Row54
import Programme.«20261030-0634-proof-complexity».P3Row55
import Programme.«20261030-0634-proof-complexity».P3Row56
import Programme.«20261030-0634-proof-complexity».P3Row57
import Programme.«20261030-0634-proof-complexity».P3Row58
import Programme.«20261030-0634-proof-complexity».P3Row59
import Programme.«20261030-0634-proof-complexity».P3Row60
import Programme.«20261030-0634-proof-complexity».P3Row61
import Programme.«20261030-0634-proof-complexity».P3Row62
import Programme.«20261030-0634-proof-complexity».P3Row63
import Programme.«20261030-0634-proof-complexity».P3Row64
import Programme.«20261030-0634-proof-complexity».P3Row65
import Programme.«20261030-0634-proof-complexity».P3Row66
import Programme.«20261030-0634-proof-complexity».P3Row67
import Programme.«20261030-0634-proof-complexity».P3Row68
import Programme.«20261030-0634-proof-complexity».P3Row69
import Programme.«20261030-0634-proof-complexity».FactorUnit
import Programme.«20261027-0607-proof-complexity».K7Reproof
namespace Programme.«20261030-0634-proof-complexity».P3Top
open Programme.«20261030-0634-proof-complexity».P3Table
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt)
open Programme.«20261027-0607-proof-complexity».Peel (IsPrime)
open Programme.«20261025-0459-proof-complexity».OntoFPHP (ontoFPHP)
open Programme.«20261025-0459-proof-complexity».OntoFPHP (PPCRefutation)
theorem allcheck (a b : Fin 70) : Check a b := by
  rcases a with ⟨a,ha⟩
  change Check a b
  match a with
  | 0 => exact check0 b
  | 1 => exact check1 b
  | 2 => exact check2 b
  | 3 => exact check3 b
  | 4 => exact check4 b
  | 5 => exact check5 b
  | 6 => exact check6 b
  | 7 => exact check7 b
  | 8 => exact check8 b
  | 9 => exact check9 b
  | 10 => exact check10 b
  | 11 => exact check11 b
  | 12 => exact check12 b
  | 13 => exact check13 b
  | 14 => exact check14 b
  | 15 => exact check15 b
  | 16 => exact check16 b
  | 17 => exact check17 b
  | 18 => exact check18 b
  | 19 => exact check19 b
  | 20 => exact check20 b
  | 21 => exact check21 b
  | 22 => exact check22 b
  | 23 => exact check23 b
  | 24 => exact check24 b
  | 25 => exact check25 b
  | 26 => exact check26 b
  | 27 => exact check27 b
  | 28 => exact check28 b
  | 29 => exact check29 b
  | 30 => exact check30 b
  | 31 => exact check31 b
  | 32 => exact check32 b
  | 33 => exact check33 b
  | 34 => exact check34 b
  | 35 => exact check35 b
  | 36 => exact check36 b
  | 37 => exact check37 b
  | 38 => exact check38 b
  | 39 => exact check39 b
  | 40 => exact check40 b
  | 41 => exact check41 b
  | 42 => exact check42 b
  | 43 => exact check43 b
  | 44 => exact check44 b
  | 45 => exact check45 b
  | 46 => exact check46 b
  | 47 => exact check47 b
  | 48 => exact check48 b
  | 49 => exact check49 b
  | 50 => exact check50 b
  | 51 => exact check51 b
  | 52 => exact check52 b
  | 53 => exact check53 b
  | 54 => exact check54 b
  | 55 => exact check55 b
  | 56 => exact check56 b
  | 57 => exact check57 b
  | 58 => exact check58 b
  | 59 => exact check59 b
  | 60 => exact check60 b
  | 61 => exact check61 b
  | 62 => exact check62 b
  | 63 => exact check63 b
  | 64 => exact check64 b
  | 65 => exact check65 b
  | 66 => exact check66 b
  | 67 => exact check67 b
  | 68 => exact check68 b
  | 69 => exact check69 b
  | a+70 => omega

theorem top : Bal 3 5 9 U (fun _ => -1) 2 := top_of_checks allcheck

theorem top_extension : Programme.«20261030-0634-proof-complexity».FactorUnit.TopExtension 3 := ⟨U, top⟩

theorem design : ∃ T : List Nat → Int, T [] = -20 ∧ ∀ e ≤ 2, Bal 3 5 9 T T e := by
  exact Programme.«20261030-0634-proof-complexity».FactorBoundary.design_of_top (by decide) (by decide) U top

theorem no_deg3 (n : Nat) (hn : 5 ≤ n) : ¬ PPCRefutation 3 (ontoFPHP n 9) 3 := by
  exact Programme.«20261030-0634-proof-complexity».FactorUnit.no_deg_p_of_top
    Programme.«20261027-0607-proof-complexity».K7Reproof.isPrime3 ⟨U,top⟩ n hn

-- This is the uniform goal; only its p=3 instance is established here.
def UniformOddPrimeTop : Prop := ∀ p : Nat, IsPrime p → p % 2 = 1 → Programme.«20261030-0634-proof-complexity».FactorUnit.TopExtension p
#print axioms top
#print axioms top_extension
#print axioms design
#print axioms no_deg3
end Programme.«20261030-0634-proof-complexity».P3Top
