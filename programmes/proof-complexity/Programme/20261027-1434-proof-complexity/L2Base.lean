import Programme.«20261027-1434-proof-complexity».Peel
import Programme.«20261026-1402-proof-complexity».TExt

/-! Level-2 base functions on `ontoFPHP 7 8`: `R0` (the product of the rectangles on pigeons
`0,1` x holes `0,1` and pigeons `2,3` x holes `2,3`) and `T 7` (th's 3x3 block), with their odd
supports, parity and zero-link checks. -/

namespace Programme.«20261027-1434-proof-complexity».L2Base

open Programme.«20261026-1402-proof-complexity».ExtLin
open Programme.«20261027-1434-proof-complexity».PeelBase Programme.«20261027-1434-proof-complexity».Peel

def R0 : List Nat → Int := tprod (rect 7 0 1 0 1) (rect 7 2 3 2 3)

def Fb : Nat → List Nat → Int
  | 0 => R0
  | _ => Programme.«20261026-1402-proof-complexity».TExt.T 7

def SR : List (List Nat) := [[16, 0], [16, 1], [16, 7], [16, 8], [17, 0], [17, 1], [17, 7], [17, 8], [23, 0], [23, 1], [23, 7], [23, 8], [24, 0], [24, 1], [24, 7], [24, 8]]
def ST : List (List Nat) := [[7, 1], [7, 2], [8, 0], [8, 2], [9, 0], [9, 1], [14, 1], [14, 2], [14, 8], [14, 9], [15, 0], [15, 2], [15, 7], [15, 9], [16, 0], [16, 1], [16, 7], [16, 8]]

def Sb : Nat → List (List Nat)
  | 0 => SR
  | _ => ST

theorem par0 : parOK 2 R0 SR = true := by decide +kernel
theorem par1 : parOK 2 (Programme.«20261026-1402-proof-complexity».TExt.T 7) ST = true := by decide +kernel
theorem supp0 : suppOK 2 SR = true := by decide +kernel
theorem supp1 : suppOK 2 ST = true := by decide +kernel
theorem zl0 : zlOK R0 = true := by decide +kernel
theorem zl1 : zlOK (Programme.«20261026-1402-proof-complexity».TExt.T 7) = true := by decide +kernel

end Programme.«20261027-1434-proof-complexity».L2Base
