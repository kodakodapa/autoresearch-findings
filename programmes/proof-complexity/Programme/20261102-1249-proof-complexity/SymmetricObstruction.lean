import Programme.«20261026-1402-proof-complexity».ExtLemma
set_option maxRecDepth 10000
namespace Programme.«20261102-1249-proof-complexity».SymmetricObstruction
open Programme.«20261026-1402-proof-complexity».ExtLemma
 theorem no_symmetric_unit (f : List Nat → Int)
    (single : ∀ g, CM 7 8 g → g.length = 1 → f g = f [0])
    (pair : ∀ g, CM 7 8 g → g.length = 2 → f g = f [8, 0])
    (h0 : Bal 2 7 8 f f 0) (h1 : Bal 2 7 8 f f 1) :
    (2 : Int) ∣ f [] := by
  have a := (h0 [] (by unfold CM; decide) rfl).1 0 (by decide) (by simp [pfree])
  have b := (h1 [0] (by unfold CM; decide) rfl).1 1 (by decide) (by simp [pfree])
  have s1 : f [1] = f [0] := single _ (by unfold CM; decide) rfl
  have s2 : f [2] = f [0] := single _ (by unfold CM; decide) rfl
  have s3 : f [3] = f [0] := single _ (by unfold CM; decide) rfl
  have s4 : f [4] = f [0] := single _ (by unfold CM; decide) rfl
  have s5 : f [5] = f [0] := single _ (by unfold CM; decide) rfl
  have s6 : f [6] = f [0] := single _ (by unfold CM; decide) rfl
  have t9 : f [9,0] = f [8,0] := pair _ (by unfold CM; decide) rfl
  have t10 : f [10,0] = f [8,0] := pair _ (by unfold CM; decide) rfl
  have t11 : f [11,0] = f [8,0] := pair _ (by unfold CM; decide) rfl
  have t12 : f [12,0] = f [8,0] := pair _ (by unfold CM; decide) rfl
  have t13 : f [13,0] = f [8,0] := pair _ (by unfold CM; decide) rfl
  change (2 : Int) ∣ (0 + f [0] + f [1] + f [2] + f [3] + f [4] + f [5] + f [6]) - f [] at a
  change (2 : Int) ∣ (0 + 0 + f [8,0] + f [9,0] + f [10,0] + f [11,0] + f [12,0] + f [13,0]) - f [0] at b
  rw [s1,s2,s3,s4,s5,s6] at a
  rw [t9,t10,t11,t12,t13] at b
  omega
#print axioms no_symmetric_unit
end Programme.«20261102-1249-proof-complexity».SymmetricObstruction
