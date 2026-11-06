import Programme.«20261102-0806-proof-complexity».P11RawUpdate

namespace Programme.«20261102-0806-proof-complexity».P11RowsUpdate
open Programme.«20261102-0806-proof-complexity».P11Candidate Programme.«20261102-0806-proof-complexity».P11RawUpdate

def weight (flip : Bool) (b : Nat) : Nat :=
  if b = 0 then (if flip then 11 else 1)
  else if b = 1 then (if flip then 1 else 11) else 121

theorem rows_extend (g : List Nat) {i j : Nat} (hj : j < 21) (flip : Bool) :
    rows ((i * 21 + j) :: g) flip =
      (List.range 15).map (fun a =>
        (if flip then count g a 1 + 11 * count g a 0 + 121 * count g a 2
         else count g a 0 + 11 * count g a 1 + 121 * count g a 2) +
        if pigeonClass i = a then weight flip (j / 10) else 0) := by
  unfold rows
  apply List.map_congr_left
  intro a ha
  simp only [count_extend g hj]
  have hb : j / 10 = 0 ∨ j / 10 = 1 ∨ j / 10 = 2 := by omega
  rcases hb with hb | hb | hb <;>
    cases flip <;> by_cases h : pigeonClass i = a <;>
    simp [hb, h, weight, Nat.mul_add] <;> omega

#print axioms rows_extend
end Programme.«20261102-0806-proof-complexity».P11RowsUpdate
