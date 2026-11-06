import Programme.«20261102-1249-proof-complexity».UniformC3.Lift

namespace Programme.«20261102-1249-proof-complexity».UniformC3
open Programme.«20261026-1402-proof-complexity».ExtLemma

def correction2 (z : Nat) : Int :=
  (if z < 59 then (if z < 46 then (if z < 36 then (if z = 29 then (-1) else 0) else (if z = 36 then (-1) else 0)) else (if z < 55 then (if z = 46 then (-1) else 0) else (if z = 55 then (-1) else 0))) else (if z < 66 then (if z < 65 then (if z = 59 then (-1) else 0) else (if z = 65 then (-1) else 0)) else (if z < 72 then (if z = 66 then (-1) else 0) else (if z < 76 then (if z = 72 then (-1) else 0) else (if z = 76 then (-1) else 0)))))

def squareCoeff2 (g : List Nat) : Int := 1 + 2 * correction2 (g.foldl (fun z v => z * 9 + v) 0)

theorem squareCoeff2_unit (g : List Nat) : (2 : Int) ∣ squareCoeff2 g - 1 := by
  refine ⟨correction2 (g.foldl (fun z v => z * 9 + v) 0), ?_⟩
  unfold squareCoeff2
  omega

def SquareCheck2 (a : Fin 9) : Prop :=
  (∀ i : Fin 3, pfree 3 [a.val] i.val → rowS 3 0 squareCoeff2 [a.val] i.val = 0) ∧
  (∀ j : Fin 3, hfree 3 [a.val] j.val → colS 3 0 squareCoeff2 [a.val] j.val = 0)

instance (a : Fin 9) : Decidable (SquareCheck2 a) := by
  unfold SquareCheck2 pfree hfree
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem squareCheck2 : ∀ a : Fin 9, SquareCheck2 a := by decide

end Programme.«20261102-1249-proof-complexity».UniformC3
