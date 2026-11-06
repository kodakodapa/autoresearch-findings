import Programme.«20261104-1627-proof-complexity».PivotChecked3
import Programme.«20261104-1627-proof-complexity».PivotBounds
namespace Programme.«20261104-1627-proof-complexity».PivotBoardReconstruction
open Programme.«20261104-1627-proof-complexity».PivotFiniteCertificates Programme.«20261104-1627-proof-complexity».RectangularSparse Programme.«20261104-1627-proof-complexity».RectangularReconstruction
theorem board3 (x : Nat → Int)
    (hx : ∀ k, k < 240 → (3 : Int) ∣ dot (List.range 360) x (T 3 5 k)) :
    ∀ i, i < 60 → (3 : Int) ∣ dot (List.range 360) x (P 3 5 i) -
      dot (List.range 90) (G 3 5 i)
        (fun k => dot (List.range 360) x (fun j => value (C3[j]?.getD []) k)) := by
  exact check_sound (P 3 5) (G 3 5) (T 3 5)
    (fun j => C3[j]?.getD []) (fun i => H3[i]?.getD [])
    (Programme.«20261104-1627-proof-complexity».PivotBounds.sound C3 Programme.«20261104-1627-proof-complexity».PivotBounds.bounds3.1)
    (Programme.«20261104-1627-proof-complexity».PivotBounds.sound H3 Programme.«20261104-1627-proof-complexity».PivotBounds.bounds3.2)
    Programme.«20261104-1627-proof-complexity».PivotChecked3.canonical_checked x hx
#print axioms board3
end Programme.«20261104-1627-proof-complexity».PivotBoardReconstruction
