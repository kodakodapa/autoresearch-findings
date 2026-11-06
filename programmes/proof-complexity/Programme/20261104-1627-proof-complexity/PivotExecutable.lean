import Programme.«20261104-1627-proof-complexity».PivotFiniteCertificates
namespace Programme.«20261104-1627-proof-complexity».PivotExecutable
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261104-1627-proof-complexity».PivotCanonicalData Programme.«20261104-1627-proof-complexity».PivotFiniteCertificates
/-- Avoid well-founded sorting reduction on the two-edge pivot supports. -/
def order : Matching → Matching
 | [] => []
 | [a] => [a]
 | [a,b] => if a.1 ≤ b.1 then [a,b] else [b,a]
 | a::b::c::s => ordered (a::b::c::s)
theorem order_eq (M : Matching) : order M = ordered M := by
  cases M with
  | nil => simp [order, ordered]
  | cons a s =>
    cases s with
    | nil => simp [order, ordered]
    | cons b s =>
      cases s with
      | nil => simp [order, ordered, List.mergeSort_pair]
      | cons c s => rfl
def rrFast (n : Nat) (N : Matching) (a b : Nat) : Vector :=
  (cols n N).map (fun j => (1, ⟨order (N ++ [(b,j)]),true,a⟩)) ++
  (cols n N).map (fun j => (-1, ⟨order (N ++ [(a,j)]),true,b⟩))
def rcFast (m n : Nat) (N : Matching) (i j : Nat) : Vector :=
  ((rows m N).filter (· != i)).map (fun a => (1, ⟨order (N ++ [(a,j)]),true,i⟩)) ++
  ((cols n N).filter (· != j)).map (fun b => (-1, ⟨order (N ++ [(i,b)]),false,j⟩))
def pivotsFast (old n : Nat) : List Vector :=
  ((matchings old n 1).flatMap fun N =>
    (rows old N).map fun a => rrFast n N a old) ++
  ((matchings old n 1).flatMap fun N =>
    (cols n N).map fun b => rcFast (old+1) n N old b)
theorem pivotsFast_eq (old n : Nat) : pivotsFast old n = pivots old n := by
  simp only [pivotsFast, pivots, rrFast, rcFast, order_eq, rr, rc]
def g (old n i k : Nat) : Int :=
  vectorCoeff ((pivotsFast old n)[k]?.getD []) (coordinate old n i)
theorem g_eq (old n i k : Nat) : g old n i k = G old n i k := by
  simp only [g, G, pivotsFast_eq]
end Programme.«20261104-1627-proof-complexity».PivotExecutable
