import Programme.«20261104-1627-proof-complexity».MatchingLabels

namespace Programme.«20261104-1627-proof-complexity».PivotCanonicalData
open Programme.«20261104-1627-proof-complexity».MatchingLabels

def tails (old n : Nat) : List Label :=
  (labels (old+1) n 3).filter fun g =>
    g.base.any (fun e => e.1 == old) || (g.isRow && g.mark == old)

def pivots (old n : Nat) : List Vector :=
  ((matchings old n 1).flatMap fun N =>
    (rows old N).map fun a => rr n N a old) ++
  ((matchings old n 1).flatMap fun N =>
    (cols n N).map fun b => rc (old+1) n N old b)

def data (old n : Nat) :=
  (matchings old n 2,
   (tails old n).map (fun g => (g.base,g.isRow,g.mark)),
   (pivots old n).map (fun v => v.map fun a => (a.1,a.2.base,a.2.isRow,a.2.mark)),
   matchings (old+1) n 3)

#eval data 3 5
#eval data 4 5
end Programme.«20261104-1627-proof-complexity».PivotCanonicalData
