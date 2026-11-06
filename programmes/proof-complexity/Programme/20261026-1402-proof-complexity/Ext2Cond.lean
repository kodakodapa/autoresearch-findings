import Programme.«20261026-1402-proof-complexity».Ext0

/-!
# Degree 3 from two computed EXT levels

With level zero proved (`Work.Ext0.ext0`, needs `p ∣ k`), K8 (`no_refutation_of_ext_ge`) reduces
"no degree-3 PC refutation of `ontoFPHP n k` for all `n ≥ n0`" to the two finite statements
`EXT p n0 k 1` and `EXT p n0 k 2` at one base size `n0`. Exact elimination over `F_p`
(`agents/pr/checks/ext_levels12.py`) finds both at `(p, n0, k) = (5, 5, 5), (5, 5, 10), (3, 5, 9)`.
-/

namespace Programme.«20261026-1402-proof-complexity».Ext2Cond

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261026-1402-proof-complexity».ExtLemma

theorem deg3_of_ext12 {p n0 k : Nat} (hp : 1 < p) (hn0 : 0 < n0) (hk : p ∣ k)
    (h1 : EXT p n0 k 1) (h2 : EXT p n0 k 2) (n : Nat) (hn : n0 ≤ n) :
    ¬ PPCRefutation p (ontoFPHP n k) 3 :=
  no_refutation_of_ext_ge hp hn0 (by omega) (fun d hd => by
    rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with rfl | rfl | rfl
    · exact Programme.«20261026-1402-proof-complexity».Ext0.ext0 hn0 hk
    · exact h1
    · exact h2) n hn

end Programme.«20261026-1402-proof-complexity».Ext2Cond

#print axioms Programme.«20261026-1402-proof-complexity».Ext2Cond.deg3_of_ext12
