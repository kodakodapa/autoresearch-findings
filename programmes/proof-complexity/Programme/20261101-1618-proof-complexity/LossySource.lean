import Programme.«20261101-1618-proof-complexity».LossyOne
import Programme.«20261101-1618-proof-complexity».ClauseLinearCondition

namespace Programme.«20261101-1618-proof-complexity».LossySource
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-1618-proof-complexity».LossyOne

/-- Zero-based successor and return-pointer blocks, disjoint from g=f. -/
def succVar (i u v : Nat) : Var :=
  if u = 0 ∧ v = 0 then s i else (3, 2^i * (2*(2^u * (2*v+1))+1))
def retVar (i u j : Nat) : Var :=
  if u = 0 then h i j else (4, 2^i * (2*(2^u * (2*j+1))+1))

/-- Unary source Lossy(Iter), with m return values, N outputs and L levels.
Pair clauses are ordered duplicates, as in LossyOne. -/
def cnf (m N L : Nat) : List Clause :=
  ((List.range m).flatMap fun j => onehot ((List.range N).map (f j))) ++
  ((List.range N).flatMap fun i => (List.range L).flatMap fun u =>
    onehot ((List.range m).map (retVar i u))) ++
  ((List.range N).flatMap fun i => (List.range L).flatMap fun u =>
    onehot ((List.range L).map (succVar i u))) ++
  ((List.range N).flatMap fun i => (List.range m).flatMap fun j =>
    ((List.range N).filter (· != i)).flatMap fun k =>
      [[(succVar i 0 0,false),(retVar i 0 j,false),(f j k,false)]] ++
      ((List.range L).flatMap fun u =>
        ((List.range u).map fun v =>
          [(succVar i u v,false),(retVar i v j,false),(f j k,false)]) ++
        (((List.range L).filter (u < ·)).map fun v =>
          [(succVar i u v,false),(succVar i v v,false),
           (retVar i v j,false),(f j k,false)])))

theorem length_one (m N : Nat) : cnf m N 1 = Programme.«20261101-1618-proof-complexity».LossyOne.cnf m N := by
  have hr (i : Nat) : retVar i 0 = h i := by funext j; rfl
  simp [cnf, Programme.«20261101-1618-proof-complexity».LossyOne.cnf, onehot, succVar, hr, ← List.map_eq_flatMap]

theorem length_one_exact (N : Nat) (hN : 1 < N) :
    Programme.«20261101-1618-proof-complexity».ClauseLinear.Refutes (cnf 1 N 1) 1 ∧
      ∀ d < 1, ¬ Programme.«20261101-1618-proof-complexity».ClauseLinear.Refutes (cnf 1 N 1) d := by
  rw [length_one]
  exact Programme.«20261101-1618-proof-complexity».LossyOne.exact_degree N hN

#print axioms length_one
#print axioms length_one_exact
end Programme.«20261101-1618-proof-complexity».LossySource
