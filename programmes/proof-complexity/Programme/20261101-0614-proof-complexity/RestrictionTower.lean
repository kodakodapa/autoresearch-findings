import Programme.«20261101-0614-proof-complexity».FamilyRestriction
namespace Programme.«20261101-0614-proof-complexity».Composition
open Programme.«20261031-2024-proof-complexity».NativeIter

theorem refutes_restrict_add (M N L d t : Nat)
    (hM : 1 ≤ M) (hN : 2 ≤ N) (hL : 1 ≤ L) :
    Refutes (cnf (M+t) (N+t) L) d → Refutes (cnf M N L) d := by
  induction t with
  | zero => simpa
  | succ t ih =>
    intro h
    apply ih
    apply refutes_restrict (M+t) (N+t) L d (by omega) (by omega) hL
    exact h

theorem lower_propagates (M N L d t : Nat)
    (hM : 1 ≤ M) (hN : 2 ≤ N) (hL : 1 ≤ L)
    (h : ¬ Refutes (cnf M N L) d) :
    ¬ Refutes (cnf (M+t) (N+t) L) d :=
  fun r => h (refutes_restrict_add M N L d t hM hN hL r)

#print axioms refutes_restrict_add
#print axioms lower_propagates
end Programme.«20261101-0614-proof-complexity».Composition
