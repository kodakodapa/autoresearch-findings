import Programme.«20261101-0614-proof-complexity».SingletonBridge
import Programme.«20261101-0614-proof-complexity».SingletonLower
import Programme.«20261101-0614-proof-complexity».RestrictionTower
namespace Programme.«20261101-0614-proof-complexity».CompositionLowerThree
open Programme.«20261031-2024-proof-complexity».NativeIter

theorem singleton_lower (d : Nat) (hd : d < 4) :
    ¬ Refutes (Programme.«20261101-0614-proof-complexity».Composition.cnf 1 2 3) d := by
  intro h
  exact SingletonLower.exact_degree_four.2 d hd
    (SingletonBridge.transport 2 3 d (by decide) (by decide) h)

theorem lower (M d : Nat) (hM : 1 ≤ M) (hd : d < 4) :
    ¬ Refutes (Programme.«20261101-0614-proof-complexity».Composition.cnf M (M+1) 3) d := by
  have h := Programme.«20261101-0614-proof-complexity».Composition.lower_propagates 1 2 3 d (M-1)
    (by decide) (by decide) (by decide) (singleton_lower d hd)
  have ha : 1+(M-1) = M := by omega
  have hb : 2+(M-1) = M+1 := by omega
  simpa only [ha,hb] using h
#print axioms singleton_lower
#print axioms lower
end Programme.«20261101-0614-proof-complexity».CompositionLowerThree
