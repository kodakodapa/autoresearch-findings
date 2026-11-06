import Programme.«20261101-0614-proof-complexity».SingletonTwo
import Programme.«20261101-0614-proof-complexity».RestrictionTower
import Programme.«20261101-0614-proof-complexity».SingletonBridge

namespace Programme.«20261101-0614-proof-complexity».LowerTwoReproof
open Programme.«20261031-2024-proof-complexity».NativeIter

/-- Alternative to the direct filtered assignment for the general composition family. -/
theorem lower (M N d : Nat) (hM : 1 ≤ M) (hMN : M < N) (hd : d < 3) :
    ¬ Refutes (Programme.«20261101-0614-proof-complexity».Composition.cnf M N 2) d := by
  have hbase : ¬ Refutes (Programme.«20261101-0614-proof-complexity».Composition.cnf 1 (N-M+1) 2) d := by
    intro hr
    have hp : Refutes (Programme.«20261101-0614-proof-complexity».Composition.cnf 1 (N-M+1) 2) d := hr
    exact Programme.«20261101-0614-proof-complexity».SingletonTwo.lower (N-M+1) d (by omega) hd
      (Programme.«20261101-0614-proof-complexity».SingletonBridge.transport (N-M+1) 2 d (by omega) (by decide) hp)
  have ht := Programme.«20261101-0614-proof-complexity».Composition.lower_propagates 1 (N-M+1) 2 d (M-1)
    (by decide) (by omega) (by decide) hbase
  have h₁ : 1 + (M-1) = M := by omega
  have h₂ : N-M+1+(M-1) = N := by omega
  simpa only [h₁,h₂] using ht

#print axioms lower
end Programme.«20261101-0614-proof-complexity».LowerTwoReproof
