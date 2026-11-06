import Programme.«20261101-0614-proof-complexity».SingletonFinite
import Programme.«20261101-0614-proof-complexity».SingletonAssemble

namespace Programme.«20261101-0614-proof-complexity».SingletonLower
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity».SingletonData Programme.«20261101-0614-proof-complexity».SignedDual

noncomputable def dual : ConeDual.Certificate (Singleton.cnf 2 3) 3 :=
  SingletonAssemble.dual SingletonFinite.positive

theorem no_degree_three : ¬ Refutes (Singleton.cnf 2 3) 3 :=
  ConeDual.no_refutation dual

theorem exact_degree_four : Refutes (Singleton.cnf 2 3) 4 ∧
    ∀ d < 4, ¬ Refutes (Singleton.cnf 2 3) d := by
  constructor
  · exact Singleton.upper 2 3 (by decide) (by decide)
  · intro d hd h
    exact no_degree_three (Singleton.cone_degree_mono (by omega) h)

#print axioms no_degree_three
#print axioms exact_degree_four
end Programme.«20261101-0614-proof-complexity».SingletonLower
