import Programme.«20261101-0614-proof-complexity».SingletonLower
import Programme.«20261101-0614-proof-complexity».SingletonBridge
import Programme.«20261101-0614-proof-complexity».RestrictReproof

namespace Programme.«20261101-0614-proof-complexity».LowerThreeReproof
open Programme.«20261031-2024-proof-complexity».NativeIter

/-- Descent using the skeptic's substitution rather than the restriction tower. -/
theorem lower (M d : Nat) (hM : 1 ≤ M) (hd : d < 4) :
    ¬ Refutes (Programme.«20261101-0614-proof-complexity».Composition.cnf M (M+1) 3) d := by
  induction M with
  | zero => omega
  | succ m ih =>
    intro hr
    by_cases hm : m = 0
    · subst m
      exact Programme.«20261101-0614-proof-complexity».SingletonLower.exact_degree_four.2 d hd
        (Programme.«20261101-0614-proof-complexity».SingletonBridge.transport 2 3 d (by decide) (by decide) hr)
    · apply ih (by omega)
      exact Programme.«20261101-0614-proof-complexity».RestrictReproof.refutes_restrict m (m+1) 3 d
        (by omega) (by omega) (by decide) hr

#print axioms lower
end Programme.«20261101-0614-proof-complexity».LowerThreeReproof
