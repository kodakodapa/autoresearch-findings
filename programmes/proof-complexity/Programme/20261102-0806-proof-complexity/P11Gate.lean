import Programme.«20261030-0634-proof-complexity».FactorUnit

namespace Programme.«20261102-0806-proof-complexity».P11Gate
open Programme.«20261027-0607-proof-complexity».Peel (IsPrime)
open Programme.«20261026-1402-proof-complexity».ExtLemma (Bal)
open Programme.«20261025-0459-proof-complexity».OntoFPHP (PPCRefutation ontoFPHP)

theorem prime11 : IsPrime 11 := by
  constructor
  · decide
  · intro a ha
    have hle := Nat.le_of_dvd (by decide : 0 < 11) ha
    have hc : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨
        a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 := by omega
    rcases hc with h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst a <;> simp_all

/-- The missing hypothesis is precisely canonical top-layer balance. -/
theorem no_deg11_of_top
    (h : ∃ U : List Nat → Int, Bal 11 21 121 U (fun _ => -1) 10)
    (n : Nat) (hn : 21 ≤ n) : ¬ PPCRefutation 11 (ontoFPHP n 121) 11 := by
  exact Programme.«20261030-0634-proof-complexity».FactorUnit.no_deg_p_of_top prime11 h n hn

end Programme.«20261102-0806-proof-complexity».P11Gate
#print axioms Programme.«20261102-0806-proof-complexity».P11Gate.prime11
#print axioms Programme.«20261102-0806-proof-complexity».P11Gate.no_deg11_of_top
