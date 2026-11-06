import Programme.«20261030-0634-proof-complexity».P3Top

namespace Programme.«20261102-0806-proof-complexity».P3Anchor

open Programme.«20261025-0459-proof-complexity».OntoFPHP

/-- Re-establish the existing universal bound for this run's verification ledger. -/
theorem no_deg3 (n : Nat) (hn : 5 ≤ n) :
    ¬ PPCRefutation 3 (ontoFPHP n 9) 3 :=
  Programme.«20261030-0634-proof-complexity».P3Top.no_deg3 n hn

end Programme.«20261102-0806-proof-complexity».P3Anchor

#print axioms Programme.«20261102-0806-proof-complexity».P3Anchor.no_deg3
#print axioms Programme.«20261030-0634-proof-complexity».P3Top.no_deg3
