import Programme.«20261025-0459b-proof-complexity».CPDag
import Programme.«20261025-0805-proof-complexity».HallCPX
import Programme.«20261025-0805-proof-complexity».HallN2X

/-! Re-establishment in this run of carried C1 results (statements identical to the library). -/

namespace Programme.«20261025-1751-proof-complexity».C1Close

open Programme.«20261024-1110-proof-complexity».Haken (CNF Clause.eval)
open Programme.«20261025-0459b-proof-complexity».CPDag (DRefutation)
open Programme.«20261025-0459b-proof-complexity».Hall (Hall)

/-- DAG-like cutting planes is sound: a CNF with a `DRefutation` is unsatisfiable. -/
theorem dag_sound {V} [DecidableEq V] {F : CNF V} (R : DRefutation F) :
    ¬ ∃ α : V → Bool, ∀ C ∈ F, C.eval α = true :=
  Programme.«20261025-0459b-proof-complexity».CPDag.dag_sound R

/-- K78: explicit quasi-polynomial DAG-like CP lower bound for the Hall CNF. -/
theorem hall_cp_explicit (n ℓ : Nat) (hℓ : 1 ≤ ℓ) (hℓn : ℓ < n) (Rf : DRefutation (Hall n)) :
    (n - ℓ) ^ (ℓ + 1) ≤ 2 ^ (4 * ℓ + 5) * Rf.size * (2 * n + 7) * ℓ *
      ((3 * ℓ) ^ (3 * ℓ) * ((ℓ + 1) * (n.log2 + 1) * 2 ^ ℓ * (2 * ℓ + 1) ^ (2 * ℓ)) ^ (3 * ℓ)) ^ 2 :=
  Programme.«20261025-0805-proof-complexity».HallCPX.hall_cp_explicit n ℓ hℓ hℓn Rf

/-- K79: at `n = 2^550` every DAG-like CP refutation of `Hall n` has more than `n^2` lines. -/
theorem hall_n2 (Rf : DRefutation (Hall (2 ^ 550))) : (2 ^ 550) ^ 2 < Rf.size :=
  Programme.«20261025-0805-proof-complexity».HallN2X.hall_n2 Rf

end Programme.«20261025-1751-proof-complexity».C1Close

#print axioms Programme.«20261025-1751-proof-complexity».C1Close.dag_sound
#print axioms Programme.«20261025-1751-proof-complexity».C1Close.hall_cp_explicit
#print axioms Programme.«20261025-1751-proof-complexity».C1Close.hall_n2
