import Programme.«20261102-0635-proof-complexity».ProofBAudit
import Programme.«20261029-1156-proof-complexity».StdPCExact

namespace Programme.«20261102-0635-proof-complexity».SmallOrdinary
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261029-1156-proof-complexity».StdPC

/-- The independently checked square-subset design gives an ordinary-PC
lower bound already at three holes. This is a semantic-design transfer,
not a construction of the reduced-space invariant of StepSix. -/
theorem no_degree_two (n : Nat) (hn : 3 ≤ n) :
    ¬ Refutes 2 (ontoFPHP n 4) 2 := by
  apply not_refutes (by decide)
  have hp : Programme.«20261027-0607-proof-complexity».Peel.IsPrime 2 :=
    ⟨Nat.le_refl 2, fun a ha => by
      have := Nat.le_of_dvd (by decide : 0 < 2) ha
      rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with h | h | h <;>
        subst h <;> simp_all⟩
  exact Programme.«20261102-0635-proof-complexity».ProofBAudit.consequence hp Programme.«20261102-0635-proof-complexity».ProofBAudit.instance2 n hn

/-- The stronger established degree-four threshold, retained separately
with its actual five-hole bound. -/
theorem exact_degree_four (n D : Nat) (hn : 5 ≤ n) :
    Refutes 2 (ontoFPHP n 4) D ↔ 4 ≤ D :=
  Programme.«20261029-1156-proof-complexity».StdPCExact.std_f2_k4_exact n D hn
end Programme.«20261102-0635-proof-complexity».SmallOrdinary
#print axioms Programme.«20261102-0635-proof-complexity».SmallOrdinary.no_degree_two
#print axioms Programme.«20261102-0635-proof-complexity».SmallOrdinary.exact_degree_four
