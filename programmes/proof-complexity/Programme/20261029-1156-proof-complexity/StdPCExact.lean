import Programme.«20261029-1156-proof-complexity».StdPCConv
import Programme.«20261027-0607-proof-complexity».Lucas
import Programme.«20261025-1627-proof-complexity».OntoF2K4
import Programme.«20261025-0459-proof-complexity».OntoLucas

/-!
# Exact onto-FPHP degrees for standard polynomial calculus

The library's exact-degree theorems (`pc_degree_exact`, `f2_k4_exact`, `f3_k3_exact`) are stated
for `PPCRefutation`; by `Work.StdPCConv.refutes_iff` they hold verbatim for the standard calculus
`Work.StdPC.Refutes` (syntactic polynomials over `F_p`, Boolean axioms `x² - x`).
-/

namespace Programme.«20261029-1156-proof-complexity».StdPCExact

open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261029-1156-proof-complexity».StdPC Programme.«20261029-1156-proof-complexity».StdPCConv

/-- For prime `p`, `p ∤ c` and `n ≥ 2p - 3`: standard PC over `F_p` refutes onto-FPHP^{n+pc}_n
in degree `D` iff `D ≥ p`. -/
theorem std_pc_degree_exact {p c : Nat} (hp : Programme.«20261027-0607-proof-complexity».Peel.IsPrime p)
    (hc : ¬ p ∣ c) (n : Nat) (hn : 2 * p - 3 ≤ n) (D : Nat) :
    Refutes p (ontoFPHP n (p * c)) D ↔ p ≤ D := by
  rw [refutes_iff hp.1]
  exact Programme.«20261027-0607-proof-complexity».Lucas.pc_degree_exact hp hc n hn D

/-- Over `F_2`, for `n ≥ 5`: standard PC refutes onto-FPHP^{n+4}_n in degree `D` iff `D ≥ 4`. -/
theorem std_f2_k4_exact (n D : Nat) (hn : 5 ≤ n) : Refutes 2 (ontoFPHP n 4) D ↔ 4 ≤ D := by
  rw [refutes_iff (by decide)]
  exact Programme.«20261025-1627-proof-complexity».OntoF2K4.f2_k4_exact n D hn

/-- Over `F_3`, for `n ≥ 3`: standard PC refutes onto-FPHP^{n+3}_n in degree `D` iff `D ≥ 3`. -/
theorem std_f3_k3_exact (n D : Nat) (hn : 3 ≤ n) : Refutes 3 (ontoFPHP n 3) D ↔ 3 ≤ D := by
  rw [refutes_iff (by decide)]
  exact Programme.«20261025-0459-proof-complexity».OntoLucas.f3_k3_exact n D hn

end Programme.«20261029-1156-proof-complexity».StdPCExact

#print axioms Programme.«20261029-1156-proof-complexity».StdPCExact.std_pc_degree_exact
#print axioms Programme.«20261029-1156-proof-complexity».StdPCExact.std_f2_k4_exact
#print axioms Programme.«20261029-1156-proof-complexity».StdPCExact.std_f3_k3_exact
