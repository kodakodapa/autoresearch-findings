import Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour
import Programme.«20261104-1627-proof-complexity».RectangularOne
namespace Programme.«20261104-1627-proof-complexity».RemainingSpanning
open Programme.«20261104-1627-proof-complexity».MatchingLabels
open Programme.«20261025-0459-proof-complexity».OntoFPHP
open Programme.«20261029-1156-proof-complexity».StdPC

theorem levels {n k : Nat} (hn : 7 ≤ n)
    (s2 : Spanning 3 (n+k) n 2) (s3 : Spanning 3 (n+k) n 3)
    (s4 : Spanning 3 (n+k) n 4) :
    ∀ r, 0 < r → r ≤ 4 → Spanning 3 (n+k) n r := by
  intro r hr h4
  have cases : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases cases with h | h | h | h
  · subst r; exact spanning_one (by omega) (by omega)
  · subst r; exact s2
  · subst r; exact s3
  · subst r; exact s4

def invariant {n k : Nat} (hk : 9 ∣ k) (hn : 7 ≤ n)
    (s2 : Spanning 3 (n+k) n 2) (s3 : Spanning 3 (n+k) n 3)
    (s4 : Spanning 3 (n+k) n 4) :
    Programme.«20261102-0635-proof-complexity».StepSix.Invariant 3 4 (ontoFPHP n k) :=
  Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.invariant hk hn (levels hn s2 s3 s4)

theorem no_stdpc_le {n k d : Nat} (hk : 9 ∣ k) (hn : 7 ≤ n)
    (s2 : Spanning 3 (n+k) n 2) (s3 : Spanning 3 (n+k) n 3)
    (s4 : Spanning 3 (n+k) n 4) (hd : d ≤ 4) :
    ¬ Refutes 3 (ontoFPHP n k) d := by
  intro h
  exact Programme.«20261102-0635-proof-complexity».StepSix.no_refutation
    (invariant hk hn s2 s3 s4) (Programme.«20261104-1627-proof-complexity».InvariantAssembly.der_mono hd h)
end Programme.«20261104-1627-proof-complexity».RemainingSpanning
#print axioms Programme.«20261104-1627-proof-complexity».RemainingSpanning.invariant
#print axioms Programme.«20261104-1627-proof-complexity».RemainingSpanning.no_stdpc_le
