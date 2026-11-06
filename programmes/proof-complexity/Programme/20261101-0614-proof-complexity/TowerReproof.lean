import Programme.«20261101-0614-proof-complexity».FamilyRestriction
namespace Programme.«20261101-0614-proof-complexity».TowerReproof
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity».Composition

/-- Descend on the final number of outer rows, preserving the deficit. -/
theorem descend (B : Nat) : ∀ M N A L d : Nat,
    1 ≤ M → 2 ≤ N → 1 ≤ L → M ≤ B → A + M = B + N →
    Refutes (cnf B A L) d → Refutes (cnf M N L) d := by
  induction B with
  | zero => intro M N A L d hM hN hL hle; omega
  | succ B ih =>
    intro M N A L d hM hN hL hle he h
    by_cases hb : M = B+1
    · have ha : A = N := by omega
      simpa only [hb, ha] using h
    · have hmb : M ≤ B := by omega
      have ha : 1 ≤ A := by omega
      have hn : 2 ≤ A-1 := by omega
      have hp : Refutes (cnf B (A-1) L) d := by
        apply refutes_restrict B (A-1) L d (by omega) hn hL
        simpa only [Nat.sub_add_cancel ha] using h
      exact ih M N (A-1) L d hM hN hL hmb (by omega) hp

theorem lower_propagates (M N L d t : Nat)
    (hM : 1 ≤ M) (hN : 2 ≤ N) (hL : 1 ≤ L)
    (h : ¬ Refutes (cnf M N L) d) :
    ¬ Refutes (cnf (M+t) (N+t) L) d := by
  intro r
  exact h (descend (M+t) M N (N+t) L d hM hN hL (by omega) (by omega) r)
#print axioms descend
#print axioms lower_propagates
end Programme.«20261101-0614-proof-complexity».TowerReproof
