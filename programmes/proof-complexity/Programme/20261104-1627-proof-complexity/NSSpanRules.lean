import Programme.«20261104-1627-proof-complexity».InvariantAssembly
import Programme.«20261025-1627-proof-complexity».NoDrop
namespace Programme.«20261104-1627-proof-complexity».NSSpanRules
open Programme.«20261024-1633-proof-complexity».NS
open Programme.«20261024-1633-proof-complexity».PCTseitin
open Programme.«20261029-1156-proof-complexity».StdPC
open Programme.«20261025-1627-proof-complexity».NoDrop
open Programme.«20261104-1627-proof-complexity».InvariantAssembly
/-- Canonical matching-quotient NS span pulled back to ordinary polynomials. -/
def W (p : Nat) (A : List (Poly Nat)) (e : Nat) (P : Poly Nat) : Prop :=
  NSIn p A e (fun a => P.eval a)
theorem rules (p D : Nat) (A : List (Poly Nat)) : SpanRules p D A (W p A) where
  axiom_mem := fun _ h hd => nsIn_ax h hd
  boolean_mem := by
    intro x _
    refine ⟨[], by simp, ?_⟩
    intro a _
    simp [eval_boolAx]
  linear_mem := by
    intro u v P Q hP hQ
    exact nsIn_congr (nsIn_lin u v hP hQ) (fun a => by
      rw [eval_lc, Int.sub_self]; exact Int.dvd_zero _)
  equal_mem := fun _ _ h he _ => nsIn_congr h (peq_eval he)
  multiply_mem := by
    intro x P h hd
    exact nsIn_congr (nsIn_xmul x h (by omega)) (fun a => by
      rw [eval_mulVar]
      simp [xv])
/-- Canonical NoDrop and unit exclusion remain explicit obligations. -/
def invariant {p D : Nat} {A : List (Poly Nat)}
    (nd : NoDrop p A D) (unit : ¬ NSIn p A D (fun _ => 1)) :
    Programme.«20261102-0635-proof-complexity».StepSix.Invariant p D A where
  top := W p A D
  lower := W p A (D - 1)
  axiom_mem := (rules p D A).axiom_mem
  boolean_mem := (rules p D A).boolean_mem
  linear_mem := (rules p D A).linear_mem
  equal_mem := (rules p D A).equal_mem
  multiply_mem := (rules p D A).multiply_mem
  nodrop := by
    intro P h hd
    exact nd _ h ⟨P, hd, fun a => by simp⟩
  unit := by
    intro h
    apply unit
    exact nsIn_congr h (fun a => by rw [eval_one]; simp)
end Programme.«20261104-1627-proof-complexity».NSSpanRules
#print axioms Programme.«20261104-1627-proof-complexity».NSSpanRules.rules
#print axioms Programme.«20261104-1627-proof-complexity».NSSpanRules.invariant
