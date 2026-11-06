import Peer.pr.UniformC3.Unconditional

namespace Work.SkReproof
open Peer.pr.UniformC3
open Peer.pr.UniformC3.Block
open Programme.«20261027-0607-proof-complexity».Peel (IsPrime)
open Programme.«20261026-1402-proof-complexity».ExtLemma (Bal)
open Programme.«20261025-0459-proof-complexity».OntoFPHP (ontoFPHP PPCRefutation)
open Programme.«20261029-1156-proof-complexity».StdPC (Refutes refutes_ppc)

-- Rebuild the certificate; no call to any of the six claimed theorems.
theorem lift (p : Nat) (hp : IsPrime p) : SquareLiftAssumption p := by
  have hp2 : 2 ≤ p := by have := hp.1; omega
  obtain ⟨u,hu⟩ := commonValue_unit hp
  let P := squarePartition p (by omega)
  let C : Certificate p P := {
    value := fun M => u * explicitValue p M
    unit := by
      intro M hM hlen
      exact cong_trans (cong_scale (explicit_common_congruence hp2 hM hlen) u) hu
    row := by
      intro M hM hlen i
      have h := explicit_row hp2 hM hlen i
      change sum3 (fun j => ((capacity p j : Int)-cc M j) * (u*explicitValue p (inc M i j))) = 0
      calc
        _ = u * sum3 (fun j => ((capacity p j : Int)-cc M j) * explicitValue p (inc M i j)) := by
          simp [sum3, Int.mul_add, Int.mul_assoc, Int.mul_left_comm]
        _ = 0 := by rw [h, Int.mul_zero]
    col := by
      intro M hM hlen j
      have h := explicit_col hp2 hM hlen j
      change sum3 (fun i => ((capacity p i : Int)-rc M i) * (u*explicitValue p (inc M i j))) = 0
      calc
        _ = u * sum3 (fun i => ((capacity p i : Int)-rc M i) * explicitValue p (inc M i j)) := by
          simp [sum3, Int.mul_add, Int.mul_assoc, Int.mul_left_comm]
        _ = 0 := by rw [h, Int.mul_zero]
  }
  exact ⟨C.toIntegralLift hp2 P⟩

theorem design {p : Nat} (hp : IsPrime p) (c : Nat) :
    ∃ T : List Nat → Int, (∀ e ≤ p-1, Bal p (2*p-1) (c*p*p) T T e) ∧
      (p : Int) ∣ T [] - 1 := by
  obtain ⟨H⟩ := lift p hp
  let R := rectangleFromSquare hp H c
  have hk : p ∣ c*p*p := ⟨c*p, Nat.mul_comm _ _⟩
  obtain ⟨T,h0,hbal⟩ :=
    Programme.«20261030-0634-proof-complexity».FactorBoundary.design_of_top
      (by have := hp.1; omega : 0 < 2*p-1) hk R.top (R.top_bal hp)
  obtain ⟨u,hu⟩ := Programme.«20261030-0634-proof-complexity».FactorUnit.empty_unit hp
  refine ⟨fun g => u*T g, ?_, ?_⟩
  · intro e he
    exact Programme.«20261026-1402-proof-complexity».ExtLin.Bal_smul u (hbal e he)
  · change (p : Int) ∣ u*T [] - 1
    rw [h0]
    exact hu

theorem ppc {p : Nat} (hp : IsPrime p) (c n : Nat) (hn : 2*p-1 ≤ n) :
    ¬ PPCRefutation p (ontoFPHP n (c*p*p)) p := by
  obtain ⟨T,hT,hunit⟩ := design hp c
  have hnonzero : ¬ (p : Int) ∣ T [] := by
    intro hzero
    have hone : (p : Int) ∣ 1 := by
      have := Int.dvd_sub hzero hunit
      have he : T [] - (T [] - 1) = 1 := by omega
      rwa [he] at this
    have := Int.le_of_dvd (by decide : (0 : Int) < 1) hone
    have := hp.1
    omega
  exact Programme.«20261027-0607-proof-complexity».PeelV.no_deg_p_of_design hp
    (show p ∣ c*p*p from ⟨c*p, Nat.mul_comm _ _⟩) (Nat.le_refl _) hT hnonzero n hn

theorem standard {p : Nat} (hp : IsPrime p) (c n : Nat) (hn : 2*p-1 ≤ n) :
    ¬ Refutes p (ontoFPHP n (c*p*p)) p := by
  intro h
  exact ppc hp c n hn (refutes_ppc hp.1 h)

theorem two (c n : Nat) (hn : 3 ≤ n) :
    ¬ Refutes 2 (ontoFPHP n (c*2*2)) 2 := by
  exact standard isPrime2 c n hn

theorem three (c n : Nat) (hn : 5 ≤ n) :
    ¬ Refutes 3 (ontoFPHP n (c*3*3)) 3 := by
  exact standard isPrime3 c n hn

#print axioms lift
#print axioms design
#print axioms ppc
#print axioms standard
#print axioms two
#print axioms three
end Work.SkReproof

-- These proof equalities typecheck only with definitionally equal theorem types.
example : @Work.SkReproof.lift = @Peer.pr.UniformC3.squareLiftAssumption := Subsingleton.elim _ _
example : @Work.SkReproof.design = @Peer.pr.UniformC3.uniform_unit_design_unconditional := Subsingleton.elim _ _
example : @Work.SkReproof.ppc = @Peer.pr.UniformC3.uniform_no_degree_p_unconditional := Subsingleton.elim _ _
example : @Work.SkReproof.standard = @Peer.pr.UniformC3.uniform_no_standard_degree_p_unconditional := Subsingleton.elim _ _
example : @Work.SkReproof.two = @Peer.pr.UniformC3.no_standard_degree_two := Subsingleton.elim _ _
example : @Work.SkReproof.three = @Peer.pr.UniformC3.no_standard_degree_three := Subsingleton.elim _ _
