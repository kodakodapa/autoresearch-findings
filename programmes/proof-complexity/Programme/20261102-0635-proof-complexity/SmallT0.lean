import Programme.«20261102-0635-proof-complexity».SquareTwo
import Programme.«20261030-0634-proof-complexity».FactorBoundary
import Programme.«20261027-0607-proof-complexity».VUnit
import Programme.«20261029-1156-proof-complexity».StdPCExact

namespace Programme.«20261102-0635-proof-complexity».SmallT0
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261030-0634-proof-complexity»
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- All three-pigeon subsets, in increasing order. -/
def triples : List (List Nat) :=
  (List.range 7).flatMap fun a => (List.range 7).flatMap fun b =>
    (List.range 7).filterMap fun c => if a < b ∧ b < c then some [a,b,c] else none
/-- Signed square functional after relabelling the selected pigeons in order. -/
def squareValue (s g : List Nat) : Int :=
  if g.all (fun v => s.contains (v / 3)) then
    let m := (g.map fun v => 2^(3 * (s.filter (fun i => i < v/3)).length + v%3)).sum
    ((List.finRange 18).map fun j => if Programme.«20261102-0635-proof-complexity».SquareTwo.mask j = m then
      Programme.«20261102-0635-proof-complexity».SquareTwo.sign j else 0).sum
  else 0
/-- Rectangular subset transfer of the signed 3 by 3 square functional. -/
def K (g : List Nat) : Int := (triples.map (fun s => squareValue s g)).sum
def U (g : List Nat) : Int := (K g - 1) / 2

def Check (a : Fin 21) : Prop :=
  (∀ i : Fin 7, pfree 3 [a.val] i.val →
    (2 : Int) ∣ rowS 3 4 U [a.val] i.val + 1) ∧
  (∀ j : Fin 3, hfree 3 [a.val] j.val →
    (2 : Int) ∣ colS 3 4 U [a.val] j.val + 1)
instance (a : Fin 21) : Decidable (Check a) := by
  unfold Check pfree hfree
  infer_instance
 theorem checks : ∀ a : Fin 21, Check a := by decide
 theorem top_bal : Bal 2 3 4 U (fun _ => -1) 1 := by
  intro g hg hl
  obtain ⟨a, rfl⟩ : ∃ a, g = [a] := by
    match g, hl with
    | [a], _ => exact ⟨a, rfl⟩
  have ha : a < 21 := CM_lt hg (by simp)
  obtain ⟨hr, hc⟩ := checks ⟨a, ha⟩
  exact ⟨fun i hi hf => hr ⟨i, hi⟩ hf, fun j hj hf => hc ⟨j, hj⟩ hf⟩
/-- Explicit splice, with empty value -3 (hence residue one). -/
def T0 : List Nat → Int := TopSplice.splice 1 (FactorBoundary.lower 3 1) U
 theorem balanced : ∀ e ≤ 1, Bal 2 3 4 T0 T0 e := by
  apply TopSplice.splice_bal 2 3 4 1 (FactorBoundary.lower 3 1) U (fun _ => -1)
  · intro e he
    exact FactorBoundary.lower_bal (by decide) (by decide) he
  · intro g _ hl
    exact (FactorBoundary.lower_top 3 1 g hl).symm
  · exact top_bal
 theorem empty_value : T0 [] = -3 := by decide
 theorem unit : (2 : Int) ∣ T0 [] - 1 := by rw [empty_value]; decide
theorem no_degree_two (n : Nat) (hn : 3 ≤ n) :
    ¬ Programme.«20261029-1156-proof-complexity».StdPC.Refutes 2
      (Programme.«20261025-0459-proof-complexity».OntoFPHP.ontoFPHP n 4) 2 := by
  apply Programme.«20261029-1156-proof-complexity».StdPC.not_refutes (by decide)
  have hp : Programme.«20261027-0607-proof-complexity».Peel.IsPrime 2 :=
    ⟨Nat.le_refl 2, fun a ha => by
      have := Nat.le_of_dvd (by decide : 0 < 2) ha
      rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with h | h | h <;>
        subst h <;> simp_all⟩
  exact Programme.«20261027-0607-proof-complexity».VUnit.no_refutation_of_unit
    hp (by decide) (by decide) T0 balanced unit n hn
end Programme.«20261102-0635-proof-complexity».SmallT0
#print axioms Programme.«20261102-0635-proof-complexity».SmallT0.balanced
#print axioms Programme.«20261102-0635-proof-complexity».SmallT0.empty_value
#print axioms Programme.«20261102-0635-proof-complexity».SmallT0.unit

#print axioms Programme.«20261102-0635-proof-complexity».SmallT0.no_degree_two
