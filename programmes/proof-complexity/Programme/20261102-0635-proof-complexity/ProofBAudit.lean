import Programme.«20261027-0607-proof-complexity».VUnit
import Programme.«20261030-0634-proof-complexity».P3Top
namespace Programme.«20261102-0635-proof-complexity».ProofBAudit
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261027-0607-proof-complexity».Peel (IsPrime)
open Programme.«20261025-0459-proof-complexity».OntoFPHP (ontoFPHP PPCRefutation)
/-- Missing existence statement; this definition asserts no theorem. -/
def UnitDesign (p c : Nat) : Prop :=
  ∃ T : List Nat → Int, (p : Int) ∣ T [] - 1 ∧
    ∀ e ≤ p - 1, Bal p (2*p-1) (c*p*p) T T e
def UniformBridgeConjecture : Prop :=
  ∀ p c : Nat, IsPrime p → 1 ≤ c → UnitDesign p c
theorem consequence {p c : Nat} (hp : IsPrime p) (h : UnitDesign p c)
    (n : Nat) (hn : 2*p-1 ≤ n) :
    ¬ PPCRefutation p (ontoFPHP n (c*p*p)) p := by
  obtain ⟨T, h1, hT⟩ := h
  exact Programme.«20261027-0607-proof-complexity».VUnit.no_refutation_of_unit
    hp (Nat.dvd_mul_left p (c*p)) (Nat.le_refl _) T hT h1 n hn
/-- Existing library instance; not a verification of the new square lift. -/
theorem instance3 : UnitDesign 3 1 := by
  obtain ⟨T, ht, hb⟩ := Programme.«20261030-0634-proof-complexity».P3Top.design
  refine ⟨T, ?_, hb⟩
  rw [ht]
  decide
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- p=2,c=1 residues from the supplied square-subset construction. -/
def top2 (g : List Nat) : Int :=
  if (g.map (fun v => 2^v)).sum ∈ [10, 20, 33, 68, 80, 129, 160, 258, 264, 514, 544, 640, 1028, 1032, 1280, 2049, 2064, 2112, 4100, 4112, 4352, 5120, 8193, 8224, 8256, 10240, 16386, 16392, 16512, 16896, 32770, 32800, 32896, 34816, 40960, 65540, 65544, 65792, 66048, 81920, 131073, 131088, 131136, 132096, 135168, 262148, 262160, 262400, 263168, 278528, 327680, 524289, 524320, 524352, 526336, 528384, 655360, 1048578, 1048584, 1048704, 1049088, 1056768, 1081344] then 1 else 0
def Check2 (a : Fin 21) : Prop :=
  (∀ i : Fin 7, pfree 3 [a.val] i.val →
    (2 : Int) ∣ rowS 3 4 top2 [a.val] i.val + 1) ∧
  (∀ j : Fin 3, hfree 3 [a.val] j.val →
    (2 : Int) ∣ colS 3 4 top2 [a.val] j.val + 1)
instance (a : Fin 21) : Decidable (Check2 a) := by
  unfold Check2 pfree hfree
  infer_instance
theorem checks2 : ∀ a : Fin 21, Check2 a := by decide
theorem top2_bal : Bal 2 3 4 top2 (fun _ => -1) 1 := by
  intro g hg hl
  obtain ⟨a, rfl⟩ : ∃ a, g = [a] := by
    match g, hl with
    | [a], _ => exact ⟨a, rfl⟩
  have ha : a < 21 := CM_lt hg (by simp)
  obtain ⟨hr, hc⟩ := checks2 ⟨a, ha⟩
  constructor
  · intro i hi hf
    exact hr ⟨i, hi⟩ hf
  · intro j hj hf
    exact hc ⟨j, hj⟩ hf
theorem instance2 : UnitDesign 2 1 := by
  obtain ⟨T, ht, hb⟩ :=
    Programme.«20261030-0634-proof-complexity».FactorBoundary.design_of_top
      (by decide : 0 < 3) (by decide : 2 ∣ 4) top2 top2_bal
  refine ⟨T, ?_, hb⟩
  rw [ht]
  decide
#print axioms consequence
#print axioms instance2
#print axioms instance3
end Programme.«20261102-0635-proof-complexity».ProofBAudit
