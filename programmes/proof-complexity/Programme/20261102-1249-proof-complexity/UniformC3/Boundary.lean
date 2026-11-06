import Programme.«20261102-1249-proof-complexity».UniformC3.Lift

namespace Programme.«20261102-1249-proof-complexity».UniformC3
open Programme.«20261026-1402-proof-complexity».ExtLemma
open Programme.«20261026-1402-proof-complexity».ExtLin
open Programme.«20261026-1402-proof-complexity».SymDesign
open Programme.«20261025-0459-proof-complexity».OntoFPHP (rsum var ontoFPHP PPCRefutation)
open Programme.«20261025-0459-proof-complexity».OntoSubst (rsum_congr)
open Programme.«20261025-1627-proof-complexity».MomGen (canon)
open Programme.«20261025-1627-proof-complexity».OntoExt2 (var_lt)
open Programme.«20261027-0607-proof-complexity».Peel (IsPrime)

/-- Intermediate output of the square-to-rectangle transfer, not the external input. -/
structure RectangularLift (p k : Nat) where
  coeff : List Nat → Int
  unit : ∀ g, CM (2*p-1) k g → g.length = p → (p : Int) ∣ coeff g - 1
  harmonic : ∀ g, CM (2*p-1) k g → g.length = p-1 →
    (∀ i < 2*p-1+k, pfree (2*p-1) g i → rowS (2*p-1) k coeff g i = 0) ∧
    (∀ j < 2*p-1, hfree (2*p-1) g j → colS (2*p-1) k coeff g j = 0)

def RectangularLift.top {p k : Nat} (H : RectangularLift p k) (g : List Nat) : Int :=
  (H.coeff g - 1) / (p : Int)

theorem cm_extend {n k : Nat} {g : List Nat} (hg : CM n k g) {v : Nat}
    (hv : v < (n+k)*n) (hnot : v ∉ g) (hm : isMatch n (v::g) = true) :
    CM n k (canon ((n+k)*n) (v::g)) ∧
      (canon ((n+k)*n) (v::g)).length = g.length+1 := by
  have hb : ∀ x ∈ v::g, x < (n+k)*n := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hv
    · exact CM_lt hg hx
  refine ⟨⟨canon_idem _, ?_⟩, ?_⟩
  · rw [isMatch_congr n _ _ (mem_canon' hb)]
    exact hm
  · simpa using canon_len_eq (List.nodup_cons.mpr ⟨hnot, CM_nodup hg⟩) hb

theorem RectangularLift.coeff_eq {p k : Nat} (H : RectangularLift p k)
    {g : List Nat} (hg : CM (2*p-1) k g) (hl : g.length = p) :
    H.coeff g = 1 + (p : Int) * H.top g := by
  have h := Int.mul_ediv_cancel' (H.unit g hg hl)
  unfold RectangularLift.top
  omega

theorem RectangularLift.line_eq {p k : Nat} (H : RectangularLift p k)
    (hp : 1 < p) {g : List Nat} (hg : CM (2*p-1) k g) (hl : g.length = p-1)
    (v : Nat → Nat) (M : Nat)
    (hv : ∀ t < M, v t < (2*p-1+k)*(2*p-1))
    (hf : ∀ t < M, v t ∉ g) :
    lineS (2*p-1) k H.coeff g v M =
      lineS (2*p-1) k (fun _ => 1) g v M +
        (p : Int) * lineS (2*p-1) k H.top g v M := by
  rw [← lineS_smul, ← lineS_add]
  unfold lineS
  apply rsum_congr
  intro t ht
  split
  · rename_i hm
    have he := cm_extend hg (hv t ht) (hf t ht) hm
    exact H.coeff_eq he.1 (by omega)
  · rfl

theorem RectangularLift.top_bal {p c : Nat} (hp : IsPrime p)
    (H : RectangularLift p (c*p*p)) :
    Bal p (2*p-1) (c*p*p) H.top (fun _ => -1) (p-1) := by
  have hp2 := hp.1
  have hn : 0 < 2*p-1 := by omega
  have hp0 : (p : Int) ≠ 0 := by omega
  intro g hg hl
  have hh := H.harmonic g hg hl
  have hncast : ((2*p-1 : Nat) : Int) - (g.length : Int) = p := by omega
  constructor
  · intro i hi hf
    have he := H.line_eq hp2 hg hl (fun j => var (2*p-1) i j) (2*p-1)
      (fun j hj => var_lt _ _ _ _ hi hj) (notin_of_pfree hf)
    change rowS _ _ _ _ _ = rowS _ _ _ _ _ + (p : Int) * rowS _ _ _ _ _ at he
    rw [hh.1 i hi hf, rowS_const hn _ hg hf, hncast, Int.mul_one] at he
    have hu : rowS (2*p-1) (c*p*p) H.top g i = -1 := by
      apply Int.eq_of_mul_eq_mul_left hp0
      rw [Int.mul_neg, Int.mul_one]
      omega
    rw [hu, Int.sub_self]
    exact Int.dvd_zero _
  · intro j hj hf
    have he := H.line_eq hp2 hg hl (fun i => var (2*p-1) i j) (2*p-1+c*p*p)
      (fun i hi => var_lt _ _ _ _ hi hj) (fun i _ => notin_of_hfree hf i hj)
    change colS _ _ _ _ _ = colS _ _ _ _ _ + (p : Int) * colS _ _ _ _ _ at he
    rw [hh.2 j hj hf, colS_const hn _ hg hj hf, Int.mul_one] at he
    have hc : (((2*p-1+c*p*p : Nat) : Int) - g.length) =
        (p : Int) + (c : Int)*(p : Int)*(p : Int) := by
      push_cast
      omega
    rw [hc] at he
    have hu : colS (2*p-1) (c*p*p) H.top g j = -1 - (c : Int)*(p : Int) := by
      apply Int.eq_of_mul_eq_mul_left hp0
      rw [Int.mul_sub, Int.mul_neg, Int.mul_one]
      simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] at he ⊢
      omega
    rw [hu]
    refine ⟨-(c : Int), ?_⟩
    simp only [Int.mul_neg, Int.mul_comm]
    omega

theorem unit_design_of_rectangular_lift {p c : Nat} (hp : IsPrime p)
    (H : RectangularLift p (c*p*p)) :
    ∃ T : List Nat → Int,
      (∀ e ≤ p-1, Bal p (2*p-1) (c*p*p) T T e) ∧ (p : Int) ∣ T [] - 1 := by
  have hp2 := hp.1
  have hk : p ∣ c*p*p := ⟨c*p, Nat.mul_comm _ _⟩
  obtain ⟨T, ht0, ht⟩ :=
    Programme.«20261030-0634-proof-complexity».FactorBoundary.design_of_top
      (by omega : 0 < 2*p-1) hk H.top (H.top_bal hp)
  obtain ⟨u, hu⟩ := Programme.«20261030-0634-proof-complexity».FactorUnit.empty_unit hp
  refine ⟨fun g => u * T g, fun e he => Bal_smul u (ht e he), ?_⟩
  change (p : Int) ∣ u * T [] - 1
  rw [ht0]
  exact hu

theorem no_refutation_of_rectangular_lift {p c : Nat} (hp : IsPrime p)
    (H : RectangularLift p (c*p*p)) (n : Nat) (hn : 2*p-1 ≤ n) :
    ¬ PPCRefutation p (ontoFPHP n (c*p*p)) p := by
  obtain ⟨T, hT, h1⟩ := unit_design_of_rectangular_lift hp H
  exact Programme.«20261027-0607-proof-complexity».VUnit.no_refutation_of_unit
    hp ⟨c*p, Nat.mul_comm _ _⟩ (Nat.le_refl _) T hT h1 n hn

#print axioms unit_design_of_rectangular_lift
#print axioms no_refutation_of_rectangular_lift
end Programme.«20261102-1249-proof-complexity».UniformC3
