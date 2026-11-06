import Programme.«20261104-1627-proof-complexity».ZTwoCoordinates

namespace Programme.«20261104-1627-proof-complexity».AnchoredColumnNormalize
open Programme.«20261104-1627-proof-complexity».MatchingLabels Programme.«20261104-1627-proof-complexity».MixedAggregate Programme.«20261104-1627-proof-complexity».MixedEliminate

def d0 (v : Vector) (a : Nat) : Int :=
  vectorCoeff v (edgeColLabel a 2 0) - vectorCoeff v (edgeColLabel a 1 0)
def d2 (v : Vector) (a : Nat) : Int :=
  vectorCoeff v (edgeColLabel a 1 2) - vectorCoeff v (edgeColLabel a 0 2)

theorem single_col (i j a b r : Nat) (hi : i < 3) (hj : j < 3)
    (ha : a < 3) (hb : b < 3) (hr : r < 3) :
    vectorCoeff (z 3 3 1 [(i,j)]) (edgeColLabel a b r) =
      if a = i ∧ b = j ∧ r ≠ j then -1 else 0 := by
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  have hr' : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hi' with rfl | rfl | rfl
  all_goals rcases hj' with rfl | rfl | rfl
  all_goals rcases ha' with rfl | rfl | rfl
  all_goals rcases hb' with rfl | rfl | rfl
  all_goals rcases hr' with rfl | rfl | rfl
  all_goals decide +kernel

def corrections (v : Vector) : List (Int × Vector) :=
  (List.range 3).flatMap fun a =>
    [(-(d2 v a + d0 v a), z 3 3 1 [(a,0)]), (-d0 v a, z 3 3 1 [(a,1)])]
def normalized (v : Vector) : Vector := v ++ combine (corrections v)

theorem normalized_col (v : Vector) (a b r : Nat)
    (ha : a < 3) (hb : b < 3) (hr : r < 3) :
    vectorCoeff (normalized v) (edgeColLabel a b r) =
      vectorCoeff v (edgeColLabel a b r) +
      (if b = 0 ∧ r ≠ 0 then d2 v a + d0 v a else 0) +
      (if b = 1 ∧ r ≠ 1 then d0 v a else 0) := by
  rw [normalized, vectorCoeff_append, coeff_combine]
  simp only [corrections, show List.range 3 = [0,1,2] by rfl,
    List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [single_col 0 0 a b r (by omega) (by omega) ha hb hr,
    single_col 0 1 a b r (by omega) (by omega) ha hb hr,
    single_col 1 0 a b r (by omega) (by omega) ha hb hr,
    single_col 1 1 a b r (by omega) (by omega) ha hb hr,
    single_col 2 0 a b r (by omega) (by omega) ha hb hr,
    single_col 2 1 a b r (by omega) (by omega) ha hb hr]
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  have hr' : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases ha' with rfl | rfl | rfl
  all_goals rcases hb' with rfl | rfl | rfl
  all_goals rcases hr' with rfl | rfl | rfl
  all_goals simp <;> omega

/-- Zero triangle circulation is enough after the two local anchored corrections. -/
theorem normalized_independent (v : Vector)
    (ht : ∀ a < 3, (3 : Int) ∣ circulation v a 0 1 2) :
    ∀ a < 3, ∀ r < 3, ∀ b < 3, b ≠ r →
      (3 : Int) ∣ vectorCoeff (normalized v) (edgeColLabel a b r) -
        vectorCoeff (normalized v) (edgeColLabel a (anchor r) r) := by
  intro a ha r hr b hb hbr
  have h := ht a ha
  obtain ⟨q,hq⟩ := h
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  have hr' : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hr' with rfl | rfl | rfl
  all_goals rcases hb' with rfl | rfl | rfl
  all_goals simp only [anchor, ite_true, show ¬(1 : Nat) = 0 by omega,
    show ¬(2 : Nat) = 0 by omega, ite_false]
  all_goals try omega
  all_goals rw [normalized_col v _ _ _ ha (by omega) (by omega),
    normalized_col v _ _ _ ha (by omega) (by omega)]
  all_goals simp only [d0, d2, circulation] at hq ⊢
  all_goals simp at hq ⊢
  all_goals first | exact ⟨q, by omega⟩ | exact ⟨-q, by omega⟩ | exact ⟨0, by omega⟩


theorem single_kernel (p a b : Nat) (ha : a < 3) (hb : b < 3) :
    Kernel p 3 3 2 (z 3 3 1 [(a,b)]) := by
  apply z_base_one_kernel p [(a,b)]
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  rcases ha' with rfl | rfl | rfl
  all_goals rcases hb' with rfl | rfl | rfl
  all_goals decide +kernel

theorem single_generator (a b : Nat) (ha : a < 3) (hb : b < 3) :
    z 3 3 1 [(a,b)] ∈ syzygies 3 3 2 := by
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  rcases ha' with rfl | rfl | rfl
  all_goals rcases hb' with rfl | rfl | rfl
  all_goals decide +kernel

theorem corrections_generators (v : Vector) :
    ∀ t ∈ corrections v, t.2 ∈ syzygies 3 3 2 := by
  intro t ht
  obtain ⟨a,ha,ht⟩ := List.mem_flatMap.mp ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  all_goals exact single_generator a _ (List.mem_range.mp ha) (by omega)

theorem normalized_kernel {p : Nat} (v : Vector) (hv : Kernel p 3 3 2 v) :
    Kernel p 3 3 2 (normalized v) := by
  apply kernel_append hv
  apply kernel_combine
  intro t ht
  obtain ⟨a,ha,ht⟩ := List.mem_flatMap.mp ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  all_goals exact single_kernel p a _ (List.mem_range.mp ha) (by omega)

/-- The explicit cc correction followed by anchored single-edge corrections
has the exact column-independence hypothesis required by MixedEliminate. -/
theorem corrected_independent (v : Vector) (hv : Kernel 3 3 3 2 v) :
    ∀ a < 3, ∀ r < 3, ∀ b < 3, b ≠ r →
      (3 : Int) ∣ vectorCoeff (normalized (Programme.«20261104-1627-proof-complexity».CCNormalize.corrected 3 v))
        (edgeColLabel a b r) -
        vectorCoeff (normalized (Programme.«20261104-1627-proof-complexity».CCNormalize.corrected 3 v))
          (edgeColLabel a (anchor r) r) := by
  exact normalized_independent _ (Programme.«20261104-1627-proof-complexity».CCNormalize.corrected_triangle v hv)

theorem corrected_kernel (v : Vector) (hv : Kernel 3 3 3 2 v) :
    Kernel 3 3 3 2 (normalized (Programme.«20261104-1627-proof-complexity».CCNormalize.corrected 3 v)) := by
  exact normalized_kernel _ (Programme.«20261104-1627-proof-complexity».CCNormalize.corrected_kernel v hv)

theorem corrected_residual_columns (v : Vector) (hv : Kernel 3 3 3 2 v) :
    ∀ a < 3, ∀ b < 3, ∀ r < 3, b ≠ r →
      (3 : Int) ∣ vectorCoeff
        (residual 3 3 (normalized (Programme.«20261104-1627-proof-complexity».CCNormalize.corrected 3 v)))
          (edgeColLabel a b r) := by
  exact residual_columns (by omega) _ (corrected_independent v hv)


def allCorrections (v : Vector) : List (Int × Vector) :=
  (-circulation v 0 0 1 2, cc 3 [] 0 1) ::
    corrections (Programme.«20261104-1627-proof-complexity».CCNormalize.corrected 3 v)

theorem allCorrections_generators (v : Vector) :
    ∀ t ∈ allCorrections v, t.2 ∈ syzygies 3 3 2 := by
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · change cc 3 [] 0 1 ∈ syzygies 3 3 2
    decide +kernel
  · exact corrections_generators _ t ht

theorem normalized_eq (v : Vector) :
    normalized (Programme.«20261104-1627-proof-complexity».CCNormalize.corrected 3 v) = v ++ combine (allCorrections v) := by
  change (v ++ _) ++ _ = v ++ (_ ++ _)
  exact List.append_assoc _ _ _

/-- Complete certificate of the assigned column-normalization step. -/
theorem column_normalization (v : Vector) (hv : Kernel 3 3 3 2 v) :
    ∃ c : List (Int × Vector),
      (∀ t ∈ c, t.2 ∈ syzygies 3 3 2) ∧
      Kernel 3 3 3 2 (v ++ combine c) ∧
      (∀ a < 3, ∀ r < 3, ∀ b < 3, b ≠ r →
        (3 : Int) ∣ vectorCoeff (v ++ combine c) (edgeColLabel a b r) -
          vectorCoeff (v ++ combine c) (edgeColLabel a (anchor r) r)) := by
  refine ⟨allCorrections v, allCorrections_generators v, ?_, ?_⟩
  · rw [← normalized_eq]; exact corrected_kernel v hv
  · rw [← normalized_eq]; exact corrected_independent v hv

end Programme.«20261104-1627-proof-complexity».AnchoredColumnNormalize
#print axioms Programme.«20261104-1627-proof-complexity».AnchoredColumnNormalize.normalized_independent

#print axioms Programme.«20261104-1627-proof-complexity».AnchoredColumnNormalize.corrections_generators
#print axioms Programme.«20261104-1627-proof-complexity».AnchoredColumnNormalize.corrected_independent
#print axioms Programme.«20261104-1627-proof-complexity».AnchoredColumnNormalize.corrected_kernel
#print axioms Programme.«20261104-1627-proof-complexity».AnchoredColumnNormalize.corrected_residual_columns

#print axioms Programme.«20261104-1627-proof-complexity».AnchoredColumnNormalize.column_normalization
